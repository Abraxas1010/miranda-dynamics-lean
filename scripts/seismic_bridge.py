#!/usr/bin/env python3
"""seismic_bridge.py

Fetch real-world seismic data bundles for HeytingLean's offline validator.

Primary services:
- USGS Earthquake Catalog (events; GeoJSON)
- EarthScope/IRIS FDSN Station (StationXML; station coordinates)
- EarthScope/IRIS FDSN Dataselect (waveforms; GeoCSV)
- IRISWS distaz + traveltime (distance/azimuth; ak135 travel time predictions)

Design goals:
- Minimal dependencies (stdlib-only; `requests` used if available).
- Cache downloads and pace requests.
- Output a single JSON bundle consumed by `seismic_validate_demo`.

Note: the detector itself is implemented in Lean (STA/LTA). This script only fetches/normalizes
data and provides an ak135 P-arrival prediction.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import json
import os
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET


def _http_get(url: str, *, timeout_sec: int = 30) -> bytes:
    """HTTP GET with an optional `requests` fast-path."""
    try:
        import requests  # type: ignore

        resp = requests.get(url, timeout=timeout_sec)
        resp.raise_for_status()
        return resp.content
    except Exception:
        req = urllib.request.Request(url, headers={"User-Agent": "HeytingLean-seismic-bridge"})
        with urllib.request.urlopen(req, timeout=timeout_sec) as r:
            return r.read()


def _mkdirp(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def _cache_read(path: str) -> bytes | None:
    try:
        with open(path, "rb") as f:
            return f.read()
    except FileNotFoundError:
        return None


def _cache_write(path: str, data: bytes) -> None:
    _mkdirp(os.path.dirname(path))
    with open(path, "wb") as f:
        f.write(data)


def _parse_iso8601_to_unix_ms(s: str) -> int:
    # USGS uses strings like "2026-01-21T12:34:56.789Z".
    # Also allow naive timestamps.
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    dt_obj = dt.datetime.fromisoformat(s)
    return int(dt_obj.timestamp() * 1000)


def _unix_ms_to_iso8601(ms: int) -> str:
    return dt.datetime.utcfromtimestamp(ms / 1000).replace(tzinfo=dt.timezone.utc).isoformat().replace(
        "+00:00", "Z"
    )


def build_station_url(
    base: str,
    *,
    network: str,
    station: str,
    level: str = "station",
    format: str = "xml",
) -> str:
    qs = {
        "net": network,
        "sta": station,
        "level": level,
        "format": format,
    }
    return base.rstrip("/") + "/fdsnws/station/1/query?" + urllib.parse.urlencode(qs)


def parse_stationxml_station(xml_bytes: bytes) -> dict:
    """Extract a station record (lat/lon/elev) from StationXML.

    This is intentionally minimal and assumes `level=station`.
    """
    root = ET.fromstring(xml_bytes)
    # StationXML uses namespaces.
    ns = {"s": root.tag.split("}")[0].strip("{")}
    sta = root.find(".//s:Station", ns)
    if sta is None:
        raise ValueError("StationXML: no <Station> element found")

    code = sta.attrib.get("code")
    lat = sta.findtext("s:Latitude", default="", namespaces=ns)
    lon = sta.findtext("s:Longitude", default="", namespaces=ns)
    elev = sta.findtext("s:Elevation", default="", namespaces=ns)

    if not code or not lat or not lon:
        raise ValueError("StationXML: missing station fields")

    net_el = root.find(".//s:Network", ns)
    net_code = net_el.attrib.get("code") if net_el is not None else ""

    return {
        "network": net_code,
        "code": code,
        "latitude": float(lat),
        "longitude": float(lon),
        "elevation_m": float(elev) if elev else 0.0,
    }


def build_dataselect_url(
    base: str,
    *,
    network: str,
    station: str,
    location: str,
    channel: str,
    starttime_iso: str,
    endtime_iso: str,
    format: str = "geocsv",
) -> str:
    qs = {
        "net": network,
        "sta": station,
        "loc": location,
        "cha": channel,
        "starttime": starttime_iso,
        "endtime": endtime_iso,
        "format": format,
    }
    return base.rstrip("/") + "/fdsnws/dataselect/1/query?" + urllib.parse.urlencode(qs)


def parse_geocsv_samples(geocsv_bytes: bytes, *, max_samples: int = 20000) -> dict:
    """Parse GeoCSV waveform response.

    GeoCSV is CSV with leading comment lines beginning with '#'.
    We extract the last numeric column as sample amplitudes, and attempt to parse a sample rate
    from timestamps if possible.
    """
    text = geocsv_bytes.decode("utf-8", errors="replace")
    header = None
    data_lines: list[str] = []
    for line in text.splitlines():
        if not line.strip():
            continue
        if line.startswith("#"):
            continue
        if header is None:
            header = [h.strip() for h in line.split(",")]
            continue
        data_lines.append(line)

    if header is None:
        raise ValueError("GeoCSV: missing header")

    # Determine sampling interval from the first two samples.
    if len(data_lines) < 2:
        raise ValueError("GeoCSV: too few data points")
    p0 = [p.strip() for p in data_lines[0].split(",")]
    p1 = [p.strip() for p in data_lines[1].split(",")]
    t0 = _parse_iso8601_to_unix_ms(p0[0])
    t1 = _parse_iso8601_to_unix_ms(p1[0])
    dt_ms = max(1, t1 - t0)
    sample_rate_hz = 1000.0 / float(dt_ms)

    # Downsample to keep JSON bundles manageable.
    # We estimate total samples from window length and computed sample rate.
    start_ms = t0
    end_ms = _parse_iso8601_to_unix_ms([p.strip() for p in data_lines[-1].split(",")][0])
    window_sec = max(1.0, (end_ms - start_ms) / 1000.0)
    est_total = int(window_sec * sample_rate_hz)
    stride = max(1, est_total // max_samples)

    sample_vals: list[float] = []
    for idx, line in enumerate(data_lines):
        if idx % stride != 0:
            continue
        if len(sample_vals) >= max_samples:
            break
        parts = [p.strip() for p in line.split(",")]
        try:
            sample_vals.append(float(parts[-1]))
        except ValueError:
            continue

    return {
        "start_time_ms": int(start_ms),
        "start_time": _unix_ms_to_iso8601(int(start_ms)),
        "end_time": _unix_ms_to_iso8601(int(end_ms)),
        "sample_rate_hz": float(sample_rate_hz) / float(stride),
        "samples": sample_vals,
        "n_samples": len(sample_vals),
        "downsample_stride": stride,
    }


def build_usgs_event_url(*, starttime: str, endtime: str, min_magnitude: float, max_magnitude: float | None) -> str:
    qs = {
        "format": "geojson",
        "starttime": starttime,
        "endtime": endtime,
        "minmagnitude": str(min_magnitude),
    }
    if max_magnitude is not None:
        qs["maxmagnitude"] = str(max_magnitude)
    return "https://earthquake.usgs.gov/fdsnws/event/1/query?" + urllib.parse.urlencode(qs)


def fetch_recent_events(
    *,
    days_back: int,
    min_magnitude: float,
    max_magnitude: float | None,
    cache_dir: str,
) -> list[dict]:
    now = dt.datetime.utcnow().replace(tzinfo=dt.timezone.utc)
    start = now - dt.timedelta(days=days_back)
    url = build_usgs_event_url(
        starttime=start.date().isoformat(),
        endtime=now.date().isoformat(),
        min_magnitude=min_magnitude,
        max_magnitude=max_magnitude,
    )
    max_tag = "none" if max_magnitude is None else str(max_magnitude)
    cache_path = os.path.join(cache_dir, f"usgs_events_{days_back}d_{min_magnitude}_to_{max_tag}.json")
    raw = _cache_read(cache_path)
    if raw is None:
        raw = _http_get(url)
        _cache_write(cache_path, raw)

    j = json.loads(raw.decode("utf-8"))
    out: list[dict] = []
    for feat in j.get("features", []):
        props = feat.get("properties", {})
        geom = feat.get("geometry", {})
        coords = geom.get("coordinates", [])
        if len(coords) < 2:
            continue
        if props.get("mag") is None:
            continue
        out.append(
            {
                "id": feat.get("id") or "",
                "time_ms": int(props.get("time")),
                "time": dt.datetime.utcfromtimestamp(int(props.get("time")) / 1000)
                .replace(tzinfo=dt.timezone.utc)
                .isoformat()
                .replace("+00:00", "Z"),
                "latitude": float(coords[1]),
                "longitude": float(coords[0]),
                "depth_km": float(coords[2]) if len(coords) >= 3 else 0.0,
                "magnitude": float(props.get("mag")),
                "magnitude_type": props.get("magType") or "",
                "place": props.get("place") or "",
            }
        )
    return out


def _distaz_url(*, base: str, event_lat: float, event_lon: float, station_lat: float, station_lon: float) -> str:
    qs = {
        "stalat": f"{station_lat}",
        "stalon": f"{station_lon}",
        "evtlat": f"{event_lat}",
        "evtlon": f"{event_lon}",
    }
    return base.rstrip("/") + "/irisws/distaz/1/query?" + urllib.parse.urlencode(qs)


def fetch_distaz(*, base: str, event: dict, station: dict, cache_dir: str) -> dict:
    cache_path = os.path.join(cache_dir, f"distaz_{event['id']}_{station['network']}.{station['code']}.xml")
    raw = _cache_read(cache_path)
    if raw is None:
        url = _distaz_url(
            base=base,
            event_lat=event["latitude"],
            event_lon=event["longitude"],
            station_lat=station["latitude"],
            station_lon=station["longitude"],
        )
        raw = _http_get(url)
        _cache_write(cache_path, raw)
        time.sleep(0.2)
    root = ET.fromstring(raw)
    dist = float(root.findtext("distance", default="nan"))
    az = float(root.findtext("azimuth", default="nan"))
    baz = float(root.findtext("backAzimuth", default="nan"))
    return {"distance_deg": dist, "azimuth": az, "back_azimuth": baz}


def _traveltime_url(
    *, base: str, model: str, phases: str, evdepth_km: float, distdeg: float, noheader: bool = True
) -> str:
    qs = {
        "model": model,
        "phases": phases,
        "evdepth": f"{evdepth_km:.1f}",
        "distdeg": f"{distdeg:.2f}",
        "noheader": "true" if noheader else "false",
    }
    return base.rstrip("/") + "/irisws/traveltime/1/query?" + urllib.parse.urlencode(qs)


def predict_p_arrival_ak135(*, irisws_base: str, event: dict, station: dict, distaz: dict, cache_dir: str) -> dict:
    """Predict earliest P-family arrival using IRISWS traveltime and ak135."""
    distdeg = float(distaz["distance_deg"])
    cache_path = os.path.join(cache_dir, f"traveltime_{event['id']}_{station['network']}.{station['code']}_{distdeg:.2f}.txt")
    raw = _cache_read(cache_path)
    if raw is None:
        phases = "P,Pdiff,PKP,PKIKP,PKiKP"
        url = _traveltime_url(
            base=irisws_base,
            model="ak135",
            phases=phases,
            evdepth_km=float(event["depth_km"]),
            distdeg=distdeg,
            noheader=True,
        )
        raw = _http_get(url)
        _cache_write(cache_path, raw)
        time.sleep(0.2)

    lines = [ln.strip() for ln in raw.decode("utf-8", errors="replace").splitlines() if ln.strip()]
    best = None
    for ln in lines:
        parts = ln.split()
        if len(parts) < 4:
            continue
        phase = parts[2]
        try:
            tt_sec = float(parts[3])
        except ValueError:
            continue
        if best is None or tt_sec < best[0]:
            best = (tt_sec, phase)

    if best is None:
        return {"should_reach": False, "model": "ak135", "phase": None, "travel_time_sec": None, "arrival_time_ms": None}

    tt_sec, phase = best
    arrival_ms = int(event["time_ms"] + int(tt_sec * 1000.0))
    return {
        "should_reach": True,
        "model": "ak135",
        "phase": phase,
        "travel_time_sec": tt_sec,
        "arrival_time_ms": arrival_ms,
        "arrival_time": _unix_ms_to_iso8601(arrival_ms),
    }


def fetch_station(*, station_base: str, key: str, cache_dir: str) -> dict:
    net, sta = key.split(".", 1)
    url = build_station_url(station_base, network=net, station=sta)
    cache_path = os.path.join(cache_dir, f"station_{net}_{sta}.xml")
    raw = _cache_read(cache_path)
    if raw is None:
        raw = _http_get(url)
        _cache_write(cache_path, raw)
        time.sleep(0.2)
    s = parse_stationxml_station(raw)
    return s


def fetch_waveform(
    *,
    dataselect_base: str,
    cache_dir: str,
    network: str,
    station: str,
    location: str,
    channel: str,
    start_iso: str,
    end_iso: str,
    max_samples: int,
) -> dict:
    url = build_dataselect_url(
        dataselect_base,
        network=network,
        station=station,
        location=location,
        channel=channel,
        starttime_iso=start_iso,
        endtime_iso=end_iso,
        format="geocsv",
    )
    cache_path = os.path.join(cache_dir, f"geocsv_{network}_{station}_{location}_{channel}_{start_iso}_{end_iso}.csv")
    raw = _cache_read(cache_path)
    if raw is None:
        raw = _http_get(url, timeout_sec=60)
        _cache_write(cache_path, raw)
        time.sleep(0.4)
    wf = parse_geocsv_samples(raw, max_samples=max_samples)
    wf.update({"station": f"{network}.{station}", "channel": channel, "location": location})
    return wf


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument(
        "--stations",
        required=True,
        help="Comma-separated NET.STA list (e.g. IU.ANMO,IU.HRV,...)",
    )
    p.add_argument("--min-magnitude", type=float, default=6.0)
    p.add_argument("--max-magnitude", type=float, default=None)
    p.add_argument("--days-back", type=int, default=30)
    p.add_argument("--max-events", type=int, default=3)
    p.add_argument("--output", default="data/seismic/validation_bundle.json")

    p.add_argument("--cache-dir", default="data/seismic/cache")
    p.add_argument("--station-base", default="https://service.iris.edu")
    p.add_argument("--dataselect-base", default="https://service.iris.edu")
    p.add_argument("--irisws-base", default="https://service.iris.edu")

    p.add_argument("--channel", default="BHZ")
    p.add_argument("--location", default="*")
    p.add_argument("--max-samples", type=int, default=25000)

    p.add_argument("--sta-sec", type=float, default=1.0)
    p.add_argument("--lta-sec", type=float, default=20.0)
    p.add_argument("--snr-threshold", type=float, default=3.0)
    p.add_argument("--tolerance-sec", type=float, default=10.0)
    args = p.parse_args()

    _mkdirp(args.cache_dir)
    try:
        station_keys = [s.strip() for s in args.stations.split(",") if s.strip()]
        if not station_keys:
            raise ValueError("--stations must be non-empty")

        events = fetch_recent_events(
            days_back=args.days_back,
            min_magnitude=args.min_magnitude,
            max_magnitude=args.max_magnitude,
            cache_dir=args.cache_dir,
        )
        events = [e for e in events if e.get("id")]
        events = sorted(events, key=lambda e: e["time_ms"], reverse=True)[: args.max_events]
        if len(events) < 1:
            raise ValueError("no events returned")

        stations = [fetch_station(station_base=args.station_base, key=k, cache_dir=args.cache_dir) for k in station_keys]
        station_by_key = {f"{s['network']}.{s['code']}": s for s in stations}

        predictions = []
        waveforms = []

        window_pre_sec = 5 * 60
        window_post_sec = 30 * 60

        for ev in events:
            for key in station_keys:
                st = station_by_key.get(key)
                if st is None:
                    continue
                distaz = fetch_distaz(base=args.irisws_base, event=ev, station=st, cache_dir=args.cache_dir)
                pred = predict_p_arrival_ak135(irisws_base=args.irisws_base, event=ev, station=st, distaz=distaz, cache_dir=args.cache_dir)
                pred_rec = {
                    "event_id": ev["id"],
                    "station": key,
                    "should_reach": bool(pred["should_reach"]),
                    "predicted_p_arrival": pred.get("arrival_time"),
                    "predicted_p_arrival_ms": pred.get("arrival_time_ms"),
                    "phase": pred.get("phase"),
                    "distance_deg": distaz.get("distance_deg"),
                    "azimuth": distaz.get("azimuth"),
                    "model": pred.get("model"),
                }
                predictions.append(pred_rec)

                if not pred["should_reach"] or pred.get("arrival_time_ms") is None:
                    continue

                start_ms = int(pred["arrival_time_ms"] - int(window_pre_sec * 1000))
                end_ms = int(pred["arrival_time_ms"] + int(window_post_sec * 1000))
                start_iso = _unix_ms_to_iso8601(start_ms)
                end_iso = _unix_ms_to_iso8601(end_ms)
                try:
                    wf = fetch_waveform(
                        dataselect_base=args.dataselect_base,
                        cache_dir=args.cache_dir,
                        network=st["network"],
                        station=st["code"],
                        location=args.location,
                        channel=args.channel,
                        start_iso=start_iso,
                        end_iso=end_iso,
                        max_samples=args.max_samples,
                    )
                    wf.update({"event_id": ev["id"], "start_time": start_iso, "end_time": end_iso, "sample_rate": wf.get("sample_rate_hz")})
                    waveforms.append(wf)
                except Exception as e:
                    # Missing data/gaps are expected; record a stub.
                    waveforms.append(
                        {
                            "event_id": ev["id"],
                            "station": key,
                            "channel": args.channel,
                            "start_time": start_iso,
                            "end_time": end_iso,
                            "error": str(e),
                        }
                    )

        bundle = {
            "metadata": {
                "generated_at": dt.datetime.utcnow().replace(tzinfo=dt.timezone.utc).isoformat().replace("+00:00", "Z"),
                "travel_time_model": "ak135",
                "travel_time_service": "IRISWS traveltime",
                "detection": {
                    "algorithm": "STA/LTA",
                    "sta_sec": args.sta_sec,
                    "lta_sec": args.lta_sec,
                    "snr_threshold": args.snr_threshold,
                },
                "tolerance_sec": args.tolerance_sec,
                "stations_queried": station_keys,
                "min_magnitude": args.min_magnitude,
                "max_magnitude": args.max_magnitude,
                "days_back": args.days_back,
                "max_events": args.max_events,
                "waveform_window": {"pre_sec": window_pre_sec, "post_sec": window_post_sec},
            },
            "stations": stations,
            "events": events,
            "predictions": predictions,
            "waveforms": waveforms,
        }
        _mkdirp(os.path.dirname(args.output))
        with open(args.output, "w", encoding="utf-8") as f:
            json.dump(bundle, f)
        print(json.dumps({"ok": True, "output": args.output, "n_events": len(events), "n_waveforms": len(waveforms)}))
        return 0
    except Exception as e:
        print(json.dumps({"ok": False, "error": str(e)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
