#!/usr/bin/env python3
"""generate_validation_report.py

Combine the real-data bundle (from `scripts/seismic_bridge.py`) and the Lean output
(from `seismic_validate_demo`) into concrete evidence artifacts.

Outputs (in `--output-dir`):
- validation_report.json
- validation_summary.md
- arrival_comparison.csv
- reaching_matrix.md
- waveform_plots/ (optional; requires matplotlib)
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from dataclasses import dataclass
from typing import Any


def _mkdirp(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def _load_lean_json(path: str) -> dict:
    """Load Lean output.

    Supports either:
    - pure JSON output (recommended: run `seismic_validate_demo --json-only ...`), or
    - mixed human report + a final "=== JSON OUTPUT ===" section.
    """
    with open(path, "r", encoding="utf-8") as f:
        txt = f.read()
    try:
        return json.loads(txt)
    except Exception:
        marker = "=== JSON OUTPUT ==="
        idx = txt.rfind(marker)
        if idx >= 0:
            tail = txt[idx + len(marker) :]
            j0 = tail.find("{")
            if j0 >= 0:
                return json.loads(tail[j0:])
        j0 = txt.rfind("{")
        if j0 >= 0:
            return json.loads(txt[j0:])
        raise


def _iso(ms: int | None) -> str | None:
    if ms is None:
        return None
    import datetime as dt

    return (
        dt.datetime.utcfromtimestamp(ms / 1000).replace(tzinfo=dt.timezone.utc).isoformat().replace("+00:00", "Z")
    )


@dataclass
class Metrics:
    total_pairs: int
    predicted_reach: int
    predicted_no_reach: int
    observed_reach: int
    observed_no_reach: int
    true_positive: int
    true_negative: int
    false_positive: int
    false_negative: int
    accuracy: float
    timing_error_mean_sec: float | None
    timing_error_std_sec: float | None
    timing_abs_error_mean_sec: float | None
    timing_abs_error_std_sec: float | None
    timing_abs_error_max_sec: float | None
    false_negative_rate: float | None
    false_positive_rate: float | None


def compute_metrics(pairs: list[dict]) -> Metrics:
    tp = tn = fp = fn = 0
    pred_reach = pred_no = obs_reach = obs_no = 0
    timing_errors: list[float] = []
    timing_abs_errors: list[float] = []

    for r in pairs:
        should = bool(r.get("should_reach", True))
        did = bool(r.get("did_reach", False))
        ok = bool(r.get("waveform_ok", False))
        if not ok:
            continue

        if should:
            pred_reach += 1
        else:
            pred_no += 1
        if did:
            obs_reach += 1
        else:
            obs_no += 1

        if should and did:
            tp += 1
            if r.get("timing_error_ms") is not None:
                err_s = float(r["timing_error_ms"]) / 1000.0
                timing_errors.append(err_s)
                timing_abs_errors.append(abs(err_s))
        elif (not should) and (not did):
            tn += 1
        elif (not should) and did:
            fp += 1
        elif should and (not did):
            fn += 1

    total = tp + tn + fp + fn
    acc = (tp + tn) / total if total else 0.0

    mean = std = None
    if timing_errors:
        mean = sum(timing_errors) / len(timing_errors)
        var = sum((x - mean) ** 2 for x in timing_errors) / len(timing_errors)
        std = math.sqrt(var)

    abs_mean = abs_std = abs_max = None
    if timing_abs_errors:
        abs_mean = sum(timing_abs_errors) / len(timing_abs_errors)
        abs_var = sum((x - abs_mean) ** 2 for x in timing_abs_errors) / len(timing_abs_errors)
        abs_std = math.sqrt(abs_var)
        abs_max = max(timing_abs_errors)

    fn_rate = fn / pred_reach if pred_reach else None
    fp_rate = fp / pred_no if pred_no else None

    return Metrics(
        total_pairs=total,
        predicted_reach=pred_reach,
        predicted_no_reach=pred_no,
        observed_reach=obs_reach,
        observed_no_reach=obs_no,
        true_positive=tp,
        true_negative=tn,
        false_positive=fp,
        false_negative=fn,
        accuracy=acc,
        timing_error_mean_sec=mean,
        timing_error_std_sec=std,
        timing_abs_error_mean_sec=abs_mean,
        timing_abs_error_std_sec=abs_std,
        timing_abs_error_max_sec=abs_max,
        false_negative_rate=fn_rate,
        false_positive_rate=fp_rate,
    )


def write_arrival_csv(pairs: list[dict], out_path: str) -> None:
    _mkdirp(os.path.dirname(out_path))
    with open(out_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "event_id",
                "station",
                "should_reach",
                "did_reach",
                "predicted_arrival_ms",
                "predicted_arrival_iso",
                "observed_arrival_ms",
                "observed_arrival_iso",
                "timing_error_ms",
                "timing_error_sec",
                "within_tolerance",
                "waveform_ok",
            ]
        )
        for r in pairs:
            pred_ms = r.get("predicted_arrival_ms")
            obs_ms = r.get("observed_arrival_ms")
            err_ms = r.get("timing_error_ms")
            w.writerow(
                [
                    r.get("event_id"),
                    r.get("station"),
                    r.get("should_reach"),
                    r.get("did_reach"),
                    pred_ms,
                    _iso(pred_ms),
                    obs_ms,
                    _iso(obs_ms),
                    err_ms,
                    (float(err_ms) / 1000.0) if err_ms is not None else "",
                    r.get("within_tolerance"),
                    r.get("waveform_ok"),
                ]
            )


def write_reaching_matrix(pairs: list[dict], out_path: str) -> None:
    # rows: events, columns: stations.
    events = sorted({r.get("event_id") for r in pairs if r.get("event_id")})
    stations = sorted({r.get("station") for r in pairs if r.get("station")})
    lookup = {(r.get("event_id"), r.get("station")): r for r in pairs}

    lines = []
    header = "| event_id | " + " | ".join(stations) + " |"
    sep = "|---|" + "|".join(["---"] * len(stations)) + "|"
    lines.append(header)
    lines.append(sep)
    for eid in events:
        row = [eid]
        for st in stations:
            r = lookup.get((eid, st))
            if not r:
                row.append("NA")
                continue
            if not r.get("waveform_ok", False):
                row.append("ERR")
            else:
                should = bool(r.get("should_reach", True))
                did = bool(r.get("did_reach", False))
                if should and did:
                    row.append("TP")
                elif (not should) and (not did):
                    row.append("TN")
                elif (not should) and did:
                    row.append("FP")
                else:
                    row.append("FN")
        lines.append("| " + " | ".join(row) + " |")

    _mkdirp(os.path.dirname(out_path))
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def try_write_plots(bundle: dict, lean_pairs: list[dict], out_dir: str) -> None:
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except Exception:
        return

    _mkdirp(out_dir)
    wf_by_key = {}
    for wf in bundle.get("waveforms", []):
        if "samples" not in wf or "start_time_ms" not in wf:
            continue
        wf_by_key[(wf.get("event_id"), wf.get("station"))] = wf

    # Limit plots to keep repo size reasonable.
    for r in lean_pairs[:18]:
        key = (r.get("event_id"), r.get("station"))
        wf = wf_by_key.get(key)
        if not wf:
            continue
        samples = wf.get("samples")
        if not isinstance(samples, list) or not samples:
            continue
        sr = wf.get("sample_rate_hz")
        if not isinstance(sr, (int, float)) or sr <= 0:
            continue
        start_ms = int(wf.get("start_time_ms"))
        t = [i / float(sr) for i in range(len(samples))]
        plt.figure(figsize=(10, 3))
        plt.plot(t, samples, linewidth=0.6)
        pred = r.get("predicted_arrival_ms")
        obs = r.get("observed_arrival_ms")
        if isinstance(pred, int):
            plt.axvline((pred - start_ms) / 1000.0, color="orange", linestyle="--", label="pred")
        if isinstance(obs, int):
            plt.axvline((obs - start_ms) / 1000.0, color="green", linestyle="--", label="obs")
        plt.title(f"{key[0]} @ {key[1]}")
        plt.xlabel("seconds from window start")
        plt.tight_layout()
        safe = f"{key[0]}_{key[1].replace('.', '_')}".replace("/", "_")
        plt.savefig(os.path.join(out_dir, safe + ".png"))
        plt.close()


def write_summary(meta: dict, metrics: Metrics, out_path: str) -> None:
    lines = []
    lines.append(f"## Seismic Validation Summary ({meta.get('generated_at', '')})")
    lines.append("")
    lines.append("### Metrics")
    lines.append(f"- total_pairs: {metrics.total_pairs}")
    lines.append(f"- accuracy: {metrics.accuracy:.3f}")
    lines.append(f"- true_positive: {metrics.true_positive}")
    lines.append(f"- true_negative: {metrics.true_negative}")
    lines.append(f"- false_positive: {metrics.false_positive}")
    lines.append(f"- false_negative: {metrics.false_negative}")
    if metrics.timing_error_mean_sec is not None:
        lines.append(f"- timing_error_mean_sec: {metrics.timing_error_mean_sec:.3f}")
    if metrics.timing_error_std_sec is not None:
        lines.append(f"- timing_error_std_sec: {metrics.timing_error_std_sec:.3f}")
    if metrics.timing_abs_error_mean_sec is not None:
        lines.append(f"- timing_abs_error_mean_sec: {metrics.timing_abs_error_mean_sec:.3f}")
    if metrics.timing_abs_error_std_sec is not None:
        lines.append(f"- timing_abs_error_std_sec: {metrics.timing_abs_error_std_sec:.3f}")
    if metrics.timing_abs_error_max_sec is not None:
        lines.append(f"- timing_abs_error_max_sec: {metrics.timing_abs_error_max_sec:.3f}")
    if metrics.false_negative_rate is not None:
        lines.append(f"- false_negative_rate: {metrics.false_negative_rate:.3f}")
    if metrics.false_positive_rate is not None:
        lines.append(f"- false_positive_rate: {metrics.false_positive_rate:.3f}")
    lines.append("")
    lines.append("### Configuration")
    lines.append(f"- travel_time_model: {meta.get('travel_time_model')}")
    det = meta.get("detection", {})
    if isinstance(det, dict):
        lines.append(f"- detection.algorithm: {det.get('algorithm')}")
        lines.append(f"- detection.sta_sec: {det.get('sta_sec')}")
        lines.append(f"- detection.lta_sec: {det.get('lta_sec')}")
        lines.append(f"- detection.snr_threshold: {det.get('snr_threshold')}")
    lines.append(f"- tolerance_sec: {meta.get('tolerance_sec')}")
    lines.append(f"- stations_queried: {', '.join(meta.get('stations_queried', []))}")
    lines.append("")

    _mkdirp(os.path.dirname(out_path))
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", required=True)
    ap.add_argument("--lean-output", required=True)
    ap.add_argument("--output-dir", required=True)
    args = ap.parse_args()

    with open(args.bundle, "r", encoding="utf-8") as f:
        bundle = json.load(f)
    lean_out = _load_lean_json(args.lean_output)

    pairs = lean_out.get("pairs", [])
    if not isinstance(pairs, list):
        raise SystemExit("lean output missing pairs")

    meta = lean_out.get("metadata", {})
    if not isinstance(meta, dict):
        meta = {}

    metrics = compute_metrics(pairs)
    out_dir = args.output_dir
    _mkdirp(out_dir)

    report = {
        "metrics": metrics.__dict__,
        "metadata": meta,
        "pairs": pairs,
    }

    if isinstance(lean_out.get("standard_metrics"), dict):
        report["standard_metrics"] = lean_out["standard_metrics"]
    if isinstance(lean_out.get("categorical_summary"), dict):
        report["categorical_summary"] = lean_out["categorical_summary"]
    with open(os.path.join(out_dir, "validation_report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    write_arrival_csv(pairs, os.path.join(out_dir, "arrival_comparison.csv"))
    write_reaching_matrix(pairs, os.path.join(out_dir, "reaching_matrix.md"))
    write_summary(meta, metrics, os.path.join(out_dir, "validation_summary.md"))
    try_write_plots(bundle, pairs, os.path.join(out_dir, "waveform_plots"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
