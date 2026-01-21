#!/usr/bin/env python3
"""Create a minimal fixture from a full seismic validation bundle.

This produces a small JSON file suitable for checking into git.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def create_fixture(
    input_path: Path,
    output_path: Path,
    max_events: int,
    truncate_waveforms: int,
) -> dict:
    bundle = json.loads(input_path.read_text())

    events = bundle.get("events", [])
    events = events[: max(0, max_events)]
    event_ids = {e.get("id") for e in events if isinstance(e, dict) and e.get("id")}
    bundle["events"] = events

    preds = bundle.get("predictions", [])
    bundle["predictions"] = [
        p for p in preds if isinstance(p, dict) and p.get("event_id") in event_ids
    ]

    waveforms = bundle.get("waveforms", [])
    kept_waveforms = [
        w for w in waveforms if isinstance(w, dict) and w.get("event_id") in event_ids
    ]
    for w in kept_waveforms:
        samples = w.get("samples")
        if isinstance(samples, list) and len(samples) > truncate_waveforms:
            w["samples"] = samples[:truncate_waveforms]
    bundle["waveforms"] = kept_waveforms

    meta = bundle.get("metadata")
    if isinstance(meta, dict):
        meta = dict(meta)
        meta["is_fixture"] = True
        bundle["metadata"] = meta

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n")
    return bundle


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--max-events", type=int, default=2)
    parser.add_argument("--truncate-waveforms", type=int, default=1000)
    args = parser.parse_args()

    out = create_fixture(
        input_path=Path(args.input),
        output_path=Path(args.output),
        max_events=args.max_events,
        truncate_waveforms=max(0, args.truncate_waveforms),
    )

    print(
        f"Created fixture with {len(out.get('events', []))} events, "
        f"{len(out.get('waveforms', []))} waveforms"
    )


if __name__ == "__main__":
    main()

