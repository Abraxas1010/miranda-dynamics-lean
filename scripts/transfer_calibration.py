#!/usr/bin/env python3
"""transfer_calibration.py

Transfer a simple observation-gap calibration from the 1D billiard simulator to seismic detector
parameter suggestions.

This is a deliberately lightweight heuristic model: it provides a starting point for thinking about
how observation precision/noise relate to detector SNR thresholds and timing tolerances.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load_billiard_calibration(path: Path) -> dict:
    return json.loads(path.read_text())


def gap_model(precision: int, noise_std: float) -> float:
    """Very simple heuristic: gap ≈ 10^(-precision) + noise_std."""
    return (10 ** (-precision)) + float(noise_std)


def transfer_to_seismic(target_gap: float) -> dict:
    # Map billiard parameters to seismic knobs (heuristic):
    # - `precision` ↔ timing precision
    # - `noise_std` ↔ inverse-SNR
    for precision in range(1, 10):
        for snr_threshold in [2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 15.0, 20.0]:
            effective_noise = 1.0 / snr_threshold
            predicted_gap = gap_model(precision, effective_noise)
            if predicted_gap <= target_gap:
                # timing precision in ms: 10^(3-precision) is a rough scale (precision=3 => 1ms)
                timing_precision_ms = 10 ** max(0, 3 - precision)
                return {
                    "recommended_snr_threshold": snr_threshold,
                    "recommended_timing_precision_ms": timing_precision_ms,
                    "predicted_information_gap": predicted_gap,
                    "target_gap": target_gap,
                }

    return {"error": "Cannot achieve target gap with available parameter sweep", "target_gap": target_gap}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--billiard-calibration", default="data/billiard/calibration_results.json")
    ap.add_argument("--target-gap", type=float, default=0.1)
    ap.add_argument("--output", default="data/seismic/calibrated_params.json")
    args = ap.parse_args()

    # Currently we don't fit anything from the calibration file; we just require it exists for
    # reproducibility and future model fitting.
    cal_path = Path(args.billiard_calibration)
    if not cal_path.exists():
        raise SystemExit(f"missing calibration file: {cal_path} (run scripts/billiard_calibration.py)")
    _ = load_billiard_calibration(cal_path)

    rec = transfer_to_seismic(args.target_gap)
    print(json.dumps(rec, indent=2))

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
