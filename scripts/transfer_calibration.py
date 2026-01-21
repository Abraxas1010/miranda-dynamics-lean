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


def _x1(precision: int) -> float:
    return 10.0 ** (-int(precision))


def load_billiard_calibration(path: Path) -> dict:
    return json.loads(path.read_text())


def _fit_linear_model(rows: list[tuple[float, float, float]]) -> tuple[tuple[float, float, float, float], float]:
    """Fit y ≈ a*x1 + b*x2 + d*x2^2 + c (least squares), returning params and R^2."""
    if not rows:
        return (0.0, 0.0, 0.0), float("nan")

    # Normal equations for 4-parameter linear regression.
    # Features: [x1, x2, x2^2, 1].
    # Solve (X^T X) beta = X^T y.
    m = 4
    xtx = [[0.0 for _ in range(m)] for _ in range(m)]
    xty = [0.0 for _ in range(m)]
    ys: list[float] = []
    for x1, x2, y in rows:
        ys.append(y)
        f = [x1, x2, x2 * x2, 1.0]
        for i in range(m):
            xty[i] += f[i] * y
            for j in range(m):
                xtx[i][j] += f[i] * f[j]

    # Augmented matrix for Gaussian elimination.
    a = [xtx[i] + [xty[i]] for i in range(m)]

    for col in range(m):
        pivot = max(range(col, m), key=lambda r: abs(a[r][col]))
        if abs(a[pivot][col]) < 1e-18:
            continue
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
        inv = 1.0 / a[col][col]
        for j in range(col, m + 1):
            a[col][j] *= inv
        for r in range(m):
            if r == col:
                continue
            factor = a[r][col]
            if abs(factor) < 1e-18:
                continue
            for j in range(col, m + 1):
                a[r][j] -= factor * a[col][j]

    beta = (a[0][m], a[1][m], a[2][m], a[3][m])

    ybar = sum(ys) / len(ys)
    sst = sum((y - ybar) ** 2 for y in ys)
    sse = 0.0
    for x1, x2, y in rows:
        yhat = beta[0] * x1 + beta[1] * x2 + beta[2] * (x2 * x2) + beta[3]
        sse += (y - yhat) ** 2
    r2 = float("nan") if sst == 0.0 else (1.0 - sse / sst)
    return beta, r2


def fit_gap_model(calibration: dict) -> dict:
    """Fit RMS error as a function of (precision, noise_std).

    Model: rms_error ≈ a*(10^-precision) + b*noise_std + c
    """
    rows: list[tuple[float, float, float]] = []
    for run in calibration.get("calibration_runs", []):
        if not isinstance(run, dict):
            continue
        precision = run.get("precision")
        noise_std = run.get("noise_std")
        rms = run.get("rms_error")
        if not isinstance(precision, int):
            continue
        if not isinstance(noise_std, (int, float)):
            continue
        if not isinstance(rms, (int, float)):
            continue
        rows.append((_x1(precision), float(noise_std), float(rms)))

    (a, b, d, c), r2 = _fit_linear_model(rows)
    return {
        "model": "rms_error ≈ a*(10^-precision) + b*noise_std + d*noise_std^2 + c",
        "params": {"a": a, "b": b, "d": d, "c": c},
        "r2": r2,
        "n": len(rows),
    }


def gap_model(model: dict, precision: int, noise_std: float) -> float:
    params = model.get("params", {})
    a = float(params.get("a", 0.0))
    b = float(params.get("b", 0.0))
    d = float(params.get("d", 0.0))
    c = float(params.get("c", 0.0))
    x2 = float(noise_std)
    return a * _x1(precision) + b * x2 + d * (x2 * x2) + c


def transfer_to_seismic(model: dict, target_gap: float) -> dict:
    # Map billiard parameters to seismic knobs (heuristic):
    # - `precision` ↔ timing precision
    # - `noise_std` ↔ inverse-SNR
    for precision in range(1, 10):
        for snr_threshold in [2.0, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 15.0, 20.0]:
            effective_noise = 1.0 / snr_threshold
            predicted_gap = gap_model(model, precision, effective_noise)
            predicted_gap = max(0.0, predicted_gap)
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
    # A practical default that tends to map to SNR thresholds in the ~2–4 range for the
    # current calibration configuration.
    ap.add_argument("--target-gap", type=float, default=0.4)
    ap.add_argument("--output", default="data/seismic/calibrated_params.json")
    args = ap.parse_args()

    cal_path = Path(args.billiard_calibration)
    if not cal_path.exists():
        raise SystemExit(f"missing calibration file: {cal_path} (run scripts/billiard_calibration.py)")
    calibration = load_billiard_calibration(cal_path)

    model = fit_gap_model(calibration)
    rec = transfer_to_seismic(model, args.target_gap)
    rec["fitted_model"] = model
    print(json.dumps(rec, indent=2))

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
