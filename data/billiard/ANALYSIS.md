# Billiard Calibration (WIP)

This directory hosts calibration artifacts for a simple 1D billiard system intended to
characterize *information loss introduced by observation* (finite precision, noise).

The core scientific idea:

- The underlying dynamics are deterministic (piecewise-linear evolution + elastic collisions).
- Any epistemic gap in inferred state comes from the observation process.

## How to run

```bash
# Generate a calibration dataset (multiple trials reduce Monte Carlo noise)
python3 scripts/billiard_calibration.py \
  --num-balls 3 \
  --evolution-time 5.0 \
  --num-samples 50 \
  --trials 50 \
  --seed 42

# Fit a simple model and propose seismic parameters
python3 scripts/transfer_calibration.py \
  --billiard-calibration data/billiard/calibration_results.json
```

The transfer script reports an `R^2` score for the fitted model.

## Lean-side scaffolding

The corresponding Lean modules are under:

- `RESEARCHER_BUNDLE/HeytingLean/MirandaDynamics/Billiard/`

These are intended for future integration of observation kernels and reaching relations; they do not
attempt to prove reversibility for floating-point evolution.

