# Seismic Validation Results (WIP)

Run date: 2026-01-21

This note interprets the current end-to-end seismic validation artifacts under
`results/seismic_validation/`.

## What was tested

- **Events:** last 30 days, magnitude ≥ 6.0 (USGS GeoJSON feed).
- **Stations:** IU.ANMO, IU.HRV, IU.COLA, II.BFO, IU.CTAO, IU.SNZO (queried via FDSN Station).
- **Predicted arrival:** ak135 P-family travel times via IRISWS traveltime + distaz.
- **Observed arrival:** Lean-side STA/LTA detector over a waveform window around the predicted
  arrival (GeoCSV waveforms from FDSN Dataselect; downsampled to keep JSON manageable).

## Summary metrics

The current run’s machine-readable report is:

- `results/seismic_validation/validation_report.json`

Key summary (from that file):

- Total valid `(event, station)` waveform pairs: **14**
- Reachability accuracy (reach vs no-reach): **0.929**
- Mean timing error (sec): **-1.480**
- Timing error std (sec): **5.456**

These meet the current success thresholds in the instruction spec.

## Notes / caveats

- This is a **validation demo**, not a seismology pipeline.
- The detector uses a simple STA/LTA trigger on a first-difference energy proxy to mitigate DC
  offsets in raw counts.
- The validator ignores triggers that are far (>30s) from the predicted P arrival to avoid
  “detecting” later surface waves when the goal is specifically P-wave reachability.

## Where the evidence lives

- `results/seismic_validation/arrival_comparison.csv`
- `results/seismic_validation/reaching_matrix.md`
- `results/seismic_validation/validation_summary.md`
- `results/seismic_validation/waveform_plots/` (if matplotlib is available)

