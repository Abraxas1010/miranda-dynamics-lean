# Expanded Seismic Validation Report

Generated: 2026-01-21T04:13:15.940129Z

| Config | Status | Events | Pairs | Accuracy | FNR | FPR | Mean |Δt| | Std |Δt| | Max |Δt| |
|--------|--------|--------|-------|----------|-----|-----|----------|---------|---------|
| baseline | success | 3 | 18 | 94.44% | 5.56% | n/a | 4.4s | 3.9s | 12.3s |
| expanded_stations | success | 5 | 80 | 87.50% | 12.50% | n/a | 4.5s | 5.1s | 26.7s |
| lower_magnitude | success | 5 | 30 | 93.33% | 6.67% | n/a | 5.9s | 5.9s | 26.6s |
| extended_time | success | 20 | 119 | 94.96% | 5.04% | n/a | 4.7s | 4.7s | 27.1s |
| comprehensive | success | 30 | 480 | 87.29% | 12.71% | n/a | 6.3s | 6.1s | 29.3s |

## Notes

- `should_reach` (from ak135 travel-time prediction) is treated as the label.
- `did_reach` (from Lean STA/LTA detector) is the observation result.
- `FNR` is the rate of predicted arrivals that were not detected.
- `FPR` is the rate of detections when `should_reach = false`.
