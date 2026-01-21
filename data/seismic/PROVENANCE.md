# Seismic Data Provenance

This directory contains empirical validation inputs/fixtures for the MirandaDynamics seismic
reaching demo.

## Data Sources

### USGS Earthquake Catalog (Event Metadata)
- URL: `https://earthquake.usgs.gov/fdsnws/event/1/`
- Format: GeoJSON
- License: Public domain (U.S. Government work)
- Citation: U.S. Geological Survey Earthquake Hazards Program

### IRIS/DSMC FDSN Web Services (Stations + Waveforms)
- Station service: `https://service.iris.edu/fdsnws/station/1/`
- Dataselect service: `https://service.iris.edu/fdsnws/dataselect/1/`
- License / policy: see IRIS Data Use Policy and network-specific usage notes
- Citation: IRIS DMC, Data Services Products

### IRISWS Traveltime (Predicted Arrivals)
- URL: `https://service.iris.edu/irisws/traveltime/1/`
- Model: `ak135`

## Validation Run: 2026-01-21

This repo tracks a **small synthetic fixture** (`data/seismic/sample_bundle.json`) and a
**small real-data snapshot** fixture (`data/seismic/realistic_fixture.json`) for reproducible,
network-free runs.

The full real-data bundle for the baseline run is archived as:

- `data/seismic/archived/validation_2026-01-21.json`

### Parameters (from the archived bundle metadata)
- Minimum magnitude: 6.0
- Time window: 30 days prior to fetch time
- Max events: 3
- Stations: IU.ANMO, IU.HRV, IU.COLA, II.BFO, IU.CTAO, IU.SNZO
- Detection algorithm: STA/LTA
  - STA: 1.0 s
  - LTA: 20.0 s
  - SNR threshold: 3.0
- Travel-time model: ak135 (IRISWS traveltime)
- Waveform window: pre=300 s, post=1800 s
- Timing tolerance (validator): 10.0 s

### Events Used (archived bundle)

| Event ID | Magnitude | Location | Origin time (UTC) |
|----------|-----------|----------|-------------------|
| us7000rqjy | 6.0 | 260 km ESE of Tadine, New Caledonia | 2026-01-19T13:02:20.746Z |
| us7000rq0d | 6.0 | 295 km W of Bandon, Oregon | 2026-01-16T03:25:52.639Z |
| us7000rpcg | 6.2 | 133 km SE of Kuril’sk, Russia | 2026-01-13T07:34:08.725Z |

### Results (baseline run)
- Accuracy: 92.86% (13/14)
- Mean |predicted - observed| (true positives): 4.3 s

Full machine-readable results are in `results/seismic_validation/validation_report.json`.

## Reproducibility

### Run with bundled fixture (no network)

```bash
cd RESEARCHER_BUNDLE
lake build --wfail seismic_validate_demo
lake exe seismic_validate_demo
```

### Re-run the baseline on real data (network required)

```bash
python3 scripts/seismic_bridge.py \
  --stations IU.ANMO,IU.HRV,IU.COLA,II.BFO,IU.CTAO,IU.SNZO \
  --min-magnitude 6.0 \
  --days-back 30 \
  --max-events 3 \
  --output data/seismic/validation_bundle.json

cd RESEARCHER_BUNDLE
lake exe seismic_validate_demo -- ../data/seismic/validation_bundle.json > ../results/seismic_validation/lean_output.json
cd ..

python3 scripts/generate_validation_report.py \
  --bundle data/seismic/validation_bundle.json \
  --lean-output results/seismic_validation/lean_output.json \
  --output-dir results/seismic_validation/
```

Note: live re-fetching is not bit-for-bit reproducible (the event window changes). For stable
baseline comparisons, use `data/seismic/archived/validation_2026-01-21.json`.
