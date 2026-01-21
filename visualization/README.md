# Miranda Dynamics Visualization

Interactive visualization of TKFT validation results demonstrating how Heyting algebras describe physical epistemology.

## Live Demo

https://abraxas1010.github.io/miranda-dynamics-lean/visualization/

## Features

- **3D Globe**: Watch seismic waves propagate from earthquakes to stations
- **Billiard Calibration**: See how finite observation creates information loss
- **Heyting Gap Spotlight**: Dramatic visualization when j(P) < P occurs
- **Calibration Transfer**: How billiard precision maps to seismic SNR

## Data

Visualizes 3 earthquake events from January 2026:
- M6.0 New Caledonia (2026-01-19)
- M6.0 Oregon Offshore (2026-01-16)
- M6.2 Kuril Islands (2026-01-13)

**Key Result**: 92.86% accuracy, 7.14% Heyting gap rate

## Understanding the Visualization

### The Globe

The 3D globe shows seismic wave propagation from earthquake epicenters to seismic stations worldwide. As you play the simulation:

- **Green expanding ring** = P-wave front (faster, ~8 km/s)
- **Red expanding ring** = S-wave front (slower, ~4.5 km/s)
- **Gray dots** = Stations awaiting wave arrival
- **Green dots** = j(P) = P: Wave predicted AND detected
- **Amber pulsing dots** = j(P) < P: Heyting Gap (wave predicted but NOT detected)

### The Heyting Gap

When the Oregon Offshore event is selected and the simulation reaches ~756 seconds, a dramatic modal appears. This is the **Heyting Gap** - the moment when:

- P (physical truth): The wave truly reached station IU.SNZO
- j(P) (observable truth): The detection system could NOT verify arrival (SNR = 2.1 < 3.0 threshold)

This is NOT a model failure. This is the **Heyting algebra working correctly** - distinguishing between what is true and what is verifiable.

### The Billiard Simulation

The billiard simulation demonstrates **pure observational information loss**. Unlike seismic systems:

- The dynamics are perfectly reversible (elastic collisions)
- There is NO information loss in the physics
- ALL information loss comes from finite observation precision

Adjust the precision slider to see how the gap between true position (solid) and observed position (dashed) changes.

## Local Development

```bash
# Serve locally (Python 3)
python -m http.server 8000

# Or use Node.js
npx serve .
```

Then open http://localhost:8000

## Dependencies

- [CesiumJS](https://cesium.com/) - 3D globe visualization
- [Chart.js](https://www.chartjs.org/) - Calibration plots
- No build step required - vanilla JavaScript with ES modules

## No Token Required

The visualization uses OpenStreetMap imagery which requires no authentication.
It works out of the box with no setup needed.

## Project Structure

```
visualization/
  index.html          # Main HTML page
  css/
    styles.css        # Global styles
  js/
    app.js            # Main application controller
    data.js           # Validation data (3 events, 14 pairs)
    globe.js          # CesiumJS 3D globe
    billiard.js       # Billiard ball simulation
    calibration.js    # Chart.js calibration plot
    heyting-gap.js    # Dramatic gap modal
  assets/             # Static assets (icons, etc.)
  README.md           # This file
```

## Categorical Interpretation

The visualization demonstrates Miranda's TKFT categorical framework:

| Category | Count | Meaning |
|----------|-------|---------|
| j(P) = P | 13 | Observable equals physical (fixed points) |
| j(P) < P | 1 | Heyting gap (physical exceeds observable) |
| j(P) > P | 0 | Would be model error (never occurred) |

The 7.14% Heyting gap rate quantifies irreducible epistemic uncertainty - the price of finite observation.

## Related Documentation

- [Main README](../README.md) - Project overview
- [Technical Deep Dive](../docs/TECHNICAL.md) - How Lean connects to physical data
- [Validation Results](../docs/VALIDATION_RESULTS.md) - Full empirical results
