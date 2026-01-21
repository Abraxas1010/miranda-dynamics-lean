# Seismic Integration — Evidence + Lean Mapping (WIP)

Date: 2026-01-21

This note records (1) authoritative external references for the EarthScope/IRIS and USGS services
used by the seismic “physical system integration” plan, and (2) how the plan maps into Lean
identifiers in this repository (reusing the existing MirandaDynamics/TKFT interface style).

## 1) Evidence (external)

### Station metadata and waveform access (IRIS/EarthScope)

- FDSN Station web service (StationXML output; EarthScope/IRIS endpoint):
  - Docs: https://service.iris.edu/fdsnws/station/1/

- FDSN dataselect web service (waveform access; supports formats including GeoCSV):
  - Docs: https://service.iris.edu/fdsnws/dataselect/1/

Notes:
- EarthScope has been migrating services; some docs indicate the canonical endpoint may be
  `service.earthscope.org` with redirects from `service.iris.edu`.
- For “no heavy dependency” parsing, `format=geocsv` is preferable to miniSEED.

### Real-time streaming (optional)

- SeedLink (near-real-time miniSEED over TCP):
  - Docs: https://ds.iris.edu/ds/nodes/dmc/services/seedlink/

### Auxiliary geometry + travel times (IRISWS)

- Distance/azimuth service (distaz):
  - Docs: https://service.iris.edu/irisws/distaz/1/

- Travel-time service (ak135/iasp91/etc.):
  - Docs: https://service.iris.edu/irisws/traveltime/1/

### Event catalogs (USGS)

- USGS Earthquake Catalog API (GeoJSON):
  - Example endpoint (parameterized): https://earthquake.usgs.gov/fdsnws/event/1/
  - Additional API documentation: https://earthquake.usgs.gov/fdsnws/event/1/

Note:
- Some IRIS event services have been retired historically; using USGS for event catalogs is a
  stable, well-documented choice.

## 2) Evidence-to-Lean mapping (what we formalize vs what stays “external”)

### What we can mechanize now (Lean)

- Pure types + IO-free semantics:
  - `HeytingLean.MirandaDynamics.Seismic.Basic` (Station/Event/Waveform structs)
- Observation-window nucleus:
  - A `HeytingLean.Core.Nucleus (Set α)` built from “finite observation” equivalence.
  - This is fully provable (no physics axioms needed): it’s just saturation under an equivalence.

### What remains external (interfaces, not axioms)

- Travel-time / path-existence physics:
  - packaged as explicit structures (similar to `MirandaDynamics.External.*`).
- “This specific physics model implies reachability predicate `P`”
  - remains a hypothesis boundary until we pick concrete equipment/specs and a concrete travel-time
    model (IASPEI91/TauP, etc.).

## 3) Reuse plan

- Follow the existing “interface-first” pattern:
  - `lean/HeytingLean/MirandaDynamics/External/Interfaces.lean`
  - `lean/HeytingLean/MirandaDynamics/TKFT/Reaching.lean`

- Use Python only as a data acquisition bridge:
  - fetch StationXML + GeoCSV + USGS GeoJSON
  - emit a cached JSON bundle consumed by a Lean executable (offline, QA-friendly)
