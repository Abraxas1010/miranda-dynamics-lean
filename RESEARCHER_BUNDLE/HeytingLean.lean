/-!
# HeytingLean / Miranda Dynamics - Umbrella Import

This is the standalone Miranda Dynamics PaperPack, formalizing computational
universality results from Professor Eva Miranda and collaborators.

## Main Modules

- `MirandaDynamics.TKFT`: Topological Kleene Field Theory (reaching relations, bordisms)
- `MirandaDynamics.Billiards`: Cantor encoding for billiard computation
- `MirandaDynamics.Discrete`: Halting ↔ periodic orbit bridges
- `MirandaDynamics.Computation`: Flow realization and generalized shifts
- `MirandaDynamics.External`: Interfaces for literature claims (no axioms)

## Verification

```
lake build --wfail
grep -r "sorry" HeytingLean/MirandaDynamics/ # Should return nothing
```
-/

import HeytingLean.MirandaDynamics
