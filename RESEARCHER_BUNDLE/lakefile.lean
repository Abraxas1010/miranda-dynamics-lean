import Lake
open Lake DSL

package «MirandaDynamics» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

-- Pin auxiliary libraries to Mathlib v4.24.0-compatible revisions for reproducibility
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "91c18fa62838ad0ab7384c03c9684d99d306e1da"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "dea6a3361fa36d5a13f87333dc506ada582e025c"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "725ac8cd67acd70a7beaf47c3725e23484c1ef50"
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "8da40b72fece29b7d3fe3d768bac4c8910ce9bee"

@[default_target]
lean_lib «HeytingLean» where
  -- Build the umbrella `HeytingLean` module, which imports the MirandaDynamics spine and pulls
  -- in any cross-namespace dependencies (e.g. `HeytingLean.Bridges.*`) through normal imports.
  roots := #[`HeytingLean]

-- Demo executables
lean_exe miranda_dynamics_demo where
  root := `HeytingLean.MirandaDynamics.DemoMain

lean_exe miranda_billiards_demo where
  root := `HeytingLean.MirandaDynamics.Billiards.DemoMain

lean_exe miranda_billiards_geometry_demo where
  root := `HeytingLean.MirandaDynamics.Billiards.GeometryDemoMain

lean_exe miranda_discrete_demo where
  root := `HeytingLean.MirandaDynamics.Discrete.DemoMain

lean_exe miranda_partialflow_demo where
  root := `HeytingLean.MirandaDynamics.Dynamics.PartialFlowDemoMain

-- Seismic validation demo (observation-first grounding)
lean_exe seismic_validate_demo where
  root := `HeytingLean.CLI.SeismicValidateMain
