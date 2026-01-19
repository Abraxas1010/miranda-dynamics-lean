import HeytingLean.MirandaDynamics.Fluids.VectorCalculus.Curl3

/-!
# Tests: MirandaDynamics curl sanity

Compile-time smoke tests for the coordinate curl definition on `Fin 3 → ℝ`.
-/

namespace HeytingLean.Tests.MirandaDynamics.Curl

open HeytingLean.MirandaDynamics.Fluids.VectorCalculus

open HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3

example (c x : V) : curl (fun _ => c) x = 0 :=
  curl_const (c := c) (x := x)

end HeytingLean.Tests.MirandaDynamics.Curl
