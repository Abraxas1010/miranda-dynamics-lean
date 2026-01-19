import HeytingLean.MirandaDynamics.TKFT.PartialFlowReaching

/-!
# Tests: MirandaDynamics partial-flow reaching

This file is a proof-level sanity check that the `PartialFlow` generalization is compatible with the
existing `Flow`-based reaching relation.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Tests

open TKFT

universe u

section

variable {τ : Type u} [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
variable {α : Type u} [TopologicalSpace α]

theorem reachingRelOfPartialFlow_ofFlow_eq' (ϕ : Flow τ α) (In Out : Set α) :
    TKFT.PartialFlow.reachingRelOfPartialFlow
        (ϕ := Dynamics.PartialFlow.ofFlow (τ := τ) (α := α) ϕ) In Out =
      TKFT.reachingRelOfFlow (ϕ := ϕ) In Out :=
  TKFT.PartialFlow.reachingRelOfPartialFlow_ofFlow_eq (ϕ := ϕ) In Out

end

end Tests
end MirandaDynamics
end HeytingLean

