import HeytingLean.MirandaDynamics.External.Claims

/-!
# MirandaDynamics.External: consequences of external claims (still no axioms)

These theorems are “glue code”: they turn named external-claim wrappers into the generic
non-computability consequences provided by `Undecidability/Transfers` and `External/Interfaces`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace External

universe u

theorem not_computable_of_billiardsComputes {β : Type u} [Primcodable β] {Periodic : β → Prop} (n : ℕ)
    (h : BilliardsComputesClaim (β := β) n Periodic) : ¬ComputablePred Periodic :=
  not_computable_of_haltingReduction (β := β) (P := Periodic) n h.haltingToPeriodic

theorem not_computable_of_eulerTuringComplete {β : Type u} [Primcodable β] {Predicate : β → Prop} (n : ℕ)
    (h : EulerTuringCompleteClaim (β := β) n Predicate) : ¬ComputablePred Predicate :=
  not_computable_of_haltingReduction (β := β) (P := Predicate) n h.haltingToPredicate

theorem not_computable_of_navierStokesTuringComplete {β : Type u} [Primcodable β] {Predicate : β → Prop} (n : ℕ)
    (h : NavierStokesTuringCompleteClaim (β := β) n Predicate) : ¬ComputablePred Predicate :=
  not_computable_of_haltingReduction (β := β) (P := Predicate) n h.haltingToPredicate

end External
end MirandaDynamics
end HeytingLean

