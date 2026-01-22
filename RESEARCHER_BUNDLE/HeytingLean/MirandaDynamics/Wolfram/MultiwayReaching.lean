import HeytingLean.WPP.Multiway
import HeytingLean.MirandaDynamics.TKFT.Reaching

/-!
# MirandaDynamics.Wolfram: multiway systems as TKFT reaching relations

Miranda TKFT packages “computation” via abstract reaching relations between boundary
types. Wolfram-style multiway evolution is also a reaching relation: reachability in the
reflexive-transitive closure of a one-step rewrite relation.

This module gives a *definition-level* bridge:

- a `HeytingLean.WPP.WppRule` induces a `HeytingLean.MirandaDynamics.TKFT.ReachingRel`.

No correspondence theorem is asserted here beyond what is definitional.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Wolfram

open HeytingLean.WPP
open HeytingLean.MirandaDynamics.TKFT

universe u

/-- Turn a WPP multiway system (`WppRule`) into a TKFT-style reaching relation. -/
def reachingRelOfWppRule {State : Type u} (R : WppRule State) : TKFT.ReachingRel State State :=
  ⟨fun s t => WppRule.StepStar (R := R) s t⟩

@[simp] theorem reachingRelOfWppRule_rel_iff {State : Type u} (R : WppRule State) (s t : State) :
    (reachingRelOfWppRule (R := R)).rel s t ↔ WppRule.StepStar (R := R) s t :=
  Iff.rfl

end Wolfram
end MirandaDynamics
end HeytingLean

