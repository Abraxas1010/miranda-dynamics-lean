import HeytingLean.MirandaDynamics.TKFT.DiscreteBordism

/-!
# Tests: MirandaDynamics TKFT bordisms (discrete model)

Sanity checks for the semantics-first TKFT bordism layer and the discrete gluing model.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Tests

open TKFT

def trivialBordism : TKFT.DiscreteBordism Unit Unit where
  State := Unit
  step := id
  init := fun _ => ()
  done := fun _ => some ()
  done_step := by
    intro _ _ h
    exact h

example :
    (TKFT.DiscreteBordism.glue trivialBordism trivialBordism).reachingRel =
      TKFT.ReachingRel.comp trivialBordism.reachingRel trivialBordism.reachingRel := by
  simpa using
    (TKFT.DiscreteBordism.reachingRel_glue_eq_comp (In := Unit) (Mid := Unit) (Out := Unit)
      trivialBordism trivialBordism)

end Tests
end MirandaDynamics
end HeytingLean
