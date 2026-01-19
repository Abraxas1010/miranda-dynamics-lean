import HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap
import HeytingLean.MirandaDynamics.Billiards.PaperLinkGeneric

/-!
# MirandaDynamics.Billiards: generic PaperLink instance for the WS7.4 cross-section model

`PaperBilliardMap.lean` defines a cross-section dynamics where the “next collision” map is exactly
`paperFctrl?` lifted to the subtype `CtrlDomain`.

This file provides that model as an instance of the generic `PaperLink` interface from
`PaperLinkGeneric.lean`, so that iteration/return scaffolding can be reused without committing to
any particular geometric billiard table yet.
-/

noncomputable section

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

namespace PaperBilliardMap

open Set

variable {m : ℕ} (next : Fin m → Bool → Fin m × Bool × ℤ)

def paperLinkGeneric : Billiards.PaperLink (CollisionState m) m next :=
  { Good := Good
    next? := next? next
    encode := encode (m := m)
    encode_mem := by
      intro s _hs
      simpa [encode] using s.pos_mem
    semiconj := by
      intro s _hs
      simpa [encode] using semiconj (m := m) (next := next) s }

end PaperBilliardMap

end Billiards
end MirandaDynamics
end HeytingLean

