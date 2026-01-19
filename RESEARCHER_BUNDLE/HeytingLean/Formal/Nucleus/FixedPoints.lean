import Mathlib.Order.Sublocale

/-!
# Formal/Nucleus/FixedPoints — fixed points of a nucleus form a frame

Mathlib models nuclei on a frame `X` via `Nucleus`.
For a nucleus `n : Nucleus X`, the fixed-point core is the sublocale `n.toSublocale`.
The carrier of a sublocale is itself a frame.

This is a standalone extract for the Miranda Dynamics PaperPack.
-/

namespace HeytingLean
namespace Formal
namespace Nucleus

universe u

variable {X : Type u} [Order.Frame X]

/-- Fixed points of a nucleus, presented as the associated sublocale. -/
abbrev FixedPoints (n : Nucleus X) : Type u :=
  n.toSublocale

instance (n : Nucleus X) : Order.Frame (FixedPoints n) := by
  infer_instance

end Nucleus
end Formal
end HeytingLean
