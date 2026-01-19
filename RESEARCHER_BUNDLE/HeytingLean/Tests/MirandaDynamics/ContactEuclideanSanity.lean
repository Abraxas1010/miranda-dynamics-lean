import HeytingLean.MirandaDynamics.Geometry.Contact.Euclidean

/-!
# Tests: MirandaDynamics contact (Euclidean) sanity

Compile-time smoke tests for the Euclidean pointwise contact/Reeb definitions.
-/

namespace HeytingLean.Tests.MirandaDynamics.ContactEuclidean

open HeytingLean.MirandaDynamics.Geometry
open HeytingLean.MirandaDynamics.Geometry.Contact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (α : Forms.Form (E := E) 1) (x : E) (R R' : E)
    (hND : Contact.NondegKer (E := E) α x)
    (hR : Contact.IsReebAt (E := E) α x R)
    (hR' : Contact.IsReebAt (E := E) α x R') :
    R' = R :=
  Contact.reeb_unique_of_nondegKer (E := E) (α := α) (x := x) hND hR hR'

end HeytingLean.Tests.MirandaDynamics.ContactEuclidean

