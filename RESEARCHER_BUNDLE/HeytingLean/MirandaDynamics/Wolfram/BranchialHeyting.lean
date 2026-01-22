import HeytingLean.WPP.Wolfram.Branchial

/-!
# MirandaDynamics.Wolfram: branchial structure (re-export)

For the standalone Miranda repo we currently treat “branchial space” as a structural input
coming from the Wolfram multiway layer (in `HeytingLean.WPP.Wolfram.Branchial`).

This module exists mainly to give the Miranda/Wolfram namespace a stable home so later work
can connect branchial constructions to a Heyting algebra / nucleus story, without duplicating
WPP internals.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Wolfram

-- Re-export branchial constructions from WPP.Wolfram
export HeytingLean.WPP.Wolfram.System (siblingEdges branchialEdgesAtDepth pathCountAtDepth)

end Wolfram
end MirandaDynamics
end HeytingLean

