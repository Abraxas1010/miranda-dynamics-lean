import HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance

/-!
# MirandaDynamics.Wolfram: causal invariance vs confluence

This module is a lightweight bridge layer that re-exports the *already verified*
Wolfram-Physics-style result living in `HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance`:

- Church–Rosser / confluence and causal invariance are independent properties.

This is the piece of the Wolfram integration that is “pure rewriting theory”.
It is orthogonal to the Miranda TKFT reaching-relations spine.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Wolfram

open HeytingLean.WPP.Wolfram

abbrev confluence_causal_invariance_independent :=
  HeytingLean.WPP.Wolfram.Counterexamples.confluence_causal_invariance_independent

abbrev CE1_confluentNF := HeytingLean.WPP.Wolfram.Counterexamples.CE1.confluentNF
abbrev CE1_not_causalInvariant := HeytingLean.WPP.Wolfram.Counterexamples.CE1.not_causalInvariant

abbrev CE2_causalInvariant := HeytingLean.WPP.Wolfram.Counterexamples.CE2.causalInvariant
abbrev CE2_not_confluentNF := HeytingLean.WPP.Wolfram.Counterexamples.CE2.not_confluentNF

end Wolfram
end MirandaDynamics
end HeytingLean

