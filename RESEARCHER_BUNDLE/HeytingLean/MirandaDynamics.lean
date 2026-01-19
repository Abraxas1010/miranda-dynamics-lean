import HeytingLean.MirandaDynamics.Reach
import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.TKFT.Category
import HeytingLean.MirandaDynamics.TKFT.FlowReaching
import HeytingLean.MirandaDynamics.TKFT.PartialFlowReaching
import HeytingLean.MirandaDynamics.TKFT.BordismSemantics
import HeytingLean.MirandaDynamics.TKFT.DiscreteBordism
import HeytingLean.MirandaDynamics.TKFT.RelCatBridge
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus
import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorNucleus
import HeytingLean.MirandaDynamics.Billiards.CantorTapeUpdate
import HeytingLean.MirandaDynamics.Billiards.SpecularReflection
import HeytingLean.MirandaDynamics.Billiards.Geometry
import HeytingLean.MirandaDynamics.Billiards.UnitSquare
import HeytingLean.MirandaDynamics.Billiards.UnitSquareMap
import HeytingLean.MirandaDynamics.Billiards.PaperMap
import HeytingLean.MirandaDynamics.Billiards.PaperMapFull
import HeytingLean.MirandaDynamics.Billiards.CantorDigits
import HeytingLean.MirandaDynamics.Billiards.PaperMapPiecewise
import HeytingLean.MirandaDynamics.Billiards.PaperMapGenShift
import HeytingLean.MirandaDynamics.Billiards.CantorBlocks
import HeytingLean.MirandaDynamics.Billiards.CantorCylinders
import HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit
import HeytingLean.MirandaDynamics.Billiards.HeadStateEncoding
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControl
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlBlocks
import HeytingLean.MirandaDynamics.Billiards.PaperMapFiniteControlConjugacy
import HeytingLean.MirandaDynamics.Billiards.GeometryToPaperTarget
import HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlPaperLink
import HeytingLean.MirandaDynamics.Computation.TuringMachine
import HeytingLean.MirandaDynamics.Computation.GeneralizedShift
import HeytingLean.MirandaDynamics.Computation.GeneralizedShiftControl
import HeytingLean.MirandaDynamics.Computation.GeneralizedShiftPeriodic
import HeytingLean.MirandaDynamics.Computation.FlowRealization
import HeytingLean.MirandaDynamics.Computation.FlowRealizationPeriodic
import HeytingLean.MirandaDynamics.Topology.BettiComplexity
import HeytingLean.MirandaDynamics.Undecidability.Transfers
import HeytingLean.MirandaDynamics.External.Interfaces
import HeytingLean.MirandaDynamics.External.Claims
import HeytingLean.MirandaDynamics.External.Consequences
import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.MirandaDynamics.Discrete.HaltSys
import HeytingLean.MirandaDynamics.Discrete.GeneralizedShiftBridge
import HeytingLean.MirandaDynamics.Discrete.FlowBridge
import HeytingLean.MirandaDynamics.HeytingTuring.Correspondence
import HeytingLean.MirandaDynamics.Fluids.ContactLinear
import HeytingLean.MirandaDynamics.Fluids.ContactLinearFlow
import HeytingLean.MirandaDynamics.Geometry.Forms.Manifold
import HeytingLean.MirandaDynamics.Geometry.Contact.Euclidean
import HeytingLean.MirandaDynamics.Fluids.VectorCalculus.Curl3
import HeytingLean.MirandaDynamics.Fluids.VectorCalculus.GradDiv3

/-!
# MirandaDynamics (umbrella)

This umbrella module collects the Lean-realistic spine of the “Miranda integration” project:

- reachability/simulation tooling (re-exported),
- TKFT-style reaching relations and their compositional laws,
- a nucleus/fixed-point view of “periodicity” (specialized to the existing Flow lens),
- undecidability-transfer lemmas (halting → dynamical predicate).

The analytic geometry/PDE results from the external literature are *referenced in docs* but are not
reproved here.
-/
