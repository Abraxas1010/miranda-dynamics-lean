import HeytingLean.MirandaDynamics.Wolfram.CausalInvariance
import HeytingLean.MirandaDynamics.Wolfram.MultiwayReaching
import HeytingLean.MirandaDynamics.Wolfram.BranchialHeyting
import HeytingLean.MirandaDynamics.Wolfram.MirandaTKFT

/-!
# MirandaDynamics.Wolfram: bridge umbrella

This namespace is the *Miranda-facing* access point for the existing Wolfram Physics
formalization already living in the main HeytingLean repo.

In this standalone repository, the policy is:

- **Copy from main** (do not re-prove): `HeytingLean.WPP.Wolfram.*` and the Wolfram CLI tools.
- Provide a thin Miranda/TKFT-facing API surface that is stable for later correspondence work.

Important: this file does **not** claim any “big correspondence theorem” (TKFT ≃ multiway)
unless it is already available as a proved theorem. It only exposes definitional bridges and
re-exports verified results.
-/

