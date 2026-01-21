import HeytingLean.MirandaDynamics.Billiard.Reaching

/-!
# MirandaDynamics.Billiard: calibration helpers

This module provides executable bookkeeping for calibration runs.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiard

/-- Run a calibration experiment (ground truth + observations). -/
structure CalibrationRun where
  initialState : BilliardState
  evolutionTime : Float
  observationParams : ObservationParams
  trueTrajectory : Array BilliardState
  trueFinalState : BilliardState
  observations : Array Observation
  deriving Repr

def rmsError (xs ys : Array Float) : Float :=
  let n := min xs.size ys.size
  if n = 0 then
    0.0
  else
    Id.run do
      let mut acc : Float := 0.0
      for i in List.range n do
        let dx := xs[i]! - ys[i]!
        acc := acc + dx * dx
      return Float.sqrt (acc / Float.ofNat n)

/-- Measure calibration error: RMS error between true and observed final positions. -/
def calibrationError (run : CalibrationRun) : Float :=
  let truePos := run.trueFinalState.balls.map (·.pos)
  match run.observations.back? with
  | none => 0.0
  | some obs => rmsError truePos obs.positions

/-- Calibration objective: average error across runs. -/
def calibrationObjective (runs : Array CalibrationRun) : Float :=
  if runs.size = 0 then
    0.0
  else
    Id.run do
      let mut acc : Float := 0.0
      for r in runs do
        acc := acc + calibrationError r
      return acc / Float.ofNat runs.size

end Billiard
end MirandaDynamics
end HeytingLean
