# Discrete Halting ↔ Periodic Bridge

## Overview

The central insight of computational dynamics: **halting is periodic**.

A Turing machine halts if and only if its corresponding dynamical system
reaches a period-2 (or period-k) orbit. This transforms the halting problem
from a termination question into an orbit structure question.

## The Main Theorem

```lean
-- Main mechanized statement (Mathlib’s partial-recursion halting model):
theorem reachesPeriod2_iff_halts (n : Nat) (c : Nat.Partrec.Code) :
    ReachesPeriod2 n c ↔ Undecidability.Halting.Halts n c
```

**Interpretation**:
- `Undecidability.Halting.Halts n c`: the partial-recursion code `c` halts on input `n`
- `ReachesPeriod2 n c`: the induced dynamical system reaches a 2-cycle

## Why Period-2?

In billiard encodings, a halted machine corresponds to the ball bouncing
back and forth between two walls—a period-2 orbit. The choice of period-2
is conventional; period-k works similarly.

## Discrete Stepping as Flows

`Discrete/FlowBridge.lean` shows how discrete Turing machine steps can be
viewed as a degenerate flow:

```lean
def discreteFlow (step : α → α) : Flow ℤ α where
  toFun n x := step^[n.toNat] x
  ...
```

This allows applying TKFT machinery to discrete systems.

## Generalized Shift Integration

`Discrete/GeneralizedShiftBridge.lean` connects halting to generalized shift
spaces (a la symbolic dynamics):

```lean
theorem halts_iff_reaches_period_in_shift (tm : TuringMachine) (cfg : Config) :
    tm.halts cfg ↔ reachesPeriodInShift (embed tm cfg)
```

## Files

| File | Contents |
|------|----------|
| `Discrete/HaltingToPeriodic.lean` | Main equivalence theorem |
| `Discrete/FlowBridge.lean` | Discrete → Flow translation |
| `Discrete/GeneralizedShiftBridge.lean` | Shift space embedding |
| `Discrete/HaltSys.lean` | Halting system abstraction |

## Undecidability Transfer

Combined with `Undecidability/Transfers.lean`:

```lean
theorem not_computable_of_halting_reduces {P : ℕ → Prop}
    (hred : ReducesToHalting P) : ¬Computable P
```

If detecting property P reduces to detecting halting, P is undecidable.

## References

- Miranda, E., & Ramos, I. (2025). *Classical billiards can compute*. Section 4
- Cardona, R., et al. (2021). *Turing complete Euler flows*. Section 2
