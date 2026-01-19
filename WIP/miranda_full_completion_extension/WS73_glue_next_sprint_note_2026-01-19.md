# WS7.3 Glue Next Sprint Note (2026-01-19): straight + rewrite + parabolic return step

This note records the **next concrete mechanizable phase** after the corridor-local deterministic
results for:

- straight gadget between-wall flight (`PaperReadWriteStraightBetweenDeterministic.lean`);
- rewrite gadget between-wall flight with *global* redirecting union
  (`PaperReadWriteRewriteBetweenDeterministicGlobal.lean`);
- two-parabola head-shift corridor minimal-time hits
  (`ParabolicShiftCorridorDeterministic.lean`).

The long-horizon goal is still WS7.3 proper: a **geometric** collision cross-section and a global
deterministic minimal-time `next?` (or a return map) whose decoding simulates one step of
`GenShiftCtrlMap.next?`, yielding `PaperLink.semiconj` into `paperFctrl?`.

## What we can mechanize next (without committing to the full infinite table)

### 1) A staged “macro return step” as a composition of corridor-local `next?`

Define a *macro* partial map which is explicitly the composition of the already-proved corridor
steps:

1. straight between-wall hit (redirecting wall),
2. rewrite between-wall hit (redirecting wall),
3. parabolic two-bounce head shift.

This macro is not yet a single global `Table.DeterministicNext.next?` over the union of *all* walls;
it is a **staged return-step model** used to isolate the remaining glue obligations.

Implementation sketch:

- Define a cross-section type `ReturnState` containing exactly the parameters needed to run each
  corridor step (head index `k`, prefix `pref`, `cur`, control state, and any cached “domain proofs”
  needed by existing entry structures).
- Define `returnNext? : ReturnState → Option ReturnState` by chaining:
  - `AppendixBetween.next?` (straight between),
  - `RewriteBetweenGlobal.next?` (rewrite between),
  - `ParabolicShiftCorridorDeterministic.next2?` (parabolic corridor),
  plus any simple deterministic “connector” normalizations (coordinate shifts) between corridors.

Deliverable: a file that compiles and exposes `returnNext?_eq_some` on a concrete `Good` predicate.

### 2) A `decode_step` theorem for the macro return step

Once `ReturnState` is defined so that it *already contains* the discrete controlled-shift data, the
decoding map can be chosen directly:

- `decode : ReturnState → GenShiftCtrlCfg (Fin m) Bool`.

Then prove the commuting square:

- `Option.map decode (returnNext? s) = GenShiftCtrlMap.next? next (decode s)` on `Good s`.

This discharges the same `decode_step` shape used by
`GeometryToGenShiftCtrlLink.lean`, but for a staged return-step model.

Deliverable: a `GeometryToGenShiftCtrl.Link` instance for `ReturnState`, and the induced
`PaperLink.semiconj` into `paperFctrl?` (purely symbolic, but with corridor-local geometry feeding it).

## The remaining hard blockers (true WS7.3 geometry)

Even after a macro-step model exists, the **actual** WS7.3 geometry still requires:

1) A single billiard table boundary as an (infinite) union of:
   - straight separating walls,
   - straight redirecting walls,
   - rewrite separating + rewrite redirecting walls,
   - parabolic shift walls,
   with a collision-space cross-section in its phase space.

2) Global deterministic minimal-time `next?` on that collision space:
   - `Good → next?` defined,
   - collision uniqueness,
   - exclusion of corners/endpoints/tangencies,
   - “no spurious collisions” across the full union for the relevant flight segments.

3) A *geometric* `decode` from collision states to `GenShiftCtrlCfg` (or directly to `(x,z)`):
   - must extract the correct discrete branch data from wall membership,
   - must be stable under the dynamics (so that `decode_step` holds for the global `next?`).

The corridor-local deterministic results are prerequisites for (2), but do not by themselves provide
the global “no spurious collision” proofs across the entire union.

## Minimal inputs needed to push further

- Clarify the intended **connector geometry** between the end of the rewrite corridor and the entry
  of the parabolic corridor in the paper’s actual table:
  - coordinate conventions (which axis is “vertical incoming” for the parabolic gadget),
  - any affine coordinate shifts that align the output of one corridor with the next.
- Confirm where the authoritative Appendix flight-line convention is recorded in the repo
  (some earlier notes reference `miranda_integration.md`, but that filename is not present in-tree).

