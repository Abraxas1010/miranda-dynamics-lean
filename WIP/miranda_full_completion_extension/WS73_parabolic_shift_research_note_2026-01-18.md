# WS7.3 / Parabolic shift walls (geometry gap): research + formalization map
Date: 2026-01-18

Goal: formalize the “parabolic shift walls” used in Miranda–Ramos (arXiv:2512.19156) Lemma 1
(`x_{t,k} ↦ x_{t,k+ε}` realized by billiard reflections), and connect them to the already mechanized
Lean spine (`tau`, `headInterval`, `encodeWithHead_shift`, and the WS7.4 map `paperFctrl?`).

## Evidence (external math)

The paper uses the standard *reflective property of a parabola*:
- rays parallel to the axis reflect through the focus;
- rays emitted from the focus reflect parallel to the axis.

Accessible references (non-Lean):
- Wikipedia: Parabola (reflection property overview): https://en.wikipedia.org/wiki/Parabola
- UVA physics notes (parabolic mirror property statement): https://galileo.phys.virginia.edu/classes/202.sc2k.spring03/chap25/chap25.html
- “Geometry of the parabola” (tangent-based proof sketch): https://www.mathed.page/parabolas/geometry/index.html

Paper references for “billiards can compute”:
- Miranda–Ramos (Dec 2025): https://ar5iv.labs.arxiv.org/html/2512.19156
- Moore (1990, PRL): “Unpredictability and undecidability in dynamical systems.” (paper bib: `tmp_paper/arxiv.bbl`)

## Mathlib/Lean mapping (what exists vs what’s missing)

Existing Lean infrastructure:
- `SpecularReflection.lean` provides `reflect` and the explicit formula `reflect_apply`.
- `LineCollision.lean` provides ray→line intersection algebra `timeToLine?`.
- `CantorEncoding.lean` provides `tau` and `encodeWithHead_shift`.
- WS7.4 target maps (`paperFgen?`, `paperFctrl?`) already encode the intended affine head update.

What appears **not** to exist in Mathlib (as of repo snapshot):
- a ready-made “parabola reflection property” lemma packaged for billiard-style use.
  (No obvious `Parabola`/`Conic` reflection lemma found by quick local search.)

External search note (2026-01-18):
- Searches for “mathlib parabola reflection property Lean” and “Lean parabola focus directrix” did not surface
  an existing Mathlib lemma capturing the optical reflection property (results were primarily calculus/geometry
  textbooks and Wikipedia-level references).
- Useful background references for the focus/directrix parameterization:
  - LibreTexts conics section: https://math.libretexts.org/Courses/City_College_of_San_Francisco/CCSF_Calculus/10%3A_Parametric_Equations_and_Polar_Coordinates/10.06%3A_Conic_Sections
  - Wikipedia (conic sections, focus/directrix): https://en.wikipedia.org/wiki/Conic_section

## New mechanized core lemma (this repo)

We can avoid calculus by using the explicit reflection formula:

- File: `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftWalls.lean`
- Core theorem: `Parabola.reflect_neg_eY_eq_smul_focus_sub`
  - For the standard parabola `y = x^2/(4f)` (focus `(0,f)`) and normal field `n(p) = (x(p), -2f)`,
    `reflect n(p) (-eY)` points toward the focus, with an explicit scalar:
    `reflect n(p) (-eY) = (4f / (x(p)^2 + 4f^2)) • (focus - p)`.
- Reverse-direction theorem: `Parabola.reflect_focus_sub_eq_smul_neg_eY`
  - The “focus → vertical” direction, derived using involutivity + linearity of `reflect`.

Additional (2026-01-18) generalization needed for the paper corridor:
- The paper’s shift gadget uses **parabolic walls sharing a common focus** but not necessarily the
  same vertex height. We added a vertical-translation family that keeps the normal field unchanged
  and preserves the reflection property:
  - `Parabola.setWithFocus f₀ f` (focus fixed at `(0,f₀)`)
  - `Parabola.reflect_neg_eY_eq_smul_focusWith_sub`
  - `Parabola.reflect_focusWith_sub_eq_smul_neg_eY`

This is the algebraic nucleus required to build the two-parabola shift corridor used in Lemma 1.

Therefore the mechanization plan for the shift gadget is:
1) Define an explicit parabola wall as a set in `V = ℝ²`, e.g. a standard-focus parabola
   (in coordinates) plus translations.
2) Define its normal field by an explicit gradient / tangent slope computation.
3) Prove a local reflection lemma (at a point on the parabola, for non-tangent incidence):
   `reflect normal v` is parallel to the axis (or passes through the focus), matching the
   classical “focus ↔ parallel” property.
4) Compose two parabolic reflections (and any necessary corridor straight segments) to realize
   the affine update used by `tau` (paper Lemma 1), then package into `PaperLink.semiconj`.

Notes:
- This remains the hardest WS7.3 gap; the appendix gives full explicit formulas only for the
  straight-wall read/write gadget, not the parabolic shift walls.
- For the shift gadget we will likely need to *choose* explicit parabolas consistent with the
  paper’s focus-sharing requirement and then prove the induced map is the desired affine update.

## Two-parabola corridor: affine update (new, mechanized)

We can realize an **affine map on the horizontal coordinate** using *two* parabolic walls sharing a
common focus, by composing the “parallel → focus” and “focus → parallel” reflection properties.

Mechanized in:
- `lean/HeytingLean/MirandaDynamics/Billiards/ParabolicShiftCorridor.lean`

Key idea:
- Fix a common focus `(a,f₀)` and two parabolas in the translated family
  `y = (x-a)^2/(4f) + (f₀ - f)`.
- Let `p₁` be the point on the outer parabola (`f₁`) at `x = x₀`.
- The ray obtained by reflecting a vertical downward ray `(-eY)` at `p₁` is collinear with
  `focus - p₁` (already in `ParabolicShiftWalls.lean`).
- The line segment from the focus to `p₁` meets the inner parabola (`f₂`) at
  `p₂ = focus + (f₂/f₁) • (p₁ - focus)`; in particular
  `x(p₂) = a + (f₂/f₁) * (x₀ - a)` is **affine** in `x₀`.
- Reflecting a ray aimed at the focus at `p₂` yields a vertical ray again.

Specializations (matches the paper’s Lemma 1 / `CantorEncoding.headShift`):
- Nonnegative branch (`k ≥ 0`): choose `a=1`, `f₁=3`, `f₂=1` so `x ↦ x/3 + 2/3`.
- Negative branch (`k < 0`): use the inverse affine map about `a=0` (time-reversal of the same
  two-parabola gadget) to obtain `x ↦ 3x`.

External context (optics reflection property, and “two reflectors” composition):
- OpenStax University Physics v3 (parabolic mirror: parallel rays → focus): https://openstax.org/books/university-physics-volume-3/pages/2-2-spherical-mirrors
- Avery (1895) quote (two parabolic reflectors “conjugate” under two reflections): https://etc.usf.edu/clipart/35900/35987/parabolic_35987.htm
