/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Bounded
import Tdaf.Analysis.Convex.Subgradient.Convergence
import Tdaf.Analysis.Convex.Subgradient.Integral
import Tdaf.Analysis.Convex.Subgradient.Primitive
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §24: Differential Continuity and Monotonicity

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §24, pp. 227–240: the continuity and
monotonicity properties of `∂f`, first on the line and then on `ℝⁿ`, ending with the
characterisation of the subdifferentials as the maximal cyclically monotone mappings.

## The two ambient spaces

Theorems 24.1–24.3 are about a closed proper convex function **on `R`**, and this module states
them over `ℝ` itself rather than over `Rn 1`. That is the book's own reading — `R` is the real
line, and every object in those three theorems (a one-sided derivative, a non-decreasing function,
a subset of `R²`) is a real-analytic object, not a coordinate one. It also matches
`Tdaf/Analysis/Convex/Subgradient/OneDim.lean`, which is stated for `f : ℝ → EReal`; §6 and §15
made the same choice for the same reason. The pairing on the line is `innerₗ ℝ`, which is
multiplication, and `pairing 1` never appears.

Theorems 24.4–24.9 are about `Rn n` and use `pairing n`.

## `f'₊` and `f'₋` are the backbone's `rightDeriv` and `leftDeriv`

Rockafellar extends the one-sided derivatives "beyond the interval `dom f`, setting both `= +∞` for
points lying to the right of `dom f` and both `= -∞` for points lying to the left". The backbone's
`rightDeriv` / `leftDeriv` are defined with exactly that extension built in — as *guarded* infima
and suprema, `+∞` when no point of `dom f` lies to the right and `-∞` when none lies to the left —
so no surface definition is needed and nothing here has to case-split on the position of `x`
relative to `dom f`. Where `f` is finite the guard is inert and `f'₊(x) = f'(x; 1)`,
`f'₋(x) = -f'(x; -1)`.

## The complete non-decreasing curves

The book gives two descriptions of a **complete non-decreasing curve** in `R²`, one after the
other:

* line 9181, as a *definition*: `Γ = {(x, x*) | φ₋(x) ≤ x* ≤ φ₊(x)}` for a non-decreasing
  `φ : R → [-∞, +∞]` that is not everywhere infinite;
* line 9195, as a *characterisation*: the maximal totally ordered subsets of `R²` for the
  coordinatewise partial ordering.

The second is pure order theory and is what this module takes as `IsCompleteNonDecreasingCurve`,
per design decision D12: it is `IsMaxChain (· ≤ ·)` from Mathlib's order library, with the product
order on `ℝ × ℝ` supplying "coordinatewise", and no hand-rolled development. The first is the
backbone's `monotoneCurve φ`, and `isCompleteNonDecreasingCurve_monotoneCurve` is the implication
from the book's definition to the order-theoretic one. The reverse implication is a backbone gap;
see below.

## Contents

| label | declarations |
|---|---|
| Theorem 24.1 | `theorem_24_1_monotone_rightDeriv`, `theorem_24_1_monotone_leftDeriv`,
  `theorem_24_1_finite_iff`, `theorem_24_1_chain`, `theorem_24_1_tendsto_rightDeriv_Ioi`,
  `theorem_24_1_tendsto_rightDeriv_Iio`, `theorem_24_1_tendsto_leftDeriv_Ioi`,
  `theorem_24_1_tendsto_leftDeriv_Iio`, `theorem_24_1_subgradient` |
| Theorem 24.2 | `theorem_24_2_exists`, `theorem_24_2_unique`, `theorem_24_2` |
| Corollary 24.2.1 | `corollary_24_2_1_rightDeriv`, `corollary_24_2_1_leftDeriv` |
| Theorem 24.3 | `theorem_24_3`, `theorem_24_3_unique`,
  `theorem_24_3_subgradientRel_eq_monotoneCurve`, `theorem_24_3_swap` |
| Theorem 24.4 | `theorem_24_4`, `theorem_24_4_seq` |
| Theorem 24.5 | `theorem_24_5_lt`, `theorem_24_5_limsup`, `theorem_24_5_subgradient` |
| Corollary 24.5.1 | `corollary_24_5_1_upperSemicontinuous`, `corollary_24_5_1_subgradient` |
| Theorem 24.6 | `theorem_24_6_lt`, `theorem_24_6_limsup`, `theorem_24_6_subgradient` |
| Theorem 24.7 | `theorem_24_7_bound`, `theorem_24_7_nonempty`, `theorem_24_7_isCompact`,
  `theorem_24_7_isClosed`, `theorem_24_7_isBounded` |
| Theorem 24.8 | `theorem_24_8`, `theorem_24_8_of_isCyclicallyMonotone` |
| Theorem 24.9 | `theorem_24_9`, `theorem_24_9_subgradientRel`, `theorem_24_9_unique` |
| §24 closing (9613–9631) | `isMonotoneRel_subgradientRel_rn`,
  `isMonotoneRel_iff_isCyclicallyMonotone_line` |

## The section's definitions

* `Rockafellar.IsCompleteNonDecreasingCurve Γ` — `IsMaxChain (· ≤ ·) Γ`, the book's line-9195
  characterisation. `isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel` is its bridge to the
  backbone's `IsMaximalMonotoneRel (innerₗ ℝ)`, and nothing below unfolds the definition.
* `Rockafellar.subgradientNormal f x y` — Rockafellar's `∂f(x)_y`, "the points `x* ∈ ∂f(x)` such
  that `y` is normal to `∂f(x)` at `x*`", written with the backbone's `normalCone`.
  `subgradientNormal_eq_sep` is its bridge to the maximisation form the backbone's Theorem 24.6
  produces.

## What is not here

**Deferred by scope.**

* **Theorem 24.2's integral formula.** The book *defines* `f(x) = ∫ₐˣ φ(t) dt` for an arbitrary
  non-decreasing `φ : R → [-∞, +∞]` and proves that this `f` is closed proper convex with
  `f'₋ = φ₋ ≤ φ ≤ φ₊ = f'₊`. The integral is improper at the two finite endpoints of the interval
  where `φ` is finite, and it is `+∞` outside that interval — one-dimensional Lebesgue theory, not
  convex analysis. **Everything the theorem asserts is nevertheless stated here**: `theorem_24_2`
  gives existence, the identification of the two one-sided derivatives, and uniqueness up to an
  additive constant. What is missing is only the *formula* exhibiting the primitive, and nothing
  in the book depends on it — Rockafellar's own later use, in the proof of Theorem 24.9, is of
  Corollary 24.2.1, which is proved here.
* **The homeomorphism `(x, x*) ↦ x + x*` from `Γ` onto `R`** (line 9193, "an elementary exercise").
  This is the one-dimensional shadow of **Corollary 31.5.1**, and it is deferred to §31 rather than
  proved twice: when §31 is written it must be *derived* there and specialised back to `n = 1`, not
  re-proved on the line. Note that the backbone does use the *surjectivity* half of it — that is
  `exists_mem_monotoneCurve_sub`, which is what makes `monotoneCurve φ` maximal — but injectivity
  and bicontinuity are nowhere needed and are nowhere proved.

**Omitted with a reason.**

* **The two worked examples** (lines 9049–9069, the function `|x| - 2(1-x)^{1/2}` on `[-3, 1]`, and
  lines 9073–9095, the non-closed `f` whose `f'₊` is not right-continuous at `0`) are numerical
  illustrations, not results. The second is recorded as a design note in the backbone's
  `Subgradient/OneDim.lean`, which is where the closedness hypothesis of the four limit formulas is
  justified.
* **The counterexample to equality in Theorem 24.5** (line 9325, `f i x = |x|^{p i}` with `p i ↓ 1`
  against `f x = |x|`) is likewise an illustration; it is recorded in the backbone's
  `Subgradient/Convergence.lean` module docstring.
* **"`ρ` is cyclically monotone iff `Q` is symmetric positive semi-definite"** (line 9623) is left
  by the book itself as an exercise deduced from Theorem 24.9, and is not a numbered result.
* **The opening paragraph's `ri (dom f) ⊆ dom ∂f ⊆ dom f` and `range ∂f = dom ∂f*`** are Theorem
  23.4 and Corollary 23.5.1 quoted, and belong to §23.

## Backbone gaps

**`Subgradient/Primitive.lean`: every subdifferential on the line is the curve of a non-decreasing
function that is finite somewhere.** Wanted:

```
theorem exists_monotone_ne_bot_ne_top_monotoneCurve_eq (hf : ClosedProperConvexFn f) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧
      subgradientRel (innerₗ ℝ) f = monotoneCurve φ
```

`subgradientRel_eq_monotoneCurve_rightDeriv` already gives `∂f = Γ(f'₊)` with `f'₊` non-decreasing,
so the only missing clause is that `φ` may be chosen **finite at a point**. `f'₊` itself is finite
on `int (dom f)` and so serves whenever `dom f` has an interior point; the one case it does not
cover is `dom f` a single point `a`, where `f'₊` is `-∞` to the left of `a` and `+∞` from `a` on.
There a suitable `φ` exists — take `-∞` on `Iio a`, `0` at `a` and `+∞` on `Ioi a`, whose curve is
`{a} × ℝ = ∂f` — but exhibiting it means either a two-branch definition or the perturbation of
`f'₊` at one point (`φ = f'₊` off `a`, `φ a = y₀` for any `y₀ ∈ ∂f a`), and checking that the
perturbation leaves `Γ` unchanged. That check is the missing lemma, and it belongs next to
`subgradientRel_eq_monotoneCurve_rightDeriv`, not here. **Consequence for this module**: the
implication from the book's *definition* of a complete non-decreasing curve to the order-theoretic
characterisation is stated (`isCompleteNonDecreasingCurve_monotoneCurve`); the converse is not.
Theorem 24.3 itself is unaffected, because it is stated in the order-theoretic form the book gives
at line 9195.

## Where the book's statements had to change

**Theorem 24.4 needs neither convexity nor closedness of `f`, only lower semicontinuity and
properness.** Rockafellar states it for a closed proper convex `f` and proves it through Theorem
23.5, i.e. through the conjugate. The backbone's `isClosed_subgradientRel` writes the graph as an
intersection of preimages of `epi f` and uses convexity nowhere. The surface states the book's
hypotheses and records the difference rather than re-deriving them.

**Theorem 24.5's properness is derived, not assumed.** The book asks only that the functions be
*finite* on the open convex `C`; the backbone asks for `Proper` and `C ⊆ dom`. The two are the
same here, and `proper_of_finite_on_isOpen` below is the derivation: an improper convex function is
`-∞` throughout `ri (dom f)` (Theorem 7.2), `C` is open and inside `dom f`, hence inside
`ri (dom f)`, and `f` is finite at the point of `C` the theorem quantifies over. So the surface
states the book's hypotheses verbatim and pays one private lemma for them, rather than adding
`Proper` to the statement.

**Theorem 24.7 is stated with a constant that is at least the book's `α`.** Rockafellar defines
`α = sup {|x*| : x* ∈ ∂f(S)}` and then proves the two inequalities for it. The backbone produces a
Lipschitz constant on a compact collar of `S` first and reads all three statements off it, so what
is stated is the existence of *some* `α` with the three properties — which is what every consumer
uses, and which is implied by (not equivalent to) the book's sharper reading.

## The warning at line 9631

Rockafellar states explicitly that maximal *monotonicity* of `∂f` — Corollary 31.5.2 — **does not**
follow from Theorem 24.9 together with "cyclically monotone implies monotone": a mapping maximal in
the smaller class need not be maximal in the larger one. This module therefore states
`theorem_24_9` for maximal *cyclic* monotonicity only, and `isMonotoneRel_subgradientRel_rn` for
plain monotonicity of `∂f`, with no bridge between them. The backbone keeps the two apart in the
same way. On the **line** the two classes do coincide (book line 9623, and
`isMonotoneRel_iff_isCyclicallyMonotone_line` here), which is exactly why Theorem 24.3 can be
stated for maximal chains; that
coincidence is one-dimensional and is not available for `n > 1`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
-/

open Set Filter Topology
open scoped Pointwise RealInnerProductSpace

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### Theorem 24.1: the one-sided derivatives on the line

`f'₊` and `f'₋` are the backbone's `rightDeriv` and `leftDeriv`, which carry Rockafellar's
extension by `±∞` outside `dom f` in their definitions. -/

section OneDim

variable {f : ℝ → EReal}

/-- **Rockafellar, Theorem 24.1**: `f'₊` is a non-decreasing function on `R`.

Closedness is not needed for this clause, nor for the next three: the interlacing chain is an
inequality between difference quotients and holds for every proper convex `f`. -/
theorem theorem_24_1_monotone_rightDeriv (hf : ConvexFn f) (hp : Proper f) :
    Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

/-- **Rockafellar, Theorem 24.1**: `f'₋` is a non-decreasing function on `R`. -/
theorem theorem_24_1_monotone_leftDeriv (hf : ConvexFn f) (hp : Proper f) :
    Monotone (leftDeriv f) :=
  monotone_leftDeriv hf hp

/-- **Rockafellar, Theorem 24.1**: `f'₊` and `f'₋` are finite exactly on `int (dom f)`.

The book says "finite on the interior of `dom f`"; the backbone's biconditional says slightly more,
namely that finiteness of the two one-sided derivatives *characterises* the interior points. -/
theorem theorem_24_1_finite_iff (hf : ConvexFn f) (hp : Proper f) {x : ℝ} :
    (⊥ < leftDeriv f x ∧ rightDeriv f x < ⊤) ↔ x ∈ interior (dom f) :=
  bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp

/-- **Rockafellar, Theorem 24.1**, the interlacing chain:
`f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)` when `z₁ < x < z₂`. -/
theorem theorem_24_1_chain (hf : ConvexFn f) (hp : Proper f) {z₁ x z₂ : ℝ} (h₁ : z₁ < x)
    (h₂ : x < z₂) :
    rightDeriv f z₁ ≤ leftDeriv f x ∧ leftDeriv f x ≤ rightDeriv f x ∧
      rightDeriv f x ≤ leftDeriv f z₂ :=
  ⟨rightDeriv_le_leftDeriv hp h₁, leftDeriv_le_rightDeriv hf hp x, rightDeriv_le_leftDeriv hp h₂⟩

/-- **Rockafellar, Theorem 24.1**, first limit formula: `lim_{z ↓ x} f'₊(z) = f'₊(x)`.

Closedness is essential here and in the three companions. For the convex proper `f` that is `1` at
`0`, `0` on `(0, ∞)` and `+∞` on `(-∞, 0)`, `f'₊` is `-∞` at `0` and `0` to the right of it, so
this limit fails; the backbone records the example. -/
theorem theorem_24_1_tendsto_rightDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Ioi hf x

/-- **Rockafellar, Theorem 24.1**, second limit formula: `lim_{z ↑ x} f'₊(z) = f'₋(x)`. -/
theorem theorem_24_1_tendsto_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Iio hf x

/-- **Rockafellar, Theorem 24.1**, third limit formula: `lim_{z ↓ x} f'₋(z) = f'₊(x)`. -/
theorem theorem_24_1_tendsto_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Ioi hf x

/-- **Rockafellar, Theorem 24.1**, fourth limit formula: `lim_{z ↑ x} f'₋(z) = f'₋(x)`. -/
theorem theorem_24_1_tendsto_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Iio hf x

/-- **Rockafellar, §24 (line 9043)**, the remark following Theorem 24.1:
`∂f(x) = {x* ∈ R | f'₋(x) ≤ x* ≤ f'₊(x)}`, "as already pointed out after Theorem 23.2".

Only properness is needed. -/
theorem theorem_24_1_subgradient (hp : Proper f) (x : ℝ) :
    subgradient (innerₗ ℝ) f x
      = {y : ℝ | leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x} :=
  Set.ext fun _ => mem_subgradient_iff_le_rightDeriv hp

end OneDim

/-! ### Theorem 24.2 and Corollary 24.2.1: the primitive of a non-decreasing function -/

section Primitive

variable {φ : ℝ → EReal}

/-- **Rockafellar, Theorem 24.2**, existence with the identification of the two one-sided
derivatives: for a non-decreasing `φ` finite at `a` there is a closed proper convex `f` on `R` with
`f'₋ = φ₋` and `f'₊ = φ₊`, where `φ₋(x) = lim_{z ↑ x} φ(z)` and `φ₊(x) = lim_{z ↓ x} φ(z)`.

The book exhibits this `f` as `∫ₐˣ φ(t) dt`; the integral is deferred by scope and is not needed —
the backbone builds `f` from the *graph* `Γ(φ)`, which is a maximal monotone relation, and reads
the derivatives off `∂f`. -/
theorem theorem_24_2_exists (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧
      (∀ x, leftDeriv f x = ⨆ z ∈ Iio x, φ z) ∧ (∀ x, rightDeriv f x = ⨅ z ∈ Ioi x, φ z) :=
  exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq hφ hb ht

/-- **Rockafellar, Theorem 24.2**, uniqueness clause: two closed proper convex functions on `R`
squeezed around the same `φ` — `f'₋ ≤ φ ≤ f'₊` and `g'₋ ≤ φ ≤ g'₊` — differ by a constant.

This is the clause of Theorem 24.2 that is **reachable without the integral**, and the backbone
proves it without one: the two squeezes force `∂f = ∂g`, and a subdifferential determines a closed
proper convex function up to an additive constant. -/
theorem theorem_24_2_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (hf₁ : ∀ x, leftDeriv f x ≤ φ x) (hf₂ : ∀ x, φ x ≤ rightDeriv f x)
    (hg₁ : ∀ x, leftDeriv g x ≤ φ x) (hg₂ : ∀ x, φ x ≤ rightDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_eq_add_coe_of_le_le hf hg hf₁ hf₂ hg₁ hg₂

/-- **Rockafellar, Theorem 24.2** in the shape the book states it, minus the integral formula: for a
non-decreasing `φ` finite at `a` there is a closed proper convex `f` on `R` with `f'₋ ≤ φ ≤ f'₊`,
and any other such function is `f + α`. -/
theorem theorem_24_2 (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ (∀ x, leftDeriv f x ≤ φ x) ∧
      (∀ x, φ x ≤ rightDeriv f x) ∧
      ∀ g : ℝ → EReal, ClosedProperConvexFn g → (∀ x, leftDeriv g x ≤ φ x) →
        (∀ x, φ x ≤ rightDeriv g x) → ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_closedProperConvexFn_forall_le_le hφ hb ht

/-- **Rockafellar, Corollary 24.2.1**, right-derivative half: on the interior of its effective
domain — the book's non-empty open interval `I` — a proper convex function on `R` is the integral
of `f'₊`,

```
f(y) - f(x) = ∫ₓʸ f'₊(t) dt.
```

**This corollary is not deferred.** The plan recorded it as out of scope together with Theorem
24.2's integral formula, but the two are different statements: here the integrand is the derivative
of a function already known to be convex and finite on an open interval, so the fundamental theorem
of calculus applies directly and no improper integral and no Lebesgue theory of monotone functions
appears. The backbone proves it in `Subgradient/Integral.lean`. -/
theorem corollary_24_2_1_rightDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : Proper f) {x y : ℝ}
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (rightDeriv f t).toReal :=
  sub_eq_intervalIntegral_rightDeriv hf hp hx hy

/-- **Rockafellar, Corollary 24.2.1**, left-derivative half: `f(y) - f(x) = ∫ₓʸ f'₋(t) dt`.

The two one-sided derivatives differ only on the jump set of `f'₊`, which is countable and
therefore null. -/
theorem corollary_24_2_1_leftDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : Proper f) {x y : ℝ}
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (leftDeriv f t).toReal :=
  sub_eq_intervalIntegral_leftDeriv hf hp hx hy

end Primitive

/-! ### Theorem 24.3: the complete non-decreasing curves

Rockafellar's characterisation at line 9195 — "the maximal totally ordered subsets of `R²` with
respect to the coordinatewise partial ordering" — is Mathlib's `IsMaxChain (· ≤ ·)` for the product
order on `ℝ × ℝ`, and that is what the surface takes as the definition (design decision D12). -/

section Curve

variable {Γ : Set (ℝ × ℝ)}

/-- **Rockafellar, §24 (line 9195).** A **complete non-decreasing curve** in `R²` is a maximal
totally ordered subset for the coordinatewise partial ordering — a maximal chain.

The book introduces the notion at line 9181 by the formula
`Γ = {(x, x*) | φ₋(x) ≤ x* ≤ φ₊(x)}` for a non-decreasing `φ` that is not everywhere infinite, and
then records this order-theoretic description as an equivalent one.
`isCompleteNonDecreasingCurve_monotoneCurve` is the implication from the formula to the definition
taken here; the converse is a backbone gap, recorded in the module docstring. -/
def IsCompleteNonDecreasingCurve (Γ : Set (ℝ × ℝ)) : Prop :=
  IsMaxChain (· ≤ ·) Γ

/-- **The bridge to the backbone**: a maximal chain of `ℝ × ℝ` is exactly a maximal monotone
relation on the line. Monotonicity of a relation on `R` *is* total ordering of its graph
(`isMonotoneRel_iff_forall_le_or_le`), the only difference between the two spellings being that
`IsChain` excuses the diagonal, which `le_refl` supplies.

Nothing below unfolds `IsCompleteNonDecreasingCurve`; every proof goes through this lemma. -/
theorem isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel :
    IsCompleteNonDecreasingCurve Γ ↔ IsMaximalMonotoneRel (innerₗ ℝ) Γ := by
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ ↔ IsMonotoneRel (innerₗ ℝ) σ := by
    intro σ
    rw [isMonotoneRel_iff_forall_le_or_le]
    refine ⟨fun h p hp q hq => ?_, fun h => fun p hp q hq _ => h p hp q hq⟩
    rcases eq_or_ne p q with rfl | hne
    · exact Or.inl le_rfl
    · exact h hp hq hne
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).1 h₁, fun σ hσ hsub => ((h₂ ((hchain σ).2 hσ) hsub) ▸ subset_rfl : σ ⊆ Γ)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).2 h₁, fun σ hσ hsub =>
      Subset.antisymm hsub (h₂ σ ((hchain σ).1 hσ) hsub)⟩

/-- **Rockafellar, §24 (line 9181) implies line 9195**: the region between the two one-sided limits
of a non-decreasing `φ` that is finite somewhere is a complete non-decreasing curve.

This is the direction of the book's equivalence that the backbone supplies, and it is the one
Theorem 24.2 consumes: maximality of `Γ(φ)` is what produces the primitive. -/
theorem isCompleteNonDecreasingCurve_monotoneCurve {φ : ℝ → EReal} (hφ : Monotone φ) {a : ℝ}
    (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) : IsCompleteNonDecreasingCurve (monotoneCurve φ) :=
  isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel.2
    (isMaximalMonotoneRel_monotoneCurve hφ hb ht)

/-- **Rockafellar, Theorem 24.3**: the graphs of the subdifferential mappings of the closed proper
convex functions on `R` are precisely the complete non-decreasing curves in `R²`. -/
theorem theorem_24_3 :
    IsCompleteNonDecreasingCurve Γ ↔
      ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ Γ = subgradientRel (innerₗ ℝ) f := by
  rw [isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel]
  exact isMaximalMonotoneRel_iff_exists_closedProperConvexFn

/-- **Rockafellar, Theorem 24.3**, second clause: `f` is uniquely determined by `Γ` up to an
additive constant.

`eq_add_coe_of_subgradientRel_subset` needs only the *inclusion* `∂f ⊆ ∂g`, which is what makes
Theorem 24.9's maximality argument work; here the two graphs are equal. -/
theorem theorem_24_3_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **Rockafellar, Theorem 24.3**, the converse direction in the book's line-9181 vocabulary: the
graph of `∂f` *is* the region between the two one-sided limits of `f'₊`.

This is the whole of the converse except for the book's requirement that the generating `φ` be
finite somewhere; see the module docstring's backbone gap. -/
theorem theorem_24_3_subgradientRel_eq_monotoneCurve {f : ℝ → EReal} (hf : ClosedProperConvexFn f) :
    subgradientRel (innerₗ ℝ) f = monotoneCurve (rightDeriv f) :=
  subgradientRel_eq_monotoneCurve_rightDeriv hf

/-- **Rockafellar, §24 (line 9203)**, the remark following Theorem 24.3: if `Γ` is a complete
non-decreasing curve then so is `Γ* = {(x*, x) | (x, x*) ∈ Γ}`.

The book proves it by conjugacy — `Γ* = graph ∂f*` by Theorem 23.5. Order-theoretically it is
free: `Prod.swap` is an order isomorphism of `ℝ × ℝ`, so it carries chains to chains and maximal
chains to maximal chains. -/
theorem theorem_24_3_swap (h : IsCompleteNonDecreasingCurve Γ) :
    IsCompleteNonDecreasingCurve (Prod.swap '' Γ) := by
  have hswap : ∀ p q : ℝ × ℝ, p.swap ≤ q.swap ↔ p ≤ q := fun p q => by
    simp only [Prod.le_def, Prod.fst_swap, Prod.snd_swap]
    exact and_comm
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ → IsChain (· ≤ ·) (Prod.swap '' σ) := by
    rintro σ hσ _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    rcases hσ hp hq hpq with hle | hle
    · exact Or.inl ((hswap p q).2 hle)
    · exact Or.inr ((hswap q p).2 hle)
  refine ⟨hchain Γ h.1, fun t ht hsub => ?_⟩
  have hpre : Γ ⊆ Prod.swap '' t := by
    rintro p hp
    exact ⟨p.swap, hsub ⟨p, hp, rfl⟩, by simp⟩
  have hEq : Γ = Prod.swap '' t := h.2 (hchain t ht) hpre
  rw [hEq, ← Set.image_comp]
  simp

end Curve

/-! ### Theorem 24.4: the graph of `∂f` is closed -/

section GraphClosed

variable {n : ℕ} {f : Rn n → EReal}

/-- **Rockafellar, Theorem 24.4**: the graph of `∂f` is a closed subset of `Rⁿ × Rⁿ`.

Convexity is not used, and closedness of `f` enters only through lower semicontinuity; the book's
proof runs through Theorem 23.5 and the conjugate, whereas the backbone writes the graph directly
as an intersection of preimages of `epi f`. -/
theorem theorem_24_4 (hf : ClosedProperConvexFn f) : IsClosed (subgradientRel (pairing n) f) :=
  isClosed_subgradientRel continuous_inner hf.proper hf.lowerSemicontinuous

/-- **Rockafellar, Theorem 24.4** in the book's own words: if `xᵢ* ∈ ∂f(xᵢ)` with `xᵢ → x` and
`xᵢ* → x*`, then `x* ∈ ∂f(x)`. -/
theorem theorem_24_4_seq (hf : ClosedProperConvexFn f) {xs ys : ℕ → Rn n} {x y : Rn n}
    (hmem : ∀ i, ys i ∈ subgradient (pairing n) f (xs i)) (hx : Tendsto xs atTop (𝓝 x))
    (hy : Tendsto ys atTop (𝓝 y)) : y ∈ subgradient (pairing n) f x := by
  have hp : Tendsto (fun i => ((xs i, ys i) : Rn n × Rn n)) atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hy
  exact (theorem_24_4 hf).mem_of_tendsto hp (Filter.Eventually.of_forall hmem)

end GraphClosed

/-! ### Theorem 24.5 and Corollary 24.5.1: convergence of directional derivatives -/

section Convergence

variable {n : ℕ} {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal}

/-- **Finiteness on a non-empty open set forces properness** (Theorem 7.2), and supplies the
inclusion `C ⊆ dom f` at the same time. This is what lets Theorem 24.5 be stated with the book's
own hypotheses instead of the backbone's. -/
private theorem proper_of_finite_on_isOpen {g : Rn n → EReal} (hg : ConvexFn g) (hC : IsOpen C)
    (hfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤) {x : Rn n} (hx : x ∈ C) : Proper g ∧ C ⊆ dom g := by
  have hCdom : C ⊆ dom g := fun z hz => mem_dom.2 (lt_top_iff_ne_top.2 (hfin z hz).2)
  refine ⟨?_, hCdom⟩
  by_contra hp
  have hxi : x ∈ interior (dom g) := hC.subset_interior_iff.2 hCdom hx
  exact (hfin x hx).1 (hg.eq_bot_of_mem_relint_dom hp
    (Convex.interior_subset_relint hg.convex_dom ⟨x, hxi⟩ hxi))

/-- **Rockafellar, Theorem 24.5**, first assertion, spelled without junk values: every real `μ`
above `f'(x; y)` eventually bounds `fᵢ'(xᵢ; yᵢ)`.

This is the `limsup` inequality of the book with the extended-real limit superior replaced by its
defining property, which is the form every consumer uses. `theorem_24_5_limsup` is the literal
statement.

The hypotheses are the book's: the `fᵢ` and `g` are convex on `Rⁿ` and *finite on* the open convex
`C`. Properness and `C ⊆ dom` are derived by `proper_of_finite_on_isOpen`. -/
theorem theorem_24_5_lt (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  obtain ⟨hgp, hgC⟩ := proper_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => proper_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_dirDeriv_lt hC hCc hf (fun i => (h i).1) (fun i => (h i).2) hg hgp hgC hconv hx
    hxs hys hμ

/-- **Rockafellar, Theorem 24.5**, first assertion, literally:
`limsup_i fᵢ'(xᵢ; yᵢ) ≤ f'(x; y)`.

Equality can fail: `fᵢ(x) = |x|^{pᵢ}` with `pᵢ ↓ 1` converges pointwise to `|x|` on `R` with every
`fᵢ'(0; 1) = 0` while `f'(0; 1) = 1`. -/
theorem theorem_24_5_limsup (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) :
    limsup (fun i => dirDeriv (f i) (xs i) (ys i)) atTop ≤ dirDeriv g x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) ≤ (μ : EReal) :=
    (theorem_24_5_lt hC hCc hf hfin hg hgfin hconv hx hxs hys hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Rockafellar, Theorem 24.5**, second assertion: given `ε > 0` there is an index `i₀` with
`∂fᵢ(xᵢ) ⊆ ∂f(x) + εB` for all `i ≥ i₀`, `B` the Euclidean unit ball. -/
theorem theorem_24_5_subgradient (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradient (pairing n) (f i) (xs i)
      ⊆ subgradient (pairing n) g x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨hgp, hgC⟩ := proper_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => proper_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_subgradient_subset_add_closedBall hC hCc hf (fun i => (h i).1)
    (fun i => (h i).2) hg hgp hgC hconv hx hxs hε

/-- **Rockafellar, Corollary 24.5.1**, first assertion: `f'(x; y)` is an upper semicontinuous
function of `(x, y) ∈ int (dom f) × Rⁿ`.

The constant sequence `f, f, f, …` in Theorem 24.5. Upper semicontinuity cannot be strengthened to
continuity in `x`; it is continuous in `y` for each fixed interior `x`, because `f'(x; ·)` is then
a finite convex function on `Rⁿ`. -/
theorem corollary_24_5_1_upperSemicontinuous {f : Rn n → EReal} (hf : ConvexFn f) (hfp : Proper f)
    {x : Rn n} (hx : x ∈ interior (dom f)) (y : Rn n) :
    UpperSemicontinuousAt (fun p : Rn n × Rn n => dirDeriv f p.1 p.2) (x, y) :=
  upperSemicontinuousAt_dirDeriv hf hfp hx y

/-- **Rockafellar, Corollary 24.5.1**, second assertion: for `x ∈ int (dom f)` and `ε > 0` there is
a `δ > 0` with `∂f(z) ⊆ ∂f(x) + εB` for every `z` within `δ` of `x`. -/
theorem corollary_24_5_1_subgradient {f : Rn n → EReal} (hf : ConvexFn f) (hfp : Proper f)
    {x : Rn n} (hx : x ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.ball x δ, subgradient (pairing n) f z
      ⊆ subgradient (pairing n) f x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_subgradient_subset_add_closedBall hf hfp hx hε)
  exact ⟨δ, hδ, fun z hz => hmem (by simpa [Metric.mem_ball] using hz)⟩

end Convergence

/-! ### Theorem 24.6: approach to a point of `dom f` along a direction -/

section Boundary

variable {n : ℕ} {f : Rn n → EReal} {x y : Rn n}

/-- **Rockafellar, §24 (line 9373).** `∂f(x)_y` is the set of points `x* ∈ ∂f(x)` at which `y` is
*normal* to `∂f(x)`.

`subgradientNormal_eq_sep` is the bridge to the maximisation form — `x*` maximises `⟨y, ·⟩` over
`∂f(x)` — which is the form the backbone's Theorem 24.6 produces, and which exhibits `∂f(x)_y` as
an exposed face of `∂f(x)`. -/
def subgradientNormal (f : Rn n → EReal) (x y : Rn n) : Set (Rn n) :=
  {v ∈ subgradient (pairing n) f x | y ∈ normalCone (pairing n) (subgradient (pairing n) f x) v}

/-- **The bridge**: `y` is normal to a set at `v` exactly when `v` maximises `⟨y, ·⟩` over it.
Rockafellar's `∂f(x)_y` is therefore the face of `∂f(x)` exposed by `y`, and the two spellings
differ only by moving `- v` across the inequality and using the symmetry of the pairing. -/
theorem subgradientNormal_eq_sep (f : Rn n → EReal) (x y : Rn n) :
    subgradientNormal f x y
      = {v ∈ subgradient (pairing n) f x | ∀ w ∈ subgradient (pairing n) f x, ⟪y, w⟫ ≤ ⟪y, v⟫} := by
  have key : ∀ w : Rn n, pairing n w y = ⟪y, w⟫ := fun w => by
    rw [pairing_apply]; exact real_inner_comm _ _
  ext v
  simp only [subgradientNormal, Set.mem_sep_iff, mem_normalCone, map_sub, LinearMap.sub_apply,
    sub_nonpos, key]

/-- **Rockafellar, Theorem 24.6**, first assertion, spelled without junk values: every real `μ`
above the second-order derivative `f'(x; y; z)` eventually bounds `f'(xᵢ; z)`.

`f'(x; y; ·)` is the directional derivative of the convex function `f'(x; ·)` at `y`, which is
`dirDeriv (dirDeriv f x) y`. Rockafellar assumes `f` closed; the backbone does not, because it
replaces the vanishing step `|xᵢ - x|` by a fixed larger one and so needs continuity of `f` only at
interior points, never a polytope and never Theorem 20.5. -/
theorem theorem_24_6_lt (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f) {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) {z : Rn n} {μ : ℝ}
    (hμ : dirDeriv (dirDeriv f x) y z < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv f (xs i) z < (μ : EReal) :=
  eventually_dirDeriv_lt_of_tendsto_dir hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ

/-- **Rockafellar, Theorem 24.6**, first assertion, literally:
`limsup_i f'(xᵢ; z) ≤ f'(x; y; z)` for every `z`. -/
theorem theorem_24_6_limsup (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f) {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) (z : Rn n) :
    limsup (fun i => dirDeriv f (xs i) z) atTop ≤ dirDeriv (dirDeriv f x) y z := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv f (xs i) z ≤ (μ : EReal) :=
    (theorem_24_6_lt hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Rockafellar, Theorem 24.6**, second assertion: given `ε > 0` there is an index `i₀` with
`∂f(xᵢ) ⊆ ∂f(x)_y + εB` for all `i ≥ i₀`. -/
theorem theorem_24_6_subgradient (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f)
    {xs : ℕ → Rn n} (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradient (pairing n) f (xs i)
      ⊆ subgradientNormal f x y + Metric.closedBall (0 : Rn n) ε := by
  rw [subgradientNormal_eq_sep]
  exact eventually_subgradient_subset_exposed_add_closedBall hf hfp hx hxsdom hxsne hxs hdir hy
    hα hαy hε

end Boundary

/-! ### Theorem 24.7: local boundedness of `∂f` and the Lipschitz property -/

section Bounded

variable {n : ℕ} {f : Rn n → EReal} {S : Set (Rn n)}

/-- **Rockafellar, Theorem 24.7**, quantitative half: a single `α` bounds the subgradients over a
compact `S ⊆ int (dom f)`, bounds the directional derivatives there, and is a Lipschitz constant
for `f` on `S`.

The book takes `α = sup {|x*| : x* ∈ ∂f(S)}` and proves the two inequalities for it; the backbone
produces a Lipschitz constant on a compact collar of `S` and reads all three off it, so what is
asserted is the existence of some such `α` — see the module docstring. -/
theorem theorem_24_7_bound (hf : ConvexFn f) (hp : Proper f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) :
    ∃ α : NNReal, LipschitzOnWith α (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ v ∈ subgradient (pairing n) f x, ‖v‖ ≤ (α : ℝ)) ∧
      ∀ x ∈ S, ∀ z : Rn n, dirDeriv f x z ≤ (((α : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨α, hlip, hpair, hdir⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := pairing n) hf hp hS hSD
  refine ⟨α, hlip, fun x hx v hv => ?_, hdir⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have h := hpair x hx v hv v
  rw [pairing_apply, real_inner_self_eq_norm_mul_norm] at h
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hv0)

/-- **Rockafellar, Theorem 24.7**: `∂f(S) = ⋃ {∂f(x) | x ∈ S}` is non-empty for a non-empty
`S ⊆ int (dom f)`. This is Theorem 23.4 applied at any point of `S`. -/
theorem theorem_24_7_nonempty (hf : ConvexFn f) (hp : Proper f) (hne : S.Nonempty)
    (hSD : S ⊆ interior (dom f)) : ((subgradientRel (pairing n) f).image S).Nonempty :=
  image_subgradientRel_nonempty hf hp hne hSD

/-- **Rockafellar, Theorem 24.7**, topological half: `∂f(S)` is compact for a closed proper convex
`f` and a compact `S ⊆ int (dom f)`. Closedness of `∂f(S)` is Theorem 24.4. -/
theorem theorem_24_7_isCompact (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) : IsCompact ((subgradientRel (pairing n) f).image S) :=
  isCompact_image_subgradientRel hf hS hSD

/-- **Rockafellar, Theorem 24.7**: `∂f(S)` is closed. -/
theorem theorem_24_7_isClosed (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) : IsClosed ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isClosed

/-- **Rockafellar, Theorem 24.7**: `∂f(S)` is bounded. -/
theorem theorem_24_7_isBounded (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) :
    Bornology.IsBounded ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isBounded

end Bounded

/-! ### Theorems 24.8 and 24.9: cyclic monotonicity -/

section Cyclic

variable {n : ℕ} {ρ : SetRel (Rn n) (Rn n)} {f : Rn n → EReal}

/-- A closed proper convex function on `Rⁿ` exists: the zero function, read as an affine function
of the pairing. This is what makes Theorem 24.8 true for the empty mapping, which Rockafellar's
proof sets aside ("the graph of `ρ`, which can be supposed to be non-empty"). -/
private theorem closedProperConvexFn_zero (n : ℕ) :
    ClosedProperConvexFn (affineFn (pairing n) 0 0) :=
  ⟨convexFn_affineFn 0 0, closedFn_affineFn (continuous_pairing (pairing n) 0),
    proper_affineFn 0 0⟩

/-- **Rockafellar, Theorem 24.8**, sufficiency: a cyclically monotone multivalued mapping from `Rⁿ`
to `Rⁿ` is contained in the subdifferential of a closed proper convex function.

The empty mapping is included, which Rockafellar's own proof excludes by fiat: it is contained in
the subdifferential of the zero function. -/
theorem theorem_24_8_of_isCyclicallyMonotone (hρ : IsCyclicallyMonotone (pairing n) ρ) :
    ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f := by
  rcases Set.eq_empty_or_nonempty ρ with rfl | hne
  · exact ⟨affineFn (pairing n) 0 0, closedProperConvexFn_zero n, Set.empty_subset _⟩
  obtain ⟨g, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone hρ hne
  exact ⟨g, ⟨hconv, hclosed, hproper⟩, hsub⟩

/-- **Rockafellar, Theorem 24.8**: a multivalued mapping from `Rⁿ` to `Rⁿ` is contained in the
subdifferential of a closed proper convex function if and only if it is cyclically monotone. -/
theorem theorem_24_8 :
    (∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f) ↔
      IsCyclicallyMonotone (pairing n) ρ :=
  ⟨fun ⟨_, hf, hsub⟩ => (isCyclicallyMonotone_subgradientRel hf.proper).mono hsub,
    theorem_24_8_of_isCyclicallyMonotone⟩

/-- **Rockafellar, Theorem 24.9**, one half: the subdifferential of a closed proper convex function
is a maximal cyclically monotone mapping.

**Not** a statement about maximal *monotonicity*: see the module docstring and the book's own
warning at line 9631. -/
theorem theorem_24_9_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalCyclicallyMonotone (pairing n) (subgradientRel (pairing n) f) :=
  isMaximalCyclicallyMonotone_subgradientRel hf

/-- **Rockafellar, Theorem 24.9**: the subdifferential mappings of the closed proper convex
functions on `Rⁿ` are exactly the maximal cyclically monotone mappings from `Rⁿ` to `Rⁿ`. -/
theorem theorem_24_9 :
    IsMaximalCyclicallyMonotone (pairing n) ρ ↔
      ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel (pairing n) f :=
  isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn

/-- **Rockafellar, Theorem 24.9**, second clause: the function is uniquely determined by its
subdifferential mapping up to an additive constant.

The backbone proves the sharper statement, in which only the *inclusion* `∂f ⊆ ∂g` is assumed; that
sharper form is what the maximality argument of Theorem 24.9 consumes. -/
theorem theorem_24_9_unique {g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (pairing n) f = subgradientRel (pairing n) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **Rockafellar, §24 (line 9613)**: `∂f` is a monotone mapping, this being the case `m = 1` of
cyclic monotonicity.

Kept deliberately separate from `theorem_24_9`. The book warns at line 9631 that maximal
monotonicity of `∂f` — Corollary 31.5.2 — does **not** follow from Theorem 24.9 together with
"cyclically monotone implies monotone", because a mapping maximal in the smaller class need not be
maximal in the larger one. No declaration in this module bridges the two. -/
theorem isMonotoneRel_subgradientRel_rn (hp : Proper f) :
    IsMonotoneRel (pairing n) (subgradientRel (pairing n) f) :=
  isMonotoneRel_subgradientRel hp

/-- **Rockafellar, §24 (line 9623)**: when `n = 1`, the monotone mappings and the cyclically
monotone mappings are the same.

The book derives this from Theorems 24.3 and 24.9; the backbone proves it directly, by rotating a
cycle so that the pair maximising `x + x*` comes first and deleting it. For `n > 1` it is false —
a linear `ρ` with matrix `Q` is monotone as soon as the symmetric part of `Q` is positive
semi-definite, and cyclically monotone only if `Q` itself is symmetric. -/
theorem isMonotoneRel_iff_isCyclicallyMonotone_line {σ : SetRel ℝ ℝ} :
    IsMonotoneRel (innerₗ ℝ) σ ↔ IsCyclicallyMonotone (innerₗ ℝ) σ :=
  ⟨IsMonotoneRel.isCyclicallyMonotone, IsCyclicallyMonotone.isMonotoneRel⟩

end Cyclic

end Rockafellar
