/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.BoundaryDirDeriv
import Tdaf.Analysis.Convex.Subgradient.Cofinite
import Tdaf.Analysis.Convex.Subgradient.Preservation
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §26: The Legendre Transformation

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §26, pp. 251–260: the classical Legendre
transformation, and the exact sense in which it is the conjugacy correspondence restricted to the
functions whose subdifferential is a genuine one-to-one mapping.

All eleven numbered results of the section are here — Theorems 26.1, 26.3, 26.4, 26.5, 26.6,
Lemmas 26.2 and 26.7, and Corollaries 26.3.1, 26.3.2, 26.3.3 and 26.4.1 — together with all three
of the section's counterexamples.

## Contents

| label | declaration |
|---|---|
| §26 opening, p. 251 | `SingleValued`, `inverseMap`, `OneToOne`, `oneToOne_iff` |
| §26 definition, p. 251 | `EssentiallySmoothBook`, `essentiallySmooth_iff_book` |
| Theorem 26.1 | `theorem_26_1`, `theorem_26_1_gradient`, `theorem_26_1_empty`,
  `theorem_26_1_domSubgradient` |
| Lemma 26.2 | `EssentiallySmoothDir`, `lemma_26_2`, `lemma_26_2_at` |
| §26 counterexample, p. 253 | `essStrictlyConvexFn`, `essStrictlyConvexFn_not_strictConvexOn_dom` |
| §26 counterexample, p. 254 | `strictOnRelintFn`, `strictOnRelintFn_not_essentiallyStrictlyConvex` |
| Theorem 26.3 | `theorem_26_3`, `theorem_26_3'` |
| Corollary 26.3.1 | `corollary_26_3_1` |
| Corollary 26.3.2 | `corollary_26_3_2` |
| Corollary 26.3.3 | `corollary_26_3_3` |
| §26 definition, p. 256 | `legendreDomain`, `legendreDomain_eq_gradientRange` |
| Theorem 26.4 | `theorem_26_4_wellDefined`, `theorem_26_4_eq`, `theorem_26_4_subset_dom_conj` |
| Corollary 26.4.1 | `corollary_26_4_1_dom`, `corollary_26_4_1_relint_subset`,
  `corollary_26_4_1_subset_dom`, `corollary_26_4_1_eq`, `corollary_26_4_1_strictConvexOn` |
| §26 counterexample, p. 257 | `halfPlaneFn`, `legendreDomain_halfPlaneFn`,
  `not_convex_legendreDomain_halfPlaneFn` |
| §26 definition, p. 258 | `LegendreType` (backbone), `legendreType_iff` |
| Theorem 26.5 | `theorem_26_5`, `theorem_26_5_legendreDomain`, `theorem_26_5_conj_apply`,
  `theorem_26_5_legendreDomain_conj`, `theorem_26_5_apply`, `theorem_26_5_bijOn`,
  `theorem_26_5_continuousOn`, `theorem_26_5_continuousOn_conj`, `theorem_26_5_gradient_conj`,
  `theorem_26_5_gradient_gradient_conj` |
| Theorem 26.6 | `theorem_26_6`, `theorem_26_6_conj`, `theorem_26_6_apply` |
| Lemma 26.7 | `lemma_26_7` |

## The section's definitions

* `Rockafellar.SingleValued ρ` / `Rockafellar.inverseMap ρ` / `Rockafellar.OneToOne ρ` — the book's
  vocabulary for multivalued mappings (p. 251). `ρ` is single-valued when `ρ x` has at most one
  element, `ρ⁻¹ x* = {x | x* ∈ ρ x}`, and `ρ` is one-to-one when `ρ` and `ρ⁻¹` are both
  single-valued. `oneToOne_iff` is the bridge to the backbone's phrasing, where injectivity is
  "the subdifferentials at distinct points are disjoint".
* `Rockafellar.EssentiallySmoothBook f` — conditions (a), (b), (c) with condition (c) quantified,
  as the book quantifies it, over *boundary points* of `C = int (dom f)`.
  `essentiallySmooth_iff_book` identifies it with the backbone's `EssentiallySmooth`, which
  quantifies over points outside `C`. See "Where the book's quantifier had to move" below.
* `Rockafellar.EssentiallySmoothDir f` — conditions (a), (b), (c′): the directional form of
  Lemma 26.2. **Both forms are carried**, with `lemma_26_2` as the equivalence, because §§27–32 use
  different ones: (c) is what a limit-of-gradients argument produces and (c′) is what a user with a
  concrete `f` can check.
* `Rockafellar.legendreDomain f` — Rockafellar's `D`, the image of `C = int (dom f)` under the
  gradient mapping (p. 256). `legendreDomain_eq_gradientRange` is the bridge to the backbone's
  `gradientRange`, valid as soon as condition (b) holds.
* `Rockafellar.halfPlaneFn`, `Rockafellar.essStrictlyConvexFn`, `Rockafellar.strictOnRelintFn` —
  the section's three counterexamples, transcribed as Lean definitions.

**`LegendreType` is the backbone's**, not a surface copy: `LegendreType f` is
`EssentiallySmooth f ∧ StrictConvexOnFn f (int (dom f))`, which is precisely Rockafellar's "the
pair `(C, f)` is a convex function of Legendre type" for `C = int (dom f)`. The book states it for
the *pair*; since `C` is determined by `f`, so is the pair, and `legendreType_iff` records the
book's own characterisation (`∂f` one-to-one).

## Where the book's quantifier had to move

**Condition (c) is stated at every point outside `C`, not at boundary points of `C`.** Rockafellar
quantifies over sequences in `C = int (dom f)` converging to a *boundary point* `x` of `C`; the
backbone quantifies over sequences converging to a point `x ∉ C`. The two agree — a sequence in the
open set `C` converging to a point not in `C` converges to a boundary point of `C` — and
`essentiallySmooth_iff_book` proves it, so no downstream statement has to re-derive the
frontier membership. `EssentiallySmoothBook` is the book's own form, kept so that the alignment can
be checked by reading this file.

## What is not here

**No naive involution lemma.** The book is explicit (p. 258): "In general, the Legendre conjugate of
a differentiable convex function need not be differentiable or convex, and we cannot speak of the
Legendre conjugate of the Legendre conjugate." A surface lemma asserting that the Legendre
transformation is an involution would be false, and one asserting it by unfolding a definition would
be a definitional cheat. What *is* true is Theorem 26.5: **within the class of functions of Legendre
type**, and only there, the transformation is a symmetric one-to-one correspondence.
`theorem_26_5_legendreDomain_conj` and `theorem_26_5_apply` are the two halves of "(C, f) is in turn
the Legendre conjugate of (C*, f*)", and both carry `LegendreType f` as a hypothesis.
`not_convex_legendreDomain_halfPlaneFn` is the reason the hypothesis cannot be dropped.

**The two counterexamples of pp. 253–254 are transcribed, but only their decisive half is proved.**
Both functions are stated as Lean definitions and the property that makes each of them a
counterexample is proved:

* `essStrictlyConvexFn` — the book's `(ξ₂²/2ξ₁) − 2ξ₂^(1/2)` — is **not strictly convex on**
  `dom f`, because it vanishes identically along the non-negative `ξ₁`-axis
  (`essStrictlyConvexFn_not_strictConvexOn_dom`). The book's other claim about it, that it *is*
  essentially strictly convex and essentially smooth, is not proved here; it needs the strict
  convexity of `ξ₂²/2ξ₁ − 2√ξ₂` on the open quadrant, which is a two-variable second-derivative
  computation with no convex-analytic content. See `## Backbone gaps`.
* `strictOnRelintFn` — the book's `(ξ₂²/2ξ₁) + ξ₂²` — is **not essentially strictly convex**
  (`strictOnRelintFn_not_essentiallyStrictlyConvex`), because it is a non-negative function
  vanishing on the whole non-negative `ξ₁`-axis, which is therefore a convex subset of `dom ∂f` on
  which the function is constant. The complementary claim, that it *is* strictly convex on
  `ri (dom f)`, is the same kind of computation and is likewise not proved. See `## Backbone gaps`.

The third counterexample, the parabola of p. 257, is proved in full: it is the one that refutes the
natural guess, and a reader cannot reconstruct it from the surrounding theory.

## Backbone gaps

**`StrictConvexOnFn` of a two-variable explicit formula has no supporting API.** The two
counterexamples of pp. 253–254 both need "this concrete function on `ℝ²` is strictly convex on the
open positive quadrant", and there is nothing in the backbone between `StrictConvexOnFn` (the
definition) and the theorems that consume it. What is wanted, in
`Tdaf/Analysis/Convex/Subgradient/StrictlyConvex.lean`:

* `StrictConvexOnFn.add_strictConvexOnFn` — the sum of a convex and a strictly convex function is
  strictly convex, which is `StrictConvexOnFn.add_convexFn` (in `Preservation.lean`) with the
  arguments the other way round; and
* a criterion turning a positive-definite second derivative, or strict convexity along every
  segment, into `StrictConvexOnFn`. Mathlib has `StrictConvexOn` for real-valued functions and
  `StrictConvexOn_of_deriv2_pos` for one variable; neither reaches an `EReal`-valued function of
  two variables, and the bridge `StrictConvexOnFn f C ↔ StrictConvexOn ℝ C (fun x => (f x).toReal)`
  for `f` finite on `C` does not exist. That bridge is the gap, and it is what both halves of the
  two unproved claims above would run on.

Nothing in this file's *numbered* results is blocked by either item.

## Where the book is defective

**Theorem 26.4's differentiability hypothesis is stronger than its proof needs, and the "well
defined" clause needs no closure at all.** Rockafellar assumes `f` closed proper convex with
`C = int (dom f)` non-empty and `f` differentiable on `C`. The single-valuedness of `g` and the
formula `g = f*` on `D` follow from convexity alone, at each point where a gradient happens to
exist: `theorem_26_4_wellDefined` and `theorem_26_4_eq` carry only `ConvexFn f`. The book's extra
hypotheses are what make the *domain* `D` interesting, not what make the value well defined.

**Theorem 26.6's co-finiteness enters through `dom f* = ℝⁿ`.** The book's proof cites Corollary
13.3.1 for the equivalence with the recession-function condition; the backbone's
`bijOn_gradient_univ_iff` states the domain form, and `cofinite_iff_dom_conj_eq_univ` is the one
rewrite that puts the book's own word back in. Both forms are stated here.

**Corollary 26.3.3's "`A` maps `ℝⁿ` onto `ℝᵐ`" is used only through injectivity of `A*`.** The
book's proof says so ("`A*⁻¹` is single-valued (inasmuch as `A` maps `ℝⁿ` onto `ℝᵐ`)"), and the
backbone's `IsExactImage.essentiallySmooth_mapLin` takes the injectivity directly. The surface
states the book's hypothesis and pays `injective_of_isAdjointPair_of_surjective` once.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26.
-/

open Filter Set Topology

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Multivalued mappings

Rockafellar, p. 251. A multivalued mapping `ρ` assigning to each `x ∈ ℝⁿ` a set `ρ x ⊆ ℝⁿ` is
*single-valued* when `ρ x` contains at most one element for each `x`, and *one-to-one* when `ρ` and
`ρ⁻¹` are both single-valued, where `ρ⁻¹ x* = {x | x* ∈ ρ x}`. -/

/-- **Rockafellar, §26 (p. 251).** A multivalued mapping `ρ` is **single-valued** when `ρ x`
contains at most one element for each `x`. Its effective domain `{x | ρ x ≠ ∅}` is not required to
be all of `ℝⁿ`; single-valuedness says only that `ρ` reduces to an ordinary function there. -/
def SingleValued (ρ : Rn n → Set (Rn n)) : Prop := ∀ x, (ρ x).Subsingleton

/-- **Rockafellar, §26 (p. 251).** The **inverse** of a multivalued mapping,
`ρ⁻¹ x* = {x | x* ∈ ρ x}`. -/
def inverseMap (ρ : Rn n → Set (Rn n)) : Rn n → Set (Rn n) := fun y => {x | y ∈ ρ x}

@[simp] theorem mem_inverseMap {ρ : Rn n → Set (Rn n)} {x y : Rn n} :
    x ∈ inverseMap ρ y ↔ y ∈ ρ x := Iff.rfl

/-- **Rockafellar, §26 (p. 251).** A multivalued mapping is **one-to-one** when both it and its
inverse are single-valued — equivalently, when `graph ρ` contains neither two different pairs with
the same first component nor two with the same second component. -/
def OneToOne (ρ : Rn n → Set (Rn n)) : Prop := SingleValued ρ ∧ SingleValued (inverseMap ρ)

/-- Single-valuedness of `ρ⁻¹` is the statement that `ρ` takes distinct points to disjoint sets,
which is the form the backbone's injectivity theorems are stated in. -/
theorem singleValued_inverseMap_iff {ρ : Rn n → Set (Rn n)} :
    SingleValued (inverseMap ρ) ↔ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) := by
  constructor
  · intro h x₁ x₂ hne
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    exact hne (h y hy₁ hy₂)
  · intro h y x₁ hx₁ x₂ hx₂
    by_contra hne
    exact Set.disjoint_left.1 (h x₁ x₂ hne) hx₁ hx₂

/-- `ρ` is one-to-one exactly when every `ρ x` is a subsingleton and distinct points have disjoint
images. This is the bridge between the book's vocabulary and the backbone's. -/
theorem oneToOne_iff {ρ : Rn n → Set (Rn n)} :
    OneToOne ρ ↔ (∀ x, (ρ x).Subsingleton) ∧ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) :=
  and_congr_right' singleValued_inverseMap_iff

/-! ### Essential smoothness

Rockafellar, p. 251. A proper convex function `f` is **essentially smooth** when, for
`C = int (dom f)`:

* (a) `C` is not empty;
* (b) `f` is differentiable throughout `C`;
* (c) `|∇f xᵢ| → +∞` whenever `x₁, x₂, …` is a sequence in `C` converging to a boundary point of
  `C`.

The backbone's `EssentiallySmooth` is this, with (c) quantified over points *outside* `C` rather
than over boundary points of `C`; `essentiallySmooth_iff_book` is the identification. -/

/-- **Rockafellar, §26 (p. 251)**, verbatim: conditions (a), (b) and (c) with (c) quantified over
*boundary points* of `C = int (dom f)`, as the book quantifies it. -/
def EssentiallySmoothBook (f : Rn n → EReal) : Prop :=
  (interior (dom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) ∧
    ∀ ⦃z : Rn n⦄, z ∈ frontier (interior (dom f)) → ∀ zs : ℕ → Rn n,
      (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 z) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- **The book's condition (c) and the backbone's are the same condition.** `C = int (dom f)` is
open, so its frontier is `cl C \ C`: a boundary point of `C` is in particular *not* in `C`, and
conversely a point outside `C` that a sequence in `C` converges to lies in `cl C`, hence on the
boundary. Quantifying over points outside `C` therefore adds nothing and removes a membership
that every use of (c) would otherwise have to re-derive. -/
theorem essentiallySmooth_iff_book : EssentiallySmooth f ↔ EssentiallySmoothBook f := by
  have hfr : frontier (interior (dom f)) = closure (interior (dom f)) \ interior (dom f) :=
    isOpen_interior.frontier_eq
  constructor
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz => ?_⟩
    rw [hfr] at hz
    exact hc hz.2
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz zs hzs hlim => ?_⟩
    refine hc ?_ zs hzs hlim
    rw [hfr]
    exact ⟨mem_closure_of_tendsto hlim (Eventually.of_forall hzs), hz⟩

/-! ### Theorem 26.1 -/

/-- **Rockafellar, Theorem 26.1.** Let `f` be a closed proper convex function. Then `∂f` is a
single-valued mapping if and only if `f` is essentially smooth. -/
theorem theorem_26_1 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    SingleValued (subgradient (pairing n) f) ↔ EssentiallySmooth f :=
  subsingleton_subgradient_iff_essentiallySmooth hf hp hcl

/-- **Rockafellar, Theorem 26.1**, the "in this case" clause, first half: `∂f x` consists of the
vector `∇f x` alone when `x ∈ int (dom f)`. -/
theorem theorem_26_1_gradient (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    subgradient (pairing n) f x = {gradient (fun w => (f w).toReal) x} := by
  have h := subgradient_eq_singleton_of_essentiallySmooth hf hes hx
  rwa [show (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun w => (f w).toReal) x)
      = gradient (fun w => (f w).toReal) x from rfl] at h

/-- **Rockafellar, Theorem 26.1**, the "in this case" clause, second half: `∂f x = ∅` when
`x ∉ int (dom f)`. This is the substantive half — it is what makes `∂f` an ordinary function on
`int (dom f)` and nothing anywhere else. -/
theorem theorem_26_1_empty (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) {x : Rn n} (hx : x ∉ interior (dom f)) :
    subgradient (pairing n) f x = ∅ :=
  subgradient_eq_empty_of_essentiallySmooth hf hp hcl hes hx

/-- **Rockafellar, Theorem 26.1**, both halves of the "in this case" clause as one equation:
`dom ∂f = int (dom f)` for an essentially smooth closed proper convex function. -/
theorem theorem_26_1_domSubgradient (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) :
    domSubgradient (pairing n) f = interior (dom f) :=
  domSubgradient_eq_interior_dom_of_essentiallySmooth hf hp hcl hes

/-! ### Lemma 26.2 -/

/-- **Rockafellar, Lemma 26.2**, conditions (a), (b), (c′): the definition of essential smoothness
with condition (c) replaced by

```
(c')  f'(x + λ(a − x); a − x) ↓ −∞ as λ ↓ 0, for any a ∈ C and any boundary point x of C.
```

The `↓` of the book records that the map is nondecreasing in `λ`, which holds for every convex `f`;
the *content* of (c′) is the value of the limit, so only the limit appears here. -/
def EssentiallySmoothDir (f : Rn n → EReal) : Prop :=
  (interior (dom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) ∧
    ∀ x ∉ interior (dom f), ∀ a ∈ interior (dom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥)

/-- **Rockafellar, Lemma 26.2**, at a single point: assuming (a) and (b), condition (c) at `x` and
condition (c′) at `x` along the segment from any `a ∈ C` say the same thing — namely that `f` has
no subgradient at `x`. -/
theorem lemma_26_2_at (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z)
    {a : Rn n} (ha : a ∈ interior (dom f)) (x : Rn n) :
    (∀ zs : ℕ → Rn n, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff ha x

/-- **Rockafellar, Lemma 26.2.** For a closed proper convex function, condition (c) may be replaced
by condition (c′): the two definitions of essential smoothness agree. -/
theorem lemma_26_2 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallySmooth f ↔ EssentiallySmoothDir f := by
  constructor
  · intro hes
    refine ⟨hes.interior_dom_nonempty, hes.differentiableAtFn, ?_⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hes.interior_dom_nonempty
      hes.differentiableAtFn).1 hes
  · rintro ⟨hne, hdiff, hc⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hne hdiff).2 hc

/-! ### Essential strict convexity

Rockafellar, p. 253. A real-valued function on a convex set `C` is **strictly convex on `C`** when
the convexity inequality between two different points of `C` is strict; a proper convex function on
`ℝⁿ` is **essentially strictly convex** when it is strictly convex on every convex subset of
`dom ∂f = {x | ∂f x ≠ ∅}`. Both are the backbone's `StrictConvexOnFn` and
`EssentiallyStrictlyConvex`, used without a surface copy: the definitions are literally the book's.

Rockafellar's two warnings about the definition are the counterexamples below. -/

/-! ### Theorem 26.3 -/

/-- **Rockafellar, Theorem 26.3.** A closed proper convex function is essentially strictly convex
if and only if its conjugate is essentially smooth. -/
theorem theorem_26_3 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallyStrictlyConvex (B := pairing n) f ↔ EssentiallySmooth (conj (pairing n) f) :=
  (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hf hp hcl).symm

/-- **Rockafellar, Theorem 26.3**, read at `f*`: the conjugate of a closed proper convex function is
essentially strictly convex exactly when the function itself is essentially smooth. This is the
direction Corollaries 26.3.2 and 26.3.3 use. -/
theorem theorem_26_3' (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    EssentiallyStrictlyConvex (B := pairing n) (conj (pairing n) f) ↔ EssentiallySmooth f :=
  essentiallyStrictlyConvex_conj_iff_essentiallySmooth hf hp hcl

/-! ### Corollary 26.3.1 -/

/-- **Rockafellar, Corollary 26.3.1.** Let `f` be a closed proper convex function. Then `∂f` is a
one-to-one mapping if and only if `f` is strictly convex on `int (dom f)` and essentially smooth. -/
theorem corollary_26_3_1 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    OneToOne (subgradient (pairing n) f) ↔
      (StrictConvexOnFn f (interior (dom f)) ∧ EssentiallySmooth f) :=
  oneToOne_iff.trans ((subgradient_injective_iff hf hp hcl).trans and_comm)

/-! ### Corollaries 26.3.2 and 26.3.3: preservation of essential smoothness -/

/-- **Rockafellar, Corollary 26.3.2.** Let `f₁` and `f₂` be closed proper convex functions on `ℝⁿ`
such that `f₁` is essentially smooth and `ri (dom f₁*) ∩ ri (dom f₂*) ≠ ∅`. Then `f₁ □ f₂` is
essentially smooth. -/
theorem corollary_26_3_2 {f₁ f₂ : Rn n → EReal} (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁)
    (hri : (ri (dom (conj (pairing n) f₁)) ∩ ri (dom (conj (pairing n) f₂))).Nonempty) :
    EssentiallySmooth (infConv f₁ f₂) := by
  obtain ⟨y₀, hy₁, hy₂⟩ := hri
  exact essentiallySmooth_infConv_of_relint h₁ h₂ hes hy₁ hy₂

/-- **Rockafellar, Corollary 26.3.3.** Let `f` be a closed proper convex function on `ℝⁿ` which is
essentially smooth, and let `A` be a linear transformation from `ℝⁿ` onto `ℝᵐ`. If there exists a
`y* ∈ ℝᵐ` such that `A* y* ∈ ri (dom f*)`, then the convex function `Af` on `ℝᵐ` is essentially
smooth.

`A*` is `LinearMap.adjoint A`; the surjectivity of `A` is used only to make `A*` injective, which is
what the argument consumes. -/
theorem corollary_26_3_3 {m : ℕ} {g : Rn n → EReal} (hg : ClosedProperConvexFn g)
    (hes : EssentiallySmooth g) (A : Rn n →ₗ[ℝ] Rn m) (hsurj : Function.Surjective A) {y : Rn m}
    (hy : LinearMap.adjoint A y ∈ ri (dom (conj (pairing n) g))) :
    EssentiallySmooth (mapLin A g) := by
  have hA : IsAdjointPair (innerₗ (Rn m)) (innerₗ (Rn n)) (LinearMap.adjoint A) A := by
    have h := isAdjointPair_adjoint (LinearMap.adjoint A)
    rwa [LinearMap.adjoint_adjoint] at h
  exact essentiallySmooth_mapLin_of_relint hA hg hes hsurj hy

/-! ### The Legendre conjugate

Rockafellar, p. 256. For a differentiable real-valued `f` on an open set `C ⊆ ℝⁿ`, the **Legendre
conjugate** of `(C, f)` is the pair `(D, g)` where `D = ∇f(C)` and

```
g(x*) = ⟨(∇f)⁻¹(x*), x*⟩ − f((∇f)⁻¹(x*)).
```

`∇f` need not be one-to-one for `g` to be well defined; it suffices that `⟨x, x*⟩ − f(x)` be the
same for every `x` with `∇f x = x*`, which is Theorem 26.4's first clause. -/

/-- **Rockafellar, §26 (p. 256).** Rockafellar's `D`: the image of `C = int (dom f)` under the
gradient mapping. -/
def legendreDomain (f : Rn n → EReal) : Set (Rn n) :=
  gradient (fun w => (f w).toReal) '' interior (dom f)

/-- The Riesz representative of `v` evaluated at `x` is the book's `⟨x, v⟩`. Every backbone result
about `HasGradientAt` produces the left-hand side, and every surface statement wants the right. -/
private theorem toDual_apply_eq_pairing (v x : Rn n) :
    (InnerProductSpace.toDual ℝ (Rn n) v) x = pairing n x v := by
  rw [InnerProductSpace.toDual_apply, pairing_apply]
  exact real_inner_comm x v

/-- **The bridge to the backbone's `gradientRange`**, valid as soon as condition (b) holds:
`{v | ∃ x, ∇f x = v}` and "the image of `C` under `∇f`" are the same set, because every gradient is
attained at an interior point of `dom f` (Corollary 25.1.1) and, on `C`, Mathlib's `gradient` of the
real trace *is* Rockafellar's `∇f`. -/
theorem legendreDomain_eq_gradientRange
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    legendreDomain f = gradientRange f := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hdiff hz).hasGradientAt_gradient.mem_gradientRange
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.mem_interior_dom, by
      rw [hz.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]⟩

/-! ### Theorem 26.4 -/

/-- **Rockafellar, Theorem 26.4**, first clause: the Legendre conjugate `(D, g)` of `(C, f)` is
well-defined. Whatever `x` is chosen in `(∇f)⁻¹(x*)`, the value `⟨x, x*⟩ − f(x)` is the same.

**Only convexity is needed.** The book states the theorem for a closed proper convex `f` with
non-empty `C = int (dom f)` on which `f` is differentiable; the well-definedness is a consequence of
Theorem 23.5 at the two points separately and holds wherever two gradients happen to agree. -/
theorem theorem_26_4_wellDefined (hf : ConvexFn f) {v x₁ x₂ : Rn n}
    (h₁ : HasGradientAt f (InnerProductSpace.toDual ℝ (Rn n) v) x₁)
    (h₂ : HasGradientAt f (InnerProductSpace.toDual ℝ (Rn n) v) x₂) :
    pairing n x₁ v - (f x₁).toReal = pairing n x₂ v - (f x₂).toReal := by
  obtain ⟨r₁, hr₁⟩ := h₁.exists_coe
  obtain ⟨r₂, hr₂⟩ := h₂.exists_coe
  have h := sub_eq_sub_of_hasGradientAt hf h₁ h₂ hr₁ hr₂
  rw [toDual_apply_eq_pairing, toDual_apply_eq_pairing] at h
  rw [hr₁, hr₂]
  simpa using h

/-- The conjugate against `pairing n` and the conjugate against the canonical dual pairing are the
same number, read through the Riesz isometry. The backbone's Theorem 26.4 is stated on a general
normed space, where the only pairing available is `⟨x, y⟩ = y x`; this is the one line that carries
it to the surface's self-paired `ℝⁿ`. -/
private theorem conj_pairing_eq (g : Rn n → EReal) (v : Rn n) :
    conj (pairing n) g v
      = conj (topDualPairing ℝ (Rn n)).flip g (InnerProductSpace.toDual ℝ (Rn n) v) := by
  simp only [conj_apply]
  refine iSup_congr fun x => ?_
  rw [show ((topDualPairing ℝ (Rn n)).flip x) (InnerProductSpace.toDual ℝ (Rn n) v)
      = pairing n x v from toDual_apply_eq_pairing v x]

/-- **Rockafellar, Theorem 26.4**, second and third clauses: `D ⊆ dom f*`, and `g` is the
restriction of `f*` to `D` — at a point `x*` of `D` the defining formula returns `f*(x*)`. -/
theorem theorem_26_4_eq (hf : ConvexFn f) {v x : Rn n}
    (h : HasGradientAt f (InnerProductSpace.toDual ℝ (Rn n) v) x) :
    conj (pairing n) f v = ((pairing n x v - (f x).toReal : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := h.exists_coe
  have hval := conj_eq_of_hasGradientAt hf h hr
  rw [conj_pairing_eq, hval, toDual_apply_eq_pairing, hr]
  simp

/-- **Rockafellar, Theorem 26.4**: `D` is a subset of `dom f*`. -/
theorem theorem_26_4_subset_dom_conj (hf : ConvexFn f)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    legendreDomain f ⊆ dom (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hdiff]
  rintro v ⟨x, hx⟩
  rw [mem_dom, theorem_26_4_eq hf hx]
  exact _root_.EReal.coe_lt_top _

/-! ### Corollary 26.4.1 -/

/-- **Rockafellar, Corollary 26.4.1**, first clause: for an essentially smooth closed proper convex
`f`, the domain `D` of the Legendre conjugate is `{x* | ∂f*(x*) ≠ ∅}`. -/
theorem corollary_26_4_1_dom (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) :
    legendreDomain f = domSubgradient (pairing n) (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_eq_domSubgradient_conj hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `ri (dom f*) ⊆ D`, so `D` is "almost convex". -/
theorem corollary_26_4_1_relint_subset (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) : ri (dom (conj (pairing n) f)) ⊆ legendreDomain f := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact relint_dom_conj_subset_gradientRange hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `D ⊆ dom f*`, the other half of the squeeze. -/
theorem corollary_26_4_1_subset_dom (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) : legendreDomain f ⊆ dom (conj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_subset_dom_conj hf hp hcl hes

/-- **Rockafellar, Corollary 26.4.1**: `g` is the restriction of `f*` to `D`. -/
theorem corollary_26_4_1_eq (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hes.differentiableAtFn hx).hasGradientAt_gradient

/-- **Rockafellar, Corollary 26.4.1**, last clause: `g` is strictly convex on every convex subset
of `D`. Since `g = f*` on `D` (Theorem 26.4), this is the essential strict convexity of `f*`, which
Theorem 26.3 supplies from the essential smoothness of `f`. -/
theorem corollary_26_4_1_strictConvexOn (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hes : EssentiallySmooth f) {C : Set (Rn n)} (hC : Convex ℝ C) (hCsub : C ⊆ legendreDomain f) :
    StrictConvexOnFn (conj (pairing n) f) C := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn] at hCsub
  exact strictConvexOnFn_conj_of_subset_gradientRange hf hp hcl hes hC hCsub

/-! ### Functions of Legendre type

Rockafellar, p. 258. A pair `(C, f)` with `C` an open convex set and `f` a strictly convex function
on `C` satisfying (a), (b) and (c) (equivalently (c′)) is called a **convex function of Legendre
type**. Since `C = int (dom f)` is determined by `f`, this is the backbone's `LegendreType f`, and
by Corollary 26.3.1 it holds exactly when `∂f` is one-to-one. -/

/-- **Rockafellar, p. 258**, the characterisation the book states immediately after the definition:
a closed proper convex function `f` has `∂f` one-to-one if and only if the restriction of `f` to
`C = int (dom f)` is a convex function of Legendre type. -/
theorem legendreType_iff (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    LegendreType f ↔ OneToOne (subgradient (pairing n) f) :=
  (legendreType_iff_subgradient_injective hf hp hcl).trans oneToOne_iff.symm

/-! ### Theorem 26.5 -/

/-- **Rockafellar, Theorem 26.5**, first assertion. Let `f` be a closed convex function, and let
`C = int (dom f)`, `C* = int (dom f*)`. Then `(C, f)` is a convex function of Legendre type if and
only if `(C*, f*)` is. -/
theorem theorem_26_5 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f) :
    LegendreType f ↔ LegendreType (conj (pairing n) f) :=
  (legendreType_conj_iff hf hp hcl).symm

/-- **Rockafellar, Theorem 26.5**: when `f` is of Legendre type, `(C*, f*)` **is** the Legendre
conjugate of `(C, f)` — the domain half, `D = C*`. -/
theorem theorem_26_5_legendreDomain (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    legendreDomain f = interior (dom (conj (pairing n) f)) := by
  rw [legendreDomain_eq_gradientRange hleg.1.differentiableAtFn]
  exact gradientRange_eq_interior_dom_conj hf hp hcl hleg

/-- **Rockafellar, Theorem 26.5**: the value half of "`(C*, f*)` is the Legendre conjugate of
`(C, f)`" — on `C` the defining formula of the Legendre conjugate returns `f*`. -/
theorem theorem_26_5_conj_apply (hf : ConvexFn f) (hleg : LegendreType f) {x : Rn n}
    (hx : x ∈ interior (dom f)) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  corollary_26_4_1_eq hf hleg.1 hx

/-- **Rockafellar, Theorem 26.5**: `(C, f)` is *in turn* the Legendre conjugate of `(C*, f*)` — the
domain half. Note the hypothesis: this is the involutivity of the Legendre transformation, and it
holds **only** within the Legendre-type class. See the module docstring. -/
theorem theorem_26_5_legendreDomain_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    legendreDomain (conj (pairing n) f) = interior (dom f) := by
  have hgleg := hleg.conj hf hp hcl
  have h := theorem_26_5_legendreDomain (convexFn_conj _ f) (proper_conj ⟨hf, hcl, hp⟩)
    closedFn_conj hgleg
  rwa [conj_conj_innerL hf hcl] at h

/-- **Rockafellar, Theorem 26.5**: `(C, f)` is in turn the Legendre conjugate of `(C*, f*)` — the
value half. Again only within the Legendre-type class. -/
theorem theorem_26_5_apply (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (dom (conj (pairing n) f))) :
    f (gradient (fun w => (conj (pairing n) f w).toReal) v)
      = ((pairing n v (gradient (fun w => (conj (pairing n) f w).toReal) v)
          - (conj (pairing n) f v).toReal : ℝ) : EReal) := by
  have hgleg := hleg.conj hf hp hcl
  have h := corollary_26_4_1_eq (convexFn_conj (pairing n) f) hgleg.1 hv
  rwa [conj_conj_innerL hf hcl] at h

/-- **Rockafellar, Theorem 26.5**: the gradient mapping `∇f` is one-to-one from the open convex set
`C` onto the open convex set `C*`. -/
theorem theorem_26_5_bijOn (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    Set.BijOn (gradient fun w => (f w).toReal) (interior (dom f))
      (interior (dom (conj (pairing n) f))) :=
  bijOn_gradient_of_legendreType hf hp hcl hleg

/-- **Rockafellar, Theorem 26.5**: `∇f` is continuous on `C`. -/
theorem theorem_26_5_continuousOn (hf : ConvexFn f) (hp : Proper f) (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (f w).toReal) (interior (dom f)) :=
  continuousOn_gradient_interior_dom hf hp hleg.1

/-- **Rockafellar, Theorem 26.5**: `∇f` is continuous *in both directions*, the second half being
the continuity of `∇f*` on `C*`. -/
theorem theorem_26_5_continuousOn_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (conj (pairing n) f w).toReal)
      (interior (dom (conj (pairing n) f))) :=
  continuousOn_gradient_interior_dom (convexFn_conj _ f) (proper_conj ⟨hf, hcl, hp⟩)
    (hleg.conj hf hp hcl).1

/-- **Rockafellar, Theorem 26.5**: `∇f* = (∇f)⁻¹`, one composite. -/
theorem theorem_26_5_gradient_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {x : Rn n} (hx : x ∈ interior (dom f)) :
    gradient (fun w => (conj (pairing n) f w).toReal) (gradient (fun w => (f w).toReal) x) = x :=
  gradient_conj_gradient hf hp hcl hleg hx

/-- **Rockafellar, Theorem 26.5**: `∇f* = (∇f)⁻¹`, the other composite. -/
theorem theorem_26_5_gradient_gradient_conj (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (dom (conj (pairing n) f))) :
    gradient (fun w => (f w).toReal) (gradient (fun w => (conj (pairing n) f w).toReal) v) = v :=
  gradient_gradient_conj hf hp hcl hleg hv

/-! ### Theorem 26.6 -/

/-- **Rockafellar, Theorem 26.6.** Let `f` be a (finite) differentiable convex function on `ℝⁿ`. In
order that `∇f` be a one-to-one mapping from `ℝⁿ` onto itself, it is necessary and sufficient that
`f` be strictly convex and co-finite. -/
theorem theorem_26_6 (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ ↔
      (StrictConvexOnFn f Set.univ ∧ Cofinite f) := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  rw [bijOn_gradient_univ_iff hf hp hdom hdiff,
    ← cofinite_iff_dom_conj_eq_univ (B := pairing n) ⟨hf, hcl, hp⟩]

/-- **Rockafellar, Theorem 26.6**, the concluding clauses: when `∇f` is one-to-one from `ℝⁿ` onto
itself, `f*` is likewise a (finite) differentiable convex function on `ℝⁿ` which is strictly convex
and co-finite. -/
theorem theorem_26_6_conj (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (hbij : Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ) :
    dom (conj (pairing n) f) = Set.univ ∧
      (∀ z : Rn n, DifferentiableAtFn (conj (pairing n) f) z) ∧
      StrictConvexOnFn (conj (pairing n) f) Set.univ ∧ Cofinite (conj (pairing n) f) := by
  have hcl : ClosedFn f := closedFn_of_dom_eq_univ hf hp hdom
  obtain ⟨hdc, hdiffc, hscc⟩ := conj_finite_of_bijOn_gradient_univ hf hp hdom hdiff hbij
  refine ⟨hdc, hdiffc, hscc, ?_⟩
  have hcpc : ClosedProperConvexFn (conj (pairing n) f) :=
    ⟨convexFn_conj _ f, closedFn_conj, proper_conj ⟨hf, hcl, hp⟩⟩
  rw [cofinite_iff_dom_conj_eq_univ (B := pairing n) hcpc, conj_conj_innerL hf hcl]
  exact hdom

/-- **Rockafellar, Theorem 26.6**: `f*` is the same as the Legendre conjugate of `f`, i.e.
`f*(x*) = ⟨(∇f)⁻¹(x*), x*⟩ − f((∇f)⁻¹(x*))` for every `x*`. -/
theorem theorem_26_6_apply (hf : ConvexFn f) (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (x : Rn n) :
    conj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hdiff x).hasGradientAt_gradient

/-! ### Lemma 26.7 -/

/-- **Rockafellar, Lemma 26.7.** Let `f` be a differentiable convex function on `ℝⁿ`. In order that
`f` be co-finite, it is necessary and sufficient that `|∇f(xᵢ)| → +∞` for every sequence with
`|xᵢ| → +∞`. -/
theorem lemma_26_7 (hf : ConvexFn f) (hp : Proper f) (hdom : dom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Cofinite f ↔ ∀ xs : ℕ → Rn n, Tendsto (fun i => ‖xs i‖) atTop atTop →
      Tendsto (fun i => ‖gradient (fun w => (f w).toReal) (xs i)‖) atTop atTop :=
  cofinite_iff_forall_tendsto_norm_gradient_atTop hf hp hdom hdiff

end Rockafellar
