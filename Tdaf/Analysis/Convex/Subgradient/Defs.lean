/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Rel
import Tdaf.Analysis.Convex.Duality.Support

/-!
# Subgradients, normal cones and directional derivatives

Rockafellar's §23, over a dual pair `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. A *subgradient* of `f` at `x` is a
`y : F` for which the affine function `z ↦ f x + ⟨z - x, y⟩` minorizes `f`; equivalently, one for
which the graph of that affine function is a non-vertical supporting hyperplane to `epi f` at
`(x, f x)`. The set of them is the *subdifferential* `∂f x`.

Nothing in Mathlib defines a subgradient, so the definitions here are the ones the rest of the
library will use. `subgradient` is deliberately **algebraic**: it is a system of weak linear
inequalities, one for each `z`, and neither it nor Theorem 23.5 uses any topology.

## Main definitions

* `subgradient B f x` — the subdifferential `∂f x`, a subset of `F`.
* `subgradientRel B f` — the *graph* of `∂f`, as a `SetRel E F`. Corollary 23.5.1 is literally
  `SetRel.inv` applied to it; see the design note.
* `domSubgradient B f` — the set of points at which `f` has a subgradient, Rockafellar's
  `dom ∂f`.
* `normalCone B C x` — the normal cone `N_C(x)`, with `normalPointedCone` bundling it as
  a `PointedCone ℝ F`.
* `dirDeriv f x y` — the one-sided directional derivative `f'(x; y)`, as the infimum of the
  difference quotient. Only meaningful where `f x` is finite; see the design note.

## Main results

* `mem_subgradient_iff_forall_sub_le`, `mem_subgradient_iff_conj_le`,
  `mem_subgradient_iff_conj_eq`, `mem_subgradient_iff_add_conj_le`,
  `Proper.mem_subgradient_iff_add_conj_eq` — **Theorem 23.5**, conditions (a)–(d). The first
  four are *unconditional*: neither convexity nor properness is used. Only the passage from the
  inequality (c) to the equality (d) needs `Proper`, for the reason recorded in `gotchas.md` LIB8.
* `mem_subgradient_clFn_iff`, `mem_subgradient_conj_iff` — **Theorem 23.5**, the extra
  conditions `(a*)`, `(b*)` and `(a**)` available when `(cl f) x = f x`.
* `subgradientRel_conj_eq_inv` — **Corollary 23.5.1**: for a closed proper convex `f` the
  graph of `∂f*` is the flip of the graph of `∂f`.
* `Proper.mem_subgradient_tfae` — the four conditions of **Theorem 23.5** as one `List.TFAE`.
* `biconj_eq_of_mem_subgradient`, `clFn_eq_of_mem_subgradient`,
  `subgradient_clFn` — **Corollary 23.5.2**.
* `subgradient_indicatorFn` — `∂δ(· | C) x = N_C(x)`, for `x ∈ C`.
* `subgradient_supportFn`, `subgradient_conj_indicatorFn` — **Corollary 23.5.3**:
  `∂δ*(· | C) y` is the set of maximizers of `⟨·, y⟩` over `C`.
* `mem_subgradient_indicatorFn_pointedCone` — **Corollary 23.5.4**.
* `monotoneOn_sub_div`, `dirDeriv_zero`, `posHomogeneous_dirDeriv`,
  `convexFn_dirDeriv`, `neg_dirDeriv_neg_le` — **Theorem 23.1**.
* `mem_subgradient_iff_le_dirDeriv`, `supportSet_dirDeriv`, `conj_dirDeriv`,
  `clFn_dirDeriv` — **Theorem 23.2**, both halves.
* `proper_of_mem_subgradient` — **Theorem 23.3**, first half.
* `convex_subgradient`, `isClosed_subgradient` — `∂f x` is convex always, and closed as
  soon as the pairing is continuous in its second variable.

## Design notes

### Should `∂f` be a relation?

Yes. Rockafellar calls `∂f` a *multivalued mapping*, and every statement of §24 (monotonicity,
closedness of the graph, maximality) and of §26 is about its graph, not about the individual sets
`∂f x`. Mathlib's `SetRel E F := Set (E × F)` is exactly that object, with `SetRel.inv`,
`SetRel.dom`, `SetRel.image` and `SetRel.comp` supplied. Corollary 23.5.1 says `∂(f*) = (∂f)⁻¹`,
and with `subgradientRel` that is what it literally says
(`subgradientRel_conj_eq_inv`); phrased through the pointwise sets it is a `∀ x y`
biconditional that §24 would have to re-bundle. Both forms are provided — `subgradient` is
what a user asks for at a point, `subgradientRel` is what the theory is about — and
`mem_subgradientRel` is the definitional bridge.

`∂f x` is *not* bundled as a convex set or as a closed convex set. Convexity holds unconditionally
(`convex_subgradient`), but closedness needs a hypothesis (below), so a bundled "closed convex
set" would carry that hypothesis as data and would be unusable at layer A, which is where the
subgradient inequality lives. `N_C(x)` *is* bundled, as a `PointedCone ℝ F`
(`normalPointedCone`), because it is a cone with no hypothesis whatever on `C` or `x`; the
precedent is `recessionPointedCone`.

### Where topology enters (design decision D0)

Three places, and each is one of D0's two shapes.

* `isClosed_subgradient` needs *the map `⟨z, ·⟩ : F → ℝ` to be continuous* for every `z`.
  Rockafellar gets this for free in `ℝⁿ`; here it is `[IsContinuousPairing B.flip]`, the same
  instance `closedFn_conj` asks for, and no surjectivity is involved.
* `subgradient_conj_indicatorFn` (Corollary 23.5.3) needs `C` **closed** — Rockafellar says so
  too — and it needs it through `closedFn_indicatorFn`.
* Everything derived from Fenchel–Moreau (`subgradientRel_conj_eq_inv`,
  `clFn_dirDeriv`) carries `biconj_eq_clFn`'s `[IsCompatiblePairing B]`.

**Corollary 23.5.4 needs no closedness at all.** Rockafellar derives it from
`δ(· | K)* = δ(· | K°)`, which needs `K` closed; the direct argument — put `z = 0` and `z = x + x`
into the subgradient inequality — does not, so the statement here is for an arbitrary
`PointedCone ℝ E`.

### The finiteness hypothesis on `dirDeriv`

Theorem 23.1's "let `x` be a point where `f` is finite" is not removable. `EReal` has `⊤ - ⊤ = ⊥`
and `⊥ - ⊥ = ⊥`, so off `dom f` the difference quotient is `⊥` in every direction, `f'(x; ·)` is
identically `⊥`, and `f'(x; 0) = 0` is false. Every statement of Theorem 23.1 mentioning a *value*
of `f'(x; ·)` therefore carries `f x ≠ ⊤` and `f x ≠ ⊥`. Positive homogeneity is the exception: it
is a reindexing of the infimum and holds for every `f` and every `x`.

### What is deferred

* **Theorem 23.4** (`∂f x ≠ ∅` on `ri (dom f)`, and `f'(x; ·) = δ*(· | ∂f x)` there) and
  **Theorem 23.7** rest on relative interiors, which live in
  `Tdaf/Analysis/Convex/RelativeInterior.lean`, a finite-dimensional module this file does not
  import. They are not stated here, not even weakened. Only the relative-interior-free first
  sentence of Theorem 23.4 — `∂f x = ∅` off `dom f` for proper `f` — is recorded, as
  `subgradient_eq_empty_of_notMem_dom`.
* The second half of **Theorem 23.3** (if `f` is not subdifferentiable at `x` then
  `f'(x; z - x) = -∞` for `z ∈ ri (dom f)`) is relative-interior-based and is deferred with it,
  to `Tdaf/Analysis/Convex/Subgradient/Existence.lean`.
* **Theorem 23.6** (ε-subgradients) is omitted: its proof runs through Theorems 9.7 and 13.5, and
  Theorem 13.5 is itself deferred by `Tdaf/Analysis/Convex/Duality/Support.lean`.
* **Theorems 23.8–23.10** are subdifferential *calculus* and belong in
  `Tdaf/Analysis/Convex/Subgradient/Calculus.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §23 — from the start
  through Corollary 23.5.4.
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **subdifferential** of `f` at `x` with respect to the pairing `B`: the set of `y : F`
satisfying Rockafellar's *subgradient inequality*

`f z ≥ f x + ⟨z - x, y⟩` for every `z`.

Geometrically, when `f x` is finite, `y` is a subgradient exactly when the graph of the affine
function `z ↦ f x + ⟨z - x, y⟩` is a non-vertical supporting hyperplane to `epi f` at `(x, f x)`.
The definition is purely algebraic — an infinite system of weak linear inequalities — and no
topology is used until `isClosed_subgradient`. -/
def subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set F :=
  {y | ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z}

/-- The **graph of the subdifferential**: Rockafellar's multivalued mapping `∂f : x ↦ ∂f x`, as a
`SetRel E F`. This is the object §24 and §26 are about, and it is what Corollary 23.5.1
(`subgradientRel_conj_eq_inv`) inverts. -/
def subgradientRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : SetRel E F :=
  {p | p.2 ∈ subgradient B f p.1}

/-- The **normal cone** to `C` at `x`: the `y : F` making a non-acute angle with every direction
`z - x` pointing from `x` into `C`.

Rockafellar introduces `N_C(x)` as `∂δ(x | C)` and therefore leaves it empty for `x ∉ C`. Here it
is defined for every `x`, which is what makes it a pointed cone with no hypothesis; the price is
that `subgradient_indicatorFn` carries `x ∈ C`, with
`subgradient_indicatorFn_of_notMem` for the other case. -/
def normalCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : Set F :=
  {y | ∀ z ∈ C, B (z - x) y ≤ 0}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

@[simp] theorem mem_subgradient :
    y ∈ subgradient B f x ↔ ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z := Iff.rfl

@[simp] theorem mem_subgradientRel : (x, y) ∈ subgradientRel B f ↔ y ∈ subgradient B f x := Iff.rfl

@[simp] theorem mem_normalCone : y ∈ normalCone B C x ↔ ∀ z ∈ C, B (z - x) y ≤ 0 := Iff.rfl

/-- The normal cone is a pointed convex cone, with no hypothesis on `C` or on `x`. Bundling it
buys convexity, pointedness and the universal property of `PointedCone.hull`; the precedent is
`recessionPointedCone`. -/
def normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : PointedCone ℝ F where
  carrier := normalCone B C x
  zero_mem' z _ := by simp
  add_mem' {y₁ y₂} h₁ h₂ z hz := by
    rw [map_add]
    exact add_nonpos (h₁ z hz) (h₂ z hz)
  smul_mem' c y h z hz := by
    rw [LinearMap.map_smul_of_tower]
    exact smul_nonpos_of_nonneg_of_nonpos c.2 (h z hz)

/-- The carrier of `normalPointedCone` is the normal cone. -/
@[simp] theorem coe_normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) :
    (normalPointedCone B C x : Set F) = normalCone B C x := rfl

/-- **The subdifferential is a convex set**, with no hypothesis on `f`: it is an intersection of
half-spaces of `F`, one for each `z`. Rockafellar makes the same remark immediately after the
definition. -/
theorem convex_subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    Convex ℝ (subgradient B f x) := by
  intro y₁ h₁ y₂ h₂ a b ha hb hab z
  have key : ∀ p q : ℝ, f x + (p : EReal) ≤ f z → q ≤ p → f x + (q : EReal) ≤ f z :=
    fun _ _ hp hqp => le_trans (add_le_add le_rfl (mod_cast hqp)) hp
  simp only [mem_subgradient, map_add, map_smul, smul_eq_mul] at h₁ h₂ ⊢
  rcases le_total (B (z - x) y₁) (B (z - x) y₂) with h | h
  · refine key _ _ (h₂ z) ?_
    have h1 : a * B (z - x) y₁ ≤ a * B (z - x) y₂ := mul_le_mul_of_nonneg_left h ha
    have h2 : a * B (z - x) y₂ + b * B (z - x) y₂ = B (z - x) y₂ := by rw [← add_mul, hab, one_mul]
    linarith
  · refine key _ _ (h₁ z) ?_
    have h1 : b * B (z - x) y₂ ≤ b * B (z - x) y₁ := mul_le_mul_of_nonneg_left h hb
    have h2 : a * B (z - x) y₁ + b * B (z - x) y₁ = B (z - x) y₁ := by rw [← add_mul, hab, one_mul]
    linarith

/-- **A point with a subgradient lies in the effective domain.** Were `f x = ⊤`, the subgradient
inequality would read `⊤ ≤ f z` for every `z` and force `f ≡ ⊤`, which properness forbids.

No topology and no convexity: this is a statement about the defining inequality alone. -/
theorem mem_dom_of_mem_subgradient (hp : Proper f) (hy : y ∈ subgradient B f x) : x ∈ dom f := by
  obtain ⟨z₀, hz₀⟩ := hp.dom_nonempty
  refine mem_dom.2 (lt_top_iff_ne_top.2 fun htop => ?_)
  have hle := hy z₀
  rw [htop, _root_.EReal.top_add_coe] at hle
  exact absurd (top_le_iff.1 hle) (mem_dom.1 hz₀).ne

/-- **`dom ∂f`**: the set of points at which `f` has at least one subgradient. Rockafellar's
`dom ∂f`, and the set §26's essential strict convexity quantifies over. -/
def domSubgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set E :=
  {x | (subgradient B f x).Nonempty}

@[simp] theorem mem_domSubgradient : x ∈ domSubgradient B f ↔ (subgradient B f x).Nonempty :=
  Iff.rfl

/-- `dom ∂f ⊆ dom f`: a subgradient at `x` forces `f x < ⊤`. -/
theorem domSubgradient_subset_dom (hp : Proper f) : domSubgradient B f ⊆ dom f := by
  rintro z ⟨y, hy⟩
  exact mem_dom_of_mem_subgradient hp hy

end Defs

/-! ### Theorem 23.5, conditions (a)–(d)

All four are equivalent with **no** hypothesis on `f` except at the last step: the passage from the
inequality `f x + f* y ≤ ⟨x, y⟩` to the equality needs Fenchel's inequality, hence properness.
Rockafellar states the theorem for proper convex `f`; convexity is never used. -/

section Conj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- **Theorem 23.5**, (a) ⟺ (b): `y ∈ ∂f x` says exactly that `⟨·, y⟩ - f` attains its supremum
at `x`. -/
theorem mem_subgradient_iff_forall_sub_le :
    y ∈ subgradient B f x ↔ ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x := by
  refine forall_congr' fun z => ?_
  rw [EReal.coe_sub_le_comm, EReal.coe_sub_coe_sub, map_sub, LinearMap.sub_apply, add_comm]

/-- **Theorem 23.5**, (a) ⟺ (c): the supremum in (b) *is* `f* y`, so `y ∈ ∂f x` is the inequality
`f* y ≤ ⟨x, y⟩ - f x`. Unconditional. -/
theorem mem_subgradient_iff_conj_le :
    y ∈ subgradient B f x ↔ conj B f y ≤ ((B x y : ℝ) : EReal) - f x := by
  rw [mem_subgradient_iff_forall_sub_le, conj_apply, iSup_le_iff]

/-- **Theorem 23.5**, (a) ⟺ (b) in the form "the supremum is attained": `y ∈ ∂f x` exactly when
`f* y = ⟨x, y⟩ - f x`. This is the `∞ - ∞`-free reading of (d), and it is unconditional. -/
theorem mem_subgradient_iff_conj_eq :
    y ∈ subgradient B f x ↔ conj B f y = ((B x y : ℝ) : EReal) - f x :=
  ⟨fun h => le_antisymm (mem_subgradient_iff_conj_le.1 h) (sub_le_conj B f x y),
    fun h => mem_subgradient_iff_conj_le.2 h.le⟩

/-- **Theorem 23.5**, (a) ⟺ (c) in Rockafellar's additive form `f x + f* y ≤ ⟨x, y⟩`.
Unconditional: adding a *real* number is an order isomorphism of `EReal`, so no `∞ - ∞` arises.
Contrast `Proper.mem_subgradient_iff_add_conj_eq`. -/
theorem mem_subgradient_iff_add_conj_le :
    y ∈ subgradient B f x ↔ f x + conj B f y ≤ ((B x y : ℝ) : EReal) := by
  rw [mem_subgradient_iff_conj_le, _root_.EReal.le_sub_iff_add_le
    (.inr (_root_.EReal.coe_ne_bot _)) (.inr (_root_.EReal.coe_ne_top _)), add_comm]

/-- **Theorem 23.5**, (a) ⟺ (d): `y ∈ ∂f x` exactly when Fenchel's inequality holds with equality
at `(x, y)`.

Properness is not decorative. For `f ≡ ⊤` every `y` is a subgradient at every `x` (the subgradient
inequality reads `⊤ ≤ ⊤`), while `f* ≡ ⊥` and so `f x + f* y = ⊤ + ⊥ = ⊥ ≠ ⟨x, y⟩`. This is the
trap `le_add_conj` carries too; see `gotchas.md` LIB8. -/
theorem Proper.mem_subgradient_iff_add_conj_eq (hp : Proper f) :
    y ∈ subgradient B f x ↔ f x + conj B f y = ((B x y : ℝ) : EReal) := by
  rw [mem_subgradient_iff_add_conj_le]
  exact ⟨fun h => le_antisymm h (hp.le_add_conj x y), fun h => h.le⟩

/-- **Theorem 23.5** in Rockafellar's own shape: for a proper `f` the four conditions

* (a) `y ∈ ∂f x`;
* (b) `⟨·, y⟩ - f` attains its supremum at `x`;
* (c) `f x + f* y ≤ ⟨x, y⟩`;
* (d) `f x + f* y = ⟨x, y⟩`

are equivalent. Rockafellar also assumes `f` convex; convexity is not used anywhere in the proof.
Properness is used only to close the loop back from (d), and it is genuinely needed there. -/
theorem Proper.mem_subgradient_tfae (hp : Proper f) (x : E) (y : F) :
    List.TFAE [y ∈ subgradient B f x,
      ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x,
      f x + conj B f y ≤ ((B x y : ℝ) : EReal),
      f x + conj B f y = ((B x y : ℝ) : EReal)] := by
  tfae_have 1 ↔ 2 := mem_subgradient_iff_forall_sub_le
  tfae_have 1 ↔ 3 := mem_subgradient_iff_add_conj_le
  tfae_have 1 ↔ 4 := hp.mem_subgradient_iff_add_conj_eq
  tfae_finish

/-- **Theorem 23.5**, (a) ⟺ `(a*)`: `x ∈ ∂f* y` and `y ∈ ∂f x` agree at every `x` where `f`
coincides with its biconjugate. For closed proper convex `f` that is everywhere, which is
Corollary 23.5.1. -/
theorem mem_subgradient_conj_iff (h : biconj B f x = f x) :
    x ∈ subgradient B.flip (conj B f) y ↔ y ∈ subgradient B f x := by
  have h' : conj B.flip (conj B f) x = f x := h
  rw [mem_subgradient_iff_add_conj_le, mem_subgradient_iff_add_conj_le, LinearMap.flip_apply, h',
    add_comm]

/-- **Corollary 23.5.2**, first half: at a point where `f` is subdifferentiable it agrees with its
biconjugate. No topology and no convexity: the witness `y` makes Fenchel's inequality an equality,
which pins `f** x` between `f x` and itself. -/
theorem biconj_eq_of_mem_subgradient (hy : y ∈ subgradient B f x) : biconj B f x = f x := by
  refine le_antisymm (biconj_le B f x) ?_
  have h := sub_le_conj B.flip (conj B f) y x
  rwa [LinearMap.flip_apply, mem_subgradient_iff_conj_eq.1 hy, EReal.coe_sub_coe_sub, sub_self,
    _root_.EReal.coe_zero, zero_add] at h

/-- **Theorem 23.3**, first half: a function subdifferentiable at a point where it is finite is
proper. The subgradient inequality exhibits a finite affine minorant, which rules out the value
`⊥`, and finiteness at `x` gives a point of `dom f`. -/
theorem proper_of_mem_subgradient (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hy : y ∈ subgradient B f x) :
    Proper f := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine ⟨⟨x, lt_top_iff_ne_top.2 ht⟩, fun z hz => ?_⟩
  have h := hy z
  rw [hr, hz, ← _root_.EReal.coe_add] at h
  exact _root_.EReal.coe_ne_bot _ (le_bot_iff.1 h)

/-- **Theorem 23.3**, first half, in the "subdifferentiable" phrasing. -/
theorem proper_of_subgradient_nonempty (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subgradient B f x).Nonempty) : Proper f :=
  h.elim fun _ hy => proper_of_mem_subgradient ht hb hy

/-- A proper function has no subgradients off its effective domain. This is the first sentence of
Theorem 23.4; unlike the rest of that theorem it involves no relative interiors. -/
theorem subgradient_eq_empty_of_notMem_dom (hp : Proper f) (hx : x ∉ dom f) :
    subgradient B f x = ∅ := by
  obtain ⟨z, hz⟩ := hp.dom_nonempty
  have hfx : f x = ⊤ := by
    by_contra hc
    exact hx (lt_top_iff_ne_top.2 hc)
  refine eq_empty_of_forall_notMem fun y hy => absurd (hy z) (not_le.2 ?_)
  rw [hfx, _root_.EReal.top_add_coe]
  exact hz

end Conj

/-! ### Indicator functions, normal cones and polar cones -/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E} {x : E} {y : F}

/-- **The subdifferential of an indicator function is the normal cone** (Rockafellar §23), at any
point of `C`. -/
theorem subgradient_indicatorFn (hx : x ∈ C) :
    subgradient B (indicatorFn C) x = normalCone B C x := by
  ext y
  simp only [mem_subgradient, indicatorFn_of_mem hx, zero_add, mem_normalCone]
  refine ⟨fun h z hz => ?_, fun h z => ?_⟩
  · have hz' := h z
    rw [indicatorFn_of_mem hz] at hz'
    exact_mod_cast hz'
  · by_cases hz : z ∈ C
    · rw [indicatorFn_of_mem hz]
      exact_mod_cast h z hz
    · rw [indicatorFn_of_notMem hz]
      exact le_top

/-- Off `C` there are no subgradients of `δ(· | C)`, provided `C` is nonempty — which is exactly
Rockafellar's standing hypothesis on the set. -/
theorem subgradient_indicatorFn_of_notMem (hC : C.Nonempty) (hx : x ∉ C) :
    subgradient B (indicatorFn C) x = ∅ :=
  subgradient_eq_empty_of_notMem_dom ⟨by rwa [dom_indicatorFn], indicatorFn_ne_bot C⟩
    (by rwa [dom_indicatorFn])

/-- Membership in `∂δ(· | C)` in full, for nonempty `C`. -/
theorem mem_subgradient_indicatorFn_iff (hC : C.Nonempty) :
    y ∈ subgradient B (indicatorFn C) x ↔ x ∈ C ∧ y ∈ normalCone B C x := by
  by_cases hx : x ∈ C
  · rw [subgradient_indicatorFn hx]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  · rw [subgradient_indicatorFn_of_notMem hC hx]
    exact ⟨fun h => absurd h (notMem_empty y), fun h => absurd h.1 hx⟩

/-- **Corollary 23.5.4.** For a pointed convex cone `K`, `y` is a subgradient of `δ(· | K)` at `x`
exactly when `x ∈ K`, `y` lies in the polar cone `K° = N_K(0)`, and `⟨x, y⟩ = 0`.

Rockafellar proves this from `δ(· | K)* = δ(· | K°)` and therefore assumes `K` closed. The direct
argument — put `z = 0` and `z = x + x` into the subgradient inequality — needs no topology, so no
closedness hypothesis appears here. -/
theorem mem_subgradient_indicatorFn_pointedCone (K : PointedCone ℝ E) :
    y ∈ subgradient B (indicatorFn (K : Set E)) x ↔
      x ∈ K ∧ y ∈ normalCone B (K : Set E) 0 ∧ B x y = 0 := by
  rw [mem_subgradient_indicatorFn_iff ⟨0, K.zero_mem⟩]
  simp only [mem_normalCone, sub_zero, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, h⟩
    have h0 : B (0 - x) y ≤ 0 := h 0 K.zero_mem
    have h2 : B (x + x - x) y ≤ 0 := h (x + x) (K.add_mem hx hx)
    rw [zero_sub, map_neg, LinearMap.neg_apply] at h0
    rw [add_sub_cancel_right] at h2
    have hzero : B x y = 0 := le_antisymm h2 (by linarith)
    refine ⟨hx, fun z hz => ?_, hzero⟩
    have hz' := h z hz
    rwa [map_sub, LinearMap.sub_apply, hzero, sub_zero] at hz'
  · rintro ⟨hx, hpol, hzero⟩
    refine ⟨hx, fun z hz => ?_⟩
    rw [map_sub, LinearMap.sub_apply, hzero, sub_zero]
    exact hpol z hz

end Indicator

/-! ### Closedness of the subdifferential -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

omit [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] in
/-- Adding a fixed `EReal` to a real is continuous: the three cases `⊥`, a real value, and `⊤` give
a constant, a translation, and a constant. (The map `u + ·` on `EReal` is *not* continuous when
`u = ⊤`, because `⊤ + ⊥ = ⊥`; restricting the argument to the reals is what saves it.) -/
theorem continuous_add_coe (u : EReal) : Continuous fun t : ℝ => u + (t : EReal) := by
  induction u with
  | bot => simpa only [_root_.EReal.bot_add] using continuous_const
  | coe r =>
    have h : Continuous fun t : ℝ => (r + t : ℝ) := by fun_prop
    simpa only [← _root_.EReal.coe_add] using continuous_coe_real_ereal.comp' h
  | top => simpa only [_root_.EReal.top_add_coe] using continuous_const

/-- **The subdifferential is closed** once every `⟨z, ·⟩ : F → ℝ` is continuous. This is design
decision D0 in its "the map is continuous" form: in `ℝⁿ` it is automatic, and here it is the
instance `closedFn_conj` asks for. -/
theorem isClosed_subgradient [IsContinuousPairing B.flip] (f : E → EReal) (x : E) :
    IsClosed (subgradient B f x) := by
  rw [show subgradient B f x = ⋂ z : E, {y | f x + ((B (z - x) y : ℝ) : EReal) ≤ f z} from
    Set.ext fun y => by simp]
  exact isClosed_iInter fun z =>
    isClosed_Iic.preimage ((continuous_add_coe (f x)).comp (continuous_pairing B.flip (z - x)))

end Closed

/-! ### Theorem 23.1: the directional derivative -/

section DirDeriv

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x y : E}

/-- The **one-sided directional derivative** `f'(x; y)`, defined as the infimum over `a > 0` of the
difference quotient.

By Theorem 23.1 the quotient is nondecreasing in `a` for convex `f` finite at `x`
(`monotoneOn_sub_div`), so the infimum is the limit as `a ↓ 0`, which is Rockafellar's
definition. Off `dom f` the expression degenerates: `⊤ - ⊤ = ⊥` in `EReal`, so `f'(x; ·) ≡ ⊥` and
Theorem 23.1's `f'(x; 0) = 0` fails. This is why the finiteness hypothesis is kept throughout. -/
noncomputable def dirDeriv (f : E → EReal) (x y : E) : EReal :=
  ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal)

theorem dirDeriv_apply (f : E → EReal) (x y : E) :
    dirDeriv f x y = ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) := rfl

/-- The directional derivative is a lower bound for every difference quotient. -/
theorem dirDeriv_le (f : E → EReal) (x y : E) {a : ℝ} (ha : 0 < a) :
    dirDeriv f x y ≤ (f (x + a • y) - f x) / (a : EReal) :=
  iInf₂_le (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) a ha

/-- A lower bound for all difference quotients bounds the directional derivative. -/
theorem le_dirDeriv {c : EReal} (h : ∀ a : ℝ, 0 < a → c ≤ (f (x + a • y) - f x) / (a : EReal)) :
    c ≤ dirDeriv f x y :=
  le_iInf₂ (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) h

/-- Witness extraction from the defining infimum. -/
theorem dirDeriv_lt_iff {c : EReal} :
    dirDeriv f x y < c ↔ ∃ a : ℝ, 0 < a ∧ (f (x + a • y) - f x) / (a : EReal) < c := by
  simp only [dirDeriv, iInf_lt_iff, Set.mem_Ioi, exists_prop]

/-- **Theorem 23.1**: `f'(x; 0) = 0` whenever `f x` is finite. -/
theorem dirDeriv_zero (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : dirDeriv f x 0 = 0 := by
  have h : ∀ a : ℝ, 0 < a → (f (x + a • (0 : E)) - f x) / (a : EReal) = 0 := fun a _ => by
    rw [smul_zero, add_zero, _root_.EReal.sub_self ht hb, _root_.EReal.zero_div]
  exact le_antisymm ((dirDeriv_le f x 0 one_pos).trans (h 1 one_pos).le)
    (le_dirDeriv fun a ha => (h a ha).ge)

/-- **Theorem 23.1**: `f'(x; ·)` is positively homogeneous.

Unlike the other parts of Theorem 23.1 this needs no hypothesis at all: it is the reindexing
`a ↦ a * c` of the defining infimum, and it holds for every `f` and every `x`. -/
theorem posHomogeneous_dirDeriv (f : E → EReal) (x : E) : PosHomogeneous (dirDeriv f x) := by
  intro c hc y
  have hterm : ∀ a : ℝ, 0 < a →
      (f (x + a • (c • y)) - f x) / (a : EReal)
        = (c : EReal) * ((f (x + (a * c) • y) - f x) / ((a * c : ℝ) : EReal)) := by
    intro a _
    rw [smul_smul, div_eq_mul_inv, div_eq_mul_inv, ← _root_.EReal.coe_inv, ← _root_.EReal.coe_inv,
      ← mul_assoc, mul_comm (c : EReal) _, mul_assoc, EReal.coe_mul_coe,
      show c * (a * c)⁻¹ = a⁻¹ from by field_simp]
  rw [dirDeriv_apply, dirDeriv_apply, iInf_subtype', iInf_subtype', EReal.coe_mul_iInf hc]
  refine le_antisymm (le_iInf fun b => ?_) (le_iInf fun a => ?_)
  · have hb : (0 : ℝ) < (b : ℝ) / c := div_pos b.2 hc
    refine le_trans (iInf_le _ (⟨(b : ℝ) / c, hb⟩ : Set.Ioi (0 : ℝ))) ?_
    rw [hterm _ hb, div_mul_cancel₀ (b : ℝ) hc.ne']
  · rw [hterm _ a.2]
    exact iInf_le _ (⟨(a : ℝ) * c, mul_pos a.2 hc⟩ : Set.Ioi (0 : ℝ))

/-- **Theorem 23.1**: for convex `f` finite at `x`, the difference quotient is nondecreasing in the
step `a`. This is what makes the infimum defining `dirDeriv` the limit as `a ↓ 0`, which is
Rockafellar's definition.

The proof is his: `x + a • y` is the convex combination of `x` and `x + b • y` with weights
`1 - a/b` and `a/b`. -/
theorem monotoneOn_sub_div (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) (y : E) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hbne : b ≠ 0 := hb.ne'
  simp only [hr]
  refine EReal.le_of_forall_coe_le fun s hs => ?_
  rw [EReal.sub_div_le_coe_iff hb] at hs
  rw [EReal.sub_div_le_coe_iff ha]
  have ht0 : (0 : ℝ) ≤ a / b := (div_pos ha hb).le
  have ht1 : (0 : ℝ) ≤ 1 - a / b := by
    have : a / b ≤ 1 := (div_le_one hb).2 hab
    linarith
  have hvec : (1 - a / b) • x + (a / b) • (x + b • y) = x + a • y := by
    rw [smul_add, smul_smul, div_mul_cancel₀ a hbne, sub_smul, one_smul]
    abel
  have hcomb := hf.epi_combo (le_of_eq hr) hs ht1 ht0 (by ring)
  have hscal : (1 - a / b) * r + a / b * (r + s * b) = r + s * a := by field_simp; ring
  rw [hvec, hscal] at hcomb
  exact hcomb

/-- The form in which Theorem 23.1's monotonicity is consumed: if `f'(x; y) < m` then
`f (x + a • y) ≤ f x + m * a` for every sufficiently small `a > 0`. -/
theorem exists_le_of_dirDeriv_lt (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) {y : E}
    {m : ℝ} (h : dirDeriv f x y < (m : EReal)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → f (x + a • y) ≤ ((r + m * a : ℝ) : EReal) := by
  obtain ⟨a₀, ha₀, hlt⟩ := dirDeriv_lt_iff.1 h
  refine ⟨a₀, ha₀, fun a ha hle => ?_⟩
  rw [← EReal.sub_div_le_coe_iff ha, ← hr]
  exact le_trans (monotoneOn_sub_div hf hr y ha ha₀ hle) hlt.le

/-- **Theorem 23.1**: `f'(x; ·)` is a convex function, for convex `f` finite at `x`.

Monotonicity of the difference quotient is what makes the proof short: the two witnesses supplied
by `exists_le_of_dirDeriv_lt` can be taken at a *common* step `a`, so the convex combination
is formed at the single point `x + a • (s • y₁ + t • y₂)`. -/
theorem convexFn_dirDeriv (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    ConvexFn (dirDeriv f x) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine convexFn_of_epi_combo fun y₁ y₂ μ ν h₁ h₂ s t hs ht' hst => ?_
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : t = 1 := by linarith
    subst this
    simpa using h₂
  rcases ht'.eq_or_lt with ht0 | ht0
  · subst ht0
    have : s = 1 := by linarith
    subst this
    simpa using h₁
  refine EReal.le_coe_of_forall_lt fun p hp => ?_
  obtain ⟨e, he, hesum⟩ : ∃ e : ℝ, 0 < e ∧ s * μ + t * ν + e = p - e :=
    ⟨(p - (s * μ + t * ν)) / 2, by linarith, by ring⟩
  have h1 : dirDeriv f x y₁ < ((μ + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₁ (mod_cast lt_add_of_pos_right μ he)
  have h2 : dirDeriv f x y₂ < ((ν + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₂ (mod_cast lt_add_of_pos_right ν he)
  obtain ⟨a₁, ha₁, H₁⟩ := exists_le_of_dirDeriv_lt hf hr h1
  obtain ⟨a₂, ha₂, H₂⟩ := exists_le_of_dirDeriv_lt hf hr h2
  have ha : 0 < min a₁ a₂ := lt_min ha₁ ha₂
  have hA := H₁ _ ha (min_le_left a₁ a₂)
  have hB := H₂ _ ha (min_le_right a₁ a₂)
  have hvec : s • (x + min a₁ a₂ • y₁) + t • (x + min a₁ a₂ • y₂)
      = x + min a₁ a₂ • (s • y₁ + t • y₂) := by
    match_scalars
    · linear_combination hst
    · ring
    · ring
  have hcomb := hf.epi_combo hA hB hs ht' hst
  rw [hvec, show s * (r + (μ + e) * min a₁ a₂) + t * (r + (ν + e) * min a₁ a₂)
      = r + (p - e) * min a₁ a₂ from by
    linear_combination (r + min a₁ a₂ * e) * hst + min a₁ a₂ * hesum] at hcomb
  calc dirDeriv f x (s • y₁ + t • y₂)
      ≤ (f (x + min a₁ a₂ • (s • y₁ + t • y₂)) - f x) / ((min a₁ a₂ : ℝ) : EReal) :=
        dirDeriv_le _ _ _ ha
    _ ≤ ((p - e : ℝ) : EReal) := by
        rw [hr]
        exact (EReal.sub_div_le_coe_iff ha _).2 hcomb
    _ < (p : EReal) := mod_cast sub_lt_self p he

/-- **Theorem 23.1**: `-f'(x; -y) ≤ f'(x; y)`.

No `≠ ⊥` hypothesis on `f'(x; ·)` appears, although `PosHomogeneous.neg_le`
(Corollary 4.7.2) carries one: the argument through `f'(x; 0) = 0` does not need it, and
`f'(x; ·)` really can take the value `⊥` — that is the content of Theorem 23.3's second half. -/
theorem neg_dirDeriv_neg_le (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (y : E) :
    -dirDeriv f x (-y) ≤ dirDeriv f x y := by
  have hconv := convexFn_dirDeriv hf ht hb
  have hzero := dirDeriv_zero ht hb
  have main : ∀ m n : ℝ, dirDeriv f x (-y) ≤ (m : EReal) → dirDeriv f x y ≤ (n : EReal) →
      (0 : ℝ) ≤ m + n := by
    intro m n hm hn
    have hc := hconv.epi_combo hm hn (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    rw [show ((1 : ℝ) / 2) • (-y) + ((1 : ℝ) / 2) • y = (0 : E) from by
      rw [smul_neg, neg_add_cancel], hzero, ← _root_.EReal.coe_zero,
      _root_.EReal.coe_le_coe_iff] at hc
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨n, hn1, hn2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
  have h3 : dirDeriv f x (-y) < ((-n : ℝ) : EReal) := by
    rw [_root_.EReal.coe_neg]
    exact _root_.EReal.lt_neg_comm.1 hn2
  obtain ⟨m, hm1, hm2⟩ := EReal.exists_real_btwn_of_lt_coe h3
  have := main m n hm1.le hn1.le
  linarith

end DirDeriv

/-! ### Theorem 23.2 -/

section DirDerivSubgradient

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- **Theorem 23.2**, first half: `y` is a subgradient of `f` at `x` exactly when the linear
function `⟨·, y⟩` is majorized by the directional derivative `f'(x; ·)`.

Neither convexity of `f` nor monotonicity of the difference quotient is used: the subgradient
inequality at `z = x + a • v` *is* the inequality `⟨v, y⟩ ≤ (f (x + a • v) - f x) / a`. -/
theorem mem_subgradient_iff_le_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    y ∈ subgradient B f x ↔ ∀ v : E, ((B v y : ℝ) : EReal) ≤ dirDeriv f x v := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  constructor
  · intro h v
    refine le_dirDeriv fun a ha => ?_
    rw [hr, EReal.coe_le_sub_div_iff ha]
    have hv := h (x + a • v)
    rw [add_sub_cancel_left, hr, ← _root_.EReal.coe_add, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at hv
    rwa [mul_comm (B v y) a]
  · intro h z
    have h1 := dirDeriv_le f x (z - x) one_pos
    rw [one_smul, show x + (z - x) = z from by abel] at h1
    have h2 := (h (z - x)).trans h1
    rw [hr, EReal.coe_le_sub_div_iff one_pos, mul_one, _root_.EReal.coe_add] at h2
    rw [hr]
    exact h2

/-- The set §13 attaches to `f'(x; ·)` is the subdifferential: `supportSet` unfolds to the
system of inequalities `⟨v, y⟩ ≤ f'(x; v)`, which is `mem_subgradient_iff_le_dirDeriv`. -/
theorem supportSet_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    supportSet B (dirDeriv f x) = subgradient B f x :=
  Set.ext fun _ => (mem_subgradient_iff_le_dirDeriv ht hb).symm

/-- **Theorem 23.2**, the dual half: the conjugate of `f'(x; ·)` is the *indicator* of `∂f x`.

This is `conj_eq_indicatorFn_of_posHomogeneous` — the engine of Corollary 13.2.1 — applied to
`f'(x; ·)`, which is positively homogeneous and finite at the origin. Convexity of `f` is not
needed, and neither is any topology. -/
theorem conj_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    conj B (dirDeriv f x) = indicatorFn (subgradient B f x) := by
  rw [conj_eq_indicatorFn_of_posHomogeneous (posHomogeneous_dirDeriv f x)
      ⟨0, by rw [dirDeriv_zero ht hb]; simp⟩,
    supportSet_dirDeriv ht hb]

end DirDerivSubgradient

/-! ### Corollaries 23.5.1–23.5.3, and the closure of the directional derivative

Everything here consumes Fenchel–Moreau, so the pairing hypotheses of `biconj_eq_clFn` come
with it. -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}
  {x : E} {y : F}

/-- **Theorem 23.5**, (a) ⟺ `(a**)`: `∂(cl f) x = ∂f x` wherever `(cl f) x = f x`. Only the
continuity of the pairing is needed, through `conj_clFn`. -/
theorem mem_subgradient_clFn_iff [IsContinuousPairing B] (hx : clFn f x = f x) :
    y ∈ subgradient B (clFn f) x ↔ y ∈ subgradient B f x := by
  rw [mem_subgradient_iff_conj_le, mem_subgradient_iff_conj_le, conj_clFn, hx]

variable [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Corollary 23.5.1**, pointwise: for a closed proper convex `f`, `x ∈ ∂f* y` and `y ∈ ∂f x`
say the same thing. -/
theorem mem_subgradient_conj_iff_of_closedFn [IsCompatiblePairing B] (hf : ConvexFn f)
    (hc : ClosedFn f) :
    x ∈ subgradient B.flip (conj B f) y ↔ y ∈ subgradient B f x :=
  mem_subgradient_conj_iff (congrFun (biconj_eq_self hf hc) x)

/-- **Corollary 23.5.1**: for a closed proper convex `f`, `∂f*` is the inverse of `∂f` as a
multivalued mapping — the graph of `∂f*` is the flip of the graph of `∂f`.

This is the form §26 and §31 want, and it is why `subgradientRel` exists. -/
theorem subgradientRel_conj_eq_inv [IsCompatiblePairing B] (hf : ConvexFn f) (hc : ClosedFn f) :
    subgradientRel B.flip (conj B f) = (subgradientRel B f).inv := by
  ext ⟨y, x⟩
  simp only [SetRel.mem_inv, mem_subgradientRel]
  exact mem_subgradient_conj_iff_of_closedFn hf hc

/-- **Corollary 23.5.2**: at a point where a convex `f` is subdifferentiable, `(cl f) x = f x`. -/
theorem clFn_eq_of_mem_subgradient [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subgradient B f x) : clFn f x = f x := by
  rw [← congrFun (biconj_eq_clFn (B := B) hf) x]
  exact biconj_eq_of_mem_subgradient hy

/-- **Corollary 23.5.2**, second half: and then `∂(cl f) x = ∂f x`. -/
theorem subgradient_clFn [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subgradient B f x) : subgradient B (clFn f) x = subgradient B f x :=
  Set.ext fun _ => mem_subgradient_clFn_iff (clFn_eq_of_mem_subgradient hf hy)

/-- **Corollary 23.5.3.** For a nonempty closed convex set `C`, the subgradients at `y` of the
support function `δ*(· | C) = δ(· | C)*` are exactly the points of `C` at which the linear function
`⟨·, y⟩` attains its maximum over `C`. `subgradient_supportFn` is the same statement with
§13's `supportFn`. -/
theorem subgradient_conj_indicatorFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subgradient B.flip (conj B (indicatorFn C)) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  ext x
  have hbi := congrFun (biconj_eq_self (B := B) (convexFn_indicatorFn.2 hCc)
    (closedFn_indicatorFn hC)) x
  rw [mem_subgradient_conj_iff hbi, mem_subgradient_indicatorFn_iff hCne, Set.mem_sep_iff]
  refine and_congr_right fun _ => ?_
  simp only [mem_normalCone]
  exact forall₂_congr fun z _ => by rw [map_sub, LinearMap.sub_apply, sub_nonpos]

/-- **Corollary 23.5.3**, with §13's `supportFn`: `∂δ*(· | C) y` is the face of `C` on which
`⟨·, y⟩` is maximized. -/
theorem subgradient_supportFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subgradient B.flip (supportFn B C) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  rw [supportFn_eq_conj_indicatorFn]
  exact subgradient_conj_indicatorFn hC hCc hCne y

/-- **Theorem 23.2**, second half: the closure of `f'(x; ·)` is the support function of `∂f x`.

This is Corollary 13.2.1 (`clFn_eq_supportFn_of_posHomogeneous`) for `f'(x; ·)`, and it is
proved the same way: apply Fenchel–Moreau to `conj_dirDeriv`. -/
theorem clFn_dirDeriv [IsCompatiblePairing B] (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    clFn (dirDeriv f x) = supportFn B.flip (subgradient B f x) := by
  rw [supportFn_eq_conj_indicatorFn, ← conj_dirDeriv ht hb]
  exact (biconj_eq_clFn (convexFn_dirDeriv hf ht hb)).symm

end FenchelMoreau

end Tdaf.ConvexAnalysis
