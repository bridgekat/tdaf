/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Conjugate

/-!
# Subdifferentials of saddle-functions

A saddle-function is concave in one variable and convex in the other, so it has *two* one-sided
subdifferentials: a superdifferential in the concave variable and a subdifferential in the convex
one. Their product is the subdifferential `∂K` of the saddle-function, and this module develops it
together with the two facts that make it useful: `(u*, x*) ∈ ∂K (u, x)` says exactly that `(u, x)`
is a *saddle-point* of `K` tilted by the linear function `⟨·, u*⟩ + ⟨·, x*⟩`, and, for a closed
proper `K`, `∂K` is nonempty throughout the relative interior of the effective domain and empty
outside it.

## Main definitions

* `concaveSubgradient B g x` — the superdifferential of a concave `g`, i.e. the `y` for which
  `g z ≤ g x + ⟨z - x, y⟩` for every `z`. The sign dictionary to `subgradient` is
  `mem_concaveSubgradient_iff_neg_mem_subgradient_neg`.
* `saddleSubgradient Bu Bx K p` — Rockafellar's `∂K (u, x) = ∂₁K (u, x) × ∂₂K (u, x)`.
* `domSaddleSubgradient Bu Bx K` — the set where `∂K` is nonempty.
* `saddleTilt Bu Bx K q` — `K - ⟨·, u*⟩ - ⟨·, x*⟩` for `q = (u*, x*)`.

## Main results

* `mem_concaveSubgradient_iff_concaveConj_eq` — **Theorem 23.5**, (a) ⟺ (b), concave side.
* `concaveSubgradient_nonempty_of_mem_relint_domConcave` — **Theorem 23.4**, concave side.
* `mem_saddleSubgradient_iff_isSaddlePoint` — **Theorem 37.4**, first sentence, with no
  hypotheses at all.
* `domSaddleSubgradient_subset_domSaddle`, `kernelSet_subset_domSaddleSubgradient`,
  `kernelSet_subset_domSaddleSubgradient_subset_domSaddle` — **Theorem 37.4**, second sentence:
  `ri (dom K) ⊆ dom ∂K ⊆ dom K`. The right-hand inclusion needs only properness.
* `sub_coe_le_sub_coe_iff_le_add`, `sub_coe_le_sub_coe_iff_add_le` — the two `EReal`
  cancellations the tilt runs on; relocation candidates for `Tdaf/Order/EReal.lean`.

## Design notes

**The two variables are paired with two different spaces.** `K : U × X → EReal` is paired against
`V` in the concave variable and against `Y` in the convex one, so `∂K (u, x) ⊆ V × Y`. In
Rockafellar's `Rᵐ × Rⁿ` all four spaces coincide; here keeping them apart is what makes
`∂K*` land back in `U × Y`, which is the symmetry Theorem 37.5 is about.

**The superdifferential is a definition, not a negation.** Writing `∂₁K (u, x)` as
`-(∂(-K (·, x)) u)` would make every statement about it carry a `neg_neg`, and set negation needs
`open Pointwise`. `concaveSubgradient` is the same three-line definition as `subgradient` with the
inequality reversed, and the dictionary is proved once
(`mem_concaveSubgradient_iff_neg_mem_subgradient_neg`).

**The tilt subtracts one real, not two.** `K p - ⟨p.1, u*⟩ - ⟨p.2, x*⟩` and
`K p - (⟨p.1, u*⟩ + ⟨p.2, x*⟩)` are equal, but only the second keeps all the `EReal` arithmetic
inside a single real coercion, where `sub_coe_le_sub_coe_iff_le_add` applies with no side
condition.

## What is not here

**Corollary 37.4.1** (equivalent saddle-functions have the same subdifferential). Its proof
needs `cl₁` and `cl₂` to commute with the tilt, i.e. `cl (f + ℓ) = cl f + ℓ` for a *continuous*
linear `ℓ`, which the backbone has only in the form `clFn_add`, under properness hypotheses on
both summands.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35 and §37.
-/

namespace Tdaf.ConvexAnalysis

/-! ### Cancelling real coercions across an `EReal` inequality -/

section ERealSub

/-- Moving a real subtrahend across an `EReal` inequality: `z - c ≤ w - d ↔ z ≤ w + e` whenever
`c - d = e`. There is no side condition, because `c` and `d` are finite.

The difference is passed as a *parameter with its defining equation* rather than written out, so
that the caller supplies whatever form of `c - d` it has. The whole content is the identity
`(w - d) + c = w + e`, which needs a three-case induction; the inequality itself is then one
application of `AddLECancellable`. A relocation candidate for `Tdaf/Order/EReal.lean`. -/
theorem sub_coe_le_sub_coe_iff_le_add {z w : EReal} {c d e : ℝ} (he : c - d = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z ≤ w + (e : EReal) := by
  have hw : w - (d : EReal) + (c : EReal) = w + (e : EReal) := by
    induction w with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← _root_.EReal.coe_sub, ← _root_.EReal.coe_add, ← _root_.EReal.coe_add,
        _root_.EReal.coe_eq_coe_iff]
      linarith
  rw [← (_root_.EReal.addLECancellable_coe c).add_le_add_iff_right,
    _root_.EReal.sub_add_cancel, hw]

/-- The companion of `sub_coe_le_sub_coe_iff_le_add` with the real moved to the *left*:
`z - c ≤ w - d ↔ z + e ≤ w` whenever `d - c = e`. A relocation candidate for
`Tdaf/Order/EReal.lean`. -/
theorem sub_coe_le_sub_coe_iff_add_le {z w : EReal} {c d e : ℝ} (he : d - c = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z + (e : EReal) ≤ w := by
  have hz : z - (c : EReal) + (d : EReal) = z + (e : EReal) := by
    induction z with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← _root_.EReal.coe_sub, ← _root_.EReal.coe_add, ← _root_.EReal.coe_add,
        _root_.EReal.coe_eq_coe_iff]
      linarith
  rw [← (_root_.EReal.addLECancellable_coe d).add_le_add_iff_right,
    _root_.EReal.sub_add_cancel, hz]

/-- Subtracting a real number does not move the effective domain: `z - c < ⊤ ↔ z < ⊤`. -/
theorem sub_coe_lt_top_iff {z : EReal} {c : ℝ} : z - (c : EReal) < ⊤ ↔ z < ⊤ := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (_root_.EReal.coe_lt_top r)
    rw [← _root_.EReal.coe_sub]
    exact _root_.EReal.coe_lt_top _

/-- Subtracting a real number does not move the concave effective domain:
`⊥ < z - c ↔ ⊥ < z`. -/
theorem bot_lt_sub_coe_iff {z : EReal} {c : ℝ} : ⊥ < z - (c : EReal) ↔ ⊥ < z := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (_root_.EReal.bot_lt_coe r)
    rw [← _root_.EReal.coe_sub]
    exact _root_.EReal.bot_lt_coe _

end ERealSub

/-! ### Supergradients: the subdifferential of a concave function -/

section ConcaveSubgradient

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **superdifferential** of a concave function `g` at `x` with respect to the pairing `B`:
the set of `y : F` satisfying the reversed subgradient inequality

`g z ≤ g x + ⟨z - x, y⟩` for every `z`.

This is `subgradient` with the inequality turned around, and it is the object Rockafellar's §35
calls `∂` for a concave function. -/
def concaveSubgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) : Set F :=
  {y | ∀ z, g z ≤ g x + ((B (z - x) y : ℝ) : EReal)}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : E → EReal} {x : E} {y : F}

@[simp] theorem mem_concaveSubgradient :
    y ∈ concaveSubgradient B g x ↔ ∀ z, g z ≤ g x + ((B (z - x) y : ℝ) : EReal) := Iff.rfl

/-- **The sign dictionary**: `y` is a supergradient of `g` at `x` exactly when `-y` is a
subgradient of `-g` there. -/
theorem mem_concaveSubgradient_iff_neg_mem_subgradient_neg :
    y ∈ concaveSubgradient B g x ↔ -y ∈ subgradient B (fun z => -(g z)) x := by
  refine forall_congr' fun z => ?_
  have hcoe : ((B (z - x) (-y) : ℝ) : EReal) = -((B (z - x) y : ℝ) : EReal) := by
    rw [map_neg, _root_.EReal.coe_neg]
  have hsum : -(g x) + -((B (z - x) y : ℝ) : EReal)
      = -(g x + ((B (z - x) y : ℝ) : EReal)) := by
    have h : -(g x + ((B (z - x) y : ℝ) : EReal)) = -(g x) + -((B (z - x) y : ℝ) : EReal) :=
      _root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _)) (.inr (_root_.EReal.coe_ne_bot _))
    exact h.symm
  change _ ↔ -(g x) + ((B (z - x) (-y) : ℝ) : EReal) ≤ -(g z)
  rw [hcoe, hsum, _root_.EReal.neg_le_neg_iff]

/-- `mem_concaveSubgradient_iff_neg_mem_subgradient_neg` with the negation on the other side. -/
theorem neg_mem_concaveSubgradient_iff :
    -y ∈ concaveSubgradient B g x ↔ y ∈ subgradient B (fun z => -(g z)) x := by
  rw [mem_concaveSubgradient_iff_neg_mem_subgradient_neg, neg_neg]

/-- **Rockafellar, Theorem 23.5**, (a) ⟺ (b) on the concave side: `y ∈ ∂g x` exactly when the
infimum of `⟨·, y⟩ - g` over the space is attained at `x`. Unconditional. -/
theorem mem_concaveSubgradient_iff_forall_le_sub :
    y ∈ concaveSubgradient B g x ↔
      ∀ z, ((B x y : ℝ) : EReal) - g x ≤ ((B z y : ℝ) : EReal) - g z := by
  refine forall_congr' fun z => ?_
  rw [Tdaf.EReal.le_coe_sub_comm, Tdaf.EReal.coe_sub_coe_sub, map_sub, LinearMap.sub_apply,
    add_comm (g x)]

/-- **Rockafellar, Theorem 23.5**, (a) ⟺ (c) on the concave side: the infimum in (b) *is*
`g* y`. Unconditional. -/
theorem mem_concaveSubgradient_iff_le_concaveConj :
    y ∈ concaveSubgradient B g x ↔ ((B x y : ℝ) : EReal) - g x ≤ concaveConj B g y := by
  rw [mem_concaveSubgradient_iff_forall_le_sub, concaveConj_apply, le_iInf_iff]

/-- **Rockafellar, Theorem 23.5**, (a) ⟺ (b) on the concave side, as an equation:
`g* y = ⟨x, y⟩ - g x`. Unconditional. -/
theorem mem_concaveSubgradient_iff_concaveConj_eq :
    y ∈ concaveSubgradient B g x ↔ concaveConj B g y = ((B x y : ℝ) : EReal) - g x :=
  ⟨fun h => le_antisymm (concaveConj_le_sub B g x y)
      (mem_concaveSubgradient_iff_le_concaveConj.1 h),
    fun h => mem_concaveSubgradient_iff_le_concaveConj.2 h.ge⟩

/-- The superdifferential is convex, with no hypothesis on `g`. -/
theorem convex_concaveSubgradient : Convex ℝ (concaveSubgradient B g x) := by
  have h : Convex ℝ (subgradient B (fun z => -(g z)) x) :=
    convex_subgradient B (fun z => -(g z)) x
  intro y₁ h₁ y₂ h₂ a b ha hb hab
  rw [mem_concaveSubgradient_iff_neg_mem_subgradient_neg] at h₁ h₂ ⊢
  have hneg : -(a • y₁ + b • y₂) = a • (-y₁) + b • (-y₂) := by
    rw [neg_add, smul_neg, smul_neg]
  rw [hneg]
  exact h h₁ h₂ ha hb hab

end ConcaveSubgradient

/-! ### Theorem 23.4 on the concave side -/

section ConcaveExistence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : E → EReal} {x : E}

/-- **Rockafellar, Theorem 23.4** on the concave side: a proper concave function has a
supergradient at every relative interior point of its effective domain. -/
theorem concaveSubgradient_nonempty_of_mem_relint_domConcave [IsCompatiblePairing B]
    (hg : ConcaveFn g) (hp : Proper fun z => -(g z)) (hx : x ∈ ri (domConcave g)) :
    (concaveSubgradient B g x).Nonempty := by
  have hconv : ConvexFn fun z => -(g z) := concaveFn_iff_convexFn_neg.1 hg
  have hdom : dom (fun z => -(g z)) = domConcave g := (domConcave_eq_dom_neg g).symm
  have hx' : x ∈ ri (dom fun z => -(g z)) := by rw [hdom]; exact hx
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hconv hp hx'
  exact ⟨-y, neg_mem_concaveSubgradient_iff.2 hy⟩

end ConcaveExistence

/-! ### The subdifferential of a saddle-function -/

section SaddleSubgradient

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **subdifferential of a saddle-function** (Rockafellar, §35):
`∂K (u, x) = ∂₁K (u, x) × ∂₂K (u, x)`, the supergradients of the concave slice through `x` paired
with the subgradients of the convex slice through `u`. -/
def saddleSubgradient (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × X → EReal)
    (p : U × X) : Set (V × Y) :=
  concaveSubgradient Bu (fun u => K (u, p.2)) p.1 ×ˢ subgradient Bx (fun x => K (p.1, x)) p.2

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X}
  {q : V × Y}

@[simp] theorem mem_saddleSubgradient :
    q ∈ saddleSubgradient Bu Bx K p ↔
      q.1 ∈ concaveSubgradient Bu (fun u => K (u, p.2)) p.1 ∧
        q.2 ∈ subgradient Bx (fun x => K (p.1, x)) p.2 := Iff.rfl

/-- `∂K (u, x)` is a convex set, with no hypothesis on `K`; being a product, it is even a convex
*product* set, which is what Corollary 37.5.3 turns into a statement about saddle-points. -/
theorem convex_saddleSubgradient : Convex ℝ (saddleSubgradient Bu Bx K p) :=
  Convex.prod convex_concaveSubgradient (convex_subgradient Bx (fun x => K (p.1, x)) p.2)

/-- The set where the subdifferential of a saddle-function is nonempty: Rockafellar's
`dom ∂K`. -/
def domSaddleSubgradient (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : Set (U × X) :=
  {p | (saddleSubgradient Bu Bx K p).Nonempty}

@[simp] theorem mem_domSaddleSubgradient :
    p ∈ domSaddleSubgradient Bu Bx K ↔ (saddleSubgradient Bu Bx K p).Nonempty := Iff.rfl

end SaddleSubgradient

/-! ### Tilting a saddle-function by a linear function -/

section SaddleTilt

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Rockafellar's `K - ⟨·, u*⟩ - ⟨·, x*⟩`: the saddle-function `K` tilted by the linear function
determined by `q = (u*, x*)`. The two inner products are combined into one real coercion, which is
what keeps the `EReal` arithmetic side-condition-free. -/
noncomputable def saddleTilt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) : U × X → EReal :=
  fun p => K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal)

theorem saddleTilt_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) (p : U × X) :
    saddleTilt Bu Bx K q p = K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal) := rfl

/-- Tilting by the origin does nothing. -/
@[simp] theorem saddleTilt_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : saddleTilt Bu Bx K 0 = K := by
  funext p
  rw [saddleTilt_apply]
  norm_num

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {q : V × Y}

/-- A tilt does not move either effective domain. -/
@[simp] theorem dom₁_saddleTilt : dom₁ (saddleTilt Bu Bx K q) = dom₁ K := by
  ext u
  exact forall_congr' fun x => bot_lt_sub_coe_iff

/-- A tilt does not move either effective domain. -/
@[simp] theorem dom₂_saddleTilt : dom₂ (saddleTilt Bu Bx K q) = dom₂ K := by
  ext x
  exact forall_congr' fun u => sub_coe_lt_top_iff

theorem ProperSaddleFn.saddleTilt (hp : ProperSaddleFn K) :
    ProperSaddleFn (Tdaf.ConvexAnalysis.saddleTilt Bu Bx K q) :=
  ⟨by rw [dom₁_saddleTilt]; exact hp.dom₁_nonempty,
    by rw [dom₂_saddleTilt]; exact hp.dom₂_nonempty⟩

end SaddleTilt

/-! ### Theorem 37.4: subgradients are saddle-points of the tilted function -/

section Thm374

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X} {q : V × Y}

/-- **Rockafellar, Theorem 37.4**, first sentence: `(u*, x*) ∈ ∂K (u, x)` exactly when `(u, x)` is
a saddle-point of `K - ⟨·, u*⟩ - ⟨·, x*⟩`. There are **no hypotheses at all** — not concavity,
not convexity, not properness: both sides are the same pair of inequalities, one in each variable,
with a real number moved across.

Proof idea: the tilt subtracts `⟨u, u*⟩ + ⟨x, x*⟩` from `K (u, x)`; in the first variable the
`⟨x, x*⟩` term is common to both sides of the saddle-point inequality and cancels, leaving the
supergradient inequality for the slice `K (·, x)`, and symmetrically in the second. -/
theorem mem_saddleSubgradient_iff_isSaddlePoint :
    q ∈ saddleSubgradient Bu Bx K p ↔ IsSaddlePoint (saddleTilt Bu Bx K q) p := by
  have h₁ : ∀ u : U, ((Bu u q.1 + Bx p.2 q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bu (u - p.1) q.1 := by
    intro u
    rw [map_sub, LinearMap.sub_apply]
    ring
  have h₂ : ∀ x : X, ((Bu p.1 q.1 + Bx x q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bx (x - p.2) q.2 := by
    intro x
    rw [map_sub, LinearMap.sub_apply]
    ring
  have hfst : ∀ u : U,
      saddleTilt Bu Bx K q (u, p.2) ≤ saddleTilt Bu Bx K q p ↔
        K (u, p.2) ≤ K p + ((Bu (u - p.1) q.1 : ℝ) : EReal) := by
    intro u
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_le_add (h₁ u)]
  have hsnd : ∀ x : X,
      saddleTilt Bu Bx K q p ≤ saddleTilt Bu Bx K q (p.1, x) ↔
        K p + ((Bx (x - p.2) q.2 : ℝ) : EReal) ≤ K (p.1, x) := by
    intro x
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_add_le (h₂ x)]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).2 (ha u), fun x => (hsnd x).2 (hb x)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).1 (ha u), fun x => (hsnd x).1 (hb x)⟩

end Thm374

/-! ### Theorem 37.4: the effective domain of the subdifferential -/

section Thm374Dom

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- **Rockafellar, Theorem 37.4**, right-hand inclusion: `dom ∂K ⊆ dom K`, for a *proper*
saddle-function — closedness is not needed.

Proof idea: a subgradient pair at `p` makes `p` a saddle-point of the tilt, the tilt is again
proper (`dom₁_saddleTilt`, `dom₂_saddleTilt`), and the saddle-points of a proper saddle-function
lie in its effective domain (Corollary 36.3.1). -/
theorem domSaddleSubgradient_subset_domSaddle (hp : ProperSaddleFn K) :
    domSaddleSubgradient Bu Bx K ⊆ domSaddle K := by
  rintro p ⟨q, hq⟩
  have hsp : IsSaddlePoint (saddleTilt Bu Bx K q) p :=
    mem_saddleSubgradient_iff_isSaddlePoint.1 hq
  have hprop : ProperSaddleFn (saddleTilt Bu Bx K q) := ProperSaddleFn.saddleTilt hp
  have h := IsSaddlePoint.mem_domSaddle hprop hsp
  rw [mem_domSaddle, dom₁_saddleTilt, dom₂_saddleTilt] at h
  exact h

end Thm374Dom

section Thm374Relint

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- **Rockafellar, Theorem 37.4**, left-hand inclusion: `ri (dom K) ⊆ dom ∂K`.

Proof idea: over `ri (dom₁ K)` the convex slice `K (u, ·)` is proper with effective domain exactly
`dom₂ K` (Theorem 34.3), so a relative interior point of `dom₂ K` is a relative interior point of
its effective domain and Theorem 23.4 produces a subgradient. The concave half is the same
statement for `saddleSwap K`, whose slices are the negated concave slices of `K`. -/
theorem kernelSet_subset_domSaddleSubgradient [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (hK : ConcaveConvexFn K) (hs : SaddleStructure K) :
    kernelSet K ⊆ domSaddleSubgradient Bu Bx K := by
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  have hudom : u ∈ dom₁ K := intrinsicInterior_subset hu
  have hxdom : x ∈ dom₂ K := intrinsicInterior_subset hx
  have hxr : x ∈ ri (dom fun x' => K (u, x')) := by
    rw [hs.1.dom_slice u hu]
    exact hx
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := Bx) (hK.convex_snd u)
    (hs.1.proper_slice u hudom) hxr
  have hswapdom : x ∈ dom₁ (saddleSwap K) := by rw [dom₁_saddleSwap]; exact hxdom
  have hswapri : x ∈ ri (dom₁ (saddleSwap K)) := by rw [dom₁_saddleSwap]; exact hx
  have hdomeq : (dom fun u' => -(K (u', x))) = dom₁ K := by
    have h := hs.2.dom_slice x hswapri
    rw [dom₂_saddleSwap] at h
    exact h
  have hur : u ∈ ri (domConcave fun u' => K (u', x)) := by
    rw [domConcave_eq_dom_neg, hdomeq]
    exact hu
  have hpr : Proper fun u' => -(K (u', x)) := hs.2.proper_slice x hswapdom
  obtain ⟨v, hv⟩ := concaveSubgradient_nonempty_of_mem_relint_domConcave (B := Bu)
    (hK.concave_fst x) hpr hur
  exact ⟨(v, y), hv, hy⟩

/-- **Rockafellar, Theorem 37.4**, second sentence, in one statement:
`ri (dom K) ⊆ dom ∂K ⊆ dom K` for a closed proper saddle-function. -/
theorem kernelSet_subset_domSaddleSubgradient_subset_domSaddle [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bx] (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) :
    kernelSet K ⊆ domSaddleSubgradient Bu Bx K ∧ domSaddleSubgradient Bu Bx K ⊆ domSaddle K :=
  ⟨kernelSet_subset_domSaddleSubgradient hK ((closedSaddleFn_iff_saddleStructure hK hp).1 hcl),
    domSaddleSubgradient_subset_domSaddle hp⟩

end Thm374Relint

end Tdaf.ConvexAnalysis
