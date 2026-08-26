/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Homogeneous

/-!
# Support functions

Rockafellar's §13, over a dual pair `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. The support function of a set `s ⊆ E`
is `δ*(y | s) = sup {⟨x, y⟩ | x ∈ s}`, and this section is short for one reason: **support
functions are conjugates of indicators** (`supportFn_eq_conj_indicatorFn`), so every property
of `δ*(· | s)` is inherited from `Tdaf/Analysis/Convex/Duality/Conjugate.lean` instead of being
proved again.

## Main definitions

* `supportFn B s` — the support function `δ*(· | s)`.
* `supportSet B f` — the set `{y | ∀ x, ⟨x, y⟩ ≤ f x}` of which `f` is the support function
  when `f` is closed, proper, positively homogeneous and convex. It inverts the correspondence.
* `supportEquiv` — **Theorem 13.2** as a bijection: the nonempty closed convex subsets of `E`
  correspond to the closed proper positively homogeneous convex functions on `F`.

## Main results

* `supportFn_eq_conj_indicatorFn` — `δ*(· | s) = (δ(· | s))*`. Everything below is a citation
  of this together with a result from `Conjugate.lean`.
* `mem_closure_convexHull_iff_le_supportFn` — **Theorem 13.1**: `x ∈ cl (conv s)` if and only
  if `⟨x, y⟩ ≤ δ*(y | s)` for every `y`.
* `conj_supportFn` — **Theorem 13.2**, first half: the indicator function and the support
  function of a closed convex set are conjugate to each other.
* `exists_supportFn_iff`, `supportEquiv` — **Theorem 13.2**, the characterisation: the
  support functions of the nonempty convex sets *are* the closed proper positively homogeneous
  convex functions.
* `clFn_eq_supportFn_of_posHomogeneous` — **Corollary 13.2.1**: the closure of a positively
  homogeneous convex function is a support function.
* `supportSet_clFn` — its immediate consequence: taking the closure of a positively homogeneous
  function does not change the set it supports. The companion "the closure is again positively
  homogeneous" is `posHomogeneous_clFn` in `Convex/Closure.lean`, where it needs neither a pairing
  nor convexity.
* `supportFn_le_zero_iff`, `zero_lt_supportFn_iff` — `supportFn_le_coe_iff` at the level `0`,
  which is the level a polar cone is cut out at.
* `exists_supportFn_finite_iff` — **Corollary 13.2.2**: bounded ⟺ finite.
* `conj_eq_indicatorFn_of_posHomogeneous` — the engine of both, and of §14: the conjugate of a
  positively homogeneous function is an *indicator* function.
* `supportFn_singleton`, `supportFn_union`, `supportFn_convexHull`,
  `supportFn_closure`, `supportFn_smul`, `supportFn_add` — the support functions of
  the basic constructions, which §16 consumes.

## Design notes

**The support function lives on the other side of the pairing.** `supportFn B s : F → EReal` for
`s : Set E`. Rockafellar identifies `Rⁿ` with its dual and never has to say this; here the two
spaces are genuinely different, and a statement such as Theorem 13.2 — which asks both that
`g : F → EReal` be closed and that the set it supports be closed in `E` — needs a topology and a
compatible pairing on *both* sides. That is why the characterisation theorems ask for a class on
each side, exactly as `conjEquiv` does — `[IsCompatiblePairing B.flip]` throughout, and on the
`E` side either `[IsCompatiblePairing B]` or, where only closedness of the supported set is at
stake, the weaker `[IsContinuousPairing B]`.

**Positive homogeneity is what an indicator conjugates to, and conversely.**
`conj_eq_indicatorFn_of_posHomogeneous` is proved with no topology at all: reindexing the
supremum defining `f*` along `x ↦ a • x` shows `f*(y) = a * f*(y)` for every `a > 0`, so `f*(y)` is
`0`, `⊤` or `⊥` (`Tdaf.EReal.eq_zero_or_eq_top_or_eq_bot`), and `⊥` is excluded as soon as `f` is
not identically `⊤`. This replaces Rockafellar's computation with `(λf)* = f*λ`, and it is the
reason §13 and §14 need no separation theory beyond what §12 already used.

**Corollary 13.2.2 needs closedness — a `D0` correction.** Rockafellar deduces that a *finite*
positively homogeneous convex function is a support function from Corollary 7.4.2, "a finite convex
function on `Rⁿ` is closed". That is false in infinite dimensions: a discontinuous linear
functional is finite, convex and positively homogeneous, and is not closed, so it is not the
support function of anything. `exists_supportFn_finite_iff` therefore carries `ClosedFn`, and
reads "bounded" as "`⟨·, y⟩` is bounded above on the set, for each `y`" — which is Rockafellar's
own proof of the corollary ("a subset of `Rⁿ` is bounded if and only if every linear function is
bounded above on it").

## Deferred

**Theorems 13.3, 13.4 and 13.5 need recession functions** (`f 0⁺`, Rockafellar §8 and §13), which
live in `Tdaf/Analysis/Convex/Recession/Function.lean` and are not imported here. They are
deliberately *not* stated: `δ*(· | dom f) = (f*) 0⁺` (Theorem 13.3), Corollary 13.3.1, the lineality
space of `f*` (Theorem 13.4, finite-dimensional) and the level sets of the positively homogeneous
function generated by `f` (Theorem 13.5) all quantify over an object this file cannot name.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 (Theorem 13.1,
  Theorem 13.2, Corollary 13.1.1, Corollary 13.2.1, Corollary 13.2.2).
-/

open Set Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### The support function -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **support function** `δ*(· | s)` of a set `s ⊆ E`, with respect to the pairing `B`:
`δ*(y | s) = sup {⟨x, y⟩ | x ∈ s}`.

Rockafellar §13: the support function describes all the closed half-spaces containing `s`, since
`s ⊆ {x | ⟨x, y⟩ ≤ c}` if and only if `δ*(y | s) ≤ c` (`supportFn_le_coe_iff`). The `δ*`
notation is justified by `supportFn_eq_conj_indicatorFn`: it really is the conjugate of the
indicator function. -/
noncomputable def supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : F → EReal :=
  fun y => ⨆ x ∈ s, ((B x y : ℝ) : EReal)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t : Set E} {x : E} {y : F}

/-- The defining formula for the support function. -/
theorem supportFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) (y : F) :
    supportFn B s y = ⨆ x ∈ s, ((B x y : ℝ) : EReal) := rfl

/-- **Support functions are conjugates of indicators.** This is why §13 is short: every property of
`δ*(· | s)` below is a property of a conjugate, cited from `Conjugate.lean`. -/
theorem supportFn_eq_conj_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B s = conj B (indicatorFn s) := by
  funext y
  rw [conj_apply]
  refine iSup_congr fun x => ?_
  by_cases hx : x ∈ s
  · rw [iSup_pos hx, indicatorFn_of_mem hx, sub_zero]
  · rw [iSup_neg hx, indicatorFn_of_notMem hx, _root_.EReal.sub_top]

/-- Every value of the pairing on `s` is a lower bound for the support function. -/
theorem le_supportFn (hx : x ∈ s) (y : F) : ((B x y : ℝ) : EReal) ≤ supportFn B s y :=
  le_iSup₂ (f := fun x (_ : x ∈ s) => ((B x y : ℝ) : EReal)) x hx

/-- The defining universal property of the supremum. -/
theorem supportFn_le_iff {c : EReal} :
    supportFn B s y ≤ c ↔ ∀ x ∈ s, ((B x y : ℝ) : EReal) ≤ c := iSup₂_le_iff

/-- **The closed half-spaces containing `s`** (Rockafellar §13): `s ⊆ {x | ⟨x, y⟩ ≤ c}` if and only
if `c ≥ δ*(y | s)`. -/
theorem supportFn_le_coe_iff {c : ℝ} :
    supportFn B s y ≤ (c : EReal) ↔ ∀ x ∈ s, B x y ≤ c := by
  rw [supportFn_le_iff]
  exact forall₂_congr fun _ _ => _root_.EReal.coe_le_coe_iff

/-- `δ*(y | s) ≤ 0` says that the pairing with `y` is nowhere positive on `s` — the level `0` of
`supportFn_le_coe_iff`, which is where a polar cone is cut out. -/
theorem supportFn_le_zero_iff : supportFn B s y ≤ 0 ↔ ∀ x ∈ s, B x y ≤ 0 := by
  rw [← _root_.EReal.coe_zero, supportFn_le_coe_iff]

/-- `0 < δ*(y | s)` says that the pairing with `y` is positive somewhere on `s`. -/
theorem zero_lt_supportFn_iff : 0 < supportFn B s y ↔ ∃ x ∈ s, 0 < B x y := by
  rw [supportFn_apply, ← _root_.EReal.coe_zero]
  simp only [lt_iSup_iff, exists_prop, _root_.EReal.coe_lt_coe_iff]

/-- The support function is monotone in the set. -/
theorem supportFn_mono (h : s ⊆ t) : supportFn B s ≤ supportFn B t :=
  fun _ => iSup₂_le fun _ hx => le_supportFn (h hx) _

/-- The support function of the empty set is the constant `-∞`. -/
@[simp] theorem supportFn_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    supportFn B (∅ : Set E) = fun _ => (⊥ : EReal) := by
  funext y; simp [supportFn]

/-- The support function of a singleton is the corresponding linear function. -/
@[simp] theorem supportFn_singleton (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) :
    supportFn B {x} = fun y => ((B x y : ℝ) : EReal) := by
  funext y; simp [supportFn]

/-- The support function of a union is the pointwise supremum. -/
theorem supportFn_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s ∪ t) = supportFn B s ⊔ supportFn B t := by
  funext y
  rw [Pi.sup_apply, supportFn_apply, supportFn_apply, supportFn_apply, iSup_union]

/-- The support function of a union of a family is the pointwise supremum. -/
theorem supportFn_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    supportFn B (⋃ i, u i) = fun y => ⨆ i, supportFn B (u i) y := by
  funext y
  rw [supportFn_apply, iSup_iUnion]
  rfl

/-- The support function of a nonempty set never takes the value `-∞`. -/
theorem supportFn_ne_bot (hs : s.Nonempty) (y : F) : supportFn B s y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hs
  exact fun hc => absurd (hc ▸ le_supportFn (B := B) hx y) (by simp)

/-- A support function vanishes at the origin of the dual space, provided the set is nonempty. -/
@[simp] theorem supportFn_zero (hs : s.Nonempty) : supportFn B s 0 = 0 := by
  obtain ⟨x, hx⟩ := hs
  refine le_antisymm (iSup₂_le fun z _ => ?_) ?_
  · rw [map_zero]; rfl
  · have h := le_supportFn (B := B) hx (0 : F)
    rwa [map_zero, _root_.EReal.coe_zero] at h

/-- The support function of a nonempty set is proper. -/
theorem proper_supportFn (hs : s.Nonempty) : Proper (supportFn B s) :=
  ⟨⟨0, by rw [mem_dom, supportFn_zero hs]; exact lt_top_iff_ne_top.2 (by simp)⟩,
    supportFn_ne_bot hs⟩

/-- **The effective domain of a support function is the barrier cone** of `s` (Rockafellar §13):
the directions in which the pairing is bounded above on `s`. Theorem 14.2 and Corollary 14.2.1 are
statements about this set; they need recession cones and are deferred. -/
theorem dom_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    dom (supportFn B s) = {y : F | ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c} := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨c, hc, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (hy : supportFn B s y < ⊤)
    exact ⟨c, supportFn_le_coe_iff.1 hc.le⟩
  · obtain ⟨c, hc⟩ := hy
    exact lt_of_le_of_lt (supportFn_le_coe_iff.2 hc) (_root_.EReal.coe_lt_top c)

/-- The support function is finite at `y` exactly when the pairing is bounded above on `s` in the
direction `y`. -/
theorem supportFn_lt_top_iff : supportFn B s y < ⊤ ↔ ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c := by
  rw [← mem_dom, dom_supportFn]
  exact Iff.rfl

/-! ### Convexity and positive homogeneity

Both are inherited: convexity from `conj`, and homogeneity by reindexing the supremum. -/

/-- **The support function of any set is convex** — it is a conjugate. -/
theorem convexFn_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : ConvexFn (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact convexFn_conj B _

/-- **The support function of any set is positively homogeneous.** -/
theorem posHomogeneous_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    PosHomogeneous (supportFn B s) := by
  intro a ha y
  simp only [supportFn]
  rw [Tdaf.EReal.coe_mul_iSup ha]
  refine iSup_congr fun x => ?_
  rw [Tdaf.EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, smul_eq_mul, ← Tdaf.EReal.coe_mul_coe]

/-- Support functions are **subadditive in the dual variable**: this is Rockafellar's Theorem 4.7
(`PosHomogeneous.convexFn_iff_subadditive`) applied to `posHomogeneous_supportFn`, and it
is the inequality displayed after Theorem 13.2. -/
theorem supportFn_add_le (hs : s.Nonempty) (y₁ y₂ : F) :
    supportFn B s (y₁ + y₂) ≤ supportFn B s y₁ + supportFn B s y₂ :=
  ((posHomogeneous_supportFn B s).convexFn_iff_subadditive (supportFn_ne_bot hs)).1
    (convexFn_supportFn B s) y₁ y₂

/-- The set `{x | ⟨x, y⟩ ≤ M}` is convex: it is a level set of an affine function of the pairing. -/
theorem convex_setOf_pairing_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (M : EReal) :
    Convex ℝ {x : E | ((B x y : ℝ) : EReal) ≤ M} := by
  have h := (convexFn_affineFn (B := B) y 0).convex_le M
  simpa only [affineFn_apply, _root_.EReal.coe_zero, sub_zero] using h

/-- **The support function does not see the convex hull** (Rockafellar §13). -/
theorem supportFn_convexHull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B (convexHull ℝ s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono (subset_convexHull ℝ s) y)
  exact convexHull_min (fun z hz => le_supportFn hz y)
    (convex_setOf_pairing_le B y (supportFn B s y)) hx

/-- **The support function of a positive multiple of a set** is the corresponding multiple of the
support function. -/
theorem supportFn_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 < a) (s : Set E) (y : F) :
    supportFn B (a • s) y = (a : EReal) * supportFn B s y := by
  rw [supportFn_apply, supportFn_apply, Tdaf.EReal.coe_mul_iSup ha, ← Set.image_smul, iSup_image]
  refine iSup_congr fun z => ?_
  rw [Tdaf.EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← Tdaf.EReal.coe_mul_coe]

/-- **The support function of a sum of sets is the sum of the support functions**
(Rockafellar §13). The corresponding statement for the conjugate of a sum of *functions* is
Corollary 16.4.1 and does need a constraint qualification; for sets the identity is unconditional,
because the two suprema never interact through an `∞ - ∞`. -/
theorem supportFn_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s + t) = supportFn B s + supportFn B t := by
  funext y
  calc supportFn B (s + t) y
      = ⨆ a ∈ s, ⨆ b ∈ t, ((B (a + b) y : ℝ) : EReal) := by
        rw [supportFn_apply, ← Set.image2_add, iSup_image2]
    _ = ⨆ a ∈ s, ⨆ b ∈ t, (((B b y : ℝ) : EReal) + ((B a y : ℝ) : EReal)) := by
        refine iSup_congr fun a => iSup_congr fun _ => iSup_congr fun b => iSup_congr fun _ => ?_
        rw [map_add, LinearMap.add_apply, ← _root_.EReal.coe_add, add_comm]
    _ = ⨆ a ∈ s, (((B a y : ℝ) : EReal) + supportFn B t y) := by
        refine iSup_congr fun a => iSup_congr fun _ => ?_
        rw [supportFn_apply, ← Tdaf.EReal.biSup_add_coe, add_comm]
    _ = supportFn B s y + supportFn B t y := by
        rw [← Tdaf.EReal.biSup_add_of_ne_bot (u := fun a => ((B a y : ℝ) : EReal))
          fun a _ => _root_.EReal.coe_ne_bot _]
        rfl

end Defs

/-! ### Conjugates of positively homogeneous functions

This is the mechanism behind everything that follows, and it needs no topology: reindexing the
supremum that defines `f*` along `x ↦ a • x` shows that `f*(y)` is fixed by multiplication by every
positive scalar. -/

section PosHom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The set `{y | ∀ x, ⟨x, y⟩ ≤ f x}` of Rockafellar's Corollary 13.2.1. When `f` is closed, proper,
convex and positively homogeneous this is the set whose support function is `f`
(`supportFn_supportSet`); in general it is the effective domain of `f*`, viewed as an
indicator. -/
def supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set F :=
  {y | ∀ x, ((B x y : ℝ) : EReal) ≤ f x}

/-- Membership in `supportSet`, unfolded. -/
@[simp] theorem mem_supportSet {y : F} :
    y ∈ supportSet B f ↔ ∀ x, ((B x y : ℝ) : EReal) ≤ f x := Iff.rfl

/-- Membership in `supportSet` is exactly nonpositivity of the conjugate. -/
theorem supportSet_eq_setOf_conj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    supportSet B f = {y | conj B f y ≤ 0} := by
  ext y
  change (∀ x, ((B x y : ℝ) : EReal) ≤ f x) ↔ conj B f y ≤ 0
  rw [show ((0 : EReal)) = ((0 : ℝ) : EReal) from _root_.EReal.coe_zero.symm, conj_le_coe_iff,
    Pi.le_def]
  exact forall_congr' fun x => by rw [affineFn_apply, _root_.EReal.coe_zero, sub_zero]

/-- `supportSet` is convex: it is a level set of the convex function `f*`. -/
theorem convex_supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Convex ℝ (supportSet B f) := by
  rw [supportSet_eq_setOf_conj_le]
  exact (convexFn_conj B f).convex_le 0

/-- **The conjugate of a positively homogeneous function is fixed by every positive scalar.** This
is the substance of Rockafellar's `f = λf ↔ f* = f*λ`, obtained by reindexing the defining supremum
rather than by manipulating `(λf)*`. -/
theorem conj_smul_eq_self (hf : PosHomogeneous f) {a : ℝ} (ha : 0 < a) (y : F) :
    conj B f y = (a : EReal) * conj B f y := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    rw [conj_of_eq_bot hx₀]
    exact (_root_.EReal.coe_mul_top_of_pos ha).symm
  push Not at hb
  have hterm : ∀ x : E, ((B (a • x) y : ℝ) : EReal) - f (a • x)
      = (a : EReal) * (((B x y : ℝ) : EReal) - f x) := by
    intro x
    rw [hf a ha x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_ne (f x) ⊤ with h | h
    · rw [h, _root_.EReal.coe_mul_top_of_pos ha, _root_.EReal.sub_top, _root_.EReal.sub_top,
        _root_.EReal.coe_mul_bot_of_pos ha]
    · obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hb x) (lt_top_iff_ne_top.2 h)
      rw [hr, Tdaf.EReal.coe_mul_coe, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_sub,
        Tdaf.EReal.coe_mul_coe]
      congr 1
      ring
  have hsurj : Function.Surjective fun x : E => a • x := fun z =>
    ⟨a⁻¹ • z, smul_inv_smul₀ ha.ne' z⟩
  have hre : (⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x))) = conj B f y :=
    hsurj.iSup_comp fun z => ((B z y : ℝ) : EReal) - f z
  calc conj B f y = ⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x)) := hre.symm
    _ = ⨆ x : E, (a : EReal) * (((B x y : ℝ) : EReal) - f x) := iSup_congr hterm
    _ = (a : EReal) * conj B f y := (Tdaf.EReal.coe_mul_iSup ha _).symm

/-- **The conjugate of a positively homogeneous function is an indicator function.** Together with
`supportFn_eq_conj_indicatorFn` this is the whole duality between positive homogeneity and
being an indicator that Rockafellar opens §14 with.

The only hypothesis is that `f` is not identically `+∞`; that case is genuinely excluded, since
`(+∞)* = -∞` is no indicator. -/
theorem conj_eq_indicatorFn_of_posHomogeneous (hf : PosHomogeneous f) (hne : ∃ x, f x ≠ ⊤) :
    conj B f = indicatorFn (supportSet B f) := by
  funext y
  have hval : conj B f y = 0 ∨ conj B f y = ⊤ := by
    rcases Tdaf.EReal.eq_zero_or_eq_top_or_eq_bot (a := 2) (by norm_num)
      (conj_smul_eq_self hf (by norm_num : (0 : ℝ) < 2) y).symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨x₀, hx₀⟩ := hne
      exact absurd (conj_eq_bot_iff.1 h x₀) hx₀
  have hiff : y ∈ supportSet B f ↔ conj B f y ≤ 0 := by
    rw [supportSet_eq_setOf_conj_le]; exact Iff.rfl
  by_cases hy : y ∈ supportSet B f
  · rw [indicatorFn_of_mem hy]
    rcases hval with h | h
    · exact h
    · exact absurd (hiff.1 hy) (by rw [h]; simp)
  · rw [indicatorFn_of_notMem hy]
    rcases hval with h | h
    · exact absurd (hiff.2 h.le) hy
    · exact h

end PosHom

/-! ### Closedness of the support function -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {s : Set E}

/-- The support function is lower semicontinuous as soon as the pairing is continuous on the `F`
side. -/
theorem lowerSemicontinuous_supportFn : LowerSemicontinuous (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact lowerSemicontinuous_conj

variable [IsTopologicalAddGroup F]

/-- **The support function of any set is a closed convex function** — it is a conjugate. -/
theorem closedFn_supportFn : ClosedFn (supportFn B s) := by
  rw [supportFn_eq_conj_indicatorFn]; exact closedFn_conj

end Closed

/-! ### The closure of the set

`evalCLM B y : StrongDual ℝ E` is the continuous linear functional `⟨·, y⟩`; it is what turns
the half-space characterisations of §11 — which quantify over `StrongDual ℝ E` — into statements
about `F`. -/

section ContinuousPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B] {s : Set E}

/-- The set `{x | ⟨x, y⟩ ≤ M}` is closed when the pairing is continuous on the `E` side. -/
theorem isClosed_setOf_pairing_le (y : F) (M : EReal) :
    IsClosed {x : E | ((B x y : ℝ) : EReal) ≤ M} :=
  isClosed_Iic.preimage (_root_.EReal.continuous_coe_iff.2 (continuous_pairing B y))

/-- **The support function does not see the closure** (Rockafellar §13). -/
theorem supportFn_closure (s : Set E) : supportFn B (closure s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono subset_closure y)
  exact closure_minimal (fun z hz => le_supportFn hz y)
    (isClosed_setOf_pairing_le y (supportFn B s y)) hx

/-- `supportSet` is closed: it is a level set of the lower semicontinuous function `g*`. -/
theorem isClosed_supportSet (g : F → EReal) : IsClosed (supportSet B.flip g) := by
  rw [supportSet_eq_setOf_conj_le,
    show ((0 : EReal)) = ((0 : ℝ) : EReal) from _root_.EReal.coe_zero.symm]
  exact lowerSemicontinuous_iff_isClosed_le.1 (lowerSemicontinuous_conj (B := B.flip)) 0

end ContinuousPairing

/-! ### Theorem 13.1 -/

section Theorem131

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- **Rockafellar, Theorem 13.1.** A point lies in the closed convex hull of `s` if and only if it
satisfies every weak linear inequality that the support function of `s` records.

This is Corollary 11.5.1 read through the pairing: `closure_convexHull_eq_iInter_halfspaces`
quantifies over the continuous linear functionals on `E`, and compatibility of the pairing says
that these are precisely the `⟨·, y⟩`. -/
theorem mem_closure_convexHull_iff_le_supportFn (s : Set E) (x : E) :
    x ∈ closure (convexHull ℝ s) ↔ ∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B s y := by
  rw [← closure_convexHull_eq_iInter_halfspaces s]
  simp only [Set.mem_iInter, Set.mem_ofPred]
  constructor
  · intro h y
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc₁, hc₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
    have hbnd : ∀ z ∈ s, evalCLM B y z ≤ c := supportFn_le_coe_iff.1 hc₁.le
    have hx := h (evalCLM B y) c hbnd
    rw [evalCLM_apply] at hx
    exact absurd hc₂ (not_lt.2 (by exact_mod_cast hx))
  · intro h g c hg
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsup : supportFn B s y ≤ (c : EReal) :=
      supportFn_le_coe_iff.2 fun z hz => hy z ▸ hg z hz
    rw [hy x]
    exact_mod_cast (h y).trans hsup

/-- **Rockafellar, Corollary 13.1.1.** Closed convex hulls are ordered by their support
functions. -/
theorem closure_convexHull_subset_iff_supportFn_le (s t : Set E) :
    closure (convexHull ℝ s) ⊆ closure (convexHull ℝ t) ↔ supportFn B s ≤ supportFn B t := by
  constructor
  · intro h y
    have h' := supportFn_mono (B := B) h y
    rwa [supportFn_closure, supportFn_convexHull, supportFn_closure,
      supportFn_convexHull] at h'
  · intro h x hx
    rw [mem_closure_convexHull_iff_le_supportFn (B := B)] at hx ⊢
    exact fun y => (hx y).trans (h y)

end Theorem131

/-! ### Corollary 13.2.1

Only the space `F` carries a topology here: this is `biconj_eq_clFn` for the *flipped*
pairing. -/

section Corollary1321

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B.flip] {g : F → EReal}

/-- **Rockafellar, Corollary 13.2.1.** The closure of a positively homogeneous convex function that
is not identically `+∞` is the support function of a certain closed convex set, namely
`supportSet B.flip g = {x | ∀ y, ⟨x, y⟩ ≤ g y}`.

The improper case is included: if `g` takes `-∞` then `cl g ≡ -∞`, `supportSet B.flip g` is empty,
and both sides are the support function of `∅`. -/
theorem clFn_eq_supportFn_of_posHomogeneous
    (hg : PosHomogeneous g) (hconv : ConvexFn g) (hne : ∃ y, g y ≠ ⊤) :
    clFn g = supportFn B (supportSet B.flip g) := by
  rw [supportFn_eq_conj_indicatorFn,
    ← conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg hne]
  exact (biconj_eq_clFn (B := B.flip) hconv).symm

omit [LocallyConvexSpace ℝ F] in
/-- **Taking the closure of a positively homogeneous function does not change the set it
supports.** The two conjugates agree (`conj_clFn`) and both are indicator functions
(`conj_eq_indicatorFn_of_posHomogeneous`), so the two supported sets agree.

Convexity of `g` was a hypothesis while `posHomogeneous_clFn` was proved through Corollary 13.2.1;
neither step needs it. -/
theorem supportSet_clFn (hg : PosHomogeneous g) (hne : ∃ y, g y ≠ ⊤) :
    supportSet B.flip (clFn g) = supportSet B.flip g := by
  obtain ⟨w, hw⟩ := hne
  have hne' : ∃ y, clFn g y ≠ ⊤ := ⟨w, fun h => hw (top_le_iff.1 (h ▸ clFn_le g w))⟩
  have h₁ := conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg ⟨w, hw⟩
  have h₂ := conj_eq_indicatorFn_of_posHomogeneous (B := B.flip) (posHomogeneous_clFn hg) hne'
  rw [conj_clFn, h₁] at h₂
  rw [← dom_indicatorFn (supportSet B.flip (clFn g)), ← h₂, dom_indicatorFn]

/-- A closed positively homogeneous convex function *is* the support function of
`supportSet B.flip g`. -/
theorem supportFn_supportSet (hg : PosHomogeneous g) (hconv : ConvexFn g) (hcl : ClosedFn g)
    (hne : ∃ y, g y ≠ ⊤) : supportFn B (supportSet B.flip g) = g :=
  (clFn_eq_supportFn_of_posHomogeneous hg hconv hne).symm.trans hcl

/-- The set supporting a closed *proper* positively homogeneous convex function is nonempty: only
the empty set has `-∞` for a support function. -/
theorem nonempty_supportSet (hg : PosHomogeneous g) (hcpc : ClosedProperConvexFn g) :
    (supportSet B.flip g).Nonempty := by
  obtain ⟨y₀, hy₀⟩ := hcpc.proper.dom_nonempty
  have hg' := supportFn_supportSet (B := B) hg hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
  rcases (supportSet B.flip g).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, supportFn_empty] at hg'
    exact absurd (congrFun hg' y₀).symm (hcpc.proper.ne_bot y₀)
  · exact hne

end Corollary1321

/-! ### Theorem 13.2

Both spaces carry topologies compatible with the pairing, exactly as for `conjEquiv`: the
statement asks simultaneously that `g` be a closed function on `F` and that the set it supports be
closed in `E`. -/

section Theorem132

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {g : F → EReal}

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **Rockafellar, Theorem 13.2**, first half: the indicator function and the support function of a
closed convex set are conjugate to each other.

One direction is `supportFn_eq_conj_indicatorFn`, which is a definition unfolded; the other is
Fenchel–Moreau together with `cl δ(· | s) = δ(· | cl s)`. -/
theorem conj_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    conj B.flip (supportFn B s) = indicatorFn s := by
  rw [supportFn_eq_conj_indicatorFn]
  change biconj B (indicatorFn s) = indicatorFn s
  rw [biconj_eq_clFn (convexFn_indicatorFn.2 hs₁), clFn_indicatorFn, hs₂.closure_eq]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **Rockafellar, Theorem 13.2** with the closedness hypothesis dropped: the conjugate of a
support function is the indicator of the *closure* of the set.

`conj_supportFn` is the case where the closure does nothing. This form is what a closedness
*conclusion* is read off from: `dom` of the left side is `cl s`. -/
theorem conj_supportFn_of_convex [IsCompatiblePairing B] (hs₁ : Convex ℝ s) :
    conj B.flip (supportFn B s) = indicatorFn (closure s) := by
  rw [supportFn_eq_conj_indicatorFn]
  change biconj B (indicatorFn s) = indicatorFn (closure s)
  rw [biconj_eq_clFn (convexFn_indicatorFn.2 hs₁), clFn_indicatorFn]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **Theorem 13.1 for a closed convex set**: `s` is recovered from its support function. -/
theorem supportSet_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    supportSet B.flip (supportFn B s) = s := by
  ext x
  simp only [mem_supportSet, LinearMap.flip_apply]
  rw [← mem_closure_convexHull_iff_le_supportFn, hs₁.convexHull_eq, hs₂.closure_eq]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **Rockafellar, Theorem 13.2**, the characterisation: *the* support functions of the nonempty
convex sets are exactly the closed proper positively homogeneous convex functions.

Rockafellar states the class of sets as "non-empty convex"; since the support function does not see
the closure or the convex hull, the same functions arise from the nonempty *closed convex* sets,
and that is what is asserted here, so that the correspondence is one-to-one
(`supportEquiv`). -/
theorem exists_supportFn_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧ g = supportFn B C) ↔
      (ClosedProperConvexFn g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, -, -, rfl⟩
    exact ⟨⟨convexFn_supportFn B C, closedFn_supportFn, proper_supportFn hne⟩,
      posHomogeneous_supportFn B C⟩
  · rintro ⟨hcpc, hph⟩
    obtain ⟨y₀, hy₀⟩ := hcpc.proper.dom_nonempty
    have hg : supportFn B (supportSet B.flip g) = g :=
      supportFn_supportSet hph hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
    exact ⟨supportSet B.flip g, nonempty_supportSet hph hcpc,
      convex_supportSet B.flip g, isClosed_supportSet g, hg.symm⟩

/-- **Rockafellar, Theorem 13.2** as a bijection, the "important one-to-one correspondence between
the closed convex sets and objects of quite a different sort". It is the restriction of
`conjEquiv` along the two embeddings `s ↦ δ(· | s)` and "positively homogeneous". -/
noncomputable def supportEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {C : Set E // C.Nonempty ∧ Convex ℝ C ∧ IsClosed C} ≃
      {g : F → EReal // ClosedProperConvexFn g ∧ PosHomogeneous g} where
  toFun C := ⟨supportFn B C.1, ⟨convexFn_supportFn B C.1, closedFn_supportFn,
    proper_supportFn C.2.1⟩, posHomogeneous_supportFn B C.1⟩
  invFun g := ⟨supportSet B.flip g.1, nonempty_supportSet g.2.2 g.2.1,
    convex_supportSet B.flip g.1, isClosed_supportSet g.1⟩
  left_inv C := Subtype.ext (supportSet_supportFn C.2.2.1 C.2.2.2)
  right_inv g := Subtype.ext <| by
    obtain ⟨y₀, hy₀⟩ := g.2.1.proper.dom_nonempty
    exact supportFn_supportSet g.2.2 g.2.1.convex g.2.1.closed ⟨y₀, hy₀.ne⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **Rockafellar, Corollary 13.2.2.** The support functions of the nonempty sets on which every
`⟨·, y⟩` is bounded above are exactly the *finite* closed positively homogeneous convex functions.

The `ClosedFn` hypothesis is not in the book: see the design note above. Rockafellar's "bounded" is
here read as "`⟨·, y⟩` is bounded above on `C` for every `y`", which is what his own proof uses and
which coincides with boundedness in `Rⁿ`. -/
theorem exists_supportFn_finite_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ (∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c) ∧ g = supportFn B C) ↔
      ((∀ y, g y ≠ ⊥) ∧ (∀ y, g y ≠ ⊤) ∧ ConvexFn g ∧ ClosedFn g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, hbdd, rfl⟩
    exact ⟨supportFn_ne_bot hne, fun y => (supportFn_lt_top_iff.2 (hbdd y)).ne,
      convexFn_supportFn B C, closedFn_supportFn, posHomogeneous_supportFn B C⟩
  · rintro ⟨hb, ht, hconv, hcl, hph⟩
    have hp : Proper g := ⟨⟨0, lt_top_iff_ne_top.2 (ht 0)⟩, hb⟩
    obtain ⟨C, hne, -, -, hg⟩ :=
      (exists_supportFn_iff (B := B)).2 ⟨⟨hconv, hcl, hp⟩, hph⟩
    refine ⟨C, hne, fun y => supportFn_lt_top_iff.1 ?_, hg⟩
    rw [← hg]
    exact lt_top_iff_ne_top.2 (ht y)

end Theorem132

end Tdaf.ConvexAnalysis
