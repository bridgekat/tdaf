/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Geometry.Convex.Cone.Dual
import Tdaf.Analysis.Convex.Duality.Support
import Tdaf.Order.GaloisConnection

/-!
# Polars of convex sets and convex cones

Rockafellar's §14, over a dual pair `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. §14 opens by observing that a
positively homogeneous *indicator* function conjugates to a positively homogeneous indicator
function, so the conjugacy correspondence of §12 restricts to a correspondence between convex
cones. That restriction is polarity, and it is proved here from
`conj_eq_indicatorFn_of_posHomogeneous` together with the separation theory of §11.

## Main definitions

* `polarCone B K` — Rockafellar's polar `K° = {y | ∀ x ∈ K, ⟨x, y⟩ ≤ 0}` of a convex cone.
* `polarPointedCone B K` — the same set bundled as a `PointedCone ℝ F`.
* `polarSet B C` — the polar `C° = {y | ∀ x ∈ C, ⟨x, y⟩ ≤ 1}` of a convex set containing the
  origin.
* `gc_polarCone_polarCone`, `polarConeClosure` — polarity as an *antitone Galois
  connection* between `Set E` and `Set F` and the closure operator `K ↦ K°°` it induces; likewise
  `gc_polarSet_polarSet` and `polarSetClosure`.

## Main results

* `conj_indicatorFn_eq_indicatorFn_polarCone` — **Theorem 14.1**, third assertion: the
  indicator functions of `K` and `K°` are conjugate.
* `polarCone_polarCone` — **Theorem 14.1**, second assertion: `K°° = cl K` for a nonempty
  convex cone `K`; `polarCone_polarCone_of_isClosed` is the closed case, and
  `isClosed_polarConeClosure_iff` identifies these with the closed elements of the closure
  operator.
* `isClosed_polarCone`, `polarPointedCone` — **Theorem 14.1**, first assertion: `K°` is a
  nonempty closed convex cone, for *any* `K`.
* `polarCone_neg`, `smul_neg_polarCone`, `zero_mem_neg_polarCone`, `convex_neg_polarCone`,
  `neg_polarCone_neg_polarCone` — the same facts for Rockafellar's *dual* cone `K* = -K°`, which
  is what §31 pairs with `K`; the last is `K** = K` for a nonempty closed convex cone.
* `polarSet_polarSet` — **Theorem 14.5**, first assertion: `C°° = C` for a closed convex `C`
  containing the origin.
* `polarSubmodule`, `partialAffineFn`, `conj_partialAffineFn` — the polar of a subspace bundled
  as a submodule, and the **conjugate of a partial affine function** (Rockafellar §12, the display
  preceding Theorem 12.3): `(δ(· | L + a) + ⟨·, a*⟩ + α)* = δ(· | L^⊥ + a*) + ⟨a, ·⟩ + α*`.
* `polarCone_coe_submodule`, `polarCone_hull_range`,
  `polarCone_setOf_forall_le_zero`, `polarCone_nonnegOrthant` — the examples of §14:
  the polar of a subspace is its annihilator, the polar of a generated cone is the solution set of
  the corresponding homogeneous inequalities and conversely, and the polar of the nonnegative
  orthant is the nonpositive orthant.

## Bridges to Mathlib

* `polarPointedCone_eq_dual_neg` — Mathlib **does** have a dual cone: `PointedCone.dual p s`
  in `Mathlib/Geometry/Convex/Cone/Dual.lean` is `{y | ∀ x ∈ s, 0 ≤ p x y}`, the *inner* dual, so
  `K° = (-K)ᵛ = -(Kᵛ)`. Mathlib also has `ProperCone.dual` with `ProperCone.dual_flip_dual`, the
  bipolar theorem for a *perfect continuous* pairing (`LinearMap.IsContPerfPair`); the version
  proved here instead asks for `IsCompatiblePairing`, so it applies to a space paired
  with its own continuous dual without asking for a perfect pairing; closedness of the polar
  (`isClosed_polarCone`) needs only `IsContinuousPairing`.
* `polarSet_eq_polar_of_balanced` — Mathlib's `LinearMap.polar` is the **absolute** polar
  `{y | ∀ x ∈ s, ‖B x y‖ ≤ 1}`. It agrees with `polarSet` exactly on balanced sets;
  Rockafellar's polar is one-sided and the two are genuinely different objects otherwise.

## Design notes

**Polarity is a Galois connection, and `polarConeClosure` is its closure operator.** The
adjunction `L ⊆ K° ↔ K ⊆ L°` is `subset_polarCone_comm`, and it makes `K ↦ K°°` a
`ClosureOperator (Set E)`. The `OrderDual` sits on the *codomain* here, not on the domain as in
`conjClosure`, so the induced closure operator lives on `Set E` itself and `K ⊆ K°°` is its
unit; Theorem 14.1 then says exactly which sets are closed for it. The change of side is forced by
variance: `δ(· | K) ≤ δ(· | L)` means `L ⊆ K`, so the indicator embedding is *antitone*, and the
polarity adjunction is the image of `conj_le_iff` under it.

**`K°° = cl K`, not `K°° = K`, is the theorem.** This is design decision `D0`: the missing
hypothesis in a statement transcribed from `Rⁿ` is "closed" or "continuous", and here it is
"closed". `polarCone_polarCone` is stated with `cl K` and needs no closedness at all.

**Nonemptiness of `K` is needed.** `∅° = F` and `F° = {x | ∀ y, ⟨x, y⟩ ≤ 0}`, which is the kernel
of the pairing rather than `cl ∅ = ∅`. Rockafellar's standing hypothesis in §14 is that the cone is
nonempty, and it is kept.

## Deferred

* **Theorems 14.2 and 14.3, and Corollaries 14.2.1–14.2.2**, describe the polar of the cone
  generated by `dom f`, of a recession cone, and of a level set, in terms of the **recession cone**
  of `f*`. That is `recessionFn` in `Tdaf/Analysis/Convex/Recession/Function.lean`, which this
  file does not import.
* **Theorem 14.4** (the `ℝ^(n+2)` cone whose polar carries `f*`) needs the recession function of
  the positively homogeneous function generated by `f`, i.e. Theorem 13.5, which is still unstated
  — see the deferral in `Tdaf/Analysis/Convex/Duality/Support.lean`.
* **Theorem 14.5, second and third assertions, and Corollary 14.5.1** identify the gauge of `C`
  with the support function of `C°`, and boundedness of `C°` with `0 ∈ int C`. Both quantify over
  the **gauge**, and so do **Theorems 14.6, 14.7 and the whole of §15**; those are a separate
  module. Mathlib already has `gauge` and `egauge` (`Mathlib/Analysis/Convex/EGauge.lean`) and the
  plan is to reuse them rather than to introduce a third.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §14 (Theorem 14.1,
  Theorem 14.5).
-/

open Set Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Rockafellar's polar of a convex cone**: `K° = {y | ∀ x ∈ K, ⟨x, y⟩ ≤ 0}`.

This is a *one-sided* polar, and it is not Mathlib's `LinearMap.polar`, which is the absolute polar
`{y | ∀ x ∈ K, ‖⟨x, y⟩‖ ≤ 1}`. It is the negative of Mathlib's inner dual cone
(`polarPointedCone_eq_dual_neg`). -/
def polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Set F := {y | ∀ x ∈ K, B x y ≤ 0}

/-- **Rockafellar's polar of a convex set containing the origin**:
`C° = {y | ∀ x ∈ C, ⟨x, y⟩ ≤ 1}`. -/
def polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) : Set F := {y | ∀ x ∈ C, B x y ≤ 1}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K L : Set E} {C D : Set E} {y : F}

/-- Membership in the polar cone, unfolded. -/
@[simp] theorem mem_polarCone : y ∈ polarCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

/-- Membership in the polar set, unfolded. -/
@[simp] theorem mem_polarSet : y ∈ polarSet B C ↔ ∀ x ∈ C, B x y ≤ 1 := Iff.rfl

/-- Polarity of cones is order-reversing. -/
theorem polarCone_anti (h : K ⊆ L) : polarCone B L ⊆ polarCone B K := fun _ hy x hx => hy x (h hx)

/-- Polarity of sets is order-reversing (Rockafellar §14). -/
theorem polarSet_anti (h : C ⊆ D) : polarSet B D ⊆ polarSet B C := fun _ hy x hx => hy x (h hx)

/-- The polar of the empty set is everything. -/
@[simp] theorem polarCone_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarCone B (∅ : Set E) = univ := by ext y; simp

/-- The polar of the empty set is everything. -/
@[simp] theorem polarSet_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    polarSet B (∅ : Set E) = univ := by ext y; simp

/-- The origin lies in every polar cone. -/
@[simp] theorem zero_mem_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ polarCone B K := fun x _ => by simp

/-- The origin lies in every polar set. -/
@[simp] theorem zero_mem_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    (0 : F) ∈ polarSet B C := fun x _ => by simp

/-- A polar cone is never empty: it contains the origin. -/
theorem polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : (polarCone B K).Nonempty :=
  ⟨0, zero_mem_polarCone B K⟩

/-- The polar cone is contained in the polar set, since `0 ≤ 1`. -/
theorem polarCone_subset_polarSet : polarCone B K ⊆ polarSet B K :=
  fun _ hy x hx => (hy x hx).trans zero_le_one

/-- The polar of a union is the intersection of the polars. -/
theorem polarCone_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K L : Set E) :
    polarCone B (K ∪ L) = polarCone B K ∩ polarCone B L := by
  ext y; exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- The polar of a union of a family is the intersection of the polars. -/
theorem polarCone_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    polarCone B (⋃ i, u i) = ⋂ i, polarCone B (u i) := by
  ext y
  simp only [mem_polarCone, Set.mem_iInter, Set.mem_iUnion]
  exact ⟨fun h i x hx => h x ⟨i, hx⟩, fun h x hx => hx.elim fun i hi => h i x hi⟩

/-- **Rockafellar's remark in §14**: for a cone the two polars coincide, because the half-space
`{x | ⟨x, y⟩ ≤ 1}` contains a cone exactly when `{x | ⟨x, y⟩ ≤ 0}` does. -/
theorem polarCone_eq_polarSet_of_isCone (hK : ∀ a : ℝ, 0 < a → a • K = K) :
    polarCone B K = polarSet B K := by
  refine subset_antisymm polarCone_subset_polarSet fun y hy x hx => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmem : (2 / B x y) • x ∈ K :=
    (smul_mem_iff_of_isCone hK (by positivity)).2 hx
  have h := hy _ hmem
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at h
  linarith

/-- **The polarity adjunction**: `L ⊆ K°` and `K ⊆ L°` both say that `⟨x, y⟩ ≤ 0` for every `x ∈ K`
and `y ∈ L`. This is the image, under the antitone embedding `s ↦ δ(· | s)`, of the adjunction
`conj_le_iff` of §12. -/
theorem subset_polarCone_comm {L : Set F} : L ⊆ polarCone B K ↔ K ⊆ polarCone B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

/-- The same adjunction for polars of sets. -/
theorem subset_polarSet_comm {L : Set F} : L ⊆ polarSet B C ↔ C ⊆ polarSet B.flip L :=
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hy _ hx => h hx _ hy⟩

/-- **The unit of the polarity adjunction**: every set is contained in its bipolar. -/
theorem subset_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    K ⊆ polarCone B.flip (polarCone B K) := subset_polarCone_comm.1 (subset_refl _)

/-- Every set is contained in its bipolar, for polars of sets. -/
theorem subset_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    C ⊆ polarSet B.flip (polarSet B C) := subset_polarSet_comm.1 (subset_refl _)

/-! ### Polarity as a Galois connection

The adjunction above is exactly the shape of `gc_ofEpi_epi` and `gc_conj_conj`, and it is
recorded here so that the whole `ClosureOperator` API is available. Unlike conjugacy, the
`OrderDual` sits on the *codomain*, and the resulting closure operator therefore lives on `Set E`
itself. -/

/-- **Polarity of cones is an antitone Galois connection** between `Set E` and `Set F`. -/
theorem gc_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun K : Set E => OrderDual.toDual (polarCone B K))
      (fun L : (Set F)ᵒᵈ => polarCone B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarCone_comm

/-- **Polarity of sets is an antitone Galois connection** between `Set E` and `Set F`. -/
theorem gc_polarSet_polarSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun C : Set E => OrderDual.toDual (polarSet B C))
      (fun L : (Set F)ᵒᵈ => polarSet B.flip (OrderDual.ofDual L)) :=
  fun _ _ => subset_polarSet_comm

/-- The bipolar operator `K ↦ K°°` as a `ClosureOperator` on `Set E`. Its closed elements are, by
**Theorem 14.1** (`polarCone_polarCone_of_isClosed`), the nonempty closed convex cones. -/
def polarConeClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarCone_polarCone B).closureOperator

/-- `polarConeClosure` is the bipolar. -/
@[simp] theorem polarConeClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarConeClosure B K = polarCone B.flip (polarCone B K) := rfl

/-- Closedness for `polarConeClosure` is the bipolar equation `K°° = K`. -/
theorem isClosed_polarConeClosure_iff :
    (polarConeClosure B).IsClosed K ↔ polarCone B.flip (polarCone B K) = K := Iff.rfl

/-- The bipolar operator `C ↦ C°°` as a `ClosureOperator` on `Set E`. Its closed elements are, by
**Theorem 14.5** (`polarSet_polarSet`), the closed convex sets containing the origin. -/
def polarSetClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (Set E) :=
  (gc_polarSet_polarSet B).closureOperator

/-- `polarSetClosure` is the bipolar. -/
@[simp] theorem polarSetClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) :
    polarSetClosure B C = polarSet B.flip (polarSet B C) := rfl

/-- Closedness for `polarSetClosure` is the bipolar equation `C°° = C`. -/
theorem isClosed_polarSetClosure_iff :
    (polarSetClosure B).IsClosed C ↔ polarSet B.flip (polarSet B C) = C := Iff.rfl

/-- **Polarity is unchanged by taking the bipolar first** — the triangle identity of the
adjunction, and Rockafellar's `(cl K)° = K°` in its purely algebraic form. -/
theorem polarCone_polarCone_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (polarCone B.flip (polarCone B K)) = polarCone B K :=
  subset_antisymm (polarCone_anti (subset_polarCone_polarCone B K))
    (subset_polarCone_comm.2 (subset_refl _))

/-- **Polarity is an order anti-isomorphism between the bipolar-closed sets.**

Rockafellar's Theorem 14.1 says polarity is a one-to-one correspondence between the closed convex
cones containing the origin on the two sides. This is that correspondence with its order structure,
and with no topology: the bipolar-closed sets are exactly those cones once `E` and `F` carry
compatible topologies (`polarCone_polarCone_of_isClosed`), and the inclusion-reversal is what makes
the statement an *anti*-isomorphism. Free from `GaloisConnection.closedsOrderIso`. -/
def polarConeOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {K : Set E // polarCone B.flip (polarCone B K) = K} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarCone B (polarCone B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarCone_polarCone B).closedsOrderIso

/-- The same for polars of sets: **Theorem 14.5** in order form. -/
def polarSetOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {C : Set E // polarSet B.flip (polarSet B C) = C} ≃o
      {L : (Set F)ᵒᵈ //
        OrderDual.toDual (polarSet B (polarSet B.flip (OrderDual.ofDual L))) = L} :=
  (gc_polarSet_polarSet B).closedsOrderIso

/-! ### The polar cone as a `PointedCone` -/

/-- **The polar of an arbitrary set is a pointed convex cone** — the first assertion of
Rockafellar's Theorem 14.1, before any topology enters. Bundling it makes `Submodule.span_le` and
the rest of the `PointedCone` API available, exactly as for `halfSpaceCone` and
`recessionPointedCone`. -/
def polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : PointedCone ℝ F where
  carrier := polarCone B K
  zero_mem' := zero_mem_polarCone B K
  add_mem' {u v} hu hv x hx := by
    rw [map_add]
    exact add_nonpos (hu x hx) (hv x hx)
  smul_mem' c u hu x hx := by
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    calc (c : ℝ) * B x u ≤ (c : ℝ) * 0 := mul_le_mul_of_nonneg_left (hu x hx) c.2
      _ = 0 := mul_zero _

/-- The underlying set of `polarPointedCone` is the polar cone. -/
@[simp] theorem coe_polarPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (polarPointedCone B K : Set F) = polarCone B K := rfl

/-- Membership in `polarPointedCone`, unfolded. -/
@[simp] theorem mem_polarPointedCone : y ∈ polarPointedCone B K ↔ ∀ x ∈ K, B x y ≤ 0 := Iff.rfl

/-- The polar of any set is convex. -/
theorem convex_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) : Convex ℝ (polarCone B K) :=
  ((polarPointedCone B K : ConvexCone ℝ F)).convex

/-- The underlying set of a pointed cone is a cone in Rockafellar's sense. -/
theorem smul_coe_pointedCone (K : PointedCone ℝ E) (a : ℝ) (ha : 0 < a) :
    a • (K : Set E) = (K : Set E) := by
  ext x
  refine ⟨?_, fun hx => ⟨a⁻¹ • x, K.smul_mem (inv_pos.2 ha).le hx, smul_inv_smul₀ ha.ne' x⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact K.smul_mem ha.le hz

/-- A subspace is invariant under every positive scaling: it is a cone in Rockafellar's sense,
and a symmetric one. -/
theorem smul_coe_submodule (M : Submodule ℝ E) {a : ℝ} (ha : 0 < a) :
    a • (M : Set E) = (M : Set E) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact M.smul_mem a hu
  · intro hz
    refine ⟨a⁻¹ • z, M.smul_mem _ hz, ?_⟩
    change a • a⁻¹ • z = z
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- The polar of any set is a cone in Rockafellar's sense. -/
theorem smul_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • polarCone B K = polarCone B K := smul_coe_pointedCone (polarPointedCone B K) a ha

/-- **Negating the cone negates its polar**: `(-K)° = -(K°)`. Together with Theorem 14.1 this is
what makes Rockafellar's dual cone `K* = -K°` an involution — see
`neg_polarCone_neg_polarCone`. -/
theorem polarCone_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B (-K) = -(polarCone B K) := by
  ext y
  rw [Set.mem_neg, mem_polarCone, mem_polarCone]
  refine ⟨fun hy u hu => ?_, fun hy x hx => ?_⟩
  · have h := hy (-u) (Set.mem_neg.2 (by rwa [neg_neg]))
    rw [map_neg B u, LinearMap.neg_apply] at h
    rwa [map_neg (B u) y]
  · have h := hy (-x) (Set.mem_neg.1 hx)
    rwa [map_neg B x, LinearMap.neg_apply, map_neg (B x) y, neg_neg] at h

/-- Rockafellar's dual cone `K* = -K°` is itself invariant under every positive scaling, so it
meets the cone hypothesis of Theorem 31.4. -/
theorem smul_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) (a : ℝ) (ha : 0 < a) :
    a • (-(polarCone B K)) = -(polarCone B K) := by
  rw [← polarCone_neg]
  exact smul_polarCone B (-K) a ha

/-- The origin lies in Rockafellar's dual cone `K* = -K°`, whatever `K` is. -/
theorem zero_mem_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (0 : F) ∈ -(polarCone B K) := by
  rw [Set.mem_neg, neg_zero, mem_polarCone]
  exact fun x _ => le_of_eq (map_zero (B x))

/-- Rockafellar's dual cone `K* = -K°` is nonempty: it always contains the origin. -/
theorem neg_polarCone_nonempty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    (-(polarCone B K)).Nonempty := ⟨0, zero_mem_neg_polarCone B K⟩

/-- Rockafellar's dual cone `K* = -K°` is convex. -/
theorem convex_neg_polarCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    Convex ℝ (-(polarCone B K)) := (convex_polarCone B K).neg

/-! ### Bridges to Mathlib -/

/-- **Mathlib's dual cone is the inner one.** `PointedCone.dual B s = {y | ∀ x ∈ s, 0 ≤ ⟨x, y⟩}`, so
Rockafellar's polar is its negative — equivalently, the dual of `-K`. -/
theorem polarPointedCone_eq_dual_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarPointedCone B K = PointedCone.dual B (-K) := by
  ext y
  simp only [mem_polarPointedCone, PointedCone.mem_dual, Set.mem_neg]
  constructor
  · intro h x hx
    have hx' := h (-x) hx
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith
  · intro h x hx
    have hx' := h (x := -x) (by simpa using hx)
    rw [map_neg, LinearMap.neg_apply] at hx'
    linarith

/-- The polar cone is the negative of Mathlib's dual cone. -/
theorem polarCone_eq_neg_dual (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    polarCone B K = -(PointedCone.dual B K : Set F) := by
  rw [← coe_polarPointedCone, polarPointedCone_eq_dual_neg]
  exact congrArg _ (PointedCone.dual_neg (p := B) (s := K))

/-- **Mathlib's `LinearMap.polar` is the absolute polar** `{y | ∀ x ∈ C, ‖⟨x, y⟩‖ ≤ 1}`. It agrees
with Rockafellar's one-sided polar exactly on balanced sets, where `x ∈ C` implies `-x ∈ C`. -/
theorem polarSet_eq_polar_of_balanced (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {C : Set E} (hC : Balanced ℝ C) :
    polarSet B C = B.polar C := by
  ext y
  simp only [mem_polarSet, LinearMap.polar_mem_iff, Real.norm_eq_abs]
  refine ⟨fun h x hx => abs_le.2 ⟨?_, h x hx⟩, fun h x hx => (le_abs_self _).trans (h x hx)⟩
  have hneg : -x ∈ C := by
    have := hC (-1 : ℝ) (by norm_num)
    exact this ⟨x, hx, by simp⟩
  have := h (-x) hneg
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

end Defs

/-! ### The polar cone and the conjugate of an indicator

This is the computation Rockafellar opens §14 with, and it needs no topology: the indicator of a
cone is positively homogeneous, so its conjugate is again an indicator
(`conj_eq_indicatorFn_of_posHomogeneous`), and the set it indicates is the polar. -/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {K : Set E}

/-- The set that the conjugate of an indicator function indicates is the polar cone. -/
@[simp] theorem supportSet_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (K : Set E) :
    supportSet B (indicatorFn K) = polarCone B K := by
  ext y
  simp only [mem_supportSet, mem_polarCone]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · have hx' := h x
    rw [indicatorFn_of_mem hx] at hx'
    exact_mod_cast hx'
  · by_cases hx : x ∈ K
    · rw [indicatorFn_of_mem hx]
      exact_mod_cast h x hx
    · rw [indicatorFn_of_notMem hx]
      exact le_top

/-- **Rockafellar, Theorem 14.1**, third assertion (and the computation §14 opens with): the
indicator function of a nonempty convex cone and the indicator function of its polar are conjugate
to each other. Only one direction needs the hypotheses; the other is
`polarCone_polarCone`. -/
theorem conj_indicatorFn_eq_indicatorFn_polarCone (hK : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) : conj B (indicatorFn K) = indicatorFn (polarCone B K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  rw [← supportSet_indicatorFn]
  exact conj_eq_indicatorFn_of_posHomogeneous (posHomogeneous_indicatorFn.2 hK)
    ⟨x₀, by rw [indicatorFn_of_mem hx₀]; simp⟩

/-- **The support function of a nonempty convex cone is the indicator of its polar.** -/
theorem supportFn_eq_indicatorFn_polarCone (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    supportFn B K = indicatorFn (polarCone B K) := by
  rw [supportFn_eq_conj_indicatorFn]
  exact conj_indicatorFn_eq_indicatorFn_polarCone hK hne

end Indicator

/-! ### Closedness of the polar -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {K C : Set E}

/-- **Rockafellar, Theorem 14.1**, first assertion: the polar of any set is closed, being an
intersection of homogeneous closed half-spaces. -/
theorem isClosed_polarCone : IsClosed (polarCone B K) := by
  have h : polarCone B K = ⋂ x ∈ K, {y : F | B x y ≤ 0} := by ext y; simp [polarCone]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

/-- The polar of a set in the sense of `polarSet` is closed, for the same reason: it is an
intersection of closed half-spaces. -/
theorem isClosed_polarSet : IsClosed (polarSet B C) := by
  have h : polarSet B C = ⋂ x ∈ C, {y : F | B x y ≤ 1} := by ext y; simp [polarSet]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_pairing B.flip x) continuous_const

end Closed

section ClosureDomain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B]

/-- **The polar does not see the closure** (Rockafellar §14: `(cl K)° = K°`). -/
theorem polarCone_closure (K : Set E) : polarCone (B := B) (closure K) = polarCone B K := by
  refine subset_antisymm (polarCone_anti subset_closure) fun y hy x hx => ?_
  exact closure_minimal (fun z hz => hy z hz)
    (isClosed_le (continuous_pairing B y) continuous_const) hx

end ClosureDomain

/-! ### Theorem 14.1

The bipolar theorem. Separation supplies the only nontrivial half, exactly as in Rockafellar's
alternative derivation from Corollary 11.7.1. -/

section Theorem141

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {K : Set E}

/-- **Rockafellar, Theorem 14.1**, second assertion, in the form `D0` predicts: the bipolar of a
nonempty convex cone is its *closure*.

The inclusion `cl K ⊆ K°°` holds because `K°°` is closed and contains `K`. For the converse, a
point outside `cl K` is strongly separated from it by a continuous linear functional `f`; because
`cl K` is a nonempty cone, `f ≤ 0` on `cl K` and the separating constant is nonnegative
(`le_zero_of_isCone_of_forall_le` and `nonneg_of_isCone_of_forall_le`), so the `y`
representing `f` lies in `K°` and detects the point. -/
theorem polarCone_polarCone (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) :
    polarCone B.flip (polarCone B K) = closure K := by
  have hmem : ∀ ⦃a : ℝ⦄, 0 < a → ∀ ⦃x⦄, x ∈ K → a • x ∈ K :=
    fun _ ha _ hx => (smul_mem_iff_of_isCone hcone ha).2 hx
  refine subset_antisymm (fun x hx => ?_) ?_
  · by_contra hcon
    obtain ⟨f, u, hfK, hfx⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hcon
    have hbdd : ∀ z ∈ closure K, f z ≤ u := fun z hz => (hfK z hz).le
    have hle : ∀ z ∈ K, f z ≤ 0 := fun z hz =>
      le_zero_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd (subset_closure hz)
    have hu : 0 ≤ u := nonneg_of_isCone_of_forall_le (smul_mem_closure_of_isCone hmem) hbdd
      (hne.mono subset_closure)
    obtain ⟨y, hy⟩ := exists_pairing_eq B f
    have hyK : y ∈ polarCone B K := fun z hz => hy z ▸ hle z hz
    have := hx y hyK
    rw [LinearMap.flip_apply, ← hy x] at this
    linarith
  · exact closure_minimal (subset_polarCone_polarCone B K) (isClosed_polarCone (B := B.flip))

/-- **Rockafellar, Theorem 14.1.** For a nonempty *closed* convex cone the polarity correspondence
is an involution: `K°° = K`. -/
theorem polarCone_polarCone_of_isClosed (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    polarCone B.flip (polarCone B K) = K :=
  (polarCone_polarCone hconv hcone hne).trans hcl.closure_eq

/-- **Rockafellar, Theorem 14.1** for a bundled cone: for a closed `PointedCone`, `K°° = K`. All
three hypotheses of the previous statement are supplied by the bundling. -/
theorem polarCone_polarCone_pointedCone (K : PointedCone ℝ E) (hcl : IsClosed (K : Set E)) :
    polarCone B.flip (polarCone B (K : Set E)) = (K : Set E) :=
  polarCone_polarCone_of_isClosed (K : ConvexCone ℝ E).convex
    (smul_coe_pointedCone K) ⟨0, K.zero_mem⟩ hcl

/-- **Rockafellar, Theorem 14.1** in the form §31 states it: `K** = K` for a nonempty closed convex
cone, where `K* = -K°` is the dual cone of Theorem 31.4. The two sign flips cancel against the one
of `polarCone_neg`. -/
theorem neg_polarCone_neg_polarCone (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    -(polarCone B.flip (-(polarCone B K))) = K := by
  rw [polarCone_neg, neg_neg, polarCone_polarCone_of_isClosed hconv hcone hne hcl]

/-- **Rockafellar, Theorem 14.1**, third assertion, in the remaining direction: for a nonempty
closed convex cone the indicator of `K°` conjugates back to the indicator of `K`. -/
theorem conj_indicatorFn_polarCone (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K) :
    conj B.flip (indicatorFn (polarCone B K)) = indicatorFn K := by
  rw [conj_indicatorFn_eq_indicatorFn_polarCone (B := B.flip) (smul_polarCone B K)
      (polarCone_nonempty B K),
    polarCone_polarCone_of_isClosed hconv hcone hne hcl]

end Theorem141

/-! ### Theorem 14.5

`C°° = C` for a closed convex set containing the origin. The separation argument is the same as for
cones, with the constant normalised to `1` instead of `0`. -/

section Theorem145

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **Rockafellar, Theorem 14.5**, first assertion: the polar of a closed convex set containing the
origin is another closed convex set containing the origin, and `C°° = C`.

Containment of the origin is what makes the separating constant positive, so that the separating
functional can be rescaled to have value exactly `1` on the boundary of the half-space. -/
theorem polarSet_polarSet (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarSet B.flip (polarSet B C) = C := by
  refine subset_antisymm (fun x hx => ?_) (subset_polarSet_polarSet B C)
  by_contra hcon
  obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hconv hcl hcon
  have hu : 0 < u := by simpa using hfC 0 h0
  obtain ⟨y, hy⟩ := exists_pairing_eq B f
  have hyC : u⁻¹ • y ∈ polarSet B C := by
    intro z hz
    rw [map_smul, smul_eq_mul, ← hy z]
    rw [inv_mul_le_iff₀ hu, mul_one]
    exact (hfC z hz).le
  have hxle := hx _ hyC
  rw [LinearMap.flip_apply, map_smul, smul_eq_mul, ← hy x, inv_mul_le_iff₀ hu, mul_one] at hxle
  linarith

/-- The closed elements of `polarSetClosure` include every closed convex set containing the
origin — the reading of Theorem 14.5 as a statement about the bipolar closure operator. -/
theorem isClosed_polarSetClosure_of_isClosed (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : E) ∈ C) : (polarSetClosure B).IsClosed C :=
  isClosed_polarSetClosure_iff.2 (polarSet_polarSet hconv hcl h0)

end Theorem145

/-! ### The examples of §14 -/

section Examples

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **The polar of a subspace is its annihilator** (Rockafellar §14: "if `K` is a subspace then
`K°` is the orthogonally complementary subspace"). Under the pairing this is Mathlib's
`Submodule.dualAnnihilator`, pulled back along `B.flip : F →ₗ[ℝ] Module.Dual ℝ E`. -/
theorem polarCone_coe_submodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = (M.dualAnnihilator.comap B.flip : Set F) := by
  ext y
  simp only [mem_polarCone, SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    LinearMap.flip_apply]
  refine ⟨fun h x hx => le_antisymm (h x hx) ?_, fun h x hx => (h x hx).le⟩
  have := h (-x) (M.neg_mem hx)
  rw [map_neg, LinearMap.neg_apply] at this
  linarith

/-- The polar of a subspace, unbundled. -/
theorem polarCone_coe_submodule' (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    polarCone B (M : Set E) = {y : F | ∀ x ∈ M, B x y = 0} := by
  rw [polarCone_coe_submodule]
  ext y
  simp [Submodule.mem_dualAnnihilator]

/-- The polar of a **subspace**, bundled as a submodule of `F`: the annihilator of `M` pulled back
along `B.flip`. Its carrier is `polarCone B M`, which for a subspace is Rockafellar's "orthogonally
complementary subspace" (`polarCone_coe_submodule`). -/
noncomputable def polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) : Submodule ℝ F :=
  M.dualAnnihilator.comap B.flip

@[simp] theorem coe_polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    (polarSubmodule B M : Set F) = polarCone B (M : Set E) :=
  (polarCone_coe_submodule B M).symm

/-- **The polar does not see the cone generated** (Rockafellar §14). -/
@[simp] theorem polarCone_hull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set E) :
    polarCone B (PointedCone.hull ℝ S : Set E) = polarCone B S := by
  refine subset_antisymm (polarCone_anti PointedCone.subset_hull) fun y hy x hx => ?_
  have hle : PointedCone.hull ℝ S ≤ polarPointedCone B.flip {y} :=
    Submodule.span_le.2 fun z hz w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hy z hz
  exact hle hx y rfl

/-- **Rockafellar §14**: the polar of the convex cone generated by a family `aᵢ` is the solution set
of the homogeneous inequalities `⟨aᵢ, y⟩ ≤ 0`. -/
theorem polarCone_hull_range {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (a : ι → E) :
    polarCone B (PointedCone.hull ℝ (Set.range a) : Set E) = {y : F | ∀ i, B (a i) y ≤ 0} := by
  rw [polarCone_hull]
  ext y
  simp only [mem_polarCone, Set.mem_range, Set.mem_ofPred]
  exact ⟨fun h i => h (a i) ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

end Examples

/-! ### Partial affine functions

Rockafellar's §12, the paragraph preceding Theorem 12.3. A *partial affine function* is a proper
convex function whose effective domain is an affine set and which is affine on it; every such
function can be written as `δ(· | L + a) + ⟨·, a*⟩ + α` for a subspace `L`. Conjugacy exchanges `L`
with its polar, `a` with `a*`, and `α` with `-α - ⟨a, a*⟩`, so partial affine functions, like
subspaces, come in dual pairs. The formula is Theorem 12.3 (`conj_comp_affine`) at
`h = δ(· | L)` and `A = I`, fed by `conj_indicatorFn_eq_indicatorFn_polarCone`.

It belongs here rather than in `Duality/Conjugate.lean` because the dual datum is a polar: the
statement cannot be written before `polarCone` exists. Rockafellar makes the same remark about the
subspace example it generalises — "this observation will be broadened at the beginning of §14". -/

section PartialAffine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **A partial affine function** in Rockafellar's normal form: `δ(· | L + a) + ⟨·, b⟩ + α`, for a
subspace `L`, vectors `a` and `b`, and a real `α`. -/
noncomputable def partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) : E → EReal :=
  fun x => indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal)

/-- The defining formula for a partial affine function. -/
theorem partialAffineFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F)
    (α : ℝ) (x : E) : partialAffineFn B L a b α x
      = indicatorFn (a +ᵥ (L : Set E)) x + ((B x b : ℝ) : EReal) + (α : EReal) := rfl

/-- **The conjugate of a partial affine function** (Rockafellar §12, the display preceding
Theorem 12.3): `(δ(· | L + a) + ⟨·, a*⟩ + α)* = δ(· | L^⊥ + a*) + ⟨a, ·⟩ + α*`, where `α*` is
`-α - ⟨a, a*⟩`.

The two sides are the *same* construction read through the polar pairing, which is the sense in
which partial affine functions, like subspaces, come in dual pairs. -/
theorem conj_partialAffineFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : Submodule ℝ E) (a : E) (b : F) (α : ℝ) :
    conj B (partialAffineFn B L a b α)
      = partialAffineFn B.flip (polarSubmodule B L) b a (-α - B a b) := by
  have hcone : conj B (indicatorFn (L : Set E)) = indicatorFn (polarCone B (L : Set E)) :=
    conj_indicatorFn_eq_indicatorFn_polarCone (fun _ hc => smul_coe_submodule L hc)
      ⟨0, L.zero_mem⟩
  have hfun : partialAffineFn B L a b α
      = fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal) + (α : EReal) := by
    funext x
    rw [partialAffineFn_apply, indicatorFn_vadd]
  funext y
  have e : conj B (fun x : E => indicatorFn (L : Set E) (x - a) + ((B x b : ℝ) : EReal)
        + (α : EReal)) y
      = conj B (indicatorFn (L : Set E)) (y - b) + ((B a y : ℝ) : EReal)
        + ((-α - B a b : ℝ) : EReal) :=
    conj_comp_affine (B := B) (B' := B) (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F)
      (fun _ _ => rfl) (indicatorFn (L : Set E)) a b α y
  rw [hfun, e, hcone, partialAffineFn_apply, indicatorFn_vadd, coe_polarSubmodule,
    LinearMap.flip_apply]

end PartialAffine

section ExamplesTopology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- **Rockafellar §14**, dually: the polar of the solution set of the homogeneous inequalities
`⟨aᵢ, y⟩ ≤ 0` is the closure of the convex cone generated by the `aᵢ`. -/
theorem polarCone_setOf_forall_le_zero {ι : Sort*} (a : ι → E) :
    polarCone B.flip {y : F | ∀ i, B (a i) y ≤ 0} =
      closure (PointedCone.hull ℝ (Set.range a) : Set E) := by
  rw [← polarCone_hull_range B a]
  exact polarCone_polarCone
    ((PointedCone.hull ℝ (Set.range a) : ConvexCone ℝ E)).convex
    (smul_coe_pointedCone _) ⟨0, (PointedCone.hull ℝ (Set.range a)).zero_mem⟩

end ExamplesTopology

/-! ### The nonnegative orthant

Rockafellar's second example, in the setting of `biconj_eq_clFn_inner`: a real inner-product
space paired with itself. -/

section Orthant

variable {ι : Type*} [Fintype ι]

/-- **Rockafellar §14**: the polar of the nonnegative orthant is the nonpositive orthant. -/
theorem polarCone_nonnegOrthant :
    polarCone (innerₗ (EuclideanSpace ℝ ι)) {x : EuclideanSpace ℝ ι | ∀ i, 0 ≤ x i} =
      {y : EuclideanSpace ℝ ι | ∀ i, y i ≤ 0} := by
  classical
  ext y
  simp only [mem_polarCone, Set.mem_ofPred, innerₗ_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial]
  constructor
  · intro h i
    have hmem : ∀ j, (0 : ℝ) ≤ (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ ι) j := by
      intro j
      simp only [PiLp.single_apply]
      split <;> norm_num
    have h' := h _ hmem
    simpa using h'
  · intro h x hx
    refine Finset.sum_nonpos fun i _ => ?_
    have hi := mul_le_mul_of_nonneg_right (h i) (hx i)
    simpa using hi

end Orthant

end Tdaf.ConvexAnalysis
