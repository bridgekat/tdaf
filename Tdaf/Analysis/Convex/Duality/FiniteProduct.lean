/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.InnerPairing
import Tdaf.Analysis.Convex.Duality.RelintSeparation

/-!
# Convex analysis on a finite product

A finite product `ι → E` carries a pairing, a notion of product set, and — once `E` is
finite-dimensional — a relative interior, and all three are computed coordinatewise. This file
establishes that dictionary and then reads one theorem through it: a finite family of convex sets
has a common relative-interior point exactly when a certain family of dual vectors summing to zero
does not exist.

## Main definitions

* `piPairing B` — the pairing of `ι → E` with `ι → F` given by `⟨x, y⟩ = ∑ i, ⟨xᵢ, yᵢ⟩`, together
  with the four pairing classes as instances. It is to `Set.pi` what `prodPairing` is to `×ˢ`.

## Main results

* `Convex.relint_univ_pi` — the relative interior of a product of convex sets is the product of
  the relative interiors.
* `supportFn_univ_pi` — the support function of a product set is the sum of the support functions
  of the factors: the supremum of a separable sum over a product splits.
* `iInter_relint_nonempty_iff_supportFn`, `iInter_relint_dom_nonempty_iff` — a finite family of
  convex sets (resp. of effective domains) has a common relative-interior point exactly when there
  is no family `y` with `∑ i, yᵢ = 0`, `∑ i, δ*(yᵢ | Cᵢ) ≤ 0` and `∑ i, δ*(-yᵢ | Cᵢ) > 0`.

## Design notes

**The index is a `Fintype` and the product is non-dependent.** `piPairing` sums over `Finset.univ`,
so finiteness is data, not a proposition; and the only consumer — the diagonal subspace of
`ι → E` — needs all the factors to be the *same* space. `Convex.relint_univ_pi` would hold verbatim
for a dependent product `(i : ι) → E i`; nothing here needs it.

**The separable-sum route is not taken.** A family `f₁, …, fₘ` could be packaged as the single
function `x ↦ ∑ i, fᵢ (xᵢ)` on `ι → E`, whose conjugate is the corresponding separable sum. That
detour needs the conjugate *and* the recession function of a separable sum before it can be used.
Going through `supportFn` instead needs neither: the effective domain of a separable sum is a
product set already, and `recessionFn_conj` converts once, at the end, one coordinate at a time.

**`⊥` absorbs, so the empty factor is a case and not an accident.** `⨆ x ∈ ∅, u x = ⊥` and
`⊥ + z = ⊥`, so `supportFn_univ_pi` is true with no nonemptiness hypothesis — but its two sides are
`⊥` for *different* reasons and the proof splits. The nonempty branch is an induction over the
index `Finset` whose step is `Tdaf.EReal.biSup_add_biSup`, applied after `Function.update` has
decoupled one coordinate from the rest.

## What is not here

**No `m`-ary conjugate or recession function of a separable sum.** The conjugate of
`fun x => ∑ i, f i (x i)` against `piPairing B` is `fun y => ∑ i, conj B (f i) (y i)`, the other
half of the finite-product dictionary; nothing here needs it, and it is left to whoever wants an
`m`-ary infimal convolution.

**No sum map.** The linear map `(xᵢ) ↦ ∑ xᵢ` from `ι → E` to `E` appears only inside the proof of
`iInter_relint_nonempty_iff_supportFn`, as the adjoint of the diagonal; its recession cone and
image theory belong with the other `Set.pi` results in `Recession/Cone.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16 (Corollary 16.2.2),
  §6 (Theorem 6.5) and §13.
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The pairing of a finite product -/

section Pairing

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The pairing of `ι → E` with `ι → F`**, `⟨x, y⟩ = ∑ i, ⟨xᵢ, yᵢ⟩`.

This is `prodPairing` for a finite family instead of two factors, and it is the pairing under
which a product of sets has a separable support function. -/
def piPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (ι → E) →ₗ[ℝ] (ι → F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, B (x i) (y i))
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

@[simp] theorem piPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : ι → E) (y : ι → F) :
    piPairing B x y = ∑ i, B (x i) (y i) := rfl

/-- Flipping the product pairing flips the pairing of the factors. -/
theorem piPairing_flip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    (piPairing (ι := ι) B).flip = piPairing B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

end Pairing

section PairingInstances

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- A finite product of copies of a continuous pairing is continuous. -/
instance instIsContinuousPairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (piPairing (ι := ι) B) where
  continuous_left y := by
    simp only [piPairing_apply]
    exact continuous_finsetSum _ fun i _ => (continuous_pairing B (y i)).comp (continuous_apply i)

/-- A finite product of copies of a compatible pairing is compatible: a continuous linear
functional on `ι → E` is the sum of its restrictions along the coordinate injections, and each
of those is represented by a vector of `F`. -/
instance instIsCompatiblePairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (piPairing (ι := ι) B) where
  toIsContinuousPairing := instIsContinuousPairingPi B
  surjective_eval g := by
    classical
    choose y hy using fun i : ι =>
      exists_pairing_eq B (g.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i))
    refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
    rw [evalCLM_apply, piPairing_apply,
      ← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => E) g x]
    exact Finset.sum_congr rfl fun i _ => (hy i (x i)).symm

end PairingInstances

section InnerInstances

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- A finite product of copies of an inner pairing is an inner pairing. The product carries no
inner-product structure of its own — `ι → E` has the supremum norm — but the pairing does not
care. -/
instance isInnerPairing_piPairing [IsInnerPairing B] : IsInnerPairing (piPairing (ι := ι) B) where
  pairing_comm _ _ := Finset.sum_congr rfl fun i _ => pairing_comm B _ _
  self_nonneg _ := Finset.sum_nonneg fun i _ => self_pairing_nonneg B _
  eq_zero_of_self_eq_zero x h := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => self_pairing_nonneg B (x i)).1 h
    funext i
    exact self_pairing_eq_zero_iff.1 (hzero i (Finset.mem_univ i))

/-- The quadratic form of a finite product of inner pairings is continuous. -/
instance isContinuousInnerPairing_piPairing [TopologicalSpace E] [IsContinuousInnerPairing B] :
    IsContinuousInnerPairing (piPairing (ι := ι) B) where
  continuous_self :=
    continuous_finsetSum _ fun i _ => (continuous_self_pairing' B).comp (continuous_apply i)

end InnerInstances

/-! ### The relative interior of a product set -/

section Relint

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [Finite ι] [FiniteDimensional ℝ E] in
/-- A product set is the intersection of the preimages of its factors under the coordinate
projections. -/
theorem univ_pi_eq_iInter_proj_preimage (C : ι → Set E) :
    univ.pi C = ⋂ i, (LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i := by
  ext x
  simp [Set.mem_pi]

/-- **The relative interior of a product of convex sets is the product of the relative
interiors.** This is the `Set.pi` form of `intrinsicInterior_prod_eq`; unlike that one it needs
finite dimension, because it is `Convex.relint_iInter` applied to the coordinate preimages and
that theorem rests on `ri C ≠ ∅` for nonempty convex `C`. -/
theorem Convex.relint_univ_pi (C : ι → Set E) (hC : ∀ i, Convex ℝ (C i)) :
    ri (univ.pi C) = univ.pi fun i => ri (C i) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  by_cases hne : ∀ i, (C i).Nonempty
  · have hproj : ∀ i, ri ((LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i)
        = (LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' ri (C i) := by
      intro i
      refine Convex.relint_preimage (hC i) _ ?_
      obtain ⟨z, hz⟩ := Convex.relint_nonempty (hC i) (hne i)
      exact ⟨fun _ => z, hz⟩
    choose z hz using fun i => Convex.relint_nonempty (hC i) (hne i)
    have hnonempty : (⋂ i, ri ((LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i)).Nonempty := by
      refine ⟨z, mem_iInter.2 fun i => ?_⟩
      rw [hproj i]
      exact hz i
    rw [univ_pi_eq_iInter_proj_preimage C, univ_pi_eq_iInter_proj_preimage fun i => ri (C i),
      Convex.relint_iInter (fun i => Convex.linear_preimage (hC i) _) hnonempty]
    exact iInter_congr hproj
  · simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hleft : univ.pi C = ∅ := Set.univ_pi_eq_empty_iff.2 ⟨i₀, hi₀⟩
    have hright : (univ.pi fun i => ri (C i)) = ∅ :=
      Set.univ_pi_eq_empty_iff.2 ⟨i₀, by rw [hi₀]; exact intrinsicInterior_empty⟩
    rw [hleft, hright, intrinsicInterior_empty]

end Relint

/-! ### The support function of a product set

The supremum of a separable sum over a product of sets is the sum of the suprema. The proof is an
induction over the index `Finset`: at each step one coordinate is decoupled from the others by
`Function.update`, and `Tdaf.EReal.biSup_add_biSup` splits the resulting supremum of a sum. -/

section Support

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

omit [Fintype ι] in
/-- The supremum over a product set of a sum indexed by a `Finset`, decoupled coordinate by
coordinate. The nonemptiness hypothesis is needed only for the empty `Finset`, where the supremum
of the constant `0` has to be `0` rather than `⊥`. -/
private theorem biSup_sum_univ_pi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {C : ι → Set E}
    (hne : ∀ i, (C i).Nonempty) (y : ι → F) (t : Finset ι) :
    (⨆ x ∈ univ.pi C, ∑ i ∈ t, ((B (x i) (y i) : ℝ) : EReal))
      = ∑ i ∈ t, supportFn B (C i) (y i) := by
  classical
  obtain ⟨x₀, hx₀⟩ : (univ.pi C).Nonempty := Set.univ_pi_nonempty_iff.2 hne
  induction t using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_antisymm (iSup₂_le fun _ _ => le_rfl)
      (le_iSup₂_of_le (f := fun x (_ : x ∈ univ.pi C) => (0 : EReal)) x₀ hx₀ le_rfl)
  | cons i t hi ih =>
    have hgne : ∀ x ∈ univ.pi C, (∑ j ∈ t, ((B (x j) (y j) : ℝ) : EReal)) ≠ ⊥ := by
      intro x _
      rw [← Tdaf.EReal.coe_sum]
      exact _root_.EReal.coe_ne_bot _
    have key : (⨆ x ∈ univ.pi C, (((B (x i) (y i) : ℝ) : EReal)
          + ∑ j ∈ t, ((B (x j) (y j) : ℝ) : EReal)))
        = supportFn B (C i) (y i)
          + ⨆ x ∈ univ.pi C, ∑ j ∈ t, ((B (x j) (y j) : ℝ) : EReal) := by
      rw [supportFn_apply,
        Tdaf.EReal.biSup_add_biSup (fun z _ => _root_.EReal.coe_ne_bot _) hgne]
      refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun z hz => iSup₂_le fun x hx => ?_)
      · exact le_iSup₂_of_le (x i) (hx i (mem_univ i)) (le_iSup₂_of_le x hx le_rfl)
      · refine le_iSup₂_of_le (Function.update x i z) (fun j _ => ?_) ?_
        · rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_self]; exact hz
          · rw [Function.update_of_ne hj]; exact hx j (mem_univ j)
        · have hsum : ∑ j ∈ t, ((B (Function.update x i z j) (y j) : ℝ) : EReal)
              = ∑ j ∈ t, ((B (x j) (y j) : ℝ) : EReal) :=
            Finset.sum_congr rfl fun j hj => by
              rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
          rw [Function.update_self, hsum]
    simp only [Finset.sum_cons]
    rw [key, ih]

/-- **The support function of a product set is the sum of the support functions of its factors.**

No hypothesis is needed. If some factor is empty both sides are `⊥`: the product set is empty on
the left, and on the right the corresponding summand is `⊥` and absorbs. -/
theorem supportFn_univ_pi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : ι → Set E) (y : ι → F) :
    supportFn (piPairing B) (univ.pi C) y = ∑ i, supportFn B (C i) (y i) := by
  classical
  by_cases hne : ∀ i, (C i).Nonempty
  · have hcoe : ∀ x : ι → E,
        ((piPairing B x y : ℝ) : EReal) = ∑ i, ((B (x i) (y i) : ℝ) : EReal) := fun x => by
      rw [piPairing_apply, Tdaf.EReal.coe_sum]
    rw [supportFn_apply]
    simp only [hcoe]
    exact biSup_sum_univ_pi B hne y Finset.univ
  · simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hempty : univ.pi C = ∅ := Set.univ_pi_eq_empty_iff.2 ⟨i₀, hi₀⟩
    rw [← Finset.add_sum_erase _ (fun i => supportFn B (C i) (y i)) (Finset.mem_univ i₀), hi₀]
    simp only [hempty, supportFn_empty]
    exact (_root_.EReal.bot_add _).symm

end Support

/-! ### A common relative interior point of a finite family

The diagonal `{x | x₁ = ⋯ = xₘ}` is a subspace of `ι → E` whose annihilator, under the product
pairing, is the family of `y` summing to zero. So the criterion for a subspace to meet the relative
interior of a convex set, read in `ι → E` at a product set, becomes a criterion for a finite family
of convex sets to have a common relative interior point. -/

section Diagonal

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsCompatiblePairing B]

/-- **A finite family of convex sets has a common relative interior point** exactly when there is
no family `y` of dual vectors summing to zero with `∑ i, δ*(yᵢ | Cᵢ) ≤ 0 < ∑ i, δ*(-yᵢ | Cᵢ)`.

This is `submodule_inter_relint_nonempty_iff_supportFn` in `ι → E`, applied to the diagonal
subspace and the product set `∏ Cᵢ`, whose relative interior and support function are computed
coordinatewise by `Convex.relint_univ_pi` and `supportFn_univ_pi`. Separation on the right of the
pairing is what turns the annihilator of the diagonal into `∑ i, yᵢ = 0`. -/
theorem iInter_relint_nonempty_iff_supportFn (hB : B.SeparatingRight) (C : ι → Set E)
    (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty) :
    (⋂ i, ri (C i)).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, supportFn B (C i) (y i)) ≤ 0 ∧
        0 < ∑ i, supportFn B (C i) (-(y i)) := by
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℝ (ι → E), ∀ x : ι → E, x ∈ L ↔ ∃ z : E, ∀ i, x i = z := by
    refine ⟨LinearMap.range (LinearMap.pi fun _ : ι => LinearMap.id), fun x => ?_⟩
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, fun _ => rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, funext fun i => (hz i).symm⟩
  have hstep := submodule_inter_relint_nonempty_iff_supportFn (B := piPairing B) L
    (convex_pi fun i _ => hC i) (Set.univ_pi_nonempty_iff.2 hne)
  rw [Convex.relint_univ_pi C hC] at hstep
  simp only [supportFn_univ_pi, Pi.neg_apply] at hstep
  have hleft : ((L : Set (ι → E)) ∩ univ.pi fun i => ri (C i)).Nonempty
      ↔ (⋂ i, ri (C i)).Nonempty := by
    constructor
    · rintro ⟨x, hxL, hxpi⟩
      obtain ⟨z, hz⟩ := (hL x).1 hxL
      refine ⟨z, mem_iInter.2 fun i => ?_⟩
      have hmem := hxpi i (mem_univ i)
      rwa [hz i] at hmem
    · rintro ⟨z, hz⟩
      rw [mem_iInter] at hz
      exact ⟨fun _ => z, (hL _).2 ⟨z, fun _ => rfl⟩, fun i _ => hz i⟩
  have hann : ∀ y : ι → F, (∀ x ∈ L, piPairing B x y = 0) ↔ ∑ i, y i = 0 := by
    intro y
    constructor
    · intro h
      refine hB _ fun z => ?_
      have hz := h (fun _ => z) ((hL _).2 ⟨z, fun _ => rfl⟩)
      rw [piPairing_apply] at hz
      rw [map_sum]
      exact hz
    · intro h x hx
      obtain ⟨z, hz⟩ := (hL x).1 hx
      have hval : ∑ i, B (x i) (y i) = B z (∑ i, y i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hz i]
      rw [piPairing_apply, hval, h, map_zero]
  rw [← hleft, hstep]
  exact not_congr (exists_congr fun y => and_congr_left' (hann y))

/-- **A finite family of proper convex functions has a common relative interior point of their
effective domains** exactly when there is no family `y` summing to zero with
`∑ i, (fᵢ* 0⁺)(yᵢ) ≤ 0 < ∑ i, (fᵢ* 0⁺)(-yᵢ)`.

`iInter_relint_nonempty_iff_supportFn` at `Cᵢ = dom fᵢ`, whose support function is the recession
function of `fᵢ*` (`recessionFn_conj`). As in `submodule_inter_relint_dom_nonempty_iff`, properness
of each conjugate is a hypothesis rather than a conclusion; in finite dimensions
`proper_conj_of_proper` supplies it. -/
theorem iInter_relint_dom_nonempty_iff (hB : B.SeparatingRight) (f : ι → E → EReal)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hc : ∀ i, Proper (conj B (f i))) :
    (⋂ i, ri (dom (f i))).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, recessionFn (conj B (f i)) (y i)) ≤ 0 ∧
        0 < ∑ i, recessionFn (conj B (f i)) (-(y i)) := by
  have hrec : ∀ i, recessionFn (conj B (f i)) = supportFn B (dom (f i)) :=
    fun i => recessionFn_conj (hp i) (hc i)
  simp only [hrec]
  exact iInter_relint_nonempty_iff_supportFn hB _ (fun i => (hf i).convex_dom)
    fun i => (hp i).dom_nonempty

end Diagonal

end Tdaf.ConvexAnalysis
