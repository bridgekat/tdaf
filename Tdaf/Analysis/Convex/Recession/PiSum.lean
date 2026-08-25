/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Recession.Closedness

/-!
# Sums of finitely many convex sets

A sum `C₁ + ⋯ + Cₘ` of subsets of `E` is the image of the product set `∏ Cᵢ ⊆ ι → E` under the
linear map `(xᵢ) ↦ ∑ xᵢ`. That single observation turns every question about the closure and the
recession cone of a finite sum into a question about a linear *image*, which the recession calculus
of a linear map answers.

## Main definitions

* `piSum` — the linear map `(ι → E) →ₗ[ℝ] E`, `x ↦ ∑ i, x i`.

## Main results

* `image_piSum_univ_pi` — `∑ i, C i` is the image of `univ.pi C` under `piSum`.
* `Convex.isClosed_sum`, `Convex.closure_sum_eq`, `Convex.recessionCone_sum` — a finite sum of
  convex sets is closed, has closure the sum of the closures, and has the sum of the recession
  cones as its recession cone, as soon as the only way finitely many directions of recession can
  cancel is inside the lineality spaces.

## Design notes

**This is the two-set development for a family, with the same proofs.** `Convex.isClosed_add` and
its two companions run `Convex.isClosed_image_closure` on `C ×ˢ D` and the codiagonal
`(x, y) ↦ x + y`; the only change here is `Set.pi` for `×ˢ` and `piSum` for the codiagonal. The
binary statements are not consequences of these ones — an `ι` with two elements would deliver them
only up to a transport — so both are kept.

**The index type is a `Fintype`, and the hypothesis is stated on the family, not on pairs.** The
cancellation hypothesis for a family is genuinely `m`-ary: a sum of `m` recession directions may
vanish without any two of them cancelling, so no iteration of the binary hypothesis implies it.

## What is not here

**No `m`-ary Corollary 9.1.2.** The two-set special case "no direction of recession of one is the
opposite of a direction of recession of the other" has no useful `m`-ary reading: the natural
strengthening — that the only cancelling family is the zero family — is already the hypothesis
below with the lineality spaces replaced by `{0}`, and callers with that hypothesis can pass it
directly.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §9 (Theorem 9.1 and
  Corollary 9.1.1).
-/

open Set

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

section Defs

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- **The sum map** `(x₁, …, xₘ) ↦ x₁ + ⋯ + xₘ` of a finite product, as a linear map. It is the
`m`-ary codiagonal, and the sum of finitely many sets is its image on a product set. -/
def piSum : (ι → E) →ₗ[ℝ] E where
  toFun x := ∑ i, x i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

@[simp] theorem piSum_apply (x : ι → E) : (piSum : (ι → E) →ₗ[ℝ] E) x = ∑ i, x i := rfl

/-- **A sum of finitely many sets is the image of their product under the sum map.** This is what
turns the `m`-ary form of Rockafellar's Corollary 9.1.1 into an instance of his Theorem 9.1, and it
is the `Set.pi` form of `image_coprod_id_prod`. -/
theorem image_piSum_univ_pi (C : ι → Set E) :
    (piSum : (ι → E) →ₗ[ℝ] E) '' univ.pi C = ∑ i, C i := by
  ext y
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, fun i => hx i (mem_univ i), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i _ => hg i, rfl⟩

end Defs

section Sum

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {C : ι → Set E}

omit [FiniteDimensional ℝ E] in
/-- The cancellation hypothesis for a family, transported to the product set. A direction of
recession of `∏ cl Cᵢ` is a family of directions of recession of the factors, and the sum map
annihilates it exactly when they cancel. -/
theorem forall_mem_linealitySpace_pi (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    ∀ p ∈ recessionCone (closure (univ.pi C)), (piSum : (ι → E) →ₗ[ℝ] E) p = 0 →
      p ∈ linealitySpace (closure (univ.pi C)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  intro p hp hzero
  rw [closure_pi_set, recessionCone_pi hpine] at hp
  rw [closure_pi_set, linealitySpace_pi hpine]
  exact fun i _ => h p (fun i => hp i (mem_univ i)) hzero i

/-- **Rockafellar, Corollary 9.1.1**, closedness: a finite sum of closed convex sets is closed as
soon as the only way finitely many directions of recession can sum to zero is inside the lineality
spaces. -/
theorem Convex.isClosed_sum (hC : ∀ i, Convex ℝ (C i)) (hCc : ∀ i, IsClosed (C i))
    (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (C i)) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (C i)) :
    IsClosed (∑ i, C i) := by
  have hcl : ∀ i, closure (C i) = C i := fun i => (hCc i).closure_eq
  have hkey := forall_mem_linealitySpace_pi hne (by simp only [hcl]; exact h)
  have hmain := Convex.isClosed_image_closure (convex_pi fun i _ => hC i) piSum hkey
  rw [closure_pi_set] at hmain
  simp only [hcl] at hmain
  rwa [image_piSum_univ_pi] at hmain

/-- **Rockafellar, Corollary 9.1.1**: `cl (C₁ + ⋯ + Cₘ) = cl C₁ + ⋯ + cl Cₘ`. -/
theorem Convex.closure_sum_eq (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    closure (∑ i, C i) = ∑ i, closure (C i) := by
  have hmain := Convex.closure_image_eq (convex_pi fun i _ => hC i) piSum
    (forall_mem_linealitySpace_pi hne h)
  rwa [image_piSum_univ_pi, closure_pi_set, image_piSum_univ_pi] at hmain

/-- **Rockafellar, Corollary 9.1.1**, recession cones:
`0⁺(cl C₁ + ⋯ + cl Cₘ) = 0⁺(cl C₁) + ⋯ + 0⁺(cl Cₘ)`. -/
theorem Convex.recessionCone_sum (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty)
    (h : ∀ z : ι → E, (∀ i, z i ∈ recessionCone (closure (C i))) → ∑ i, z i = 0 →
      ∀ i, z i ∈ linealitySpace (closure (C i))) :
    recessionCone (∑ i, closure (C i)) = ∑ i, recessionCone (closure (C i)) := by
  have hpine : (univ.pi fun i => closure (C i)).Nonempty :=
    Set.univ_pi_nonempty_iff.2 fun i => (hne i).closure
  have hmain := Convex.recessionCone_image_closure (convex_pi fun i _ => hC i)
    (Set.univ_pi_nonempty_iff.2 hne) piSum (forall_mem_linealitySpace_pi hne h)
  rwa [closure_pi_set, image_piSum_univ_pi, recessionCone_pi hpine,
    image_piSum_univ_pi] at hmain

end Sum

end Tdaf.ConvexAnalysis
