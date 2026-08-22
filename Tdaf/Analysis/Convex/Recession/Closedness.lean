/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Operations.Image
import Tdaf.Analysis.Convex.Recession.Function

/-!
# When is a linear image closed?

Rockafellar's §9. The organising result is **Theorem 9.1**: a linear image `A C` of a convex set is
closed, and its recession cone is the image of the recession cone, as soon as

```
0⁺(cl C) ∩ ker A ⊆ lin (cl C).
```

Everything else in §9 — and Theorem 16.4's constraint qualification, and §27's existence theorems —
is a consequence.

## Main results

* `isClosed_image_of_recessionCone_inter_ker`, `recessionCone_image_of_recessionCone_inter_ker` —
  the two halves of **Theorem 9.1** under the *reduced* hypothesis `0⁺C ∩ ker A ⊆ {0}`.
* `Convex.isClosed_image_closure`, `Convex.closure_image_eq`,
  `Convex.recessionCone_image_closure`, `Convex.closure_image_eq_and_recessionCone` —
  **Theorem 9.1** as Rockafellar states it.
* `image_recessionCone_subset` — the unconditional inclusion.

## Design notes

**One compactness argument, used twice.** Both halves come from the same shape: a decreasing
sequence of nonempty closed convex sets, each with recession cone `{0}`, hence compact
(Theorem 8.4), hence with nonempty intersection (Cantor). For closedness the sets are
`C ∩ A⁻¹(closedBall y (n+1)⁻¹)` and the intersection point maps to `y`; for the recession cone they
are `{z | x₀ + (n+1) • z ∈ C} ∩ A⁻¹{v}` and the intersection point is the direction sought. The
change of variables in the second family is what `recessionCone_preimage_affine` is for: it is what
makes the family *decreasing* rather than merely nonempty.

**The reduction is a direct sum.** Rockafellar's hypothesis says exactly that
`N := 0⁺(cl C) ∩ ker A` is a *subspace* (it is caught inside the lineality space). Splitting
`cl C = N + (cl C ∩ M)` along any complement `M` of `N` leaves the image unchanged, because
`N ⊆ ker A`, and cuts the recession cone down to `0⁺(cl C) ∩ M`, which meets `ker A` only at `0`.
That is `eq_add_inter_of_isCompl_of_le`, and it is why that lemma had to be stated for a subspace
of the lineality space rather than for the lineality space itself.

**Finite-dimensionality is used only through Theorem 8.4.** It enters as
`isCompact_iff_recessionCone_eq_zero`, and it also supplies continuity of `A` and closedness of the
complement `M` for free. The target space needs no finite-dimensionality.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §9 (Theorem 9.1).
-/

open Filter Metric Pointwise Set Topology

namespace Tdaf.ConvexAnalysis

/-! ### Rays in a convex set -/

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- **A ray in a convex set is filled in from its base point**: if `x₀` and `x₀ + c • z` both lie
in `C`, so does `x₀ + b • z` for every `0 ≤ b ≤ c`.

`Convex.add_smul_mem` is the same statement with `b / c` in place of `b`; this form is the one that
comes up when the endpoints are indexed by `ℕ`. -/
theorem _root_.Convex.add_smul_mem_of_le (hC : Convex ℝ C) {x₀ z : E} (hx₀ : x₀ ∈ C) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (h : x₀ + c • z ∈ C) : x₀ + b • z ∈ C := by
  rcases eq_or_lt_of_le (hb.trans hbc) with hc | hc
  · have hb0 : b = 0 := le_antisymm (hbc.trans hc.symm.le) hb
    rw [hb0, zero_smul, add_zero]
    exact hx₀
  · have hmem := hC.add_smul_mem hx₀ h ⟨by positivity, (div_le_one hc).2 hbc⟩
    rwa [smul_smul, div_mul_cancel₀ _ hc.ne'] at hmem

end Ray

/-! ### The unconditional inclusion -/

section Unconditional

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]

/-- **Half of Theorem 9.1, unconditionally**: a linear map carries directions of recession to
directions of recession. No convexity, no closedness, no hypothesis on `A`. -/
theorem image_recessionCone_subset (A : E →ₗ[ℝ] G) (C : Set E) :
    A '' recessionCone C ⊆ recessionCone (A '' C) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩ a ha
  exact ⟨x + a • y, hy x hx a ha, by rw [map_add, map_smul]⟩

end Unconditional

/-! ### Theorem 9.1 under the reduced hypothesis -/

section Reduced

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {C : Set E} {A : E →ₗ[ℝ] G}

/-- **Theorem 9.1**, closedness, under the reduced hypothesis: if a closed convex set recedes in no
direction of `ker A` other than `0`, its image under `A` is closed. -/
theorem isClosed_image_of_recessionCone_inter_ker (A : E →ₗ[ℝ] G) (hC : Convex ℝ C)
    (hC' : IsClosed C) (h : recessionCone C ∩ (LinearMap.ker A : Set E) ⊆ {0}) :
    IsClosed (A '' C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | -
  · simp
  have hA : Continuous A := A.continuous_of_finiteDimensional
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  set t : ℕ → Set E := fun n => C ∩ A ⁻¹' closedBall y ((n : ℝ) + 1)⁻¹ with ht
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hy _ (hpos n)
    exact ⟨x, hx, by simpa [mem_closedBall, dist_comm] using hd.le⟩
  have htconv : ∀ n, Convex ℝ (t n) := fun n =>
    hC.inter ((convex_closedBall y _).linear_preimage A)
  have htcl : ∀ n, IsClosed (t n) := fun n => hC'.inter (isClosed_closedBall.preimage hA)
  have htd : ∀ n, t (n + 1) ⊆ t n := by
    intro n
    simp only [ht]
    refine Set.inter_subset_inter_right _ (Set.preimage_mono (closedBall_subset_closedBall ?_))
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    push_cast
    linarith
  have htrec : ∀ n, recessionCone (t n) = {0} := by
    intro n
    have hpre : (A ⁻¹' closedBall y ((n : ℝ) + 1)⁻¹).Nonempty := (htn n).mono inter_subset_right
    simp only [ht]
    rw [recessionCone_inter hC hC' ((convex_closedBall y _).linear_preimage A)
      (isClosed_closedBall.preimage hA) (htn n),
      recessionCone_preimage_closedBall A y (hpos n).le hpre]
    exact Set.Subset.antisymm h (by simp)
  have ht0 : IsCompact (t 0) :=
    (isCompact_iff_recessionCone_eq_zero (htconv 0) (htcl 0) (htn 0)).2 (htrec 0)
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  refine ⟨x, (Set.mem_iInter.1 hx 0).1, ?_⟩
  have hd : ∀ n : ℕ, dist (A x) y ≤ ((n : ℝ) + 1)⁻¹ := fun n => (Set.mem_iInter.1 hx n).2
  exact dist_le_zero.1 (ge_of_tendsto tendsto_inv_nat_add_one_atTop_nhds_zero (.of_forall hd))

/-- **Theorem 9.1**, recession cones, under the reduced hypothesis. -/
theorem recessionCone_image_of_recessionCone_inter_ker (A : E →ₗ[ℝ] G) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hne : C.Nonempty)
    (h : recessionCone C ∩ (LinearMap.ker A : Set E) ⊆ {0}) :
    recessionCone (A '' C) = A '' recessionCone C := by
  refine Set.Subset.antisymm (fun v hv => ?_) (image_recessionCone_subset A C)
  obtain ⟨x₀, hx₀⟩ := hne
  have hA : Continuous A := A.continuous_of_finiteDimensional
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  set t : ℕ → Set E := fun n => {z | x₀ + ((n : ℝ) + 1) • z ∈ C} ∩ A ⁻¹' {v} with ht
  have hsconv : ∀ n : ℕ, Convex ℝ {z | x₀ + ((n : ℝ) + 1) • z ∈ C} := fun n =>
    convex_preimage_affine_smul hC x₀ _
  have hscl : ∀ n : ℕ, IsClosed {z | x₀ + ((n : ℝ) + 1) • z ∈ C} := fun n =>
    hC'.preimage ((continuous_const_smul _).const_add x₀)
  have htconv : ∀ n, Convex ℝ (t n) := fun n =>
    (hsconv n).inter ((convex_singleton v).linear_preimage A)
  have htcl : ∀ n, IsClosed (t n) := fun n => (hscl n).inter (isClosed_singleton.preimage hA)
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨d, hdC, hdA⟩ : A x₀ + ((n : ℝ) + 1) • v ∈ A '' C :=
      hv (A x₀) ⟨x₀, hx₀, rfl⟩ _ (hpos n).le
    refine ⟨((n : ℝ) + 1)⁻¹ • (d - x₀), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [smul_inv_smul₀ (hpos n).ne']
      have hcancel : x₀ + (d - x₀) = d := by abel
      rw [hcancel]
      exact hdC
    · have : A (((n : ℝ) + 1)⁻¹ • (d - x₀)) = v := by
        rw [map_smul, map_sub, hdA, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ (hpos n).ne', one_smul]
      simpa using this
  have htd : ∀ n, t (n + 1) ⊆ t n := by
    intro n z hz
    refine ⟨?_, hz.2⟩
    refine hC.add_smul_mem_of_le hx₀ (by positivity) ?_ hz.1
    push_cast
    linarith
  have htrec : ∀ n, recessionCone (t n) = {0} := by
    intro n
    have hpre : (A ⁻¹' ({v} : Set G)).Nonempty := (htn n).mono inter_subset_right
    have hker : A ⁻¹' ({0} : Set G) = (LinearMap.ker A : Set E) := by
      ext z; simp [LinearMap.mem_ker]
    simp only [ht]
    rw [recessionCone_inter (hsconv n) (hscl n) ((convex_singleton v).linear_preimage A)
      (isClosed_singleton.preimage hA) (htn n),
      recessionCone_preimage_affine (hpos n) x₀ C,
      recessionCone_preimage A (convex_singleton v) isClosed_singleton hpre,
      recessionCone_singleton v, hker]
    exact Set.Subset.antisymm h (by simp)
  have ht0 : IsCompact (t 0) :=
    (isCompact_iff_recessionCone_eq_zero (htconv 0) (htcl 0) (htn 0)).2 (htrec 0)
  obtain ⟨z, hz⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  refine ⟨z, mem_recessionCone_of_exists_ray hC hC' ⟨x₀, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge a
    exact hC.add_smul_mem_of_le hx₀ ha (hn.trans (by linarith)) (Set.mem_iInter.1 hz n).1
  · simpa using (Set.mem_iInter.1 hz 0).2

end Reduced

/-! ### Theorem 9.1 -/

section Main

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {C : Set E} {A : E →ₗ[ℝ] G}

/-- **The reduction step of Theorem 9.1.** Rockafellar's hypothesis says exactly that
`N := 0⁺(cl C) ∩ ker A` sits inside the lineality space, hence is a subspace. Splitting `cl C`
along any complement `M` of `N` produces a set with the same image, the same image of the
recession cone, and the *reduced* hypothesis `0⁺ ∩ ker A ⊆ {0}`.

Packaged as an existential so that both halves of Theorem 9.1 can consume it. -/
theorem exists_reduction_of_recessionCone_inter_ker (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    ∃ D : Set E, Convex ℝ D ∧ IsClosed D ∧ D.Nonempty ∧
      A '' D = A '' closure C ∧ A '' recessionCone D = A '' recessionCone (closure C) ∧
      recessionCone D ∩ (LinearMap.ker A : Set E) ⊆ {0} := by
  have hD : Convex ℝ (closure C) := hC.closure
  have hD' : IsClosed (closure C) := isClosed_closure
  set N : Submodule ℝ E := linealitySubmodule (closure C) ⊓ LinearMap.ker A with hN
  have hNlin : (N : Set E) ⊆ linealitySpace (closure C) := fun z hz =>
    mem_linealitySubmodule.1 (Submodule.mem_inf.1 hz).1
  have hNker : ∀ z ∈ (N : Set E), A z = 0 := fun z hz =>
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hz).2
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl N
  have hMcl : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  have hsplit : closure C = (N : Set E) + (closure C ∩ (M : Set E)) :=
    eq_add_inter_of_isCompl_of_le hNlin hM
  have hDMne : (closure C ∩ (M : Set E)).Nonempty := by
    obtain ⟨x, hx⟩ := hne.closure
    rw [hsplit] at hx
    obtain ⟨-, -, q, hq, -⟩ := hx
    exact ⟨q, hq⟩
  refine ⟨closure C ∩ (M : Set E), hD.inter M.convex, hD'.inter hMcl, hDMne, ?_, ?_, ?_⟩
  · refine Set.Subset.antisymm (Set.image_mono inter_subset_left) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hsplit] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    exact ⟨q, hq, by rw [map_add, hNker p hp, zero_add]⟩
  · rw [recessionCone_inter hD hD' M.convex hMcl hDMne, recessionCone_coe_submodule]
    refine Set.Subset.antisymm (Set.image_mono inter_subset_left) ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.1 (show z ∈ N ⊔ M by rw [hM.sup_eq_top]; trivial)
    refine ⟨q, ⟨?_, hq⟩, by rw [map_add, hNker p hp, zero_add]⟩
    have hpneg : -p ∈ recessionCone (closure C) := (mem_linealitySpace.1 (hNlin hp)).2
    have hsum := add_mem_recessionCone hz hpneg
    simpa [add_comm, add_assoc] using hsum
  · rw [recessionCone_inter hD hD' M.convex hMcl hDMne, recessionCone_coe_submodule]
    rintro z ⟨⟨hz₁, hz₂⟩, hz₃⟩
    have hzN : z ∈ N :=
      Submodule.mem_inf.2 ⟨mem_linealitySubmodule.2 (h z hz₁ (LinearMap.mem_ker.1 hz₃)), hz₃⟩
    have hbot : z ∈ N ⊓ M := ⟨hzN, hz₂⟩
    rw [hM.inf_eq_bot] at hbot
    simpa using hbot

/-- **Rockafellar, Theorem 9.1**, closedness: if `cl C` recedes in no direction of `ker A` other
than those it also recedes in backwards, then `A (cl C)` is closed. -/
theorem Convex.isClosed_image_closure (hC : Convex ℝ C) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    IsClosed (A '' closure C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hne
  · simp
  obtain ⟨D, hDconv, hDcl, -, himg, -, hred⟩ :=
    exists_reduction_of_recessionCone_inter_ker hC hne A h
  rw [← himg]
  exact isClosed_image_of_recessionCone_inter_ker A hDconv hDcl hred

/-- **Rockafellar, Theorem 9.1**: `cl (A C) = A (cl C)`. -/
theorem Convex.closure_image_eq (hC : Convex ℝ C) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C := by
  refine Set.Subset.antisymm ?_
    (image_closure_subset_closure_image A.continuous_of_finiteDimensional)
  rw [← (Convex.isClosed_image_closure hC A h).closure_eq]
  exact closure_mono (Set.image_mono subset_closure)

/-- **Rockafellar, Theorem 9.1**, recession cones: `0⁺(A (cl C)) = A (0⁺(cl C))`. -/
theorem Convex.recessionCone_image_closure (hC : Convex ℝ C) (hne : C.Nonempty) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    recessionCone (A '' closure C) = A '' recessionCone (closure C) := by
  obtain ⟨D, hDconv, hDcl, hDne, himg, hrec, hred⟩ :=
    exists_reduction_of_recessionCone_inter_ker hC hne A h
  rw [← himg, ← hrec]
  exact recessionCone_image_of_recessionCone_inter_ker A hDconv hDcl hDne hred

/-- **Rockafellar, Theorem 9.1**, both conclusions together, as the plan states it. -/
theorem Convex.closure_image_eq_and_recessionCone (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C ∧
      recessionCone (A '' closure C) = A '' recessionCone (closure C) :=
  ⟨Convex.closure_image_eq hC A h, Convex.recessionCone_image_closure hC hne A h⟩

end Main

/-! ### Corollary 9.1.1: sums of sets -/

section Sum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C D : Set E}

omit [FiniteDimensional ℝ E] in
/-- The sum `C + D` is the image of `C ×ˢ D` under the linear map `(x, y) ↦ x + y`. This is what
turns **Corollary 9.1.1** into an instance of **Theorem 9.1**. -/
theorem image_coprod_id_prod (C D : Set E) :
    (LinearMap.id.coprod LinearMap.id : E × E →ₗ[ℝ] E) '' C ×ˢ D = C + D :=
  Set.add_image_prod

omit [FiniteDimensional ℝ E] in
/-- Rockafellar's hypothesis in Corollary 9.1.1, transported to the product. -/
theorem forall_mem_linealitySpace_prod (hCne : C.Nonempty) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    ∀ p ∈ recessionCone (closure (C ×ˢ D)),
      (LinearMap.id.coprod LinearMap.id : E × E →ₗ[ℝ] E) p = 0 →
        p ∈ linealitySpace (closure (C ×ˢ D)) := by
  rintro ⟨z, w⟩ hp hzero
  rw [closure_prod_eq, recessionCone_prod hCne.closure hDne.closure] at hp
  rw [closure_prod_eq, linealitySpace_prod hCne.closure hDne.closure]
  exact h z hp.1 w hp.2 hzero

/-- **Rockafellar, Corollary 9.1.1**, closedness: the sum of two closed convex sets is closed as
soon as the only way a direction of recession of `C` and a direction of recession of `D` can cancel
is inside the two lineality spaces. -/
theorem Convex.isClosed_add (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) :
    IsClosed (C + D) := by
  have hCcl : closure C = C := hCc.closure_eq
  have hDcl : closure D = D := hDc.closure_eq
  have hkey := forall_mem_linealitySpace_prod hCne hDne (by rw [hCcl, hDcl]; exact h)
  have := Convex.isClosed_image_closure (hC.prod hD) (LinearMap.id.coprod LinearMap.id) hkey
  rwa [closure_prod_eq, hCcl, hDcl, image_coprod_id_prod] at this

/-- **Rockafellar, Corollary 9.1.1**: `cl (C + D) = cl C + cl D`. -/
theorem Convex.closure_add_eq (hC : Convex ℝ C) (hCne : C.Nonempty) (hD : Convex ℝ D)
    (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    closure (C + D) = closure C + closure D := by
  have := Convex.closure_image_eq (hC.prod hD) (LinearMap.id.coprod LinearMap.id)
    (forall_mem_linealitySpace_prod hCne hDne h)
  rwa [image_coprod_id_prod, closure_prod_eq, image_coprod_id_prod] at this

/-- **Rockafellar, Corollary 9.1.1**, recession cones: `0⁺(cl C + cl D) = 0⁺(cl C) + 0⁺(cl D)`. -/
theorem Convex.recessionCone_add (hC : Convex ℝ C) (hCne : C.Nonempty) (hD : Convex ℝ D)
    (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    recessionCone (closure C + closure D) =
      recessionCone (closure C) + recessionCone (closure D) := by
  have := Convex.recessionCone_image_closure (hC.prod hD)
    (hCne.prod hDne) (LinearMap.id.coprod LinearMap.id)
    (forall_mem_linealitySpace_prod hCne hDne h)
  rwa [closure_prod_eq, image_coprod_id_prod,
    recessionCone_prod hCne.closure hDne.closure, image_coprod_id_prod] at this

end Sum

/-! ### Theorem 9.2: images of functions -/

section FnAlg

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {z : E}

/-- Rockafellar's hypothesis for Theorem 9.2 at the level of the epigraph: `(z, 0)` is a direction
of recession of `epi f` exactly when `f` recedes in the direction `z`, and it lies in the lineality
space exactly when `f` is *constant* along `z`. -/
theorem mk_zero_mem_linealitySpace_epi_iff (hp : Proper f) :
    ((z, (0 : ℝ)) : E × ℝ) ∈ linealitySpace (epi f) ↔ z ∈ constancySpace f := by
  rw [mk_mem_linealitySpace_epi_iff hp, mem_constancySpace]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [h₁]; norm_num, by rw [h₂]; norm_num⟩
  · rintro ⟨h₁, h₂⟩
    have hc₁ : recessionFn f z ≤ ((0 : ℝ) : EReal) := by simpa using h₁
    have hc₂ : recessionFn f (-z) ≤ ((0 : ℝ) : EReal) := by simpa using h₂
    have hb₁ : ((0 : ℝ) : EReal) ≤ recessionFn f z :=
      le_recessionFn_of_neg_le hp (ν := 0) (by simpa using hc₂)
    have hb₂ : ((0 : ℝ) : EReal) ≤ recessionFn f (-z) := by
      refine le_recessionFn_of_neg_le hp (ν := 0) ?_
      simpa using hc₁
    exact ⟨le_antisymm hc₁ hb₁, by simpa using le_antisymm hc₂ hb₂⟩

end FnAlg

section Fn

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → EReal} {A : E →ₗ[ℝ] G}

/-- **Rockafellar, Theorem 9.2**: the image of a closed proper convex function under a linear map
is again closed proper convex, and the infimum defining it is attained, provided `f` is *constant*
along every direction of recession that `A` kills.

The three conclusions are packaged together because they come from one application of Theorem 9.1:
the epigraph identity is the statement that the infimum is attained, and closedness and properness
are read off it. -/
theorem closedProperConvexFn_mapLin (hf : ConvexFn f) (hp : Proper f) (hc : IsClosed (epi f))
    (A : E →ₗ[ℝ] G)
    (h : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f ∧
      ClosedProperConvexFn (mapLin A f) := by
  set Aid : E × ℝ →ₗ[ℝ] G × ℝ := A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) with hAid
  have hconv : Convex ℝ (epi f) := hf.convex_epi
  have hclosure : closure (epi f) = epi f := hc.closure_eq
  have hne : (epi f).Nonempty := by
    obtain ⟨x, hx⟩ := hp.dom_nonempty
    obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    exact ⟨(x, r), mk_mem_epi.2 hr.le⟩
  -- Rockafellar's hypothesis, transported to the epigraph
  have hkey : ∀ q ∈ recessionCone (closure (epi f)), Aid q = 0 →
      q ∈ linealitySpace (closure (epi f)) := by
    rintro ⟨w, ν⟩ hq hzero
    rw [hclosure] at hq ⊢
    have hν : ν = 0 := congrArg Prod.snd hzero
    have hw : A w = 0 := congrArg Prod.fst hzero
    subst hν
    exact (mk_zero_mem_linealitySpace_epi_iff hp).2
      (h w (by simpa using recessionFn_le_coe_iff.2 hq) hw)
  have hclosed : IsClosed (Aid '' epi f) := by
    have := Convex.isClosed_image_closure hconv Aid hkey
    rwa [hclosure] at this
  have hrec : recessionCone (Aid '' epi f) = Aid '' recessionCone (epi f) := by
    have := Convex.recessionCone_image_closure hconv hne Aid hkey
    rwa [hclosure] at this
  -- the image of an epigraph is upward closed, hence (being closed) an epigraph
  have hmono : ∀ (y : G) (μ ν : ℝ), (y, μ) ∈ Aid '' epi f → μ ≤ ν → (y, ν) ∈ Aid '' epi f := by
    rintro y μ ν ⟨⟨x, ρ⟩, hxρ, hxy⟩ hμν
    have h₁ : A x = y := congrArg Prod.fst hxy
    have h₂ : ρ = μ := congrArg Prod.snd hxy
    refine ⟨(x, ν), mk_mem_epi.2 ((mk_mem_epi.1 hxρ).trans ?_), ?_⟩
    · exact_mod_cast h₂ ▸ hμν
    · rw [hAid, LinearMap.prodMap_apply, h₁]
      rfl
  have hepi : epi (mapLin A f) = Aid '' epi f :=
    epi_mapLin (IsEpiLike.of_isClosed hmono hclosed)
  refine ⟨hepi, ?_⟩
  -- properness: a vertical line in the image would be a direction of recession `A` kills
  have hnebot : ∀ y : G, mapLin A f y ≠ ⊥ := by
    intro y hbot
    have hline : ∀ μ : ℝ, ((y, μ) : G × ℝ) ∈ Aid '' epi f := fun μ => by
      rw [← hepi]
      exact mk_mem_epi.2 (hbot ▸ bot_le)
    have hray : ((0 : G), (-1 : ℝ)) ∈ recessionCone (Aid '' epi f) := by
      refine mem_recessionCone_of_exists_ray (hconv.linear_image Aid) hclosed
        ⟨(y, 0), fun a ha => ?_⟩
      have : ((y, (0 : ℝ)) : G × ℝ) + a • ((0 : G), (-1 : ℝ)) = (y, -a) := by
        simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [this]
      exact hline (-a)
    rw [hrec] at hray
    obtain ⟨⟨w, ν⟩, hw, hwy⟩ := hray
    have h₁ : A w = 0 := congrArg Prod.fst hwy
    have h₂ : ν = -1 := congrArg Prod.snd hwy
    subst h₂
    have hle : recessionFn f w ≤ ((-1 : ℝ) : EReal) := recessionFn_le_coe_iff.2 hw
    have hconst := h w (hle.trans (by norm_num)) h₁
    have hzero : recessionFn f w = ((0 : ℝ) : EReal) :=
      ((mk_mem_linealitySpace_epi_iff hp).1 ((mk_zero_mem_linealitySpace_epi_iff hp).2 hconst)).1
    rw [hzero, _root_.EReal.coe_le_coe_iff] at hle
    linarith
  have hdomne : (dom (mapLin A f)).Nonempty := by
    rw [dom_mapLin]
    exact hp.dom_nonempty.image A
  exact ClosedProperConvexFn.of_isClosed_epi (convexFn_mapLin A hf)
    (by rw [hepi]; exact hclosed) ⟨hdomne, hnebot⟩

/-- **Rockafellar, Theorem 9.2**, the attainment statement on its own: under the same hypothesis
the infimum defining `(A f) y` is attained whenever it is bounded above by a real. -/
theorem exists_mapLin_eq (hf : ConvexFn f) (hp : Proper f) (hc : IsClosed (epi f))
    (A : E →ₗ[ℝ] G) (h : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f)
    {y : G} {μ : ℝ} (hμ : mapLin A f y ≤ (μ : EReal)) :
    ∃ x : E, A x = y ∧ f x ≤ (μ : EReal) := by
  obtain ⟨hepi, -⟩ := closedProperConvexFn_mapLin hf hp hc A h
  obtain ⟨⟨x, ρ⟩, hxρ, hxy⟩ : ((y, μ) : G × ℝ) ∈ _ := hepi ▸ mk_mem_epi.2 hμ
  refine ⟨x, congrArg Prod.fst hxy, ?_⟩
  have h₂ : ρ = μ := congrArg Prod.snd hxy
  exact h₂ ▸ mk_mem_epi.1 hxρ

end Fn

end Tdaf.ConvexAnalysis
