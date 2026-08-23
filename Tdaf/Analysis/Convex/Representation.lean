/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Face
import Tdaf.Analysis.Convex.HullDirections
import Tdaf.Analysis.Convex.Recession.Cone

/-!
# Internal representation of a closed convex set

The second half of Rockafellar's §18.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §18.
-/

open Set Bornology

open scoped Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Lines, extreme directions, and half-line faces -/

section Directions

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C C' : Set E} {x y : E}

/-- `C` **contains no line**: no full line lies in `C`. Rockafellar's standing hypothesis in
Theorems 18.5 and 18.7. For a nonempty closed convex set it says that the lineality space is
trivial (`containsNoLine_iff_linealitySpace_eq_zero`), but unlike that formulation it is also
correct for `C = ∅`. -/
def ContainsNoLine (C : Set E) : Prop := ∀ x y : E, y ≠ 0 → ∃ t : ℝ, x + t • y ∉ C

/-- A subset of a set containing no line contains no line. -/
theorem ContainsNoLine.mono (h : ContainsNoLine C) (hC' : C' ⊆ C) : ContainsNoLine C' := by
  intro x y hy
  obtain ⟨t, ht⟩ := h x y hy
  exact ⟨t, fun hmem => ht (hC' hmem)⟩

@[simp]
theorem containsNoLine_empty : ContainsNoLine (∅ : Set E) := fun x _ _ => ⟨0, by simp⟩

/-- `y` generates an **extreme direction** of `C`: `y ≠ 0` and some closed half-line in the
direction of `y` is a face of `C`. Rockafellar's *extreme direction* is the direction of such a
half-line face; representing it by a generating vector avoids a quotient, at the cost of the set
`extremeDirections C` being closed under multiplication by positive scalars. -/
def IsExtremeDirection (C : Set E) (y : E) : Prop :=
  y ≠ 0 ∧ ∃ x, IsFace C (halfLine x y)

/-- The set of vectors that generate extreme directions of `C`. -/
def extremeDirections (C : Set E) : Set E := {y | IsExtremeDirection C y}

theorem mem_extremeDirections : y ∈ extremeDirections C ↔ IsExtremeDirection C y := Iff.rfl

/-- Extreme directions do not change under positive rescaling of the generator. -/
theorem IsExtremeDirection.smul (h : IsExtremeDirection C y) {a : ℝ} (ha : 0 < a) :
    IsExtremeDirection C (a • y) :=
  ⟨smul_ne_zero ha.ne' h.1, by
    obtain ⟨x, hx⟩ := h.2
    exact ⟨x, by rwa [halfLine_smul x y ha]⟩⟩

/-- An extreme direction of a face of `C` is an extreme direction of `C`: this is `IsFace.trans`. -/
theorem IsFace.extremeDirections_subset (h : IsFace C C') :
    extremeDirections C' ⊆ extremeDirections C := by
  rintro y ⟨hy, x, hx⟩
  exact ⟨hy, x, h.trans hx⟩

/-- The half-line in an extreme direction lies in `C`. -/
theorem IsExtremeDirection.halfLine_subset (h : IsExtremeDirection C y) :
    ∃ x, halfLine x y ⊆ C := by
  obtain ⟨-, x, hx⟩ := h
  exact ⟨x, hx.subset⟩

end Directions

section DirectionsTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C : Set E} {x y : E}

/-- A line inside a convex set is a line of directions in the lineality space. -/
theorem mem_linealitySpace_of_forall_add_smul_mem (hC : Convex ℝ C) (hCcl : IsClosed C)
    (h : ∀ t : ℝ, x + t • y ∈ C) : y ∈ linealitySpace C := by
  refine mem_linealitySpace.2 ⟨mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a _ => h a⟩, ?_⟩
  refine mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a _ => ?_⟩
  have heq : x + a • (-y) = x + (-a) • y := by module
  rw [heq]
  exact h (-a)

/-- **"Contains no line" is lineality zero**, for a nonempty closed convex set. -/
theorem containsNoLine_iff_linealitySpace_eq_zero (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hne : C.Nonempty) : ContainsNoLine C ↔ linealitySpace C = {0} := by
  constructor
  · intro h
    refine subset_antisymm (fun y hy => ?_) ?_
    · by_contra hy0
      obtain ⟨x, hx⟩ := hne
      obtain ⟨t, ht⟩ := h x y hy0
      rcases le_or_gt 0 t with hpos | hneg
      · exact ht (add_smul_mem_of_mem_recessionCone hy.1 hx hpos)
      · have hmem := add_smul_mem_of_mem_recessionCone (mem_linealitySpace.1 hy).2 hx
          (le_of_lt (neg_pos.2 hneg))
        have heq : x + (-t) • (-y) = x + t • y := by module
        rw [heq] at hmem
        exact ht hmem
    · simp
  · intro h x y hy0
    by_contra hall
    push Not at hall
    have hy : y ∈ linealitySpace C := mem_linealitySpace_of_forall_add_smul_mem hC hCcl hall
    rw [h] at hy
    exact hy0 hy

/-- An extreme direction is a direction of recession: **Theorem 8.3** applied to the half-line
face. -/
theorem extremeDirections_subset_recessionCone (hC : Convex ℝ C) (hCcl : IsClosed C) :
    extremeDirections C ⊆ recessionCone C := by
  rintro y ⟨-, x, hx⟩
  exact mem_recessionCone_of_exists_ray hC hCcl ⟨x, fun a ha => hx.subset ⟨a, ha, rfl⟩⟩

end DirectionsTopology

/-! ### Relatively open closed convex sets are affine -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x d : E}

omit [FiniteDimensional ℝ E] in
/-- **A closed convex set that coincides with its relative interior contains whole lines.** If
`C ⊆ ri C` then, for every `x ∈ C` and every direction `d` of the affine hull of `C`, the entire
line `x + ℝ d` lies in `C`.

This is what makes the exceptional cases of Theorem 18.4 exceptional: it is why a closed convex set
with empty relative boundary is an affine set (`affineSpan_subset_of_subset_relint`), and why such
a set of positive dimension contains a line. -/
theorem forall_add_smul_mem_of_subset_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hsub : C ⊆ ri C) (hx : x ∈ C) (hd : d ∈ vectorSpan ℝ C) (t : ℝ) : x + t • d ∈ C := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simpa using hx
  set J : Set ℝ := {s : ℝ | x + s • d ∈ C} with hJdef
  have hline : ∀ s : ℝ, x + s • d ∈ affineSpan ℝ C := by
    intro s
    have hv : s • d ∈ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ s hd
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv (subset_affineSpan ℝ C hx)
    rwa [vadd_eq_add, add_comm] at hmem
  have hJclosed : IsClosed J := hCcl.preimage (by fun_prop)
  have hJconv : Convex ℝ J := by
    intro u hu v hv a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hval : a • (x + u • d) + (1 - a) • (x + v • d)
        = x + (a * u + (1 - a) * v) • d := by module
    have hmem : a • (x + u • d) + (1 - a) • (x + v • d) ∈ C := hC hu hv ha hb hab
    rw [hval] at hmem
    exact hmem
  have hJ0 : (0 : ℝ) ∈ J := by
    change x + (0 : ℝ) • d ∈ C
    simpa using hx
  -- from a point of `J` one can always move a little further away from `0`
  have hkey : ∀ s ∈ J, ∃ μ > (1 : ℝ), μ * s ∈ J := by
    intro s hs
    obtain ⟨μ, hμ, hw⟩ :=
      exists_one_lt_smul_mem_of_mem_relint (hsub hs) (subset_affineSpan ℝ C hx)
    refine ⟨μ, hμ, ?_⟩
    have hval : (1 - μ) • x + μ • (x + s • d) = x + (μ * s) • d := by module
    rwa [hval] at hw
  -- `J` contains a small positive and a small negative parameter
  obtain ⟨-, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 (hsub hx)
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hsmall : ∀ s : ℝ, |s| * ‖d‖ < ε → s ∈ J := by
    intro s hs
    refine hball _ (hline s) ?_
    have he : x + s • d - x = s • d := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    exact hs
  set t₀ : ℝ := ε / (2 * ‖d‖) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀val : t₀ * ‖d‖ = ε / 2 := by rw [ht₀]; field_simp
  have ht₀J : t₀ ∈ J := hsmall t₀ (by rw [abs_of_pos ht₀pos, ht₀val]; linarith)
  have hnt₀J : -t₀ ∈ J := hsmall (-t₀) (by rw [abs_neg, abs_of_pos ht₀pos, ht₀val]; linarith)
  -- hence `J` is unbounded in both directions, and convex, so `J = ℝ`
  have hup : ¬ BddAbove J := by
    intro hbdd
    have hmem : sSup J ∈ J := hJclosed.csSup_mem ⟨0, hJ0⟩ hbdd
    obtain ⟨μ, hμ, hμJ⟩ := hkey _ hmem
    have hle : t₀ ≤ sSup J := le_csSup hbdd ht₀J
    have : sSup J < μ * sSup J := by nlinarith
    exact absurd (le_csSup hbdd hμJ) (not_le.2 this)
  have hdown : ¬ BddBelow J := by
    intro hbdd
    have hmem : sInf J ∈ J := hJclosed.csInf_mem ⟨0, hJ0⟩ hbdd
    obtain ⟨μ, hμ, hμJ⟩ := hkey _ hmem
    have hle : sInf J ≤ -t₀ := csInf_le hbdd hnt₀J
    have : μ * sInf J < sInf J := by nlinarith
    exact absurd (csInf_le hbdd hμJ) (not_le.2 this)
  obtain ⟨a, haJ, hat⟩ : ∃ a ∈ J, a < t := by
    by_contra hcon
    push Not at hcon
    exact hdown ⟨t, fun a ha => hcon a ha⟩
  obtain ⟨b, hbJ, htb⟩ : ∃ b ∈ J, t < b := by
    by_contra hcon
    push Not at hcon
    exact hup ⟨t, fun b hb => hcon b hb⟩
  have hba : (0 : ℝ) < b - a := by linarith
  refine hJconv.segment_subset haJ hbJ ⟨(b - t) / (b - a), (t - a) / (b - a),
    div_nonneg (by linarith) hba.le, div_nonneg (by linarith) hba.le, by field_simp; ring, ?_⟩
  simp only [smul_eq_mul]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- **A closed convex set that coincides with its relative interior is an affine set.** -/
theorem affineSpan_subset_of_subset_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hsub : C ⊆ ri C) : (affineSpan ℝ C : Set E) ⊆ C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  intro u hu
  have hd : u - x ∈ vectorSpan ℝ C := by
    rw [← direction_affineSpan]
    simpa using AffineSubspace.vsub_mem_direction hu (subset_affineSpan ℝ C hx)
  have := forall_add_smul_mem_of_subset_relint hC hCcl hsub hx hd 1
  simpa using this

end Affine

/-! ### Theorem 18.4 -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x d : E}

omit [FiniteDimensional ℝ E] in
/-- **The analytic core of Theorem 18.4.** If the line through a relative interior point `x` of a
closed set `C`, in a direction `d` of the affine hull of `C`, meets `C` in a bounded set, then `x`
lies on a segment joining two points of `C` that are not relative interior points: the two ends of
that bounded intersection.

`Face.lean`'s `exists_notMem_relint_mem_segment` is the case where `C` itself is compact and `d` is
chosen arbitrarily. Convexity of `C` is not used. -/
theorem exists_notMem_relint_mem_segment_of_isBounded (hCcl : IsClosed C) (hd0 : d ≠ 0)
    (hd : d ∈ vectorSpan ℝ C) (hx : x ∈ ri C)
    (hbdd : IsBounded {t : ℝ | x + t • d ∈ C}) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hxC : x ∈ C := intrinsicInterior_subset hx
  set T : Set ℝ := {t : ℝ | x + t • d ∈ C} with hTdef
  have hline : ∀ t : ℝ, x + t • d ∈ affineSpan ℝ C := by
    intro t
    have hv : t • d ∈ (affineSpan ℝ C).direction := by
      rw [direction_affineSpan]
      exact Submodule.smul_mem _ t hd
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv (subset_affineSpan ℝ C hxC)
    rwa [vadd_eq_add, add_comm] at hmem
  have hcont : Continuous fun t : ℝ => x + t • d := by fun_prop
  have hTclosed : IsClosed T := hCcl.preimage hcont
  have hTcomp : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTclosed hbdd
  have hT0 : (0 : ℝ) ∈ T := by
    change x + (0 : ℝ) • d ∈ C
    simpa using hxC
  obtain ⟨tp, htp⟩ := hTcomp.exists_isGreatest ⟨0, hT0⟩
  obtain ⟨tm, htm⟩ := hTcomp.exists_isLeast ⟨0, hT0⟩
  obtain ⟨hxA, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 hx
  set s : ℝ := ε / (2 * ‖d‖) with hsdef
  have hspos : 0 < s := by positivity
  have hsT : ∀ u : ℝ, |u| ≤ s → u ∈ T := by
    intro u hu
    refine hball _ (hline u) ?_
    have he : x + u • d - x = u • d := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    have hprod : |u| * ‖d‖ ≤ s * ‖d‖ := by nlinarith
    have hs' : s * ‖d‖ = ε / 2 := by
      rw [hsdef]
      field_simp
    linarith [hs' ▸ hprod]
  have htppos : 0 < tp := lt_of_lt_of_le hspos (htp.2 (hsT s (le_of_eq (abs_of_pos hspos))))
  have htmneg : tm < 0 := by
    have hle := htm.2 (hsT (-s) (by rw [abs_neg, abs_of_pos hspos]))
    linarith
  have hgap : (0 : ℝ) < tp - tm := by linarith
  refine ⟨x + tm • d, htm.1, x + tp • d, htp.1, ?_, ?_, ?_⟩
  · intro hari
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hari (hline tp)
    have heq : (1 - μ) • (x + tp • d) + μ • (x + tm • d)
        = x + ((1 - μ) * tp + μ * tm) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tp + μ * tm ∈ T := hw
    nlinarith [htm.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · intro hbri
    obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hbri (hline tm)
    have heq : (1 - μ) • (x + tm • d) + μ • (x + tp • d)
        = x + ((1 - μ) * tm + μ * tp) • d := by module
    rw [heq] at hw
    have hmem : (1 - μ) * tm + μ * tp ∈ T := hw
    nlinarith [htp.2 hmem, mul_pos (sub_pos.2 hμ) hgap]
  · refine ⟨tp / (tp - tm), -tm / (tp - tm), div_nonneg htppos.le hgap.le,
      div_nonneg (neg_nonneg.2 htmneg.le) hgap.le, by field_simp; ring, ?_⟩
    match_scalars <;> field_simp <;> ring

/-- **Rockafellar, Theorem 18.4**, in the form the proof produces: if the relative boundary of a
closed convex set `C` is *not convex*, then every relative interior point of `C` lies on a segment
joining two relative boundary points.

Rockafellar's own hypothesis — that `C` is neither an affine set nor a closed half of an affine
set — is equivalent to this one; see `exists_notMem_relint_mem_segment_of_not_isAffineHalf`.

The proof is his: non-convexity of the relative boundary produces two relative boundary points
`p ≠ q` whose segment meets `ri C`, the line through them meets `C` in exactly that segment
(Theorem 6.1), so every parallel line meets `C` in a bounded set (**Corollary 8.4.1**), and the
analytic core does the rest. -/
theorem exists_notMem_relint_mem_segment_of_not_convex (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hD : ¬ Convex ℝ (C \ ri C)) (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b := by
  -- a failure of convexity of the relative boundary
  obtain ⟨p, hp, q, hq, a, b, ha, hb, hab, hw⟩ :
      ∃ p ∈ C \ ri C, ∃ q ∈ C \ ri C, ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • p + b • q ∉ C \ ri C := by
    by_contra hcon
    push Not at hcon
    refine hD ?_
    intro p hp q hq a b ha hb hab
    exact hcon p hp q hq a b ha hb hab
  have hwC : a • p + b • q ∈ C := hC hp.1 hq.1 ha hb hab
  have hwri : a • p + b • q ∈ ri C := by
    by_contra hcon
    exact hw ⟨hwC, hcon⟩
  -- both coefficients are positive, and the two boundary points are distinct
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      have ha1 : a = 1 := by linarith
      rw [ha1, ← h] at hwri
      simp only [one_smul, zero_smul, add_zero] at hwri
      exact hp.2 hwri
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exfalso
      have hb1 : b = 1 := by linarith
      rw [hb1, ← h] at hwri
      simp only [one_smul, zero_smul, zero_add] at hwri
      exact hq.2 hwri
  have hb1 : b < 1 := by linarith
  set d : E := q - p with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef, sub_ne_zero]
    intro hpq
    have hpp : a • p + b • q = p := by
      rw [hpq, ← add_smul, hab, one_smul]
    rw [hpp] at hwri
    exact hp.2 hwri
  have hdmem : d ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ hq.1 hp.1
  have hwd : a • p + b • q = p + b • d := by
    have haa : a = 1 - b := by linarith
    rw [hddef, haa]
    module
  rw [hwd] at hwri
  -- the line through `p` and `q` meets `C` in the segment between them
  have hJ : ∀ t : ℝ, p + t • d ∈ C → 0 ≤ t ∧ t ≤ 1 := by
    intro t ht
    constructor
    · by_contra hcon
      push Not at hcon
      set c : ℝ := b / (b - t) with hcdef
      have hbt : 0 < b - t := by linarith
      have hc0 : 0 ≤ c := by positivity
      have hc1 : c < 1 := by
        rw [hcdef, div_lt_one hbt]
        linarith
      have hmem := Convex.segment_mem_relint hC hwri (subset_closure ht) hc0 hc1
      have heq : (1 - c) • (p + b • d) + c • (p + t • d) = p + ((1 - c) * b + c * t) • d := by
        module
      have hzero : (1 - c) * b + c * t = 0 := by
        rw [hcdef]
        field_simp
        ring
      rw [heq, hzero, zero_smul, add_zero] at hmem
      exact hp.2 hmem
    · by_contra hcon
      push Not at hcon
      set c : ℝ := (1 - b) / (t - b) with hcdef
      have hbt : 0 < t - b := by linarith
      have hc0 : 0 ≤ c := by positivity
      have hc1 : c < 1 := by
        rw [hcdef, div_lt_one hbt]
        linarith
      have hmem := Convex.segment_mem_relint hC hwri (subset_closure ht) hc0 hc1
      have heq : (1 - c) • (p + b • d) + c • (p + t • d) = p + ((1 - c) * b + c * t) • d := by
        module
      have hone : (1 - c) * b + c * t = 1 := by
        rw [hcdef]
        field_simp
        ring
      rw [heq, hone, one_smul, hddef] at hmem
      have hpq : p + (q - p) = q := by abel
      rw [hpq] at hmem
      exact hq.2 hmem
  -- hence every parallel line meets `C` in a bounded set (Corollary 8.4.1)
  set W : Submodule ℝ E := Submodule.span ℝ {d} with hWdef
  set M : AffineSubspace ℝ E := AffineSubspace.mk' p W with hMdef
  set N : AffineSubspace ℝ E := AffineSubspace.mk' x W with hNdef
  have hMdir : M.direction = W := AffineSubspace.direction_mk' p W
  have hNdir : N.direction = W := AffineSubspace.direction_mk' x W
  have hMne : ((M : Set E) ∩ C).Nonempty := ⟨p, AffineSubspace.self_mem_mk' p W, hp.1⟩
  have hMbdd : IsBounded ((M : Set E) ∩ C) := by
    refine (Metric.isBounded_closedBall (x := p) (r := ‖d‖)).subset ?_
    rintro z ⟨hzM, hzC⟩
    rw [SetLike.mem_coe, hMdef, AffineSubspace.mem_mk', vsub_eq_sub, hWdef,
      Submodule.mem_span_singleton] at hzM
    obtain ⟨t, ht⟩ := hzM
    have hz : z = p + t • d := by rw [ht]; abel
    rw [hz] at hzC
    obtain ⟨ht0, ht1⟩ := hJ t hzC
    rw [Metric.mem_closedBall, dist_eq_norm, hz]
    have he : p + t • d - p = t • d := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖d‖ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg d)
      _ = ‖d‖ := one_mul _
  have hNbdd : IsBounded ((N : Set E) ∩ C) :=
    isBounded_inter_of_direction_eq hC hCcl (by rw [hMdir, hNdir]) hMne hMbdd
  have hTbdd : IsBounded {t : ℝ | x + t • d ∈ C} := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hNbdd
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hd0
    refine Bornology.IsBounded.subset (Metric.isBounded_Icc (-(R / ‖d‖)) (R / ‖d‖)) ?_
    intro t ht
    have hxN : x + t • d ∈ N := by
      rw [hNdef, AffineSubspace.mem_mk', vsub_eq_sub, hWdef, Submodule.mem_span_singleton]
      exact ⟨t, by abel⟩
    have hmem : x + t • d ∈ Metric.closedBall x R := hR ⟨hxN, ht⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    have he : x + t • d - x = t • d := by abel
    rw [he, norm_smul, Real.norm_eq_abs] at hmem
    exact Set.mem_Icc.2 (abs_le.1 ((le_div_iff₀ hdnorm).2 hmem))
  exact exists_notMem_relint_mem_segment_of_isBounded hCcl hd0 hdmem hx hTbdd

end Segment

/-! ### Affine sets and closed halves of affine sets -/

section AffineHalf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x : E}

/-- `C` is **an affine set or a closed half of an affine set**: the intersection of its own affine
hull with a closed half-space. Rockafellar's two exceptional cases in Theorem 18.4 are one
predicate here, because the degenerate choice `φ = 0`, `α = 0` gives exactly the affine sets. -/
def IsAffineHalf (C : Set E) : Prop :=
  ∃ (φ : E →ₗ[ℝ] ℝ) (α : ℝ), C = (affineSpan ℝ C : Set E) ∩ {x | φ x ≤ α}

omit [FiniteDimensional ℝ E] in
/-- An affine set is a (degenerate) closed half of an affine set. -/
theorem isAffineHalf_of_affineSpan_subset (h : (affineSpan ℝ C : Set E) ⊆ C) : IsAffineHalf C :=
  ⟨0, 0, subset_antisymm (fun x hx => ⟨subset_affineSpan ℝ C hx, by simp⟩) fun _ hx => h hx.1⟩

/-- **The exceptional sets of Theorem 18.4 are exactly those whose relative boundary is convex.**
If the relative boundary of a closed convex set `C` is convex, then `C` is an affine set or a
closed half of one.

This is the first half of Rockafellar's proof of Theorem 18.4, run forwards instead of by
contradiction: a supporting hyperplane at a relative interior point of the relative boundary
(**Corollary 11.6.2**) contains the whole relative boundary, `ri C` lies strictly on one side of
it, and every point of `aff C` strictly on that side already lies in `C`. -/
theorem isAffineHalf_of_convex_sdiff_relint (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hD : Convex ℝ (C \ ri C)) : IsAffineHalf C := by
  rcases Set.eq_empty_or_nonempty (C \ ri C) with hempty | hDne
  · refine isAffineHalf_of_affineSpan_subset (affineSpan_subset_of_subset_relint hC hCcl ?_)
    intro z hz
    by_contra hcon
    exact (Set.eq_empty_iff_forall_notMem.1 hempty z) ⟨hz, hcon⟩
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hD hDne
  have hzD : z ∈ C \ ri C := intrinsicInterior_subset hz
  obtain ⟨g, hgmax, y, hyC, hgy⟩ := (notMem_relint_iff_exists_isMaxOn hC hzD.1).1 hzD.2
  set φ : E →ₗ[ℝ] ℝ := (g : E →ₗ[ℝ] ℝ) with hφdef
  set α : ℝ := g z with hαdef
  -- the relative boundary lies in the hyperplane `φ = α`
  have hDeq : ∀ w ∈ C \ ri C, φ w = α :=
    eq_of_isMaxOn_of_mem_relint (φ := φ) hz fun u hu => hgmax u hu.1
  -- the relative interior lies strictly below it
  have hrilt : ∀ w ∈ ri C, φ w < α := by
    intro w hw
    rcases lt_or_eq_of_le (hgmax w (intrinsicInterior_subset hw)) with h | h
    · exact h
    · exfalso
      have hconst := eq_of_isMaxOn_of_mem_relint (φ := φ) hw
        (fun u hu => by rw [show φ w = α from h]; exact hgmax u hu) y hyC
      exact hgy (hconst.trans (show φ w = α from h))
  -- every point of `aff C` strictly below the hyperplane is already in `C`
  have hkey : ∀ u ∈ affineSpan ℝ C, φ u < α → u ∈ C := by
    intro u huA hult
    by_contra huC
    obtain ⟨v, hv⟩ := Convex.relint_nonempty hC ⟨z, hzD.1⟩
    have hvC : v ∈ C := intrinsicInterior_subset hv
    set K : Set ℝ := {t : ℝ | 0 ≤ t ∧ (1 - t) • v + t • u ∈ C} with hKdef
    have hKcl : IsClosed K := by
      refine IsClosed.inter isClosed_Ici (hCcl.preimage (by fun_prop))
    have hKconv : Convex ℝ K := by
      rintro t₁ ⟨ht₁, hm₁⟩ t₂ ⟨ht₂, hm₂⟩ a b ha hb hab
      refine ⟨by positivity, ?_⟩
      have hb' : b = 1 - a := by linarith
      subst hb'
      have hval : a • ((1 - t₁) • v + t₁ • u) + (1 - a) • ((1 - t₂) • v + t₂ • u)
          = (1 - (a * t₁ + (1 - a) * t₂)) • v + (a * t₁ + (1 - a) * t₂) • u := by module
      have hmem := hC hm₁ hm₂ ha hb hab
      rw [hval] at hmem
      simpa using hmem
    have hK0 : (0 : ℝ) ∈ K := ⟨le_rfl, by simpa using hvC⟩
    have hK1 : (1 : ℝ) ∉ K := by
      rintro ⟨-, hmem⟩
      exact huC (by simpa using hmem)
    have hKle : ∀ t ∈ K, t ≤ 1 := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have ht0 : (0 : ℝ) < t := by linarith
      have hmem := hKconv hK0 ht (a := 1 - 1 / t) (b := 1 / t)
        (by rw [sub_nonneg, div_le_one ht0]; linarith) (by positivity)
        (by field_simp; ring)
      have hval : (1 - 1 / t) • (0 : ℝ) + (1 / t) • t = 1 := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rw [hval] at hmem
      exact hK1 hmem
    have hbdd : BddAbove K := ⟨1, hKle⟩
    have hmax : sSup K ∈ K := hKcl.csSup_mem ⟨0, hK0⟩ hbdd
    set s : ℝ := sSup K with hsdef
    have hs1 : s < 1 := lt_of_le_of_ne (hKle s hmax) (fun h => hK1 (h ▸ hmax))
    have hs0 : 0 ≤ s := hmax.1
    set p : E := (1 - s) • v + s • u with hpdef
    have hpC : p ∈ C := hmax.2
    -- `p` is a relative boundary point, so `φ p = α`; but `φ p < α`
    have hpri : p ∉ ri C := by
      intro hpri
      have hwA : (1 - (-1 : ℝ)) • p + (-1 : ℝ) • u ∈ affineSpan ℝ C :=
        AffineSubspace.combo_mem (subset_affineSpan ℝ C hpC) huA (-1)
      obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hpri hwA
      set t' : ℝ := s + (μ - 1) * (1 - s) with ht'
      have hval : (1 - μ) • ((1 - (-1 : ℝ)) • p + (-1 : ℝ) • u) + μ • p
          = (1 - t') • v + t' • u := by
        rw [hpdef, ht']
        module
      rw [hval] at hmem
      have ht'K : t' ∈ K := ⟨by nlinarith, hmem⟩
      have : s < t' := by nlinarith
      exact absurd (le_csSup hbdd ht'K) (not_le.2 this)
    have hpα : φ p = α := hDeq p ⟨hpC, hpri⟩
    have hvlt : φ v < α := hrilt v hv
    have hpval : φ p = (1 - s) * φ v + s * φ u := by
      rw [hpdef]
      simp [map_add, map_smul]
    rw [hpval] at hpα
    nlinarith
  -- assemble: `C = aff C ∩ {φ ≤ α}`
  refine ⟨φ, α, ?_⟩
  set K : Set E := (affineSpan ℝ C : Set E) ∩ {w | φ w ≤ α} with hKdef
  have hCK : C ⊆ K := fun w hw => ⟨subset_affineSpan ℝ C hw, hgmax w hw⟩
  have hKconv : Convex ℝ K :=
    (AffineSubspace.convex _).inter (convex_halfSpace_le (LinearMap.isLinear φ) α)
  have hKcl : IsClosed K :=
    (affineSpan ℝ C).closed_of_finiteDimensional.inter
      (isClosed_le (map_continuous g) continuous_const)
  have hriK : ri K ⊆ C := by
    intro w hw
    have hwK : w ∈ K := intrinsicInterior_subset hw
    refine hkey w hwK.1 ?_
    rcases lt_or_eq_of_le (show φ w ≤ α from hwK.2) with h | h
    · exact h
    · exfalso
      have hconst := eq_of_isMaxOn_of_mem_relint (φ := φ) hw
        (fun u hu => by rw [h]; exact hu.2) y (hCK hyC)
      exact hgy (hconst.trans h)
  have hcl := Convex.closure_eq_of_relint_subset_of_subset_closure hKconv hriK
    (hCK.trans hKcl.closure_eq.symm.subset)
  rw [hCcl.closure_eq, hKcl.closure_eq] at hcl
  exact hcl

/-- **Rockafellar, Theorem 18.4**, as stated in the book: if a closed convex set is neither an
affine set nor a closed half of an affine set, then each of its relative interior points lies on a
line segment joining two relative boundary points. -/
theorem exists_notMem_relint_mem_segment_of_not_isAffineHalf (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) (hx : x ∈ ri C) :
    ∃ a ∈ C, ∃ b ∈ C, a ∉ ri C ∧ b ∉ ri C ∧ x ∈ segment ℝ a b :=
  exists_notMem_relint_mem_segment_of_not_convex hC hCcl
    (fun hconv => hhalf (isAffineHalf_of_convex_sdiff_relint hC hCcl hconv)) hx

/-- **An affine set, or a closed half of an affine set, of dimension at least two contains a
line.** This is why Theorem 18.4 applies to every closed convex set of dimension at least two that
contains no lines, and hence why the induction in Theorem 18.5 only has to treat dimensions `0`
and `1` separately. -/
theorem not_containsNoLine_of_isAffineHalf (h : IsAffineHalf C) (hne : C.Nonempty)
    (hdim : 2 ≤ Module.finrank ℝ (vectorSpan ℝ C)) : ¬ ContainsNoLine C := by
  obtain ⟨φ, α, hCeq⟩ := h
  obtain ⟨x, hx⟩ := hne
  have hxK : x ∈ (affineSpan ℝ C : Set E) ∩ {w | φ w ≤ α} := hCeq ▸ hx
  set W : Submodule ℝ E := vectorSpan ℝ C with hWdef
  set ψ : W →ₗ[ℝ] ℝ := φ.domRestrict W with hψdef
  have hrange : Module.finrank ℝ (LinearMap.range ψ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range ψ)
  have hsum : Module.finrank ℝ (LinearMap.range ψ) + Module.finrank ℝ (LinearMap.ker ψ)
      = Module.finrank ℝ W := LinearMap.finrank_range_add_finrank_ker ψ
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker ψ) := by omega
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hbot => by
    rw [hbot] at hkerpos
    simp at hkerpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hnl
  obtain ⟨t, ht⟩ := hnl x (v : E) (fun h => hv0 (Submodule.coe_eq_zero.1 h))
  refine ht ?_
  rw [hCeq]
  constructor
  · have hmem := AffineSubspace.vadd_mem_of_mem_direction
      (show t • (v : E) ∈ (affineSpan ℝ C).direction by
        rw [direction_affineSpan]
        exact Submodule.smul_mem _ t v.2) hxK.1
    rwa [vadd_eq_add, add_comm] at hmem
  · have hφv : φ (v : E) = 0 := LinearMap.mem_ker.1 hvker
    have : φ (x + t • (v : E)) = φ x := by
      rw [map_add, map_smul, hφv, smul_zero, add_zero]
    change φ (x + t • (v : E)) ≤ α
    rw [this]
    exact hxK.2

end AffineHalf

/-! ### Half-lines: the one-dimensional case of Theorem 18.5 -/

section HalfLine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {x y : E}

/-- **The endpoint of a closed half-line is an extreme point of it.** -/
theorem mem_extremePoints_halfLine (x y : E) (hy : y ≠ 0) :
    x ∈ (halfLine x y).extremePoints ℝ := by
  refine ⟨left_mem_halfLine x y, ?_⟩
  rintro x₁ ⟨a, ha, rfl⟩ x₂ ⟨b, hb, rfl⟩ ⟨c, e, hc, he, hce, hx⟩
  have he' : e = 1 - c := by linarith
  subst he'
  have hval : c • (x + a • y) + (1 - c) • (x + b • y) = x + (c * a + (1 - c) * b) • y := by
    module
  rw [hval] at hx
  have hzero : (c * a + (1 - c) * b) • y = 0 := by
    simpa using sub_eq_zero_of_eq hx
  rcases smul_eq_zero.1 hzero with h | h
  · have ha0 : a ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c) hb]
    rw [le_antisymm ha0 ha, zero_smul, add_zero]
  · exact absurd h hy

/-- **The direction of a closed half-line is an extreme direction of it**: the half-line is a face
of itself. -/
theorem mem_extremeDirections_halfLine (x y : E) (hy : y ≠ 0) :
    y ∈ extremeDirections (halfLine x y) :=
  ⟨hy, x, Convex.isFace_self (convex_halfLine x y)⟩

/-- A closed half-line is the convex hull of its unique extreme point and its unique extreme
direction: **Theorem 18.5** in the one-dimensional unbounded case. -/
theorem halfLine_subset_convexHullPD (x y : E) (hy : y ≠ 0) :
    halfLine x y ⊆
      convexHullPD ((halfLine x y).extremePoints ℝ) (extremeDirections (halfLine x y)) := by
  have h := convexHullPD_mono (singleton_subset_iff.2 (mem_extremePoints_halfLine x y hy))
    (singleton_subset_iff.2 (mem_extremeDirections_halfLine x y hy))
  rwa [convexHullPD_singleton] at h

end HalfLine

/-! ### Theorem 18.5 -/

section Representation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **An unbounded closed convex set of dimension at most one that contains no line is a closed
half-line.** This is the only case of Theorem 18.5 that the induction cannot reduce, and
Rockafellar dismisses it as trivial. -/
theorem exists_eq_halfLine (hC : Convex ℝ C) (hCcl : IsClosed C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) (hdim : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1)
    (hb : ¬ IsBounded C) : ∃ x y : E, y ≠ 0 ∧ C = halfLine x y := by
  obtain ⟨y, hyrec, hy0⟩ := exists_ne_zero_mem_recessionCone_of_not_isBounded hC hCcl hne hb
  obtain ⟨x, hx⟩ := hne
  have hxy : x + y ∈ C := add_mem_of_mem_recessionCone hyrec hx
  have hyV : y ∈ vectorSpan ℝ C := by
    have h := vsub_mem_vectorSpan ℝ hxy hx
    simpa using h
  have hspan : (ℝ ∙ y) = vectorSpan ℝ C :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hyV)
      (by rw [finrank_span_singleton hy0]; exact hdim)
  -- the set of parameters along the line through `x` in the direction `y`
  set J : Set ℝ := {t : ℝ | x + t • y ∈ C} with hJdef
  have hJcl : IsClosed J := hCcl.preimage (by fun_prop)
  have hJconv : Convex ℝ J := by
    intro u hu v hv a b ha hb' hab
    have hb'' : b = 1 - a := by linarith
    subst hb''
    have hval : a • (x + u • y) + (1 - a) • (x + v • y) = x + (a * u + (1 - a) * v) • y := by
      module
    have hmem := hC hu hv ha hb' hab
    rw [hval] at hmem
    exact hmem
  have hJord := hJconv.ordConnected
  have hJnonneg : ∀ t : ℝ, 0 ≤ t → t ∈ J := fun t ht =>
    add_smul_mem_of_mem_recessionCone hyrec hx ht
  have hJbdd : BddBelow J := by
    by_contra hcon
    obtain ⟨t, htJ⟩ := hnl x y hy0
    rw [not_bddBelow_iff] at hcon
    obtain ⟨a, haJ, hat⟩ := hcon t
    exact htJ (hJord.out haJ (hJnonneg (max t 0) (le_max_right _ _))
      ⟨hat.le, le_max_left _ _⟩)
  have hm : sInf J ∈ J := hJcl.csInf_mem ⟨0, hJnonneg 0 le_rfl⟩ hJbdd
  refine ⟨x + sInf J • y, y, hy0, ?_⟩
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · have hzV : z - x ∈ vectorSpan ℝ C := by
      have h := vsub_mem_vectorSpan ℝ hz hx
      simpa using h
    rw [← hspan, Submodule.mem_span_singleton] at hzV
    obtain ⟨t, ht⟩ := hzV
    have hzt : z = x + t • y := by rw [ht]; abel
    have htJ : t ∈ J := by
      change x + t • y ∈ C
      rw [← hzt]
      exact hz
    refine ⟨t - sInf J, by linarith [csInf_le hJbdd htJ], ?_⟩
    rw [hzt]
    module
  · obtain ⟨a, ha, rfl⟩ := hz
    have hmem : sInf J + a ∈ J :=
      hJord.out hm (hJnonneg (max (sInf J + a) 0) (le_max_right _ _))
        ⟨by linarith, le_max_left _ _⟩
    have heq : x + sInf J • y + a • y = x + (sInf J + a) • y := by module
    rw [heq]
    exact hmem

/-- **Theorem 18.5** for bounded sets: Minkowski's theorem, `convexHull_extremePoints`, with the
extreme directions (of which there are none) carried along. -/
theorem subset_convexHullPD_of_isBounded (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hb : IsBounded C) :
    C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  have hcomp : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCcl hb
  intro z hz
  rw [← convexHull_extremePoints hcomp hC] at hz
  exact convexHull_subset_convexHullPD _ _ hz

/-- **Theorem 18.5** in dimension at most one: `C` is empty, a point, a segment, or a half-line. -/
theorem subset_convexHullPD_of_finrank_le_one (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) (hdim : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1) :
    C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  by_cases hb : IsBounded C
  · exact subset_convexHullPD_of_isBounded hC hCcl hb
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x, y, hy0, rfl⟩ := exists_eq_halfLine hC hCcl hne hnl hdim hb
  exact halfLine_subset_convexHullPD x y hy0

/-- The induction behind **Theorem 18.5**, on the dimension of `C`. -/
private theorem subset_convexHullPD_aux :
    ∀ (n : ℕ) (C : Set E), Module.finrank ℝ (vectorSpan ℝ C) ≤ n → Convex ℝ C → IsClosed C →
      ContainsNoLine C → C ⊆ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
  intro n
  induction n with
  | zero =>
    intro C hdim hC hCcl hnl
    exact subset_convexHullPD_of_finrank_le_one hC hCcl hnl (by omega)
  | succ n ih =>
    intro C hdim hC hCcl hnl
    by_cases hdim1 : Module.finrank ℝ (vectorSpan ℝ C) ≤ 1
    · exact subset_convexHullPD_of_finrank_le_one hC hCcl hnl hdim1
    push Not at hdim1
    have hne : C.Nonempty := by
      rcases C.eq_empty_or_nonempty with rfl | h
      · refine absurd hdim1 (not_lt.2 ?_)
        rw [vectorSpan_empty]
        simp
      · exact h
    have hhalf : ¬ IsAffineHalf C := fun h =>
      not_containsNoLine_of_isAffineHalf h hne hdim1 hnl
    have hbd : ∀ w ∈ C, w ∉ ri C →
        w ∈ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by
      intro w hw hwri
      obtain ⟨C', hface, hwC'⟩ := exists_isFace_mem_relint hC hw
      have hC'ne : C' ≠ C := fun h => hwri (h ▸ hwC')
      have hC'cl : IsClosed C' := hface.isClosed hC hCcl
      have hlt : Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) :=
        hface.finrank_vectorSpan_lt ⟨w, intrinsicInterior_subset hwC'⟩ hC'ne
      have hsub := ih C' (by omega) hface.convex hC'cl (hnl.mono hface.subset)
        (intrinsicInterior_subset hwC')
      exact convexHullPD_mono hface.toIsExtreme.extremePoints_subset_extremePoints
        hface.extremeDirections_subset hsub
    intro w hw
    by_cases hwri : w ∈ ri C
    · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
        exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hwri
      exact (convex_convexHullPD _ _).segment_subset (hbd a haC hari) (hbd b hbC hbri) hseg
    · exact hbd w hw hwri

/-- **Rockafellar, Theorem 18.5**: a closed convex set containing no lines is the convex hull of
its extreme points and extreme directions.

The proof is his induction on `dim C`: for a set of dimension at least two the relative boundary
is not convex (Theorem 18.4 through `not_containsNoLine_of_isAffineHalf`), so every relative
interior point lies on a segment joining two relative boundary points, and each relative boundary
point lies in the relative interior of a face of strictly smaller dimension (Theorem 18.2), which
is again closed (Corollary 18.1.1) and contains no lines. Dimensions `0` and `1` are the base
cases: a bounded set is handled by Minkowski's theorem and an unbounded one is a closed
half-line. -/
theorem convexHullPD_extremePoints_extremeDirections (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) :
    convexHullPD (C.extremePoints ℝ) (extremeDirections C) = C :=
  subset_antisymm
    (convexHullPD_min hC extremePoints_subset (extremeDirections_subset_recessionCone hC hCcl))
    (subset_convexHullPD_aux _ C le_rfl hC hCcl hnl)

/-- **Rockafellar, Corollary 18.5.3**: a nonempty closed convex set containing no lines has at
least one extreme point. Rockafellar's own derivation — a hull of directions alone is empty. -/
theorem extremePoints_nonempty_of_containsNoLine (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hnl : ContainsNoLine C) (hne : C.Nonempty) : (C.extremePoints ℝ).Nonempty := by
  rcases (C.extremePoints ℝ).eq_empty_or_nonempty with hem | h
  · rw [← convexHullPD_extremePoints_extremeDirections hC hCcl hnl, hem,
      convexHullPD_empty_left] at hne
    exact absurd hne Set.not_nonempty_empty
  · exact h

end Representation

end Tdaf.ConvexAnalysis
