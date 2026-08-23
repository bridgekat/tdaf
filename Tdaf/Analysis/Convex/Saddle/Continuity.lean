/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Convergence
import Tdaf.Analysis.Convex.Saddle.Kernel

/-!
# Continuity of finite saddle-functions

Rockafellar, *Convex Analysis*, §35, the continuity and convergence half: **Theorems 35.1–35.5**.
Every one of them is a §10 statement read for a function of two variables, and every one of them is
obtained here by applying the §10 result twice — once in each variable — and combining.

## What is here

* `ConcaveConvexOn C D K` — the bundled hypothesis of the whole section: `K : U × X → ℝ` is
  concave in its first argument on `C` for each point of `D`, and convex in its second on `D` for
  each point of `C`. Its two fields are exactly the two unbundled hypotheses that
  `Saddle/Kernel.lean`'s simple extensions take, so `hK.concave_fst` and `hK.convex_snd` feed them
  directly.
* `exists_forall_abs_le_prod` and `exists_forall_lipschitzOnWith_prod` — **Theorem 35.2**, for a
  family indexed by an arbitrary type: uniform boundedness and a single Lipschitz constant on
  `S ×ˢ T` for compact `S ⊆ ri C`, `T ⊆ ri D`.
* `ConcaveConvexOn.lipschitzOnWith_of_isCompact`, `.continuousOn` — **Theorem 35.1**, the singleton
  case.

## What is not here

Theorems 35.3–35.5 (joint continuity in a parameter, and the two convergence theorems) are the
saddle forms of Theorems 10.7–10.9; the §10 statements they consume are in `Convergence.lean` and
the transfer is the same two-variable argument as below. Theorems 35.6–35.10 (directional
derivatives, subgradients, differentiability almost everywhere) are the §23/§24/§25 half of the
section and belong with the material they extend; §25's Rademacher half is not formalized yet, so
35.9 and 35.10 are blocked in any case.

## Implementation notes

**The Lipschitz constant is `α₁ + α₂`, not Rockafellar's `2(α₁ + α₂)`.** The book measures
distance on `R^m × R^n` with the Euclidean norm and pays a factor of `2` passing between it and
the sum of the coordinate distances. Mathlib's product metric is the **supremum** metric
(`Prod.dist_eq`), for which `dist u' u ≤ dist p q` and `dist x' x ≤ dist p q` outright, so
`α₁ * dist u' u + α₂ * dist x' x ≤ (α₁ + α₂) * dist p q` with no factor to pay.

**Everything is stated for arbitrary convex `C` and `D`, not for relatively open ones.** The book
takes `C` and `D` relatively open, where `C = ri C`; the results below are the same statements with
`ri C` and `ri D` written out, which is what §10 in this project already does
(`exists_forall_abs_le_of_isCompact_relint`).

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35
  (Theorems 35.1, 35.2).
-/

open Set Filter Topology Metric
open scoped NNReal Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Concave-convex functions on a rectangle -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- `K` is **concave-convex on `C × D`**: concave in its first argument on `C` for each point of
`D`, convex in its second on `D` for each point of `C`.

This is the finite, set-relative form of `ConcaveConvexFn` (`Saddle/Defs.lean`), and it is the
hypothesis §35 runs on. The two fields are the two hypotheses `concaveConvexFn_lowerSimpleExt`
takes, so `hK.concave_fst` and `hK.convex_snd` extend `K` to all of `U × X` when that is wanted. -/
structure ConcaveConvexOn (C : Set U) (D : Set X) (K : U × X → ℝ) : Prop where
  /-- `K (·, x)` is concave on `C` for every `x ∈ D`. -/
  concave_fst : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)
  /-- `K (u, ·)` is convex on `D` for every `u ∈ C`. -/
  convex_snd : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x)

variable {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- The concave slice, as a family of *convex* functions: this is the form §10 consumes. -/
theorem ConcaveConvexOn.convexOn_neg_fst (hK : ConcaveConvexOn C D K) {x : X} (hx : x ∈ D) :
    ConvexOn ℝ C fun u => -K (u, x) :=
  (hK.concave_fst x hx).neg

end Defs

/-! ### Negation

§10 is stated for convex functions; the concave variable of a saddle-function reaches it through
`-K`, and these three lemmas carry the conclusions back. -/

section Neg

variable {ι : Type*} {g : ι → ℝ}

/-- A family of reals is bounded above iff its negation is bounded below. -/
theorem bddAbove_range_neg_iff : BddAbove (Set.range fun i => -g i) ↔ BddBelow (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

/-- A family of reals is bounded below iff its negation is bounded above. -/
theorem bddBelow_range_neg_iff : BddBelow (Set.range fun i => -g i) ↔ BddAbove (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact le_neg.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

variable {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {S : Set E} {k : ℝ≥0}

/-- Negating a real-valued function does not change its Lipschitz constants. -/
theorem LipschitzOnWith.negReal (h : LipschitzOnWith k f S) :
    LipschitzOnWith k (fun x => -f x) S := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hd : dist (-f x) (-f y) = dist (f x) (f y) := by
    rw [Real.dist_eq, Real.dist_eq, neg_sub_neg, abs_sub_comm]
  rw [hd]
  exact h.dist_le_mul x hx y hy

/-- `-f` is Lipschitz on `S` exactly when `f` is. -/
theorem lipschitzOnWith_neg_iff : LipschitzOnWith k (fun x => -f x) S ↔ LipschitzOnWith k f S :=
  ⟨fun h => by simpa only [neg_neg] using LipschitzOnWith.negReal h,
    fun h => LipschitzOnWith.negReal h⟩

end Neg

/-! ### Theorem 35.2

The engine of the section. Theorem 10.6 is applied four times: twice to bound the family — once in
each variable, the second time using the first — and twice to make it equi-Lipschitz. -/

section Family

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {ι : Type*} {C C' : Set U} {D D' : Set X} {K : ι → U × X → ℝ}

section Snd

variable [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
/-- The convex slices of a concave-convex family, at a point of `C`, as a family of convex
functions on `D`. -/
theorem convexOn_slice_snd (hK : ∀ i, ConcaveConvexOn C D (K i)) {u : U} (hu : u ∈ C) (i : ι) :
    ConvexOn ℝ D fun x => K i (u, x) :=
  (hK i).convex_snd u hu

/-- **The first bounding step**: for a fixed `u ∈ C'` the convex slices `K i (u, ·)` are uniformly
bounded on every compact `T ⊆ ri D`. This is Theorem 10.6 in the second variable. -/
theorem exists_forall_abs_le_snd {u : U} (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) (hu : u ∈ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ T, |K i (u, x)| ≤ M := by
  rcases D'.eq_empty_or_nonempty with hD'e | ⟨z, hz⟩
  · rw [hD'e, closure_empty, subset_empty_iff] at hDdense
    rw [hDdense, subset_empty_iff] at hTD
    subst hTD
    exact ⟨0, le_rfl, fun i x hx => absurd hx (notMem_empty x)⟩
  exact exists_forall_abs_le_of_isCompact_relint hD (convexOn_slice_snd hK hu) hD' hDdense
    (fun x hx => (isBounded_iff_bddBelow_bddAbove.1 (hbdd x hx)).2)
    ⟨z, hD' hz, (isBounded_iff_bddBelow_bddAbove.1 (hbdd z hz)).1⟩ hT hTD

end Snd

section Fst

variable [FiniteDimensional ℝ U]

/-- **The second bounding step**: for a fixed `x ∈ D'` the concave slices `K i (·, x)` are uniformly
bounded on every compact `S ⊆ ri C`. This is Theorem 10.6 in the first variable, reached through
`-K`. -/
theorem exists_forall_abs_le_fst {x : X} (hC : Convex ℝ C)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hbdd : ∀ u ∈ C', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C) (hx : x ∈ D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ u ∈ S, |K i (u, x)| ≤ M := by
  rcases C'.eq_empty_or_nonempty with hC'e | ⟨z, hz⟩
  · rw [hC'e, closure_empty, subset_empty_iff] at hCdense
    rw [hCdense, subset_empty_iff] at hSC
    subst hSC
    exact ⟨0, le_rfl, fun i u hu => absurd hu (notMem_empty u)⟩
  obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_of_isCompact_relint hC
    (fun i => (hK i).convexOn_neg_fst hx) hC' hCdense
    (fun u hu => bddAbove_range_neg_iff.2 (isBounded_iff_bddBelow_bddAbove.1 (hbdd u hu)).1)
    ⟨z, hC' hz, bddBelow_range_neg_iff.2 (isBounded_iff_bddBelow_bddAbove.1 (hbdd z hz)).2⟩ hS hSC
  exact ⟨M, hM0, fun i u hu => by simpa only [abs_neg] using hM i u hu⟩

end Fst

/-! ### Theorem 35.2, the two equi-Lipschitz halves -/

section EquiLipschitz

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ X]

/-- **Theorem 35.2 in the first variable**: the family is uniformly bounded on `S ×ˢ T` and
equi-Lipschitz in `u`, uniformly in `x ∈ T`. -/
theorem exists_forall_abs_le_and_lipschitzOnWith_fst (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ u ∈ S, ∀ x ∈ T, |K i (u, x)| ≤ M) ∧
      ∃ k : ℝ≥0, ∀ i, ∀ x ∈ T, LipschitzOnWith k (fun u => K i (u, x)) S := by
  rcases C'.eq_empty_or_nonempty with hC'e | ⟨z, hz⟩
  · rw [hC'e, closure_empty, subset_empty_iff] at hCdense
    rw [hCdense, subset_empty_iff] at hSC
    subst hSC
    exact ⟨⟨0, le_rfl, fun i u hu => absurd hu (notMem_empty u)⟩,
      0, fun i x _ => by intro u hu; exact absurd hu (notMem_empty u)⟩
  -- the family of concave slices, indexed by `ι × ↑T`, read as convex functions through `-K`
  set g : ι × ↑T → U → ℝ := fun q u => -K q.1 (u, (q.2 : X)) with hg
  have hgconv : ∀ q, ConvexOn ℝ C (g q) := fun q =>
    (hK q.1).convexOn_neg_fst (intrinsicInterior_subset (hTD q.2.2))
  -- pointwise boundedness on `C'` is the first bounding step
  have hgbd : ∀ u ∈ C', ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ι × ↑T, |g q u| ≤ M := by
    intro u hu
    obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_snd (u := u) hD hK hD' hDdense
      (fun x hx => hbdd u hu x hx) hT hTD (intrinsicInterior_subset (hC' hu))
    exact ⟨M, hM0, fun q => by simpa only [hg, abs_neg] using hM q.1 (q.2 : X) q.2.2⟩
  have hab : ∀ u ∈ C', BddAbove (Set.range fun q : ι × ↑T => g q u) := by
    intro u hu
    obtain ⟨M, -, hM⟩ := hgbd u hu
    exact ⟨M, by rintro _ ⟨q, rfl⟩; exact (le_abs_self _).trans (hM q)⟩
  have hbe : ∃ w ∈ ri C, BddBelow (Set.range fun q : ι × ↑T => g q w) := by
    obtain ⟨M, -, hM⟩ := hgbd z hz
    exact ⟨z, hC' hz, -M, by rintro _ ⟨q, rfl⟩; exact neg_le_of_abs_le (hM q)⟩
  obtain ⟨M, hM0, hM⟩ :=
    exists_forall_abs_le_of_isCompact_relint hC hgconv hC' hCdense hab hbe hS hSC
  obtain ⟨k, hk⟩ :=
    exists_forall_lipschitzOnWith_of_isCompact_relint hC hgconv hC' hCdense hab hbe hS hSC
  refine ⟨⟨M, hM0, fun i u hu x hx => ?_⟩, k, fun i x hx => ?_⟩
  · simpa only [hg, abs_neg] using hM (i, ⟨x, hx⟩) u hu
  · exact lipschitzOnWith_neg_iff.1 (hk (i, ⟨x, hx⟩))

/-- **Theorem 35.2 in the second variable**: the family is equi-Lipschitz in `x`, uniformly in
`u ∈ S`. -/
theorem exists_forall_lipschitzOnWith_snd (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ k : ℝ≥0, ∀ i, ∀ u ∈ S, LipschitzOnWith k (fun x => K i (u, x)) T := by
  rcases D'.eq_empty_or_nonempty with hD'e | ⟨w, hw⟩
  · rw [hD'e, closure_empty, subset_empty_iff] at hDdense
    rw [hDdense, subset_empty_iff] at hTD
    subst hTD
    exact ⟨0, fun i u _ => by intro x hx; exact absurd hx (notMem_empty x)⟩
  set g : ι × ↑S → X → ℝ := fun q x => K q.1 ((q.2 : U), x) with hg
  have hgconv : ∀ q, ConvexOn ℝ D (g q) := fun q =>
    (hK q.1).convex_snd (q.2 : U) (intrinsicInterior_subset (hSC q.2.2))
  have hgbd : ∀ x ∈ D', ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ι × ↑S, |g q x| ≤ M := by
    intro x hx
    obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_fst (x := x) hC hK hC' hCdense
      (fun u hu => hbdd u hu x hx) hS hSC (intrinsicInterior_subset (hD' hx))
    exact ⟨M, hM0, fun q => hM q.1 (q.2 : U) q.2.2⟩
  have hab : ∀ x ∈ D', BddAbove (Set.range fun q : ι × ↑S => g q x) := by
    intro x hx
    obtain ⟨M, -, hM⟩ := hgbd x hx
    exact ⟨M, by rintro _ ⟨q, rfl⟩; exact (le_abs_self _).trans (hM q)⟩
  have hbe : ∃ y ∈ ri D, BddBelow (Set.range fun q : ι × ↑S => g q y) := by
    obtain ⟨M, -, hM⟩ := hgbd w hw
    exact ⟨w, hD' hw, -M, by rintro _ ⟨q, rfl⟩; exact neg_le_of_abs_le (hM q)⟩
  obtain ⟨k, hk⟩ :=
    exists_forall_lipschitzOnWith_of_isCompact_relint hD hgconv hD' hDdense hab hbe hT hTD
  exact ⟨k, fun i u hu => hk (i, ⟨u, hu⟩)⟩

/-- **Rockafellar, Theorem 35.2**: a family of finite concave-convex functions on `C × D`,
pointwise bounded on `C' × D'`, is uniformly bounded and equi-Lipschitzian on `S ×ˢ T` for every
compact `S ⊆ ri C` and `T ⊆ ri D`.

Rockafellar's hypothesis is `conv (cl (C' × D')) ⊇ C × D` for relatively open `C`, `D`; the form
here is the one §10 uses — `C' ⊆ ri C ⊆ cl C'` and likewise for `D` — and taking `C' = ri C`,
`D' = ri D` gives the headline statement.

The Lipschitz constant is `k₁ + k₂`, not the book's `2(α₁ + α₂)`: Mathlib's product metric is the
supremum metric, so no factor is paid passing between the coordinate distances and the distance on
the product. -/
theorem exists_forall_abs_le_and_lipschitzOnWith_prod (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ p ∈ S ×ˢ T, |K i p| ≤ M) ∧
      ∃ k : ℝ≥0, ∀ i, LipschitzOnWith k (K i) (S ×ˢ T) := by
  obtain ⟨⟨M, hM0, hM⟩, k₁, hk₁⟩ := exists_forall_abs_le_and_lipschitzOnWith_fst hC hD hK hC'
    hCdense hD' hDdense hbdd hS hSC hT hTD
  obtain ⟨k₂, hk₂⟩ :=
    exists_forall_lipschitzOnWith_snd hC hD hK hC' hCdense hD' hDdense hbdd hS hSC hT hTD
  refine ⟨⟨M, hM0, fun i p hp => hM i p.1 hp.1 p.2 hp.2⟩, k₁ + k₂, fun i => ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have h₁ : dist (K i (p.1, q.2)) (K i (q.1, q.2)) ≤ (k₁ : ℝ) * dist p.1 q.1 :=
    (hk₁ i q.2 hq.2).dist_le_mul p.1 hp.1 q.1 hq.1
  have h₂ : dist (K i (p.1, p.2)) (K i (p.1, q.2)) ≤ (k₂ : ℝ) * dist p.2 q.2 :=
    (hk₂ i p.1 hp.1).dist_le_mul p.2 hp.2 q.2 hq.2
  have hd₁ : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd₂ : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  have htri : dist (K i p) (K i q)
      ≤ dist (K i (p.1, p.2)) (K i (p.1, q.2)) + dist (K i (p.1, q.2)) (K i (q.1, q.2)) :=
    dist_triangle _ _ _
  have hsum : (k₂ : ℝ) * dist p.2 q.2 + (k₁ : ℝ) * dist p.1 q.1
      ≤ ((k₁ + k₂ : ℝ≥0) : ℝ) * dist p q := by
    have e₁ : (k₁ : ℝ) * dist p.1 q.1 ≤ (k₁ : ℝ) * dist p q :=
      mul_le_mul_of_nonneg_left hd₁ k₁.coe_nonneg
    have e₂ : (k₂ : ℝ) * dist p.2 q.2 ≤ (k₂ : ℝ) * dist p q :=
      mul_le_mul_of_nonneg_left hd₂ k₂.coe_nonneg
    have : ((k₁ + k₂ : ℝ≥0) : ℝ) * dist p q = (k₁ : ℝ) * dist p q + (k₂ : ℝ) * dist p q := by
      push_cast
      ring
    linarith
  exact htri.trans ((add_le_add h₂ h₁).trans hsum)

end EquiLipschitz

/-! ### Theorem 35.1 -/

section Single

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] {L : U × X → ℝ}

/-- **Rockafellar, Theorem 35.1**: a finite concave-convex function on `C × D` is Lipschitzian on
every product of compact subsets of `ri C` and `ri D`.

This is Theorem 35.2 for the one-element family; the book states it for relatively open `C` and
`D`, where `ri C = C`. -/
theorem ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ k : ℝ≥0, LipschitzOnWith k L (S ×ˢ T) := by
  obtain ⟨-, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod (K := fun _ : Unit => L)
    hC hD (fun _ => hL) (subset_refl _) subset_closure (subset_refl _) subset_closure
    (fun _ _ _ _ => (Set.finite_range _).isBounded) hS hSC hT hTD
  exact ⟨k, hk ()⟩

/-- **Rockafellar, Theorem 35.1**, the boundedness clause: a finite concave-convex function is
bounded on every product of compact subsets of the relative interiors. -/
theorem ConcaveConvexOn.exists_forall_abs_le_of_isCompact (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S ×ˢ T, |L p| ≤ M := by
  obtain ⟨⟨M, hM0, hM⟩, -⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod (K := fun _ : Unit => L)
    hC hD (fun _ => hL) (subset_refl _) subset_closure (subset_refl _) subset_closure
    (fun _ _ _ _ => (Set.finite_range _).isBounded) hS hSC hT hTD
  exact ⟨M, hM0, hM ()⟩

end Single

end Family

/-! ### Compact relative neighbourhoods

`ri C` is locally compact, which is what turns "Lipschitz on every compact rectangle" into
"continuous". The proof is the chart of `Continuity.lean`: `ri C` is the translate of an *open*
subset of a finite-dimensional subspace, where closed balls are compact.

This lemma is about a single convex set and belongs in `RelativeInterior.lean`; it lives here
until a second consumer appears. -/

section LocallyCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **Every point of `ri C` has a compact relative neighbourhood inside `ri C`.** -/
theorem exists_isCompact_mem_nhdsWithin_relint (hC : Convex ℝ C) {x : E} (hx : x ∈ ri C) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ ri C ∧ S ∈ 𝓝[ri C] x := by
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx)
  have h0 : (0 : V) ∈ interior (chart C x V) := by
    have h := hmaps hx
    simpa using h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hsub : Metric.closedBall (0 : V) (ε / 2) ⊆ interior (chart C x V) := fun w hw =>
    hball (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hw) (by linarith)))
  refine ⟨(fun w : V => x + (w : E)) '' Metric.closedBall (0 : V) (ε / 2),
    (isCompact_closedBall _ _).image (continuous_const.add continuous_subtype_val), ?_, ?_⟩
  · rw [himg]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(w : E), ⟨w, hsub hw, rfl⟩, rfl⟩
  · refine mem_nhdsWithin.2 ⟨Metric.ball x (ε / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by linarith), ?_⟩
    rintro y ⟨hyball, hyri⟩
    refine ⟨r (y - x), ?_, hid y hyri⟩
    have hcoe : ((r (y - x) : V) : E) = y - x := eq_sub_of_add_eq' (hid y hyri)
    rw [Metric.mem_closedBall, dist_zero_right, ← Submodule.norm_coe, hcoe, ← dist_eq_norm]
    exact (Metric.mem_ball.1 hyball).le

end LocallyCompact

/-! ### Theorem 35.1, the continuity clause -/

section ContinuousOn

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {L : U × X → ℝ}

/-- **Rockafellar, Theorem 35.1**, first assertion: a finite concave-convex function on `C × D` is
continuous relative to `ri C × ri D`.

The book states it for relatively open `C` and `D`, where `ri C = C`. Continuity is local, `ri C`
and `ri D` are locally compact (`exists_isCompact_mem_nhdsWithin_relint`), and on a compact
rectangle the function is Lipschitz. -/
theorem ConcaveConvexOn.continuousOn (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L) : ContinuousOn L (ri C ×ˢ ri D) := by
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  obtain ⟨S, hScpt, hSC, hSn⟩ := exists_isCompact_mem_nhdsWithin_relint hC hu
  obtain ⟨T, hTcpt, hTD, hTn⟩ := exists_isCompact_mem_nhdsWithin_relint hD hx
  obtain ⟨k, hk⟩ := hL.exists_lipschitzOnWith_of_isCompact hC hD hScpt hSC hTcpt hTD
  have hcw : ContinuousWithinAt L (S ×ˢ T) (u, x) :=
    hk.continuousOn.continuousWithinAt
      (Set.mem_prod.2 ⟨mem_of_mem_nhdsWithin hu hSn, mem_of_mem_nhdsWithin hx hTn⟩)
  exact hcw.mono_of_mem_nhdsWithin (nhdsWithin_prod hSn hTn)

end ContinuousOn

end Tdaf.ConvexAnalysis
