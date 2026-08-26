/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Rademacher
import Tdaf.Analysis.Convex.Saddle.Subgradient
import Tdaf.Surface.Rockafellar.Part7.Section33

/-!
# Rockafellar, §35: Continuity and Differentiability of Saddle-Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §35, pp. 370–378: the §10 continuity and
convergence theorems and the §23/§24/§25 differential theory, both read for a **concave-convex**
function of a pair.

All twelve numbered results are here: Theorems 35.1–35.10 and Corollaries 35.7.1 and 35.8.1.

## The sign asymmetry, stated once

`K` is **concave in `u`** and **convex in `v`** (§33's orientation, in force throughout Part VII).
Rockafellar therefore defines

* `∂₁K (u, v)` = the **super**gradients of the *concave* slice `K (·, v)` at `u`:
  `K (u', v) ≤ K (u, v) + ⟨u*, u' - u⟩` for all `u'`;
* `∂₂K (u, v)` = the **sub**gradients of the *convex* slice `K (u, ·)` at `v`:
  `K (u, v) + ⟨v*, v' - v⟩ ≤ K (u, v')` for all `v'`;
* `∂K (u, v) = ∂₁K (u, v) × ∂₂K (u, v)`.

**The two inequalities point in opposite directions**, so `∂K` is *not* the subdifferential of `K`
read as one function on `ℝᵐ⁺ⁿ`, and it is not a monotone relation. The whole of the sign lives in
the first block, and the dictionary is `mem_subgrad₁_iff_neg_mem_subgradient_neg` below:

`u* ∈ ∂₁K (u, v) ↔ -u* ∈ ∂(-K (·, v)) (u)`.

That single `u* ↦ -u*` is what §37's Corollary 37.5.2 inserts to recover monotonicity, and what
makes Corollary 37.5.1's homeomorphism the asymmetric `(u - u*, v + v*)`. Track it; do not try to
derive it.

## Vocabulary

| book | this module | backbone |
|---|---|---|
| `K′(u, v; u′, v′)` | `dirDerivReal K (u, v) (u′, v′)` | `Saddle/Differential.lean` |
| `∂₁K (u, v)`, `K` extended-real-valued | `subgrad₁` | `concaveSubgradient (pairing m)` |
| `∂₂K (u, v)`, `K` extended-real-valued | `subgrad₂` | `subgradient (pairing n)` |
| `∂K (u, v)`, `K` extended-real-valued | `subgrad` | `saddleSubgradient (pairing m) (pairing n)` |
| `∂₁K`, `∂₂K`, `∂K`, `K` finite on `C × D` | `subgradientFst`, `subgradientSnd`,
  `subgradientSaddle` | `Saddle/Differential.lean` |

`K′` is **not** renamed: `dirDerivReal K (u, v) q` *is* `K′(u, v; q)`, a genuine limit of difference
quotients (the `EReal`-valued `dirDeriv` of §23 is an infimum, which is the limit only along a line
— that difference is exactly what Theorem 35.6 is about).

`subgrad₁`, `subgrad₂` and `subgrad` are reducible `abbrev`s, so they **are** the backbone objects;
they exist only to supply the Euclidean pairing. They carry the book's definition (15119–15155),
which is stated for an arbitrary — hence `EReal`-valued — concave-convex `K` on `ℝᵐ × ℝⁿ` and tests
against *all* of `ℝᵐ` and `ℝⁿ`. Theorems 35.7–35.10 are about a `K` that is *finite* on an open
rectangle `C × D`, and there the backbone's rectangle-relative `subgradientFst C K`,
`subgradientSnd D K`, `subgradientSaddle C D K` are what the statements use; `subgradFst_univ_eq`,
`subgradSnd_univ_eq` and `subgradSaddle_univ_eq` are the bridge at `C = D = univ`.

## Contents

| label | declarations |
|---|---|
| Theorem 35.1 | `theorem_35_1_continuousOn`, `theorem_35_1_lipschitzian` |
| Theorem 35.2 | `theorem_35_2` |
| Theorem 35.3 | `theorem_35_3`, `theorem_35_3_dense` |
| Theorem 35.4 | `theorem_35_4` |
| Theorem 35.5 | `theorem_35_5` |
| §35 definitions, 15053–15155 | `subgrad₁`, `subgrad₂`, `subgrad`, `subgrad_eq_prod`,
  `mem_subgrad₁_iff`, `mem_subgrad₂_iff`, `mem_subgrad₁_iff_neg_mem_subgradient_neg`,
  `convex_subgrad`, `subgradFst_univ_eq`, `subgradSnd_univ_eq`, `subgradSaddle_univ_eq` |
| Theorem 35.6 | `theorem_35_6`, `theorem_35_6_tendsto`, `theorem_35_6_concaveConvex`,
  `theorem_35_6_posHom` |
| Theorem 35.7 | `theorem_35_7_fst`, `theorem_35_7_snd`, `theorem_35_7_subgrad` |
| Corollary 35.7.1 | `corollary_35_7_1_fst`, `corollary_35_7_1_snd`, `corollary_35_7_1_subgrad` |
| Theorem 35.8 | `theorem_35_8_gradient`, `theorem_35_8` |
| Corollary 35.8.1 | `corollary_35_8_1` |
| Theorem 35.9 | `theorem_35_9_measure`, `theorem_35_9_dense`, `theorem_35_9_continuousOn` |
| Theorem 35.10 | `theorem_35_10`, `theorem_35_10_uniform` |

## Where the statements diverge from the book

**Theorem 35.2's hypothesis on `C′` and `D′` is `cl C′ ⊇ C`, not `conv (cl (C′ × D′)) ⊇ C × D`.**
The convex-hull weakening is in the backbone only in its `interior` form
(`bddAbove_range_of_subset_convexHull_closure`) and not in the `ri` form Part VII needs — exactly
as `Rockafellar.theorem_10_6_ab` already records for §10, of which this is the two-variable case.

**Theorems 35.6–35.10 are stated for a real-valued `K` on the open rectangle.** The book's `K` is a
concave-convex function on all of `ℝᵐ × ℝⁿ` — so `EReal`-valued — that happens to be finite on
`C × D`; the surface takes its real trace there, which is `ConcaveConvexOn C D K`. The consequence
is that `∂₁K` and `∂₂K` are tested against `C` and `D` rather than against all of `ℝᵐ` and `ℝⁿ`;
the two readings agree whenever `K` is extended off `C × D` by the simple extension of
`Saddle/Kernel.lean`, which is `-∞`/`+∞` there and makes the extra inequalities vacuous.

**Theorem 35.7's two displayed inequalities are spelled without `liminf` and `limsup`.**
`liminf_i K_i′(u_i, v_i; u′, 0) ≥ K′(u, v; u′, 0)` is stated as: every real `μ` below the
right-hand side eventually falls below `K_i′(u_i, v_i; u′, 0)`. For real-valued directional
derivatives that is the same statement and it carries no junk value.

**The `εB` of Theorems 35.7, 35.9 and 35.10 is the supremum ball of `ℝᵐ × ℝⁿ`.** Mathlib gives a
product of normed spaces the supremum norm; the book's Euclidean ball differs from it by a factor
bounded by `√2`, and every statement quantifies over all `ε > 0`.

**Theorem 35.9's gradient mapping is an arbitrary representing function.**
`HasSaddleGradientAt K q p` says `∇K p = q` with `q : ℝᵐ × ℝⁿ`; there is no canonical `∇K`
without choice, so the continuity clause takes any `G` with `HasSaddleGradientAt K (G p) p` on the
set in question. Since `prodInnerL` is injective, `G` is unique there and nothing is lost.

## What is not here

* **Corollary 35.8.1's last clause** — "this condition is satisfied if merely the `m + n` two-sided
  partial derivatives of `K` exist and are finite" (15259). *Omitted with a reason*: it is a
  statement about a coordinate basis rather than about the space, and it adds nothing to
  `corollary_35_8_1`, which is the equivalence the clause is a sufficient condition for. The
  backbone records the same omission in `Saddle/Differential.lean`.
* **The unnumbered support-function remarks at 15155–15185** — that `cl (u′ ↦ -K′(u, v; -u′, 0))`
  is the support function of `∂₁K (u, v)`, that `∂₁K` and `∂₂K` are nonempty compact convex at
  interior points of `dom K`, and the resulting `inf`/`sup` formulas for the two partial
  directional derivatives. *Deferred by scope*: they are Theorems 23.2 and 23.4 restated, and the
  backbone carries them for the slices as `forall_inner_le_dirDerivReal_iff`,
  `forall_dirDerivReal_le_inner_iff`, `subgradientFst_nonempty` and `subgradientSnd_nonempty`
  (`Saddle/Differential.lean`). Closing them at the level of `∂₁K`/`∂₂K` needs a support-function
  API for `dirDerivReal` that does not exist yet.
* **The remark following Theorem 35.10** (15299) — that pointwise convergence on a dense
  `C′ × D′` suffices, because Theorem 35.4 propagates it. *Deferred by scope*: it is
  `theorem_35_4` composed with `theorem_35_10`, and the composition adds nothing.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35, pp. 370–378.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### Two bookkeeping steps

Rockafellar states the continuity theorems for *closed bounded* subsets of `C × D`; the backbone
states them for compact *rectangles* inside `ri C × ri D`. The passage between the two is the same
four lines every time, so it is done once here. -/

section Bookkeeping

variable {m n : ℕ}

/-- Rockafellar's "Lipschitzian relative to `S`" (§10, p. 86) out of Mathlib's `LipschitzOnWith`.
`Rockafellar.LipschitzianOn` (`Part2/Section10.lean`) is stated only for `Rn n → ℝ` and does not
apply on a product; see the section report. -/
private theorem exists_lipschitz_of_lipschitzOnWith {E : Type*} [NormedAddCommGroup E]
    {f : E → ℝ} {S : Set E} {k : ℝ≥0} (h : LipschitzOnWith k f S) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ y ∈ S, ∀ x ∈ S, |f y - f x| ≤ α * ‖y - x‖ := by
  refine ⟨k, k.coe_nonneg, fun y hy x hx => ?_⟩
  have hd := h.dist_le_mul y hy x hx
  rwa [Real.dist_eq, dist_eq_norm] at hd

/-- A compact subset of `C × D` sits inside a compact *rectangle* inside `C × D`, namely the
product of its two projections. This is the reduction Rockafellar performs in one sentence at the
start of the proof of Theorem 35.1 ("it suffices to show that `K` is Lipschitzian on `S × T`"). -/
private theorem isCompact_prod_projections {C : Set (Rn m)} {D : Set (Rn n)}
    {E : Set (Rn m × Rn n)} (hE : IsCompact E) (hEsub : E ⊆ C ×ˢ D) :
    IsCompact (Prod.fst '' E) ∧ IsCompact (Prod.snd '' E) ∧ Prod.fst '' E ⊆ C ∧
      Prod.snd '' E ⊆ D ∧ E ⊆ (Prod.fst '' E) ×ˢ (Prod.snd '' E) := by
  refine ⟨hE.image continuous_fst, hE.image continuous_snd, ?_, ?_,
    fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).1
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).2

end Bookkeeping

/-! ### Theorem 35.1 -/

section Thm351

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Rockafellar, Theorem 35.1**, first assertion. Let `C` and `D` be relatively open convex sets
in `ℝᵐ` and `ℝⁿ`, and let `K` be a finite concave-convex function on `C × D`. Then `K` is
continuous relative to `C × D`.

Specialises `ConcaveConvexOn.continuousOn`. "Relatively open" is `ri C = C`; "finite concave-convex
on `C × D`" is `ConcaveConvexOn C D K`, which is real-valued, exactly as the book's `K` is. -/
theorem theorem_35_1_continuousOn (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) : ContinuousOn K (C ×ˢ D) := by
  have h := hK.continuousOn hC hD
  rwa [hCro, hDro] at h

/-- **Rockafellar, Theorem 35.1**, second assertion: `K` is Lipschitzian on every closed bounded
subset of `C × D`.

Specialises `ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact`. In `ℝᵐ⁺ⁿ` a closed bounded set is
compact, and a compact subset of `C × D` lies in the rectangle spanned by its two projections. -/
theorem theorem_35_1_lipschitzian (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) {E : Set (Rn m × Rn n)} (hEcl : IsClosed E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ q ∈ E, ∀ p ∈ E, |K q - K p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  obtain ⟨k, hk⟩ := hK.exists_lipschitzOnWith_of_isCompact hC hD hS hSC' hT hTD'
  exact exists_lipschitz_of_lipschitzOnWith (hk.mono hrect)

end Thm351

/-! ### Theorem 35.2 -/

section Thm352

variable {m n : ℕ} {ι : Type*} {C C' : Set (Rn m)} {D D' : Set (Rn n)}

/-- **Rockafellar, Theorem 35.2.** Let `C` and `D` be relatively open convex sets in `ℝᵐ` and `ℝⁿ`,
and let `{K i | i ∈ I}` be a collection of finite concave-convex functions on `C × D`. Suppose
`C′ ⊆ C` and `D′ ⊆ D` are such that `cl (C′ × D′) ⊇ C × D` and `{K i}` is pointwise bounded on
`C′ × D′`. Then, relative to every closed bounded subset of `C × D`, `{K i}` is uniformly bounded
and equi-Lipschitzian.

Specialises `exists_forall_abs_le_and_lipschitzOnWith_prod`, which — like the book — indexes the
family by an arbitrary type, so `I` may be empty.

**Divergence.** The book's hypothesis is `conv (cl (C′ × D′)) ⊇ C × D`; this is the same statement
with the convex hull dropped. `Rockafellar.theorem_10_6_ab` records the same weakening for §10, of
which this theorem is the two-variable case. -/
theorem theorem_35_2 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    {K : ι → Rn m × Rn n → ℝ} (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v)))
    {E : Set (Rn m × Rn n)} (hEcl : IsClosed E) (hEb : Bornology.IsBounded E)
    (hEsub : E ⊆ C ×ˢ D) :
    (∃ α₁ α₂ : ℝ, ∀ p ∈ E, ∀ i, α₁ ≤ K i p ∧ K i p ≤ α₂) ∧
      ∃ α : ℝ, 0 ≤ α ∧ ∀ i, ∀ q ∈ E, ∀ p ∈ E, |K i q - K i p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨⟨M, hM0, hM⟩, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod hC hD hK
    hC'ri hCd hD'ri hDd hbdd hS hSC' hT hTD'
  refine ⟨⟨-M, M, fun p hp i => abs_le.1 (hM i p (hrect hp))⟩, k, k.coe_nonneg,
    fun i q hq p hp => ?_⟩
  have hd := ((hk i).mono hrect).dist_le_mul q hq p hp
  rwa [Real.dist_eq, dist_eq_norm] at hd

end Thm352

/-! ### Theorem 35.3 -/

section Thm353

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {T : Type*} [TopologicalSpace T]
  [LocallyCompactSpace T] {F : (Rn m × Rn n) × T → ℝ}

/-- **Rockafellar, Theorem 35.3.** Let `C` and `D` be relatively open convex sets in `ℝᵐ` and `ℝⁿ`,
and let `T` be any locally compact topological space. Let `K` be a real-valued function on
`C × D × T` such that `K (u, v, t)` is concave in `u` for each `v` and `t`, convex in `v` for each
`u` and `t`, and continuous in `t` for each `u` and `v`. Then `K` is jointly continuous on
`C × D × T`.

Specialises `continuousOn_prod_of_concaveConvexOn'`. `T` is a type, so "continuous on `C × D × T`"
is `ContinuousOn F ((C ×ˢ D) ×ˢ univ)`; the backbone groups the two convex variables together,
as `(u, v)`, because the concave-convex hypothesis lives on the pair. -/
theorem theorem_35_3 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hcont : ∀ u ∈ C, ∀ v ∈ D, Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hc : ∀ u ∈ ri C, ∀ v ∈ ri D, Continuous fun t => F ((u, v), t) := by
    rw [hCro, hDro]; exact hcont
  have h := continuousOn_prod_of_concaveConvexOn' hC hD hF hc
  rwa [hCro, hDro] at h

/-- **Rockafellar, Theorem 35.3**, weakened hypothesis: continuity in `t` need only hold at the
points of dense subsets `C′` and `D′` of `C` and `D`.

Specialises `continuousOn_prod_of_concaveConvexOn`. -/
theorem theorem_35_3_dense (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcont : ∀ u ∈ C', ∀ v ∈ D', Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  have h := continuousOn_prod_of_concaveConvexOn hC hD hF hC'ri hCd hD'ri hDd hcont
  rwa [hCro, hDro] at h

end Thm353

/-! ### Theorems 35.4 and 35.5 -/

section Convergence

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {K : ℕ → Rn m × Rn n → ℝ}

/-- **Rockafellar, Theorem 35.4.** Let `C` and `D` be relatively open convex sets in `ℝᵐ` and `ℝⁿ`,
and let `K 1, K 2, …` be a sequence of finite concave-convex functions on `C × D`. Suppose that for
each `(u, v)` in a dense subset `C′ × D′` of `C × D` the limit of `K i (u, v)` exists and is finite.
The limit then exists for every `(u, v) ∈ C × D`, the limit function is finite and concave-convex on
`C × D`, and the convergence is uniform on each closed bounded subset of `C × D`.

Specialises `exists_tendstoUniformlyOn_prod_of_dense'`. -/
theorem theorem_35_4 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcv : ∀ u ∈ C', ∀ v ∈ D', ∃ L : ℝ, Tendsto (fun i => K i (u, v)) atTop (𝓝 L)) :
    ∃ L : Rn m × Rn n → ℝ, ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K i p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn K L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨L, hLcc, hLt, huc⟩ :=
    exists_tendstoUniformlyOn_prod_of_dense' hC hD hK hC'ri hCd hD'ri hDd hcv
  rw [hCro, hDro] at hLcc hLt
  refine ⟨L, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

/-- **Rockafellar, Theorem 35.5.** Under the hypotheses of Theorem 35.4 with "the limit exists"
weakened to "the values are bounded", some subsequence converges, uniformly on closed bounded
subsets of `C × D`, to a finite concave-convex function.

Specialises `exists_subseq_tendstoUniformlyOn_prod`. This is Arzelà–Ascoli for saddle-functions;
the book extracts the countable dense set by hand, the backbone gets it from separability. -/
theorem theorem_35_5 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v))) :
    ∃ (φ : ℕ → ℕ) (L : Rn m × Rn n → ℝ), StrictMono φ ∧ ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K (φ i) p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn (fun i => K (φ i)) L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨φ, L, hφ, hLcc, hLt, huc⟩ :=
    exists_subseq_tendstoUniformlyOn_prod hC hD hK hC'ri hCd hD'ri hDd hbdd
  rw [hCro, hDro] at hLcc hLt
  refine ⟨φ, L, hφ, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

end Convergence

/-! ### The subdifferential of a saddle-function

Rockafellar's definition (15119–15155), for an arbitrary — hence `EReal`-valued — concave-convex
`K` on `ℝᵐ × ℝⁿ`. The two blocks carry **opposite** inequalities; see the module docstring. -/

section Subdifferential

variable {m n : ℕ}

/-- **Rockafellar's `∂₁K (u, v) = ∂_u K (u, v)`** (15119): the set of `u* ∈ ℝᵐ` with

`K (u′, v) ≤ K (u, v) + ⟨u*, u′ - u⟩` for every `u′ ∈ ℝᵐ`,

i.e. the **super**gradients at `u` of the *concave* slice `K (·, v)`. A reducible `abbrev` for the
backbone's `concaveSubgradient` at the Euclidean pairing, so this *is* that object. -/
abbrev subgrad₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m) :=
  concaveSubgradient (pairing m) (fun u => K (u, p.2)) p.1

/-- **Rockafellar's `∂₂K (u, v) = ∂_v K (u, v)`** (15140): the set of `v* ∈ ℝⁿ` with

`K (u, v) + ⟨v*, v′ - v⟩ ≤ K (u, v′)` for every `v′ ∈ ℝⁿ`,

i.e. the **sub**gradients at `v` of the *convex* slice `K (u, ·)`. Note that the inequality points
the other way from `subgrad₁`'s: that asymmetry is the whole content of the sign convention. -/
abbrev subgrad₂ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn n) :=
  subgradient (pairing n) (fun v => K (p.1, v)) p.2

/-- **Rockafellar's `∂K (u, v) = ∂₁K (u, v) × ∂₂K (u, v)`** (15150), the subdifferential of a
saddle-function. A reducible `abbrev` for `saddleSubgradient` at the two Euclidean pairings.

It is a **product**, not a set of joint subgradients, and because its two factors carry opposite
inequalities it is *not* the subdifferential of `K` read as a function on `ℝᵐ⁺ⁿ`. -/
abbrev subgrad (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m × Rn n) :=
  saddleSubgradient (pairing m) (pairing n) K p

variable {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- `∂K (u, v) = ∂₁K (u, v) × ∂₂K (u, v)`, definitionally. -/
theorem subgrad_eq_prod : subgrad K p = subgrad₁ K p ×ˢ subgrad₂ K p := rfl

/-- The defining inequality of `∂₁K (u, v)`. -/
theorem mem_subgrad₁_iff {y : Rn m} :
    y ∈ subgrad₁ K p ↔ ∀ u' : Rn m, K (u', p.2) ≤ K p + ((pairing m (u' - p.1) y : ℝ) : EReal) :=
  Iff.rfl

/-- The defining inequality of `∂₂K (u, v)`, pointing the opposite way. -/
theorem mem_subgrad₂_iff {y : Rn n} :
    y ∈ subgrad₂ K p ↔ ∀ v' : Rn n, K p + ((pairing n (v' - p.2) y : ℝ) : EReal) ≤ K (p.1, v') :=
  Iff.rfl

/-- **Where the sign flip sits.** `∂₁K` is a *concave* subdifferential: `u*` is a supergradient of
`K (·, v)` at `u` exactly when `-u*` is a subgradient of `-K (·, v)` there.

This single negation is what §37 must insert — in Corollary 37.5.2 to make the relation monotone,
and in Corollary 37.5.1 to make the correspondence `(u - u*, v + v*)` rather than a symmetric sum.
Specialises `mem_concaveSubgradient_iff_neg_mem_subgradient_neg`. -/
theorem mem_subgrad₁_iff_neg_mem_subgradient_neg {y : Rn m} :
    y ∈ subgrad₁ K p ↔ -y ∈ subgradient (pairing m) (fun u => -K (u, p.2)) p.1 :=
  mem_concaveSubgradient_iff_neg_mem_subgradient_neg

/-- **Rockafellar, §35** (15160), the remark after the definition: `∂K (u, v)` is a convex subset of
`ℝᵐ × ℝⁿ` for every `(u, v)`, with no hypothesis on `K` at all. -/
theorem convex_subgrad : Convex ℝ (subgrad K p) := convex_saddleSubgradient

end Subdifferential

/-! ### The bridge between the two readings of `∂K`

`subgradientFst C K`, `subgradientSnd D K` and `subgradientSaddle C D K`
(`Saddle/Differential.lean`) are the finite, rectangle-relative form that Theorems 35.7–35.10 run
on; `subgrad₁`, `subgrad₂` and `subgrad` are the book's global form. At `C = D = univ` they are the
same set. -/

section Bridge

variable {m n : ℕ} (K : Rn m × Rn n → ℝ) (p : Rn m × Rn n)

/-- `∂₁` in its finite rectangle-relative form is `∂₁` in the book's global form, at `C = ℝᵐ`. -/
theorem subgradFst_univ_eq :
    subgradientFst (Set.univ : Set (Rn m)) K p = subgrad₁ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_subgradientFst, Set.mem_univ, forall_const, mem_concaveSubgradient,
    pairing_apply]
  refine forall_congr' fun u' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- `∂₂` in its finite rectangle-relative form is `∂₂` in the book's global form, at `D = ℝⁿ`. -/
theorem subgradSnd_univ_eq :
    subgradientSnd (Set.univ : Set (Rn n)) K p = subgrad₂ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_subgradientSnd, Set.mem_univ, forall_const, mem_subgradient, pairing_apply]
  refine forall_congr' fun v' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- `∂K` in its finite rectangle-relative form is `∂K` in the book's global form, at
`C × D = ℝᵐ × ℝⁿ`. -/
theorem subgradSaddle_univ_eq :
    subgradientSaddle (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K p
      = subgrad (fun z => ((K z : ℝ) : EReal)) p := by
  rw [subgrad_eq_prod, ← subgradFst_univ_eq, ← subgradSnd_univ_eq]
  rfl

end Bridge

/-! ### Theorem 35.6, the splitting identity

The only fully general result of the section, and the pivot on which `∂K = ∂₁K × ∂₂K` rests. -/

section Thm356

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}

/-- **Rockafellar, Theorem 35.6**, the displayed equation: for a concave-convex `K` finite on an
open convex `C × D` and `(u, v) ∈ C × D`,

`K′(u, v; u′, v′) = K′(u, v; u′, 0) + K′(u, v; 0, v′)`.

Specialises `dirDerivReal_prod`, `dirDerivReal_prod_fst` and `dirDerivReal_prod_snd`. Convexity of
`C` and `D` is not needed: the proof uses only that each point has a segment of room around it in
each variable separately. -/
theorem theorem_35_6 (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D) (_hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) q
      = dirDerivReal K (u, v) (q.1, 0) + dirDerivReal K (u, v) (0, q.2) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q, dirDerivReal_prod_fst hCo hDo hK hu hv q.1,
    dirDerivReal_prod_snd hCo hDo hK hu hv q.2]

/-- **Rockafellar, Theorem 35.6**, the existence clause: the joint difference quotient really has a
limit, so `K′(u, v; u′, v′)` exists. This is the part the book calls "problematical" (15053) for a
general saddle-function and settles here. Specialises `tendsto_slope_dirDerivReal_prod`. -/
theorem theorem_35_6_tendsto (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (q : Rn m × Rn n) :
    Tendsto (fun t : ℝ => (K ((u, v) + t • q) - K (u, v)) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (dirDerivReal K (u, v) q)) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q]
  exact tendsto_slope_dirDerivReal_prod hCo hDo hK hu hv q

/-- **Rockafellar, Theorem 35.6**, the shape clause: `K′(u, v; ·, ·)` is a finite concave-convex
function of `(u′, v′)` on the whole of `ℝᵐ × ℝⁿ`. Specialises `concaveConvexOn_dirDerivReal`. -/
theorem theorem_35_6_concaveConvex (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n))
      (dirDerivReal K (u, v)) :=
  concaveConvexOn_dirDerivReal hCo hDo hK hu hv

/-- **Rockafellar, Theorem 35.6**, the homogeneity clause: `K′(u, v; ·, ·)` is positively
homogeneous. Specialises `dirDerivReal_prod_smul`. -/
theorem theorem_35_6_posHom (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {c : ℝ}
    (hc : 0 < c) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) (c • q) = c * dirDerivReal K (u, v) q :=
  dirDerivReal_prod_smul hCo hDo hK hu hv hc q

end Thm356

/-! ### Theorem 35.7 and Corollary 35.7.1 -/

section Thm357

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {Ks : ℕ → Rn m × Rn n → ℝ}
  {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n} {us : ℕ → Rn m} {vs : ℕ → Rn n}

/-- **Rockafellar, Theorem 35.7**, first displayed inequality:
`liminf_i K_i′(u_i, v_i; u′, 0) ≥ K′(u, v; u′, 0)`.

Spelled without junk values: every real `μ` below `K′(u, v; u′, 0)` eventually falls below
`K_i′(u_i, v_i; u′, 0)`. Specialises `eventually_lt_dirDerivReal_fst`, with Theorem 35.6 used to
read the partial derivative off the joint one at each `(u_i, v_i)`.

The book calls this "immediate from Theorem 24.5 and the continuity properties of `K`"; the step it
leaves out is `tendsto_eval_prod_of_tendsto`, that finite concave-convex functions converge
*continuously* — `K i (u i, v i) → K (u, v)` along a moving sequence. -/
theorem theorem_35_7_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (u' : Rn m) {μ : ℝ}
    (hμ : μ < dirDerivReal K (u, v) (u', 0)) :
    ∀ᶠ i in atTop, μ < dirDerivReal (Ks i) (us i, vs i) (u', 0) := by
  rw [dirDerivReal_prod_fst hCo hDo hK hu hv u'] at hμ
  filter_upwards [eventually_lt_dirDerivReal_fst hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_fst hCo hDo (hKs i) hui hvi u']

/-- **Rockafellar, Theorem 35.7**, second displayed inequality:
`limsup_i K_i′(u_i, v_i; 0, v′) ≤ K′(u, v; 0, v′)`.

Specialises `eventually_dirDerivReal_snd_lt`, spelled as for `theorem_35_7_fst`. -/
theorem theorem_35_7_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (v' : Rn n) {μ : ℝ}
    (hμ : dirDerivReal K (u, v) (0, v') < μ) :
    ∀ᶠ i in atTop, dirDerivReal (Ks i) (us i, vs i) (0, v') < μ := by
  rw [dirDerivReal_prod_snd hCo hDo hK hu hv v'] at hμ
  filter_upwards [eventually_dirDerivReal_snd_lt hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_snd hCo hDo (hKs i) hui hvi v']

/-- **Rockafellar, Theorem 35.7**, third assertion: given `ε > 0` there is an `i₀` with

`∂K_i (u_i, v_i) ⊆ ∂K (u, v) + εB` for all `i ≥ i₀`.

Specialises `eventually_subgradientSaddle_subset`. `B` is the *supremum* unit ball of `ℝᵐ × ℝⁿ`,
not the Euclidean one; the two differ by a factor bounded by `√2` and the statement is over all
`ε > 0`. -/
theorem theorem_35_7_subgrad (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradientSaddle C D (Ks i) (us i, vs i)
      ⊆ subgradientSaddle C D K (u, v) + Metric.closedBall (0 : Rn m × Rn n) ε :=
  eventually_subgradientSaddle_subset hCo hC hDo hD hKs hK hconv hu hv hus hvs hε

/-- **Rockafellar, Corollary 35.7.1**, first assertion: for each `u′`, `K′(u, v; u′, 0)` is a
lower semicontinuous function of `(u, v)` on `C × D`.

Specialises `lowerSemicontinuousAt_dirDerivReal_fst`, which is Theorem 35.7 for the constant
sequence `K, K, K, …` — the book's own proof. -/
theorem corollary_35_7_1_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (u' : Rn m) :
    LowerSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun w => K (w, p.2)) p.1 u')
      (u, v) :=
  lowerSemicontinuousAt_dirDerivReal_fst hCo hC hDo hD hK hu hv u'

/-- **Rockafellar, Corollary 35.7.1**, second assertion: for each `v′`, `K′(u, v; 0, v′)` is an
upper semicontinuous function of `(u, v)` on `C × D`.

Specialises `upperSemicontinuousAt_dirDerivReal_snd`. -/
theorem corollary_35_7_1_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (v' : Rn n) :
    UpperSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun x => K (p.1, x)) p.2 v')
      (u, v) :=
  upperSemicontinuousAt_dirDerivReal_snd hCo hC hDo hD hK hu hv v'

/-- **Rockafellar, Corollary 35.7.1**, third assertion: given `(u, v) ∈ C × D` and `ε > 0` there is
a `δ > 0` with `∂K (x, y) ⊆ ∂K (u, v) + εB` for every `(x, y)` within `δ` of `(u, v)`.

Specialises `eventually_nhds_subgradientSaddle_subset`, which states the same thing as an
eventuality in `𝓝 (u, v)`; on a metric space the two are the same. -/
theorem corollary_35_7_1_subgrad (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : Rn m × Rn n, dist p (u, v) < δ →
      subgradientSaddle C D K p ⊆ subgradientSaddle C D K (u, v)
        + Metric.closedBall (0 : Rn m × Rn n) ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_subgradientSaddle_subset hCo hC hDo hD hK hu hv hε)
  exact ⟨δ, hδ, fun p hp => h hp⟩

end Thm357

/-! ### Theorem 35.8 and Corollary 35.8.1 -/

section Thm358

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}
  {q : Rn m × Rn n}

/-- **Rockafellar, Theorem 35.8**, first half: if `K` is differentiable at `(u, v)`, then
`∇K (u, v)` is the unique subgradient of `K` there.

Specialises `subgradientSaddle_eq_singleton_of_hasSaddleGradientAt`. `HasSaddleGradientAt K q p` is
`∇K p = q` with `q` a *pair* of vectors: a product of inner-product spaces carries the supremum
norm in Mathlib, so `∇K (u, v)` cannot be a single vector of an inner-product space. -/
theorem theorem_35_8_gradient (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (hd : HasSaddleGradientAt K q (u, v)) : subgradientSaddle C D K (u, v) = {q} :=
  subgradientSaddle_eq_singleton_of_hasSaddleGradientAt hCo hDo hK hu hv hd

/-- **Rockafellar, Theorem 35.8**: `K` is differentiable at `(u, v)` if and only if it has a unique
subgradient there.

Specialises `differentiableAt_iff_exists_subgradientSaddle_eq_singleton`. The book's converse is
proved by applying Theorem 35.4 to the rescalings `h_λ`; the backbone proves it from Corollary
35.7.1, which is downstream of Theorem 35.4 anyway and gives the Fréchet estimate directly. -/
theorem theorem_35_8 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ ∃ q, subgradientSaddle C D K (u, v) = {q} :=
  differentiableAt_iff_exists_subgradientSaddle_eq_singleton hCo hC hDo hD hK hu hv

/-- **Rockafellar, Corollary 35.8.1**: for a concave-convex `K` finite on a neighbourhood of
`(u, v)` — here, on the open rectangle `C × D` — differentiability at `(u, v)` is exactly linearity
of the directional derivative function `K′(u, v; ·, ·)`.

Specialises `differentiableAt_iff_isLinearMap_dirDerivReal`. The corollary's last clause, that
finiteness of the `m + n` two-sided partial derivatives already suffices, is not formalised: it is a
statement about a coordinate basis rather than about the space. -/
theorem corollary_35_8_1 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ IsLinearMap ℝ (dirDerivReal K (u, v)) :=
  differentiableAt_iff_isLinearMap_dirDerivReal hCo hC hDo hD hK hu hv

end Thm358

/-! ### Theorems 35.9 and 35.10 -/

section Rademacher

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Rockafellar, Theorem 35.9**, the measure-zero clause: the set of points of `C × D` at which a
finite concave-convex `K` fails to be differentiable is a null set.

Specialises `measure_diff_differentiableAt_of_concaveConvexOn`. The book's proof decomposes the
complement into the closed sets where a one-sided partial derivative jumps by at least `1/k` and
runs a Fubini argument; the backbone uses Theorem 35.1 on a ball plus Mathlib's Rademacher theorem,
exactly as §25 does. -/
theorem theorem_35_9_measure (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) :
    volume ((C ×ˢ D) \ {p : Rn m × Rn n | DifferentiableAt ℝ K p}) = 0 := by
  have : (volume : Measure (Rn m × Rn n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  exact measure_diff_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Rockafellar, Theorem 35.9**, the density clause: the set `E` of points of `C × D` at which `K`
is differentiable is dense in `C × D`.

Specialises `subset_closure_differentiableAt_of_concaveConvexOn`. -/
theorem theorem_35_9_dense (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) : C ×ˢ D ⊆ closure {p : Rn m × Rn n | DifferentiableAt ℝ K p} :=
  subset_closure_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Rockafellar, Theorem 35.9**, the continuity clause: the gradient mapping `∇K` is continuous
from `E` to `ℝᵐ × ℝⁿ`.

Specialises `continuousOn_saddleGradient`, which is Corollary 35.7.1 with both subdifferentials
collapsed to singletons by Theorem 35.8. There is no canonical `∇K` without choice, so the statement
takes any `G` representing it on `S`; `prodInnerL` is injective, so `G` is unique there. Taking
`S = E` gives the book's statement. -/
theorem theorem_35_9_continuousOn (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) {S : Set (Rn m × Rn n)} (hS : S ⊆ C ×ˢ D)
    {G : Rn m × Rn n → Rn m × Rn n} (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) :
    ContinuousOn G S :=
  continuousOn_saddleGradient hCo hC hDo hD hK hS hG

/-- **Rockafellar, Theorem 35.10**: if finite differentiable concave-convex functions `K i` converge
pointwise on the open convex `C × D` to a finite differentiable concave-convex `K`, then
`∇K i (u, v) → ∇K (u, v)` for every `(u, v) ∈ C × D`.

Specialises `tendsto_of_hasSaddleGradientAt`, which is Theorem 35.7 at a constant sequence of points
with the subdifferentials collapsed by Theorem 35.8. Differentiability is needed only at the point
in question, not everywhere as the book assumes. -/
theorem theorem_35_10 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) {p : Rn m × Rn n}
    (hp : p ∈ C ×ˢ D) {G : ℕ → Rn m × Rn n} {G' : Rn m × Rn n}
    (hG : ∀ i, HasSaddleGradientAt (Ks i) (G i) p) (hG' : HasSaddleGradientAt K G' p) :
    Tendsto G atTop (𝓝 G') :=
  tendsto_of_hasSaddleGradientAt hCo hC hDo hD hKs hK hconv hp hG hG'

/-- **Rockafellar, Theorem 35.10**, the last sentence: the gradient mappings converge uniformly on
every closed bounded subset of `C × D`.

Specialises `tendstoUniformlyOn_saddleGradient`. The book cites Theorems 35.4 and 35.9; the backbone
follows the proof of Theorem 25.7 instead, which needs only Theorem 35.7 and Corollary 35.7.1 —
both of which have already absorbed Theorem 35.4. -/
theorem theorem_35_10_uniform (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p)))
    {Gs : ℕ → Rn m × Rn n → Rn m × Rn n} {G : Rn m × Rn n → Rn m × Rn n}
    (hGs : ∀ i, ∀ p ∈ C ×ˢ D, HasSaddleGradientAt (Ks i) (Gs i p) p)
    (hG : ∀ p ∈ C ×ˢ D, HasSaddleGradientAt K (G p) p) {E : Set (Rn m × Rn n)}
    (hEcl : IsClosed E) (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    TendstoUniformlyOn Gs G atTop E :=
  tendstoUniformlyOn_saddleGradient hCo hC hDo hD hKs hK hconv hGs hG
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub

end Rademacher

end Rockafellar
