/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Correspondence
import Tdaf.Analysis.Convex.Saddle.Minimax
import Tdaf.Surface.Rockafellar.Part6.Section29

/-!
# Rockafellar, §30: Adjoint Bifunctions and Dual Programs

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §30, pp. 307–326: the **adjoint** `F*` of a
convex bifunction, the **dual program** `(P*)` it defines, and the exact circumstances — Rockafellar
calls them *normality* — under which the two programs have the same optimal value.

All ten numbered results are here: Theorems 30.1–30.5 and Corollaries 30.2.1, 30.2.2, 30.2.3, 30.5.1
and 30.5.2, with one declaration per clause for the three multi-clause results (sixteen clause rows
in all). With them: the **Gale–Kuhn–Tucker Duality Theorem**, which the book names in running text
and never states as a numbered result; the adjoint of the indicator bifunction of a linear
transformation, which is what justifies the word "adjoint"; the Lagrangian reading of the two
objective functions that §36 takes up; and both of the section's unnumbered counterexamples.

## Contents

| label | declaration |
|---|---|
| §30 definitions, 12281, 12357, 12615, 12627 | `dualProgram`, `dualProgram_apply`,
  `dualProgram_zero_apply`, `normal_iff_clFn_infBifun_zero`,
  `concaveNormal_iff_clConcave_supBifun_zero` |
| Theorem 30.1 | `theorem_30_1_concave`, `theorem_30_1_closed`, `theorem_30_1_proper`,
  `theorem_30_1_biadjoint`, `theorem_30_1_biadjoint_closed`, `theorem_30_1_injective`,
  `theorem_30_1_polyhedral` |
| §30 example, 12313 | `linearIndicatorBifun_self`,
  `linearIndicatorBifun_of_ne`, `dualProgram_linearIndicatorBifun` |
| Theorem 30.2 | `theorem_30_2_first`, `theorem_30_2_second`, `theorem_30_2_third`,
  `theorem_30_2_fourth` |
| §30 remark, 12511–12531 | `dualProgram_zero_eq_iInf_lagrangian`, `objective_eq_iSup_lagrangian`,
  `supBifun_dualProgram_eq_maximin`, `infBifun_eq_minimax` |
| Corollary 30.2.1 | `corollary_30_2_1_dual`, `corollary_30_2_1_dual'`,
  `corollary_30_2_1_primal`, `corollary_30_2_1_primal'` |
| Corollary 30.2.2 | `corollary_30_2_2_first`, `corollary_30_2_2_second`,
  `corollary_30_2_2_weak` |
| Corollary 30.2.3 | `corollary_30_2_3_first`, `corollary_30_2_3_second` |
| Theorem 30.3 | `theorem_30_3`, `theorem_30_3_a_iff_b`, `theorem_30_3_a_iff_c`,
  `theorem_30_3_b_iff_c` |
| Theorem 30.4 | `theorem_30_4_a`, `theorem_30_4_a'`, `theorem_30_4_b`, `theorem_30_4_c`,
  `theorem_30_4_d`, `theorem_30_4_e`, `theorem_30_4_f`, `theorem_30_4_g`, `theorem_30_4_h`,
  `theorem_30_4_i`, `theorem_30_4_j` |
| §30 running text, 12667 | `gale_kuhn_tucker_duality` |
| Theorem 30.5 | `theorem_30_5`, `theorem_30_5_dual` |
| Corollary 30.5.1 | `corollary_30_5_1`, `corollary_30_5_1_a_iff_b`, `corollary_30_5_1_b_iff_c`,
  `corollary_30_5_1_a_iff_c`, `corollary_30_5_1_eq` |
| Corollary 30.5.2 | `corollary_30_5_2`, `corollary_30_5_2_dual` |
| §30 counterexample, 12671 | `abnormalBifun`, `abnormalBifun_of_mem`, `abnormalBifun_of_notMem`,
  `zero_le_abnormalBifun`, `zero_le_infBifun_abnormalBifun`, `infBifun_abnormalBifun_zero`,
  `infBifun_abnormalBifun_of_pos`, `infBifun_abnormalBifun_of_neg`,
  `supBifun_dualProgram_abnormalBifun_zero`, `abnormalBifun_duality_gap`,
  `not_normal_abnormalBifun` |
| §30 counterexample, 12715 | `noDualSolutionBifun`, `noDualSolutionBifun_of_le`,
  `noDualSolutionBifun_of_lt`, `noDualSolutionBifun_zero_zero`, `noDualSolutionBifun_zero_of_ne`,
  `argmin_noDualSolutionBifun`, `infBifun_noDualSolutionBifun_zero`,
  `convexBifun_noDualSolutionBifun`, `closedBifun_noDualSolutionBifun`,
  `proper_noDualSolutionBifun_zero`, `normal_noDualSolutionBifun`,
  `infBifun_noDualSolutionBifun_le`, `kuhnTucker_noDualSolutionBifun`,
  `argmax_dualProgram_noDualSolutionBifun` |

The two counterexamples are placed at the end of the file rather than at their line numbers, because
each of them cites a theorem stated further on: the p. 316 example is shown normal by
Theorem 30.4(i) and dual-solution-free by Theorem 30.5.

## The section's definitions

* `Rockafellar.dualProgram F` — Rockafellar's `F*` (12281), the adjoint of a convex bifunction from
  `ℝᵐ` to `ℝⁿ`, which *is* the bifunction of the dual program `(P*)` (12357). It is an `abbrev` for
  the backbone's `adjointBifun (pairing m) (pairing n) F`, so it is the backbone object and not a
  copy of it, and `dualProgram_apply` — the book's own formula — holds by `rfl`.
* `Rockafellar.linearIndicatorBifun A` (§29) — the convex indicator bifunction `(Fu)(x) = δ(x | Au)`
  of a
  linear transformation (12313). Named with the `linear` prefix because the backbone's
  `indicatorBifun` is the indicator bifunction of a *convex process* (`Bifunction/Process.lean`),
  of which this is the linear-map case.
* `Rockafellar.abnormalBifun`, `Rockafellar.noDualSolutionBifun` — the section's two
  counterexamples, transcribed as Lean definitions on `Rn 1`.

**Everything else is the backbone's vocabulary, not a surface copy.** `Normal`, `ConcaveNormal`,
`ConcaveConsistent`, `ConcaveStronglyConsistent`, `ConcaveKuhnTucker`, `ConcavePolyhedralBifun`,
`supBifun`, `domConcaveBifun`, `concaveAdjointBifun` and `clBifun` are all defined in
`Optimization/{Adjoint,Normal}.lean` with Rockafellar's own definitions;
`normal_iff_clFn_infBifun_zero` and `concaveNormal_iff_clConcave_supBifun_zero` record the two
definitions of §30 in the book's own words (12615, 12627) and both are `Iff.rfl`.

## Where the book's hypotheses had to change

**Theorem 30.4(i) and (j) are false as the book states them, and carry a properness hypothesis
here.** Rockafellar disposes of them in six words: "Of course, (i) and (j) are contained in (g) and
(h)" (12665). The containment needs the objective to be proper. Without it "optimal solution" and
"optimal value" come apart: over a zero-dimensional `X` with `F0 ≡ +∞` every point is an optimal
solution, so the set of them is non-empty and bounded, while no sublevel set of `F0` is non-empty.
`theorem_30_4_i` therefore takes `Proper (F 0)` and `theorem_30_4_j` takes
`Proper fun v => -(F* 0) v`; with those the book's containment is exactly right.

**Four statements drop the closedness the book assumes.** Corollary 30.2.1's first half, Corollary
30.2.2's first formula, Corollary 30.2.3's first formula and Theorem 30.3's (a) ⟺ (c) are stated for
an arbitrary convex bifunction. The reason is uniform: each of them runs on Fenchel–Moreau for
`inf F`, and the adjoint cannot see the difference between `F` and `cl F` at all
(`adjointBifun_clBifun`). Closedness enters only where `F** = F` has to be turned back into `F`,
which is the *second* formula of each pair and clause (b) of Theorem 30.3.

**Theorem 30.1's properness clause is an `iff`, and closedness is used in one direction only.**
`theorem_30_1_proper` reads `ProperConcave (graph F*) ↔ Proper (graph F)`; this is Theorem 12.2
(`proper_conj_iff`) transported across the reflection `(x*, u*) ↦ (-u*, x*)`, and Theorem 12.2's own
closedness hypothesis is what the "⇐" direction pays.

**The Gale–Kuhn–Tucker theorem is stated for a polyhedral closed convex bifunction**, not for the
particular linear program of 12395. Rockafellar's sentence is "These are polyhedral convex programs,
so it follows that the optimal value in `(P)` and the optimal value in `(P*)` are equal, unless both
programs are inconsistent" (12667) — polyhedrality is the whole hypothesis his argument uses, and
`theorem_30_1_polyhedral` supplies the polyhedrality of `(P*)` that clause (f) then consumes.

**Theorem 30.5's dual assertion is proved, not asserted.** The book says only "The proof of the dual
assertion of the theorem is parallel" (12701). The proof here is not the parallel one: the
defining supremum of a concave Kuhn–Tucker vector *is* the second adjoint evaluated at that point
(`concaveAdjointBifun_zero_apply`), and Theorem 30.1's `F** = F` turns it into `(F0)(x)` in one
rewrite.

## What is not here

**The two worked dual pairs of 12395 and 12429** — the classical linear program
`(Fu)(x) = ⟨a*, x⟩ + δ(x | x ≥ 0, a - Ax ≤ u)` and the decomposition-principle program
`(Fu)(x) = f₀(x) + δ(x | Ax = a + u)` — are *omitted with a reason*. Both are computations of `F*`
for one particular `F`; neither is a numbered result, and neither is used later in the section. What
the surface carries instead is the general formula (`dualProgram_apply`), the adjoint of a linear
indicator bifunction (`dualProgram_linearIndicatorBifun`, which is the same computation with the
objective and the constraints stripped away), and the Gale–Kuhn–Tucker theorem at the generality its
proof actually has. Making the linear program itself a Lean object would additionally require
`PolyhedralBifun` for `⟨a*, x⟩ + δ(x | x ≥ 0, a - Ax ≤ u)`, which is §19 machinery and not §30's.

**The example deposit at 12731–13136**, "duals of ordinary convex programs", is *omitted with a
reason*, and it is worth saying what it contains. Four hundred lines, no numbered result, and three
programs: `(P)` with inequality constraints, whose adjoint is computed as an infimal convolution
`-(f₀* □ f₁*v₁* □ ⋯ □ f_m*v_m*)(x*)` for `u* ≥ 0`; the program `(Q)` with the constraint functions
additionally translated, whose adjoint is explicit; and the "intermediate" `(R)` in which each `fᵢ`
is written as `hᵢ(Aᵢx + aᵢ) + ⟨aᵢ*, x⟩ + αᵢ`, ending with the log-sum-exp illustration that is
geometric programming. The one identity in it with theorem-like content is
`(F*0)(u*) = inf (f₀ + v₁*f₁ + ⋯ + v_m*f_m)` for `u* ≥ 0` (12861) — the dual objective is the
infimum of the Lagrangian — and that is already carried, in the general form Rockafellar states it
in at 12511, by `dualProgram_zero_eq_iInf_lagrangian`. Everything else is `m`-ary §16 calculus
(Theorems 16.1 and 16.4 with right scalar multiples) plus bookkeeping over
`ℝᵏ = ℝᵐ × ℝⁿ × ⋯ × ℝⁿ`; carrying it would formalise §16's `m`-ary infimal convolution, not §30.

**The surjectivity half of Theorem 30.1's one-to-one correspondence.** `theorem_30_1_injective` says
that a closed convex bifunction is determined by its adjoint. The other half — that every closed
proper *concave* bifunction from `ℝⁿ` to `ℝᵐ` is `F*` for some closed proper convex `F` — needs the
concave-side biadjoint `G** = cl G`, which the backbone does not have. See `## Backbone gaps`.

**The abnormal example of 12671 is transcribed and its decisive halves are proved, but it is not
shown to be a convex bifunction.** Rockafellar calls it "the closed proper convex bifunction `F`";
what is proved here is `inf F0 = 1` (`infBifun_abnormalBifun_zero`), `inf Fu = 0` for `u > 0` and
`inf Fu = +∞` for `u < 0` — the perturbation function the book displays — the failure of normality
(`not_normal_abnormalBifun`, proved from the perturbation function with no appeal to convexity) and
`sup F*0 = 0` (`supBifun_dualProgram_abnormalBifun_zero`), so the duality gap the example exists to
exhibit is `abnormalBifun_duality_gap`. Its convexity is the concavity of the geometric mean
`(u, x) ↦ √(ux)` on the first quadrant composed with the increasing convex `exp`, which is
elementary two-variable real analysis with no convex-analytic content. See `## Backbone gaps`.

**The concave translation of §29.** Rockafellar writes at 12261 that "the results in §29 can be
translated into this terminology without difficulty", and does not do it. Neither does this file:
what §30 actually consumes is `ConcaveConsistent`, `ConcaveStronglyConsistent`, `ConcaveNormal`,
`ConcaveKuhnTucker` and `ConcavePolyhedralBifun`, all of which the backbone has, each defined as its
convex counterpart at the negated bifunction so that no mirror proof is needed.

## Backbone gaps

Almost everything this file once carried `private` is now in the backbone; what is left is
recorded below with the signature wanted and the module it belongs in.

* `Optimization/Normal.lean` — **Corollary 30.5.2's second assertion**, that a strongly consistent
  program with a consistent dual has a dual optimal solution. The first assertion is in the backbone
  (`exists_infBifun_eq_of_concaveStronglyConsistent`); the second is `corollary_30_5_2_dual` here,
  five lines on `kuhnTucker_nonempty_of_stronglyConsistent` and Theorem 30.5.
* **Not in this repository at all**: the convexity of the abnormal example. What is wanted is
  `theorem concaveOn_sqrt_mul : ConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  fun p => Real.sqrt (p.1 * p.2)` — the geometric mean is concave on the first quadrant — together
  with "a nondecreasing convex function of a concave function is convex". With those,
  `ConvexBifun abnormalBifun`, `ClosedBifun abnormalBifun` and `Proper (graphFn abnormalBifun)`
  follow, and `not_normal_abnormalBifun` becomes a corollary of `abnormalBifun_duality_gap` through
  Theorem 30.3 instead of a separate `liminf` argument. It belongs in Mathlib, or failing that in
  `Tdaf/Analysis/Convex/Eponyms.lean`.
* **The concave-side biadjoint**, for the surjectivity half of Theorem 30.1:
  `theorem adjointBifun_concaveAdjointBifun_eq (hG : ConcaveBifun G) :
  adjointBifun Bu Bx (concaveAdjointBifun Bu Bx G) = <the concave closure of G, bifunction-wise>`,
  in `Optimization/Adjoint.lean`. The convex-side statement
  `concaveAdjointBifun_adjointBifun_eq_clBifun` is there; its mirror is not, and neither is a
  `clConcaveBifun`. Not attempted here.

**What the backbone gained.** `mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin` (the dual half of
Theorem 30.5) and `exists_infBifun_eq_of_concaveStronglyConsistent` (Corollary 30.5.2's first
assertion) are in `Optimization/Normal.lean`, together with `domBifun_neg` and
`concaveStronglyConsistent_iff_stronglyConsistent_neg`;
`properConcave_graphFn_adjointBifun_iff` (Theorem 30.1's properness clause as a biconditional) is in
`Optimization/Adjoint.lean`, on `proper_compLin_of_surjective` in `Operations/Image.lean`;
`mem_argmax_iff_eq_iSup` is in `Optimization/Minimum.lean`; and
`Tdaf.EReal.le_zero_of_forall_le_pos` is in `Tdaf/Order/EReal.lean`.

**A placement note, not a gap.** Theorem 30.1's polyhedrality clause *does* exist —
`polyhedralFn_neg_graphFn_adjointBifun`, whose own docstring calls it Theorem 30.1 — but it lives in
`Saddle/Correspondence.lean`, which is §33, rather than in `Optimization/Adjoint.lean`, which is
§30. That is why this file imports `Saddle/Correspondence.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30, pp. 307–326.
-/

open Filter Set Topology

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The adjoint bifunction and the dual program -/

/-- **Rockafellar's adjoint bifunction `F*`** (12281): the bifunction from `ℝⁿ` to `ℝᵐ` given by

`(F*x*)(u*) = inf_{u,x} {(Fu)(x) - ⟨x, x*⟩ + ⟨u, u*⟩}`,

which is the bifunction of the **dual program** `(P*)` (12357). The `abbrev` is the backbone's
`adjointBifun` at the two Euclidean pairings, so every backbone theorem about `adjointBifun`
applies to it verbatim; `dualProgram_apply` is the book's formula, and holds by `rfl`. -/
noncomputable abbrev dualProgram {m n : ℕ} (F : Bifun (Rn m) (Rn n)) : Bifun (Rn n) (Rn m) :=
  adjointBifun (pairing m) (pairing n) F

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- The book's defining formula for the adjoint (12281). Rockafellar writes the two brackets as
`-⟨x, x*⟩ + ⟨u, u*⟩`; the backbone groups them inside one real subtraction, which is the same
number and cannot meet `∞ - ∞`. -/
theorem dualProgram_apply (F : Bifun (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    dualProgram F y v
      = ⨅ p : Rn m × Rn n, (F p.1 p.2 + ((pairing m p.1 v - pairing n p.2 y : ℝ) : EReal)) :=
  rfl

/-- **The objective function of `(P*)`** (12357): `(F*0)(u*) = inf_u {⟨u, u*⟩ + inf Fu}`. -/
theorem dualProgram_zero_apply (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ u : Rn m, (((pairing m u v : ℝ) : EReal) + infBifun F u) :=
  adjointBifun_zero_apply (pairing m) (pairing n) F v

/-- **Rockafellar's definition of a normal convex program** (12615): `(P)` is *normal* when its
perturbation function `inf F` is closed at `u = 0`. This is the backbone's `Normal`, unfolded. -/
theorem normal_iff_clFn_infBifun_zero (F : Bifun (Rn m) (Rn n)) :
    Normal F ↔ clFn (infBifun F) 0 = infBifun F 0 := Iff.rfl

/-- **Normality of the dual program** (12627): `(P*)` is normal when `cl (sup F*)` agrees with
`sup F*` at `x* = 0`. -/
theorem concaveNormal_iff_clConcave_supBifun_zero (G : Bifun (Rn n) (Rn m)) :
    ConcaveNormal G ↔ clConcave (supBifun G) 0 = supBifun G 0 := Iff.rfl

/-! ### Theorem 30.1 -/

/-- **Rockafellar, Theorem 30.1** (12303), the concavity clause: the adjoint of *any* bifunction
from `ℝᵐ` to `ℝⁿ` is a concave bifunction from `ℝⁿ` to `ℝᵐ`.

The book deduces this from the identity `(F*x*)(u*) = -f*(-u*, x*)` displayed just above the
theorem (12281–12297); no hypothesis on `F` is used, and none is carried here. -/
theorem theorem_30_1_concave (F : Bifun (Rn m) (Rn n)) : ConcaveBifun (dualProgram F) :=
  concaveBifun_adjointBifun (pairing m) (pairing n) F

/-- **Rockafellar, Theorem 30.1** (12303), the closedness clause: `F*` is a *closed* concave
bifunction, again with no hypothesis on `F`. -/
theorem theorem_30_1_closed (F : Bifun (Rn m) (Rn n)) :
    ClosedConcaveFn (graphFn (dualProgram F)) :=
  closedConcaveFn_graphFn_adjointBifun (Bu := pairing m) (Bx := pairing n) (F := F)

/-- **Rockafellar, Theorem 30.1** (12303), the properness clause: `F*` is proper if and only if `F`
is, for a closed convex `F`. -/
theorem theorem_30_1_proper (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ProperConcave (graphFn (dualProgram F)) ↔ Proper (graphFn F) :=
  properConcave_graphFn_adjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Rockafellar, Theorem 30.1** (12303): `F** = cl F` for a convex bifunction. -/
theorem theorem_30_1_biadjoint (hF : ConvexBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = clBifun F :=
  concaveAdjointBifun_adjointBifun_eq_clBifun hF

/-- **Rockafellar, Theorem 30.1** (12309): `F** = F` when `F` is closed — which is why the program
dual to `(P*)` is `(P)` again (12369). -/
theorem theorem_30_1_biadjoint_closed (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = F :=
  concaveAdjointBifun_adjointBifun_eq_self hF hcl

/-- **Rockafellar, Theorem 30.1** (12309), the injectivity half of "the adjoint operation
establishes a one-to-one correspondence": two closed convex bifunctions with the same adjoint are
equal. See `## What is not here` for the surjectivity half. -/
theorem theorem_30_1_injective {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : ConvexBifun F₁)
    (hcl₁ : ClosedBifun F₁) (hF₂ : ConvexBifun F₂) (hcl₂ : ClosedBifun F₂)
    (h : dualProgram F₁ = dualProgram F₂) : F₁ = F₂ := by
  rw [← theorem_30_1_biadjoint_closed hF₁ hcl₁, ← theorem_30_1_biadjoint_closed hF₂ hcl₂, h]

/-- **Rockafellar, Theorem 30.1** (12309), last clause: "If `F` is polyhedral, so is `F*`."

The book's one-line justification is Theorem 19.2, and that is what the proof uses: the conjugate
of a polyhedral function is polyhedral, and polyhedrality survives the linear reflection. Neither
properness nor closedness is needed. -/
theorem theorem_30_1_polyhedral (hF : PolyhedralBifun F) :
    ConcavePolyhedralBifun (dualProgram F) :=
  polyhedralFn_neg_graphFn_adjointBifun (pairing m) (pairing n) hF

/-! ### The adjoint of an indicator bifunction (12313)

Rockafellar's first example of the adjoint operation, and the one that justifies the name: "This
shows that the adjoint operation for bifunctions can rightly be viewed as a generalization of the
adjoint operation for linear transformations" (12345). -/

/-! `linearIndicatorBifun` itself is §29's, defined at the book's earlier appearance of this same
example (11639) as the backbone's indicator bifunction of the convex process `ofLinearMap A`; that
route carries its convexity, closedness, properness and `dom F = ℝᵐ` with it. Only the two
evaluation lemmas the adjoint computation needs are added here. -/

@[simp] theorem linearIndicatorBifun_self (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) :
    linearIndicatorBifun A u (A u) = 0 := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_mem (Set.mem_singleton _)

theorem linearIndicatorBifun_of_ne (A : Rn m →ₗ[ℝ] Rn n) {u : Rn m} {x : Rn n} (h : x ≠ A u) :
    linearIndicatorBifun A u x = ⊤ := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_notMem (by simpa using h)

private theorem iInf_linearIndicatorBifun_slice (A : Rn m →ₗ[ℝ] Rn n) (u v : Rn m) (y : Rn n) :
    (⨅ x : Rn n, (linearIndicatorBifun A u x + ((pairing m u v - pairing n x y : ℝ) : EReal)))
      = ((pairing m u (v - LinearMap.adjoint A y) : ℝ) : EReal) := by
  have hval : (pairing m u v - pairing n (A u) y : ℝ)
      = pairing m u (v - LinearMap.adjoint A y) := by
    rw [map_sub, isAdjointPair_adjoint A u y]
  refine le_antisymm (le_trans (iInf_le _ (A u)) (le_of_eq ?_)) (le_iInf fun x => ?_)
  · rw [linearIndicatorBifun_self, zero_add, hval]
  · by_cases hx : x = A u
    · subst hx
      rw [linearIndicatorBifun_self, zero_add, hval]
    · rw [linearIndicatorBifun_of_ne A hx, _root_.EReal.top_add_coe]
      exact le_top

private theorem iInf_pairing_coe (w : Rn m) :
    (⨅ u : Rn m, ((pairing m u w : ℝ) : EReal)) = ⨆ _ : w = 0, (0 : EReal) := by
  by_cases hw : w = 0
  · rw [iSup_pos hw, hw]
    simp
  · rw [iSup_neg hw]
    refine iInf_eq_bot.2 fun b hb => ?_
    obtain ⟨c, -, hcb⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
    have hpos : 0 < pairing m w w := by
      rw [pairing_apply]
      exact real_inner_self_pos.2 hw
    refine ⟨((c - 1) / (pairing m w w)) • w, ?_⟩
    have hval : pairing m (((c - 1) / (pairing m w w)) • w) w = c - 1 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hpos.ne']
    rw [hval]
    refine lt_trans ?_ hcb
    exact_mod_cast (by linarith : c - 1 < c)

/-- **Rockafellar, §30 (12321–12345)**: the adjoint of the convex indicator bifunction of `A` is
the *concave* indicator bifunction of the adjoint transformation `A*`,

`F*x* = -δ(· | A*x*)`.

`A*` is `LinearMap.adjoint A`, and the pairing identity `⟨Au, x*⟩ = ⟨u, A*x*⟩` is
`isAdjointPair_adjoint` (design decision D3: on `ℝⁿ` the adjoint is canonical, so it is not carried
as data). -/
theorem dualProgram_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) (y : Rn n) (v : Rn m) :
    dualProgram (linearIndicatorBifun A) y v = ⨆ _ : v = LinearMap.adjoint A y, (0 : EReal) := by
  rw [dualProgram_apply, iInf_prod]
  rw [iInf_congr fun u : Rn m => iInf_linearIndicatorBifun_slice A u v y, iInf_pairing_coe]
  by_cases h : v = LinearMap.adjoint A y
  · rw [iSup_pos h, iSup_pos (sub_eq_zero.2 h)]
  · rw [iSup_neg h, iSup_neg (fun hc => h (sub_eq_zero.1 hc))]

/-! ### Theorem 30.2 -/

/-- **Rockafellar, Theorem 30.2** (12487), first formula: `(-inf F)* = F*0`. The objective function
of the dual program is the *concave* conjugate of the concave function `-inf F`.

Rockafellar's caution at 12207 is exactly what makes the concave conjugate unavoidable here:
`g* ≠ -(-g)*`, so this is **not** a statement about `conj`. -/
theorem theorem_30_2_first (F : Bifun (Rn m) (Rn n)) :
    concaveConj (pairing m) (fun u => -(infBifun F u)) = dualProgram F 0 :=
  (adjointBifun_zero_eq_concaveConj (pairing m) (pairing n) F).symm

/-- **Rockafellar, Theorem 30.2** (12493), second formula: `(F*0)* = -cl (inf F)`. -/
theorem theorem_30_2_second (hF : ConvexBifun F) :
    concaveConj (pairing m) (dualProgram F 0) = fun u => -(clFn (infBifun F) u) := by
  have hconc : ConcaveFn (fun u => -(infBifun F u)) :=
    concaveFn_iff_convexFn_neg.2 (by simpa using convexFn_infBifun hF)
  have hbi := biconcaveConj_eq_clConcave (B := pairing m) hconc
  rw [← theorem_30_2_first F]
  have hflip : concaveConj (pairing m) (concaveConj (pairing m) (fun u => -(infBifun F u)))
      = biconcaveConj (pairing m) (fun u => -(infBifun F u)) := by
    rw [biconcaveConj, flip_pairing]
  rw [hflip, hbi]
  funext u
  rw [clConcave_apply]
  simp only [neg_neg]

/-- **Rockafellar, Theorem 30.2** (12495), third formula: `(-sup F*)* = F0`. For a closed convex
`F` the objective of `(P)` is the conjugate of the convex function `-sup F*`. -/
theorem theorem_30_2_third (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    conj (pairing n) (fun y => -(supBifun (dualProgram F) y)) = F 0 := by
  have h := concaveAdjointBifun_adjointBifun_eq_self (Bu := pairing m) (Bx := pairing n) hF hcl
  rw [← conj_flip_pairing,
    ← concaveAdjointBifun_zero_eq_conj (pairing m) (pairing n) (dualProgram F), h]

/-- **Rockafellar, Theorem 30.2** (12495), fourth formula: `(F0)* = -cl (sup F*)`. -/
theorem theorem_30_2_fourth (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    conj (pairing n) (F 0) = fun y => -(clConcave (supBifun (dualProgram F)) y) := by
  have hconv : ConvexFn (fun y => -(supBifun (dualProgram F) y)) :=
    convexFn_neg_supBifun (concaveBifun_adjointBifun (pairing m) (pairing n) F)
  have hbi := biconj_eq_clFn (B := (pairing n).flip) hconv
  rw [← theorem_30_2_third hF hcl]
  have hflip : conj (pairing n) (conj (pairing n) (fun y => -(supBifun (dualProgram F) y)))
      = biconj (pairing n).flip (fun y => -(supBifun (dualProgram F) y)) := by
    rw [biconj, flip_pairing, conj_flip_pairing]
  rw [hflip, hbi]
  funext y
  rw [clConcave_apply]
  simp only [neg_neg]

/-! ### The Lagrangian form of the two objectives (12511–12531) -/

/-- **Rockafellar, §30 (12511)**, the remark after Theorem 30.2: the objective function of `(P*)`
is the infimum of the Lagrangian of `(P)` over the primal variable,
`(F*0)(u*) = inf_x L(u*, x)`. -/
theorem dualProgram_zero_eq_iInf_lagrangian (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ x : Rn n, lagrangian (pairing m) F v x :=
  (iInf_lagrangian_eq_adjointBifun_zero (Bu := pairing m) (pairing n)).symm

/-- **Rockafellar, §30 (12517)**: for a closed convex `F` the objective function of `(P)` is the
supremum of the Lagrangian over the price variable, `(F0)(x) = sup_{u*} L(u*, x)`. -/
theorem objective_eq_iSup_lagrangian (hF : ConvexBifun F) (hcl : ClosedBifun F) (x : Rn n) :
    F 0 x = ⨆ v : Rn m, lagrangian (pairing m) F v x :=
  (iSup_lagrangian_eq (Bu := pairing m) hF hcl).symm

/-- **Rockafellar, §30 (12521)**: the optimal value of `(P*)` is `sup_{u*} inf_x L(u*, x)`. -/
theorem supBifun_dualProgram_eq_maximin (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 = maximin (saddleLagrangian (pairing m) F) := by
  rw [supBifun_apply, maximin_apply]
  exact iSup_congr fun v => dualProgram_zero_eq_iInf_lagrangian F v

/-- **Rockafellar, §30 (12527)**: for a closed convex `F` the optimal value of `(P)` is
`inf_x sup_{u*} L(u*, x)`. Together with `supBifun_dualProgram_eq_maximin` this is why normality is
the existence of a saddle-value, which is the reading §36 takes up. -/
theorem infBifun_eq_minimax (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    infBifun F 0 = minimax (saddleLagrangian (pairing m) F) := by
  rw [infBifun_apply, minimax_apply]
  exact iInf_congr fun x => objective_eq_iSup_lagrangian hF hcl x

/-! ### Corollary 30.2.1 -/

/-- **Rockafellar, Corollary 30.2.1** (12557), first half: the dual program `(P*)` is inconsistent
exactly when some perturbation of `(P)` has no lower bound, i.e. `inf Fu = -∞` for some `u`.

Rockafellar states the whole corollary for closed `F`; closedness is not needed for this half,
because the adjoint never sees the difference between `F` and `cl F`. -/
theorem corollary_30_2_1_dual (hF : ConvexBifun F) :
    ¬ ConcaveConsistent (dualProgram F) ↔ ∃ u : Rn m, infBifun F u = ⊥ :=
  not_concaveConsistent_adjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Rockafellar, Corollary 30.2.1** (12557), first half, positively. -/
theorem corollary_30_2_1_dual' (hF : ConvexBifun F) :
    ConcaveConsistent (dualProgram F) ↔ ∀ u : Rn m, infBifun F u ≠ ⊥ :=
  concaveConsistent_adjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Rockafellar, Corollary 30.2.1** (12557), second half: `(P)` is inconsistent exactly when some
perturbation of `(P*)` has no upper bound, i.e. `sup F*x* = +∞` for some `x*`.

This half really does need `F` closed: it is the first half read for the dual pair, and `F** = F`
is what identifies the objective of `(P)` with the conjugate of `-sup F*`. -/
theorem corollary_30_2_1_primal (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ¬ Consistent F ↔ ∃ y : Rn n, supBifun (dualProgram F) y = ⊤ :=
  not_consistent_iff_exists_supBifun_eq_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Rockafellar, Corollary 30.2.1** (12557), second half, positively. -/
theorem corollary_30_2_1_primal' (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Consistent F ↔ ∀ y : Rn n, supBifun (dualProgram F) y ≠ ⊤ :=
  consistent_iff_forall_supBifun_ne_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-! ### Corollary 30.2.2 -/

/-- **Rockafellar, Corollary 30.2.2** (12569), first formula: `(cl (inf F))(0) = sup F*0`.

Rockafellar states it for closed convex `F`; closedness is not used — the formula is
Fenchel–Moreau for `inf F`, and `F*` does not distinguish `F` from `cl F`. -/
theorem corollary_30_2_2_first (hF : ConvexBifun F) :
    clFn (infBifun F) 0 = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := pairing m) (pairing n) hF

/-- **Rockafellar, Corollary 30.2.2** (12573), second formula: `(cl (sup F*))(0) = inf F0`. Here
closedness of `F` is what turns `F**` back into `F`. -/
theorem corollary_30_2_2_second (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    clConcave (supBifun (dualProgram F)) 0 = infBifun F 0 :=
  clConcave_supBifun_adjointBifun_zero_eq (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Rockafellar, Corollary 30.2.2** (12583), weak duality: `inf F0 ≥ sup F*0`, always. No
hypothesis at all — it is `⟨u, u*⟩ + inf Fu` evaluated at `u = 0`. -/
theorem corollary_30_2_2_weak (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 ≤ infBifun F 0 := by
  rw [supBifun_apply]
  exact iSup_adjointBifun_zero_le (pairing m) (pairing n) F

/-! ### Corollary 30.2.3 -/

/-- **Rockafellar, Corollary 30.2.3** (12597), first formula: unless *both* programs are
inconsistent,

`liminf_{u → 0} (inf Fu) = sup F*0`.

The excluded case is Rockafellar's own: `cl (inf F)` and `liminf (inf F)` differ only when the
first is `-∞`, which says `(P*)` is inconsistent, and the second is `+∞`, which forces
`inf F0 = +∞`, i.e. `(P)` inconsistent. -/
theorem corollary_30_2_3_first (hF : ConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.liminf (infBifun F) (𝓝 (0 : Rn m)) = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact liminf_infBifun_eq_iSup_adjointBifun (Bu := pairing m) (pairing n) hF h

/-- **Rockafellar, Corollary 30.2.3** (12601), second formula: unless both programs are
inconsistent, `limsup_{x* → 0} (sup F*x*) = inf F0`. -/
theorem corollary_30_2_3_second (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.limsup (supBifun (dualProgram F)) (𝓝 (0 : Rn n)) = infBifun F 0 :=
  limsup_supBifun_adjointBifun_eq (Bu := pairing m) (Bx := pairing n) hF hcl h

/-! ### Theorem 30.3 -/

/-- **Rockafellar, Theorem 30.3(a) ⟺ (c)** (12633, 12637): a convex program is normal exactly when
there is no duality gap.

Closedness of `F` is *not* needed for this equivalence, although the theorem carries it: only
Corollary 30.2.2's first formula is used, and that formula is Fenchel–Moreau for `inf F`. -/
theorem theorem_30_3_a_iff_c (hF : ConvexBifun F) :
    Normal F ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [normal_iff_iSup_adjointBifun_eq (Bu := pairing m) (pairing n) hF, supBifun_apply]
  exact eq_comm

/-- **Rockafellar, Theorem 30.3(b) ⟺ (c)** (12635, 12637). -/
theorem theorem_30_3_b_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ConcaveNormal (dualProgram F) ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [concaveNormal_adjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl, supBifun_apply]
  exact eq_comm

/-- **Rockafellar, Theorem 30.3(a) ⟺ (b)** (12633, 12635): a convex program is normal exactly when
its dual is. -/
theorem theorem_30_3_a_iff_b (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Normal F ↔ ConcaveNormal (dualProgram F) :=
  normal_iff_concaveNormal_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Rockafellar, Theorem 30.3** (12631), the three clauses as the book states them: for a closed
convex bifunction `F`, `(P)` is normal, `(P*)` is normal, and the two optimal values agree, are
equivalent. -/
theorem theorem_30_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    [Normal F, ConcaveNormal (dualProgram F),
      infBifun F 0 = supBifun (dualProgram F) 0].TFAE := by
  tfae_have 1 ↔ 2 := theorem_30_3_a_iff_b hF hcl
  tfae_have 1 ↔ 3 := theorem_30_3_a_iff_c hF
  tfae_finish

/-! ### Theorem 30.4

Rockafellar's proof (12665) argues (a), (c) and (e), says "Dually, (b), (d) and (f) imply that
normality holds", gives one compressed sentence for (g), and disposes of (h), (i) and (j) as
"special cases" and "of course … contained in". Each declaration below records what the book
supplies for its own clause. -/

/-- **Rockafellar, Theorem 30.4(a)** (12645): a *strongly* consistent convex program is normal.

**The book proves this clause.** Its argument is the one used here: `0 ∈ ri (dom (inf F))` by
Theorem 29.1, and a convex function agrees with its closure on the relative interior of its
effective domain (Theorems 7.2, 7.4). -/
theorem theorem_30_4_a (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StronglyConsistent.normal hs hF

/-- **Rockafellar, Theorem 30.4(a)** (12645), the parenthetical *strict* form. -/
theorem theorem_30_4_a' (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StrictlyConsistent.normal hs hF

/-- **Rockafellar, Theorem 30.4(b)** (12647): if the *dual* program is strongly consistent then
normality holds for the pair.

**The book does not argue this clause**: "Dually, (b), (d) and (f) imply that normality holds"
(12665). The Lean route is the dual of (a) composed with Theorem 30.3(a) ⟺ (b), so the
dualisation the book gestures at is carried out. -/
theorem theorem_30_4_b (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : Normal F :=
  normal_of_concaveStronglyConsistent_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl hs

/-- **Rockafellar, Theorem 30.4(c)** (12649): if `(P)` has a Kuhn–Tucker vector — its optimal value
being finite, which is part of the definition — then `(P)` is normal.

**The book proves this clause**, from Theorem 29.1 and Corollary 23.5.2. The route here is
different and cheaper: a Kuhn–Tucker vector is a point at which the dual objective already attains
`inf F0`, and weak duality pins the dual optimal value there, so normality is Theorem 30.3. No
subdifferential and no finite-dimensionality is involved. -/
theorem theorem_30_4_c (hF : ConvexBifun F) (h : (KuhnTucker (pairing m) F).Nonempty) :
    Normal F :=
  normal_of_kuhnTucker_nonempty (Bu := pairing m) (pairing n) hF h

/-- **Rockafellar, Theorem 30.4(d)** (12651): if the *dual* program has a Kuhn–Tucker vector then
normality holds for the pair.

**The book does not argue this clause** (12665, "Dually …"). -/
theorem theorem_30_4_d (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : (ConcaveKuhnTucker (pairing n) (dualProgram F)).Nonempty) : Normal F := by
  refine normal_of_concaveKuhnTucker_adjointBifun_nonempty (Bu := pairing m) (Bx := pairing n)
    hF hcl ?_
  rwa [flip_pairing]

/-- **Rockafellar, Theorem 30.4(e)** (12653): a polyhedral convex program that is merely
*consistent* is normal.

**The book proves this clause**: Theorem 29.2 makes `inf F` polyhedral, and a polyhedral convex
function agrees with its closure throughout its effective domain, which contains `0`. -/
theorem theorem_30_4_e (hF : PolyhedralBifun F) (hc : Consistent F) : Normal F :=
  PolyhedralBifun.normal hF hc

/-- **Rockafellar, Theorem 30.4(f)** (12655): if `(P*)` is polyhedral and consistent then normality
holds for the pair.

**The book does not argue this clause** (12665, "Dually …"). By Theorem 30.1's last clause
(`theorem_30_1_polyhedral`) the polyhedrality hypothesis is implied by polyhedrality of `F`, which
is how the Gale–Kuhn–Tucker theorem below uses it. -/
theorem theorem_30_4_f (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hG : ConcavePolyhedralBifun (dualProgram F)) (hc : ConcaveConsistent (dualProgram F)) :
    Normal F :=
  normal_of_concavePolyhedral_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl hG hc

/-- **Rockafellar, Theorem 30.4(g)** (12657): if some sublevel set of the objective `F0` is
non-empty and bounded, then normality holds.

**The book's one sentence hides the argument.** It reads: "Condition (g) is equivalent by
Theorem 27.1(d) to having `0 ∈ int (dom (F0)*)`, i.e. `(P*)` strictly consistent." The "i.e." is
not an abbreviation: `dom ((F0)*)` is `{y | (inf Fᵧ) 0 > -∞}`, while strict consistency of `(P*)`
is `0 ∈ int {y | cl (inf Fᵧ) 0 > -∞}`, an intersection over *all* perturbations `u` of the sets
`dom ((Fu)*)`, and interiors of such intersections are not automatic. What closes it is that all
slices of a closed convex bifunction have the same recession function (Theorem 8.3 on the
epigraph), so the sets are in fact *equal*. The backbone carries that argument in
`normal_of_exists_setOf_le`.

No properness is assumed: an improper closed convex bifunction has `inf F0 = -∞` and normality is
then automatic. -/
theorem theorem_30_4_g (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {x : Rn n | F 0 x ≤ (α : EReal)}.Nonempty ∧
      Bornology.IsBounded {x : Rn n | F 0 x ≤ (α : EReal)}) : Normal F :=
  normal_of_exists_setOf_le (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Rockafellar, Theorem 30.4(h)** (12659): if some superlevel set of the dual objective `F*0` is
non-empty and bounded, then normality holds.

**The book does not argue this clause**: "similarly (h) is a special case of (a)" (12665). The
route here is not the book's — no concave mirror of Theorem 27.1(d) or of Corollary 13.3.4 is
needed. `-F*` is a closed convex bifunction with no hypothesis on `F` (Theorem 30.1), the
superlevel set `{v | α ≤ (F*0) v}` *is* the sublevel set `{v | -(F*0) v ≤ -α}`, so clause (g)
applies to it, and Theorem 30.3 transports the conclusion back. -/
theorem theorem_30_4_h (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}.Nonempty ∧
      Bornology.IsBounded {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}) : Normal F :=
  normal_of_exists_setOf_ge_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Rockafellar, Theorem 30.4(i)** (12661): if the optimal solutions to `(P)` form a non-empty
bounded set — in particular if there is exactly one — then normality holds.

**The book does not argue this clause**, and as it states it the clause is *false*: "Of course, (i)
and (j) are contained in (g) and (h)" (12665). The containment needs `F0` proper. Without it
"optimal solution" and "optimal value" come apart: over a zero-dimensional `X` with `F0 ≡ +∞` the
set of optimal solutions is non-empty and bounded while no sublevel set is. `Proper (F 0)` is
therefore carried here; with it, `argmin (F0)` is a level set of `F0` at its own minimum value and
the book's containment holds. -/
theorem theorem_30_4_i (hF : ConvexBifun F) (hcl : ClosedBifun F) (hp : Proper (F 0))
    (hne : (argmin (F 0)).Nonempty) (hbd : Bornology.IsBounded (argmin (F 0))) : Normal F :=
  normal_of_argmin_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n) hF hcl hp hne hbd

/-- **Rockafellar, Theorem 30.4(j)** (12663): if the optimal solutions to `(P*)` form a non-empty
bounded set then normality holds.

**The book does not argue this clause** (12665), and as in (i) the containment it asserts needs
properness of the dual objective. -/
theorem theorem_30_4_j (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hp : Proper fun v => -(dualProgram F 0 v))
    (hne : (argmax (dualProgram F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmax (dualProgram F 0))) : Normal F :=
  normal_of_argmax_adjointBifun_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n)
    hF hcl hp hne hbd

/-- **The Gale–Kuhn–Tucker Duality Theorem** (12667). Rockafellar names it in running text, with no
numbered statement of its own: "Theorem 30.4 can be applied, for example, to the dual pair of
linear programs described earlier in this section. These are polyhedral convex programs, so it
follows that the optimal value in `(P)` and the optimal value in `(P*)` are equal, unless both
programs are inconsistent."

Stated here at the generality the argument actually has — a polyhedral closed convex bifunction, of
which the linear program of 12395 is one instance — because that is what "these are polyhedral
convex programs, so it follows" means. Clause (e) covers the case where `(P)` is consistent, and
clause (f), fed by Theorem 30.1's polyhedrality clause, the case where `(P*)` is.

Closedness is not an extra assumption in the intended application: a *proper* polyhedral convex
bifunction is closed (`closedBifun_of_polyhedralBifun`). -/
theorem gale_kuhn_tucker_duality (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    infBifun F 0 = supBifun (dualProgram F) 0 := by
  refine (theorem_30_3_a_iff_c hF.convexBifun).1 ?_
  rcases h with hc | hc
  · exact theorem_30_4_e hF hc
  · exact theorem_30_4_f hF.convexBifun hcl (theorem_30_1_polyhedral hF) hc

/-! ### Theorem 30.5 -/

/-- **Rockafellar, Theorem 30.5** (12693), first assertion: under normality, `u*` is a Kuhn–Tucker
vector for `(P)` if and only if `u*` is an optimal solution to `(P*)`. -/
theorem theorem_30_5 (hF : ConvexBifun F) (hn : Normal F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (v : Rn m) :
    v ∈ KuhnTucker (pairing m) F ↔ v ∈ argmax (dualProgram F 0) := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bu := pairing m) (pairing n) hF hn ht hb,
    mem_argmax_iff_eq_iSup]

/-- **Rockafellar, Theorem 30.5** (12693), second assertion: under normality, `x` is a Kuhn–Tucker
vector for `(P*)` if and only if `x` is an optimal solution to `(P)`.

The book says only "the proof of the dual assertion of the theorem is parallel" (12701), and does
not carry it out. The backbone does, as `mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin`; the
only step left here is that the book's `⟨y, x⟩` is the *flipped* pairing in the backbone's
statement, and `pairing n` is symmetric. -/
theorem theorem_30_5_dual (hF : ConvexBifun F) (hcl : ClosedBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) (x : Rn n) :
    x ∈ ConcaveKuhnTucker (pairing n) (dualProgram F) ↔ x ∈ argmin (F 0) := by
  have h := mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin (Bu := pairing m) (Bx := pairing n)
    (x := x) hF hcl hn ht hb
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 30.5.1 -/

/-- **Rockafellar, Corollary 30.5.1** (12703), (b) ⟺ (c) (12707, 12709): `(ū*, x̄)` is a
saddle-point of the Lagrangian exactly when `(F0)(x̄) ≤ (F*0)(ū*)` — in which case weak duality
forces equality. -/
theorem corollary_30_5_1_b_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔ F 0 x ≤ dualProgram F 0 v :=
  isSaddlePoint_lagrangian_iff_le_adjointBifun (Bu := pairing m) (pairing n) hF hcl

/-- **Rockafellar, Corollary 30.5.1** (12703), (a) ⟺ (b) (12705, 12707): `(ū*, x̄)` is a
saddle-point of the Lagrangian exactly when normality holds and `x̄`, `ū*` are optimal solutions to
`(P)` and `(P*)`.

The book's proof is "immediate from Theorem 29.3, since the existence of a Kuhn–Tucker vector
implies normality by Theorem 30.4" — the route the backbone takes. -/
theorem corollary_30_5_1_a_iff_b (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0) := by
  rw [isSaddlePoint_lagrangian_iff_normal_and_optimal (Bu := pairing m) (pairing n) hF hcl hpr,
    mem_argmax_iff_eq_iSup]

/-- **Rockafellar, Corollary 30.5.1** (12703), (a) ⟺ (c). -/
theorem corollary_30_5_1_a_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    (Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0))
      ↔ F 0 x ≤ dualProgram F 0 v :=
  (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm.trans (corollary_30_5_1_b_iff_c hF hcl v x)

/-- **Rockafellar, Corollary 30.5.1** (12703), the three clauses as the book states them. -/
theorem corollary_30_5_1 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (v : Rn m) (x : Rn n) :
    [Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0),
      IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x),
      F 0 x ≤ dualProgram F 0 v].TFAE := by
  tfae_have 1 ↔ 2 := (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm
  tfae_have 2 ↔ 3 := corollary_30_5_1_b_iff_c hF hcl v x
  tfae_finish

/-- **Rockafellar, Corollary 30.5.1** (12709), the parenthesis: when clause (c) holds, equality
actually holds. This is weak duality (Corollary 30.2.2) in the other direction. -/
theorem corollary_30_5_1_eq (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n)
    (h : F 0 x ≤ dualProgram F 0 v) : F 0 x = dualProgram F 0 v :=
  le_antisymm h ((adjointBifun_zero_le (pairing m) (pairing n) F v).trans
    (iInf_le (fun z => F 0 z) x))

/-! ### Corollary 30.5.2 -/

/-- The optimal value of a consistent program is not `+∞`. -/
private theorem infBifun_zero_ne_top (hc : Consistent F) : infBifun F 0 ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hc
  rw [infBifun_apply]
  intro hcon
  exact hx (iInf_eq_top.1 hcon x)

/-- If the dual is consistent and normality holds, the optimal value is not `-∞`. -/
private theorem infBifun_zero_ne_bot (hF : ConvexBifun F) (hn : Normal F)
    (hc : ConcaveConsistent (dualProgram F)) : infBifun F 0 ≠ ⊥ := by
  obtain ⟨v, hv⟩ := hc
  rw [(theorem_30_3_a_iff_c hF).1 hn, supBifun_apply]
  intro hcon
  exact hv (iSup_eq_bot.1 hcon v)

/-- **Rockafellar, Corollary 30.5.2** (12729), second assertion: if `(P)` is strongly consistent and
`(P*)` is consistent then `(P*)` has an optimal solution.

The book's proof: strong consistency gives normality (Theorem 30.4(a)), the common optimal value is
then finite, a Kuhn–Tucker vector for `(P)` exists by Corollary 29.1.4, and Theorem 30.5 makes it an
optimal solution to `(P*)`. -/
theorem corollary_30_5_2_dual (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hc : ConcaveConsistent (dualProgram F)) : (argmax (dualProgram F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_a hs hF
  have ht : infBifun F 0 ≠ ⊤ := infBifun_zero_ne_top hs.consistent
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hc
  obtain ⟨v, hv⟩ := kuhnTucker_nonempty_of_stronglyConsistent (B := pairing m) hF
    (proper_infBifun_of_stronglyConsistent hF hs hb) hs ht
  exact ⟨v, (theorem_30_5 hF hn ht hb v).1 hv⟩

/-- **Rockafellar, Corollary 30.5.2** (12729), first assertion: if `(P)` is consistent and `(P*)` is
strongly consistent then `(P)` has an optimal solution.

This is the assertion the book actually proves (12731), and its proof invokes the *concave*
Corollary 29.1.4. The backbone route runs the convex one on `-F*` instead and is
`exists_infBifun_eq_of_concaveStronglyConsistent`; all that is left here is to read the attained
value as membership of `argmin`. -/
theorem corollary_30_5_2 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hc : Consistent F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : (argmin (F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_b hF hcl hs
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hs.concaveConsistent
  obtain ⟨x, hx⟩ := exists_infBifun_eq_of_concaveStronglyConsistent (Bu := pairing m)
    (Bx := pairing n) hF hcl hc hb hs
  exact ⟨x, mem_argmin_iff_eq_iInf.2 (hx.trans (infBifun_apply F 0))⟩

/-! ### The section's two counterexamples: the toolkit

Both of Rockafellar's unnumbered examples are bifunctions from `R` to `R`, so both live on `Rn 1`.
These are the coordinate lemmas they share. -/

/-- The point of `Rn 1` with coordinate `t`. -/
private noncomputable def coord1 (t : ℝ) : Rn 1 := WithLp.toLp 2 ![t]

@[simp] private theorem coord1_apply (t : ℝ) : coord1 t 0 = t := rfl

@[simp] private theorem zero_coord (i : Fin 1) : (0 : Rn 1) i = 0 := rfl

private theorem ext_one {x y : Rn 1} (h : x 0 = y 0) : x = y := by
  ext i
  fin_cases i
  exact h

private theorem pairing_one (u v : Rn 1) : pairing 1 u v = u 0 * v 0 := by
  simp [PiLp.inner_apply, mul_comm]

private theorem smul_coord (a : ℝ) (x : Rn 1) : (a • x) 0 = a * x 0 := rfl

private theorem tendsto_coord1 :
    Filter.Tendsto (fun k : ℕ => ((1 / (k + 1) : ℝ)) • coord1 1) Filter.atTop (nhds 0) := by
  have hc : Continuous fun c : ℝ => c • coord1 1 := continuous_id.smul continuous_const
  have h := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [zero_smul] at h
  exact h

/-! ### An unnumbered counterexample (12671): an abnormal program with a duality gap

Rockafellar, 12669: "There do exist convex programs which are not normal … For an example of
abnormality consider the closed proper convex bifunction `F` from `R` to `R` defined by
`(Fu)(x) = exp(-√(ux))` if `u ≥ 0, x ≥ 0`, and `+∞` otherwise." -/

/-- **Rockafellar, §30 (12671).** The abnormal example: `(Fu)(x) = exp(-√(ux))` on the closed first
quadrant, `+∞` off it. The domain condition is carried as a `⨅` over a proposition, which keeps
`Decidable` out of the statement. -/
noncomputable def abnormalBifun (u x : Rn 1) : EReal :=
  ⨅ _ : 0 ≤ u 0 ∧ 0 ≤ x 0, ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal)

/-- The value of the abnormal example on the first quadrant. -/
theorem abnormalBifun_of_mem {u x : Rn 1} (h : 0 ≤ u 0 ∧ 0 ≤ x 0) :
    abnormalBifun u x = ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal) :=
  iInf_pos h

/-- The value of the abnormal example off the first quadrant. -/
theorem abnormalBifun_of_notMem {u x : Rn 1} (h : ¬ (0 ≤ u 0 ∧ 0 ≤ x 0)) :
    abnormalBifun u x = ⊤ :=
  iInf_neg h

/-- Every value of the abnormal example is `≥ 0`: the exponential is positive. -/
theorem zero_le_abnormalBifun (u x : Rn 1) : 0 ≤ abnormalBifun u x := by
  by_cases h : 0 ≤ u 0 ∧ 0 ≤ x 0
  · rw [abnormalBifun_of_mem h]
    exact_mod_cast (Real.exp_pos _).le
  · rw [abnormalBifun_of_notMem h]
    exact le_top

/-- Hence every value of the perturbation function is `≥ 0`. -/
theorem zero_le_infBifun_abnormalBifun (u : Rn 1) : 0 ≤ infBifun abnormalBifun u :=
  le_iInf fun x => zero_le_abnormalBifun u x

/-- **Rockafellar, §30 (12681)**: the optimal value of `(P)` is `1`. At `u = 0` the objective is
`exp(-√0) = 1` on the whole non-negative axis. -/
theorem infBifun_abnormalBifun_zero : infBifun abnormalBifun 0 = 1 := by
  refine le_antisymm ?_ (le_iInf fun x => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 1)) (le_of_eq ?_)
    rw [abnormalBifun_of_mem (u := (0 : Rn 1)) (x := (0 : Rn 1)) ⟨le_rfl, le_rfl⟩]
    norm_num
  · by_cases h : 0 ≤ (0 : Rn 1) 0 ∧ 0 ≤ x 0
    · rw [abnormalBifun_of_mem h, zero_coord, zero_mul, Real.sqrt_zero, neg_zero, Real.exp_zero]
      exact le_rfl
    · rw [abnormalBifun_of_notMem h]
      exact le_top

/-- `exp(-1/ε) ≤ ε` for `ε > 0`, from `1 + r ≤ exp r`. This is the whole analytic content of the
example: `exp(-√(ux))` can be driven below any positive number by moving out along `x`. -/
private theorem exp_neg_le {ε : ℝ} (hε : 0 < ε) : Real.exp (-(1 / ε)) ≤ ε := by
  have hexp : 0 < Real.exp (1 / ε) := Real.exp_pos _
  have hkey : 1 / ε + 1 ≤ Real.exp (1 / ε) := Real.add_one_le_exp _
  have h1 : ε * (1 / ε) = 1 := by field_simp
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hexp]
  nlinarith [mul_le_mul_of_nonneg_left hkey hε.le]

/-- **Rockafellar, §30 (12675)**: `inf Fu = 0` for every `u > 0`. -/
theorem infBifun_abnormalBifun_of_pos {u : Rn 1} (hu : 0 < u 0) :
    infBifun abnormalBifun u = 0 := by
  refine le_antisymm (Tdaf.EReal.le_zero_of_forall_le_pos fun ε hε => ?_)
    (zero_le_infBifun_abnormalBifun u)
  refine le_trans (iInf_le _ (coord1 ((1 / ε) ^ 2 / u 0))) ?_
  have hx : 0 ≤ (1 / ε) ^ 2 / u 0 := by positivity
  rw [abnormalBifun_of_mem (u := u) (x := coord1 ((1 / ε) ^ 2 / u 0))
    ⟨hu.le, by rw [coord1_apply]; exact hx⟩, coord1_apply]
  have hval : u 0 * ((1 / ε) ^ 2 / u 0) = (1 / ε) ^ 2 := by field_simp
  rw [hval, Real.sqrt_sq (by positivity)]
  exact _root_.EReal.coe_le_coe_iff.2 (exp_neg_le hε)

/-- **Rockafellar, §30 (12677)**: `inf Fu = +∞` for `u < 0` — the program is inconsistent for
negative perturbations. -/
theorem infBifun_abnormalBifun_of_neg {u : Rn 1} (hu : u 0 < 0) :
    infBifun abnormalBifun u = ⊤ :=
  le_antisymm le_top (le_iInf fun x => by
    rw [abnormalBifun_of_notMem (fun h => absurd h.1 (not_le.2 hu))])

/-- **Rockafellar, §30 (12683)**: the optimal value of `(P*)` is `0`, so `(P)` and `(P*)` have a
genuine duality gap: `inf F0 = 1` while `sup F*0 = 0`. -/
theorem supBifun_dualProgram_abnormalBifun_zero :
    supBifun (dualProgram abnormalBifun) 0 = 0 := by
  refine le_antisymm ?_ ?_
  · rw [supBifun_apply]
    refine iSup_le fun v => Tdaf.EReal.le_zero_of_forall_le_pos fun ε hε => ?_
    rw [dualProgram_zero_apply]
    set t : ℝ := ε / (|v 0| + 1) with ht
    have hden : 0 < |v 0| + 1 := by positivity
    have htpos : 0 < t := by rw [ht]; positivity
    refine le_trans (iInf_le _ (coord1 t)) ?_
    rw [pairing_one, coord1_apply,
      infBifun_abnormalBifun_of_pos (u := coord1 t) (by rw [coord1_apply]; exact htpos), add_zero]
    have hle : t * v 0 ≤ ε := by
      have h1 : v 0 ≤ |v 0| := le_abs_self _
      have h2 : t * (|v 0| + 1) = ε := by rw [ht]; field_simp
      nlinarith [htpos.le]
    exact_mod_cast hle
  · refine le_trans ?_ (le_iSup (fun v => dualProgram abnormalBifun 0 v) (0 : Rn 1))
    rw [dualProgram_zero_apply]
    refine le_iInf fun u => ?_
    rw [pairing_one, zero_coord, mul_zero]
    simpa using zero_le_infBifun_abnormalBifun u

/-- **Rockafellar, §30 (12671–12685)**: the abnormal example really has a duality gap. -/
theorem abnormalBifun_duality_gap :
    supBifun (dualProgram abnormalBifun) 0 ≠ infBifun abnormalBifun 0 := by
  rw [supBifun_dualProgram_abnormalBifun_zero, infBifun_abnormalBifun_zero]
  exact fun h => absurd h.symm one_ne_zero

/-- **Rockafellar, §30 (12683)**: the example is *not normal* — `(cl (inf F))(0) = 0` while
`(inf F)(0) = 1`.

Proved directly from the perturbation function, with no appeal to convexity of `F`: the closure is
below the lower semicontinuous hull, which is a `liminf`, and `inf F` vanishes along the sequence
`u_k = 1/(k+1)`, which converges to `0`. -/
theorem not_normal_abnormalBifun : ¬ Normal abnormalBifun := by
  intro hn
  rw [normal_iff_clFn_infBifun_zero, infBifun_abnormalBifun_zero] at hn
  have hle : clFn (infBifun abnormalBifun) 0 ≤ 0 := by
    refine le_trans (clFn_le_lscHull _ 0) ?_
    rw [lscHull_eq_liminf, Filter.liminf_eq]
    refine sSup_le fun a ha => ?_
    obtain ⟨k, hk⟩ := (tendsto_coord1.eventually ha).exists
    rwa [infBifun_abnormalBifun_of_pos (u := ((1 / (k + 1) : ℝ)) • coord1 1)
      (by rw [smul_coord, coord1_apply, mul_one]; positivity)] at hk
  rw [hn] at hle
  exact absurd hle (by norm_num)

/-! ### An unnumbered counterexample (12715): a normal program whose dual has no optimal solution

Rockafellar, 12713: "An example of a normal convex program `(P)`, such that `(P)` has an optimal
solution but `(P*)` has no optimal solution, is obtained when `F` is the closed convex bifunction
from `R` to `R` given by `(Fu)(x) = x` if `x² ≤ u`, `+∞` if `x² > u`." -/

/-- **Rockafellar, §30 (12715).** The example: `(Fu)(x) = x` on `{x² ≤ u}`, `+∞` off it. -/
noncomputable def noDualSolutionBifun (u x : Rn 1) : EReal :=
  ⨅ _ : (x 0) ^ 2 ≤ u 0, ((x 0 : ℝ) : EReal)

/-- The value of the p. 316 example on its effective domain. -/
theorem noDualSolutionBifun_of_le {u x : Rn 1} (h : (x 0) ^ 2 ≤ u 0) :
    noDualSolutionBifun u x = ((x 0 : ℝ) : EReal) :=
  iInf_pos h

/-- The value of the p. 316 example off its effective domain. -/
theorem noDualSolutionBifun_of_lt {u x : Rn 1} (h : u 0 < (x 0) ^ 2) :
    noDualSolutionBifun u x = ⊤ :=
  iInf_neg (not_le.2 h)

private theorem noDualSolutionBifun_ne_bot (u x : Rn 1) : noDualSolutionBifun u x ≠ ⊥ := by
  by_cases h : (x 0) ^ 2 ≤ u 0
  · rw [noDualSolutionBifun_of_le h]
    exact _root_.EReal.coe_ne_bot _
  · rw [noDualSolutionBifun_of_lt (not_le.1 h)]
    exact top_ne_bot

/-- The objective of `(P)` vanishes at the origin. -/
theorem noDualSolutionBifun_zero_zero : noDualSolutionBifun 0 (0 : Rn 1) = 0 := by
  rw [noDualSolutionBifun_of_le (u := (0 : Rn 1)) (x := (0 : Rn 1)) (by simp)]
  simp

/-- The objective of `(P)` is `+∞` away from the origin: `x² ≤ 0` forces `x = 0`. -/
theorem noDualSolutionBifun_zero_of_ne {x : Rn 1} (hx : x ≠ 0) :
    noDualSolutionBifun 0 x = ⊤ := by
  refine noDualSolutionBifun_of_lt ?_
  rw [zero_coord]
  by_contra hcon
  rw [not_lt] at hcon
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
  exact hx (ext_one (by rw [hx0, zero_coord]))

/-- **Rockafellar, §30 (12727)**: `x = 0` is the unique optimal solution to `(P)`. -/
theorem argmin_noDualSolutionBifun : argmin (noDualSolutionBifun 0) = {(0 : Rn 1)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have h := hx 0
    rw [noDualSolutionBifun_zero_of_ne hne, noDualSolutionBifun_zero_zero] at h
    exact absurd h (by simp)
  · rintro rfl
    intro z
    rw [noDualSolutionBifun_zero_zero]
    by_cases hz : z = 0
    · rw [hz, noDualSolutionBifun_zero_zero]
    · rw [noDualSolutionBifun_zero_of_ne hz]
      exact le_top

/-- The optimal value of `(P)` is `0`. -/
theorem infBifun_noDualSolutionBifun_zero : infBifun noDualSolutionBifun 0 = 0 := by
  rw [infBifun_apply]
  refine le_antisymm (le_trans (iInf_le _ (0 : Rn 1))
    (le_of_eq noDualSolutionBifun_zero_zero)) (le_iInf fun z => ?_)
  by_cases hz : z = 0
  · rw [hz, noDualSolutionBifun_zero_zero]
  · rw [noDualSolutionBifun_zero_of_ne hz]
    exact le_top

private theorem convex_noDualSolutionSet :
    Convex ℝ {p : Rn 1 × Rn 1 | (p.2 0) ^ 2 ≤ p.1 0} := by
  intro p hp q hq a b ha hb hab
  have hp' : (p.2 0) ^ 2 ≤ p.1 0 := hp
  have hq' : (q.2 0) ^ 2 ≤ q.1 0 := hq
  change ((a • p + b • q).2 0) ^ 2 ≤ (a • p + b • q).1 0
  have h1 : (a • p + b • q).1 0 = a * p.1 0 + b * q.1 0 := rfl
  have h2 : (a • p + b • q).2 0 = a * p.2 0 + b * q.2 0 := rfl
  rw [h1, h2]
  have key : a * p.2 0 ^ 2 + b * q.2 0 ^ 2 - (a * p.2 0 + b * q.2 0) ^ 2
      = a * b * (p.2 0 - q.2 0) ^ 2 := by
    linear_combination (-(a * p.2 0 ^ 2 + b * q.2 0 ^ 2)) * hab
  have hnn : 0 ≤ a * b * (p.2 0 - q.2 0) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have h3 : a * p.2 0 ^ 2 ≤ a * p.1 0 := mul_le_mul_of_nonneg_left hp' ha
  have h4 : b * q.2 0 ^ 2 ≤ b * q.1 0 := mul_le_mul_of_nonneg_left hq' hb
  linarith

private theorem graphFn_noDualSolutionBifun :
    graphFn noDualSolutionBifun
      = fun p : Rn 1 × Rn 1 =>
          indicatorFn {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0} p + ((p.2 0 : ℝ) : EReal) := by
  funext p
  by_cases h : (p.2 0) ^ 2 ≤ p.1 0
  · rw [indicatorFn_of_mem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h, zero_add]
    exact noDualSolutionBifun_of_le h
  · rw [indicatorFn_of_notMem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h,
      _root_.EReal.top_add_coe]
    exact noDualSolutionBifun_of_lt (not_le.1 h)

/-- The p. 316 example is a convex bifunction: its graph function is a linear coordinate added to
the indicator of the convex set `{(u, x) | x² ≤ u}`. -/
theorem convexBifun_noDualSolutionBifun : ConvexBifun noDualSolutionBifun := by
  rw [convexBifun_iff, graphFn_noDualSolutionBifun]
  exact convexFn_add_coe (l := fun p : Rn 1 × Rn 1 => p.2 0)
    (convexFn_indicatorFn.2 convex_noDualSolutionSet) fun _ _ _ _ _ => rfl

private theorem continuous_coord (i : Fin 1) : Continuous fun x : Rn 1 => x i :=
  PiLp.continuous_apply (p := 2) (fun _ : Fin 1 => ℝ) i

/-- The p. 316 example is a closed bifunction: its epigraph is cut out by two continuous
inequalities. -/
theorem closedBifun_noDualSolutionBifun : ClosedBifun noDualSolutionBifun := by
  have hne : ∀ p : Rn 1 × Rn 1, graphFn noDualSolutionBifun p ≠ ⊥ := fun p =>
    noDualSolutionBifun_ne_bot p.1 p.2
  rw [closedBifun_iff, closedFn_iff_lowerSemicontinuous hne,
    lowerSemicontinuous_iff_isClosed_epi]
  have hc1 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.2 0 :=
    (continuous_coord 0).comp (continuous_snd.comp continuous_fst)
  have hc2 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.1 0 :=
    (continuous_coord 0).comp (continuous_fst.comp continuous_fst)
  have hset : epi (graphFn noDualSolutionBifun)
      = {q : (Rn 1 × Rn 1) × ℝ | (q.1.2 0) ^ 2 ≤ q.1.1 0} ∩ {q | q.1.2 0 ≤ q.2} := by
    ext q
    constructor
    · intro hq
      have hq' : graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal) := hq
      by_cases hm : (q.1.2 0) ^ 2 ≤ q.1.1 0
      · refine ⟨hm, ?_⟩
        have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
          noDualSolutionBifun_of_le hm
        rw [hval] at hq'
        exact_mod_cast hq'
      · exfalso
        have hval : graphFn noDualSolutionBifun q.1 = ⊤ :=
          noDualSolutionBifun_of_lt (not_le.1 hm)
        rw [hval] at hq'
        exact absurd (top_le_iff.1 hq') (by simp)
    · rintro ⟨hm, hle⟩
      have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
        noDualSolutionBifun_of_le hm
      change graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal)
      rw [hval]
      exact_mod_cast hle
  rw [hset]
  exact (isClosed_le (hc1.pow 2) hc2).inter (isClosed_le hc1 continuous_snd)

/-- The objective of `(P)` is a proper convex function. -/
theorem proper_noDualSolutionBifun_zero : Proper (noDualSolutionBifun 0) :=
  ⟨⟨0, by rw [mem_dom, noDualSolutionBifun_zero_zero]; simp⟩,
    fun x => noDualSolutionBifun_ne_bot 0 x⟩

/-- **Rockafellar, §30 (12723)**: the example *is* normal. Rockafellar reads this off the
lower semicontinuity of `inf Fu = -√u` at `u = 0`; here it is Theorem 30.4(i), since the set of
optimal solutions is the single point `0`. -/
theorem normal_noDualSolutionBifun : Normal noDualSolutionBifun :=
  theorem_30_4_i convexBifun_noDualSolutionBifun closedBifun_noDualSolutionBifun
    proper_noDualSolutionBifun_zero
    (by rw [argmin_noDualSolutionBifun]; exact Set.singleton_nonempty _)
    (by rw [argmin_noDualSolutionBifun]; exact Bornology.isBounded_singleton)

/-- **Rockafellar, §30 (12719)**: `inf Fu ≤ -√u` for `u ≥ 0`. The infimum is attained at
`x = -√u`, the left endpoint of `{x | x² ≤ u}`; only this half of the book's display is needed. -/
theorem infBifun_noDualSolutionBifun_le {t : ℝ} (ht : 0 ≤ t) :
    infBifun noDualSolutionBifun (coord1 t) ≤ ((-Real.sqrt t : ℝ) : EReal) := by
  have hcond : (coord1 (-Real.sqrt t) 0) ^ 2 ≤ coord1 t 0 := by
    rw [coord1_apply, coord1_apply, neg_pow, Real.sq_sqrt ht]
    simp
  refine le_trans (iInf_le _ (coord1 (-Real.sqrt t))) (le_of_eq ?_)
  rw [noDualSolutionBifun_of_le hcond, coord1_apply]

/-- **Rockafellar, §30 (12725)**: `(P)` has *no* Kuhn–Tucker vector. The perturbation function
`-√u` is lower semicontinuous at `0` but has derivative `-∞` there, so no linear minorant exists;
concretely, `⟨u, u*⟩ + inf Fu` dips below `inf F0 = 0` at `u = s²` with `s = 1/(1 + |u*|)`. -/
theorem kuhnTucker_noDualSolutionBifun :
    KuhnTucker (pairing 1) noDualSolutionBifun = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  rw [mem_kuhnTucker_iff_forall_le] at hv
  obtain ⟨-, -, hle⟩ := hv
  have habs : (0 : ℝ) < 1 + |v 0| := by positivity
  set s : ℝ := 1 / (1 + |v 0|) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have h := hle (coord1 (s ^ 2))
  rw [infBifun_noDualSolutionBifun_zero, pairing_one, coord1_apply] at h
  have hb := infBifun_noDualSolutionBifun_le (t := s ^ 2) (by positivity)
  rw [Real.sqrt_sq hs0.le] at hb
  have hchain : ((s ^ 2 * v 0 : ℝ) : EReal)
      + infBifun noDualSolutionBifun (coord1 (s ^ 2)) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := by
    rw [_root_.EReal.coe_add]
    exact add_le_add le_rfl hb
  have hfin : (0 : EReal) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := le_trans h hchain
  have hreal : (0 : ℝ) ≤ s ^ 2 * v 0 + -s := by exact_mod_cast hfin
  have hsv : s * v 0 < 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one habs]
    linarith [le_abs_self (v 0)]
  nlinarith [mul_lt_mul_of_pos_left hsv hs0]

/-- **Rockafellar, §30 (12727)**: the dual program `(P*)` has *no* optimal solution, although `(P)`
is normal and has one. By Theorem 30.5 the optimal solutions to `(P*)` are the Kuhn–Tucker vectors
for `(P)`, and there are none. -/
theorem argmax_dualProgram_noDualSolutionBifun :
    argmax (dualProgram noDualSolutionBifun 0) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have ht : infBifun noDualSolutionBifun 0 ≠ ⊤ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have hb : infBifun noDualSolutionBifun 0 ≠ ⊥ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have h := (theorem_30_5 convexBifun_noDualSolutionBifun normal_noDualSolutionBifun ht hb v).2 hv
  rw [kuhnTucker_noDualSolutionBifun] at h
  exact h

end Rockafellar
