/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.LinearProcess
import Tdaf.Analysis.Convex.Optimization.Adjoint
import Tdaf.Analysis.Convex.Optimization.Perturbation
import Tdaf.Analysis.Convex.Saddle.Minimax
import Tdaf.Surface.Rockafellar.Part5.Section25

/-!
# Rockafellar, §29: Bifunctions and Generalized Convex Programs

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §29, pp. 291–306 (lines 11597–12152): the
generalization of an ordinary convex program to a *convex bifunction* — an objective function
together with a distinguished family of perturbations of it — and the identification of its
Kuhn–Tucker vectors with the subgradients of the perturbation function at the origin.

All twelve numbered results are here. The section is the hinge of Part VI: Rockafellar's own
preface (line 279) says "Theorems 29.1, 29.3, and their corollaries contain all the facts needed in
the sequel", and §30's duality theory is stated entirely in this vocabulary.

## Contents

| label | line | declaration |
|---|---|---|
| §29 definitions, 11605–11637 | | `graphDomain`, `graphDomain_eq`, `mem_graphDomain`,
  `domBifun_eq_image_graphDomain`, `convex_graphDomain` |
| §29 definitions, 11707–11749 | | `IsOptimalSolution`, `isOptimalSolution_iff_mem_argmin`,
  `not_isOptimalSolution_of_infBifun_eq_bot`, `isSaddlePoint_lagrangian_iff_forall` |
| §29 example, 11639 | | `linearIndicatorBifun`, `linearIndicatorBifun_apply`,
  `graphFn_linearIndicatorBifun`, `convexBifun_linearIndicatorBifun`,
  `closedBifun_linearIndicatorBifun`, `proper_linearIndicatorBifun`,
  `domBifun_linearIndicatorBifun` |
| Theorem 29.1 | 11863 | `theorem_29_1_convexFn`, `theorem_29_1_dom`, `theorem_29_1_forall_le`,
  `theorem_29_1`, `theorem_29_1_set` |
| Corollary 29.1.1 | 11885 | `corollary_29_1_1_monotone`, `corollary_29_1_1_iInf`,
  `corollary_29_1_1_posHomogeneous`, `corollary_29_1_1_convexFn`, `corollary_29_1_1_convex`,
  `corollary_29_1_1_isClosed`, `corollary_29_1_1_supportFn` |
| Corollary 29.1.2 | 11899 | `corollary_29_1_2` |
| Corollary 29.1.3 | 11913 | `corollary_29_1_3`, `corollary_29_1_3_eq`,
  `corollary_29_1_3_partial` |
| §29 definitions, 11929–11941 | | `strictlyConsistent_iff` |
| Corollary 29.1.4 | 11943 | `corollary_29_1_4_nonempty`, `corollary_29_1_4_dirDeriv` |
| Corollary 29.1.5 | 11951 | `corollary_29_1_5_nbhd`, `corollary_29_1_5_nonempty`,
  `corollary_29_1_5_isClosed`, `corollary_29_1_5_isBounded`, `corollary_29_1_5_convex`,
  `corollary_29_1_5_isCompact` |
| Corollary 29.1.6 | 11955 | `corollary_29_1_6_bot`, `corollary_29_1_6_top` |
| Theorem 29.2 | 12029 | `theorem_29_2_objective`, `theorem_29_2_infBifun`,
  `theorem_29_2_argmin_nonempty`, `theorem_29_2_kuhnTucker_nonempty`,
  `theorem_29_2_polyhedral_argmin`, `theorem_29_2_polyhedral_kuhnTucker` |
| Theorem 29.3 | 12035 | `theorem_29_3`, `theorem_29_3_isSaddlePoint` |
| Corollary 29.3.1 | 12097 | `corollary_29_3_1_stronglyConsistent`,
  `corollary_29_3_1_strictlyConsistent`, `corollary_29_3_1_polyhedral` |
| §29 definition, 12107 | | `clBifun_convex`, `clBifun_closed`, `clBifun_proper` |
| Theorem 29.4 | 12109 | `theorem_29_4_apply`, `theorem_29_4_inf`, `theorem_29_4_dom_subset`,
  `theorem_29_4_dom_subset_closure` |
| Corollary 29.4.1 | 12151 | `corollary_29_4_1_relint`, `corollary_29_4_1_stronglyConsistent`,
  `corollary_29_4_1_objective`, `corollary_29_4_1_optimalValue`, `corollary_29_4_1_argmin`,
  `corollary_29_4_1_optimalSolution`, `corollary_29_4_1_eventually`,
  `corollary_29_4_1_kuhnTucker` |
| Corollary 29.4.1, refuted | 12151 | `corollary_29_4_1_perturbation` (the claim as printed),
  `corollary_29_4_1_perturbation_false` (the refutation), and the counterexample `originBifun`
  with `originBifun_zero`, `originBifun_of_ne_zero`, `convexBifun_originBifun`,
  `domBifun_originBifun`, `stronglyConsistent_originBifun`, `clBifun_originBifun`,
  `infBifun_clBifun_originBifun`, `infBifun_originBifun_of_ne_zero` |

## The section's definitions

**Almost the whole of §29's vocabulary is already the backbone's**, under the book's own names, so
this file adds only three definitions and otherwise specialises. The dictionary:

| book (line) | backbone |
|---|---|
| bifunction `F` from `ℝᵐ` to `ℝⁿ` (11605) | `Tdaf.ConvexAnalysis.Bifun (Rn m) (Rn n)` |
| graph function of `F` (11611) | `graphFn F` |
| convex / closed bifunction (11635) | `ConvexBifun F` / `ClosedBifun F` |
| *proper* bifunction (11635) | `Proper (graphFn F)` |
| `dom F` (11637) | `domBifun F` |
| objective function `F0` (11709) | `F 0` |
| optimal value in `(P)` (11709) | `infBifun F 0` |
| feasible solutions, consistent (11715) | `dom (F 0)`, `Consistent F` |
| perturbation function `inf F` (11721) | `infBifun F` |
| Kuhn–Tucker vector (11729) | `KuhnTucker (pairing m) F` |
| Lagrangian `L` (11749) | `lagrangian (pairing m) F` |
| strongly / strictly consistent (11929) | `StronglyConsistent F` / `StrictlyConsistent F` |
| polyhedral bifunction (11961) | `PolyhedralBifun F` |
| `cl F` (12107) | `clBifun F` |

The three that are new (a fourth definition, `originBifun`, is the counterexample of
`## Where the book is defective`, and a fifth, `corollary_29_4_1_perturbation`, is the false claim
it refutes):

* `Rockafellar.graphDomain F` — the book's **graph domain** (11637), `dom (graphFn F)`. The bridge
  is `domBifun_eq_image_graphDomain`: `dom F` is its projection on `ℝᵐ`, which is the identity
  every relative-interior argument in Theorem 29.4 runs on.
* `Rockafellar.linearIndicatorBifun A` — the **`(+∞)` indicator bifunction of a linear
  transformation** (11639), `(Fu)(x) = δ(x | Au)`, which Rockafellar calls "very important to us
  theoretically" and which §30 uses as the bridge between linear algebra and bifunctions. It is the
  backbone's `(ConvexProcess.ofLinearMap A).indicatorBifun`, and
  `linearIndicatorBifun_apply` is the bridge.
* `Rockafellar.IsOptimalSolution F x` — the book's **optimal solution** (11715): `(F0)(x)` is
  *finite* and equal to the optimal value. This is **not** `argmin (F 0)`. The two differ exactly
  at the two improper values: an inconsistent program has `argmin (F 0) = ℝⁿ` and no optimal
  solutions at all, and a program with optimal value `-∞` has neither. The book says so explicitly
  ("we do not speak of optimal solutions to `(P)` when `(P)` is inconsistent", 11715), and
  `isOptimalSolution_iff_mem_argmin` is the bridge under the hypotheses that remove the difference.

## Where the book's hypotheses had to change

* **Theorem 29.1's Kuhn–Tucker clause needs no convexity.** Rockafellar states the whole theorem
  for a convex bifunction, and the first assertion — that `inf F` is convex — of course needs it.
  The second is a rearrangement of the definition and holds for any `F` whatsoever;
  `theorem_29_1` carries no `ConvexBifun` hypothesis.
* **Corollary 29.1.3 does not assume that `inf F` is proper, and does not need to.**
  Rockafellar's proof cites Theorem 25.1, which is stated for a proper convex function; "the
  optimal value in `(P)` is finite" does *not* make `inf F` proper (take `(Fu)(x) = -∞` for
  `v₁ > 0`, `0` for `v₁ = 0` and `+∞` for `v₁ < 0` on `ℝ¹`). Properness is nevertheless free on
  both sides of the equivalence: a subgradient at a point of finiteness is an affine minorant, so
  it forces `inf F > -∞` everywhere (the backbone's `proper_of_mem_subgradient`, which is
  Theorem 23.3's first half), and a gradient does the same through `HasGradientAt.proper`. The
  corollary is therefore stated with the book's hypotheses.
* **Theorem 29.2's optimal-solution clause needs only `inf F 0 ≠ -∞`.** Rockafellar asks for the
  optimal value to be finite; an optimal value of `+∞` makes every point a minimiser of `F 0`. The
  book's hypothesis is what the *polyhedrality* of the minimum set needs, and
  `theorem_29_2_polyhedral_argmin` carries it.
* **Corollary 29.3.1's polyhedral branch is stated for a merely consistent program, and it is then
  partly vacuous.** "Polyhedral and merely consistent" allows `inf F 0 = -∞`, in which case a
  closed proper `(P)` has neither optimal solutions nor Kuhn–Tucker vectors, and the equivalence
  holds with both sides false. `corollary_29_3_1_polyhedral` covers that case explicitly rather
  than assuming it away.
* **Corollary 29.4.1's perturbation clause needs `F` proper, and the book omits it.** See below.

## Where the book is defective

**Corollary 29.4.1 (12151) is printed with no proof at all, and drops the properness hypothesis
that its own Theorem 29.4 carries.** Its last-but-one clause — that the perturbation functions of
`(P)` and `(cl P)` agree on a neighbourhood of `0` — is **false** without it. This is the
*stated and refuted* category of the alignment checklist: `corollary_29_4_1_perturbation` records
the claim as printed and `corollary_29_4_1_perturbation_false` refutes it, on `ℝ¹`.

The counterexample is `originBifun`, the bifunction that is `-∞` at `u = 0` and `+∞` for `u ≠ 0`.
It is convex (its epigraph is a linear subspace), `dom F = {0}` and `ri {0} = {0} ∋ 0`, so `(P)` is
strongly consistent; but its graph function takes the value `-∞`, so by Rockafellar's own
convention (line 2177) `cl (graph F)` is the *constant* `-∞`, `dom (cl F) = ℝ¹` and
`inf (cl F) ≡ -∞`, while `inf F = +∞` off the origin. The two perturbation functions therefore
agree at exactly one point. This is the `ℝ¹` degeneration of the recorded `ℝ²` counterexample
("`F u x = -∞` for `u` on a line `L ⊆ ℝ²` through the origin and `+∞` off it"); with `m = 1` the
line is the origin itself, and no two-dimensional geometry is needed. The other clauses of the
corollary survive: the objective, optimal-value, optimal-solution and Kuhn–Tucker clauses are
proved here without properness, and `corollary_29_4_1_stronglyConsistent` is too.

**Theorem 29.4's printed proof is correct, and this file's records said otherwise.** `part6.md`,
`inventory.md` and `00-overview.md` all say that "Theorem 29.4's printed proof is wrong at 12139:
it claims `((cl F)u)(y) = -∞` for *all* `y` in the improper case, but `cl f` is `+∞` outside
`cl (dom f)`". That describes the *lower semicontinuous hull* `f̄`, not `cl f`. Rockafellar defines
the closure by cases at line 2177 — "the closure of `f` is defined to be the constant function
`-∞` if `f` is an improper convex function such that `f(x) = -∞` for some `x`" — and line 2231
draws the distinction in as many words: "`f̄(x)` is `-∞` on `cl (dom f)` and `+∞` outside
`cl (dom f)`, whereas `(cl f)(x)` is `-∞` **everywhere**, for such a function `f`." The book's step
at 12137–12141 is therefore exactly right, and the backbone's `clBifun_apply_eq_clFn` takes the
same route (`clFn_of_exists_eq_bot`). Nothing in the formalization changes; the record does.

## What is not here

**Omitted with a reason.**

* **The two unnumbered worked examples**, 11771–11829 (the quadratic `⟨x,Qx⟩ + ⟨a,x⟩` minimised
  over a translated unit ball, perturbed by right scalar multiplication and translation) and
  11983–12025 (`‖·‖_∞` over a polytope whose vertices are translated). Both are illustrations
  rather than results: the first asks for the closed form of a Lagrangian that Rockafellar
  computes in one line from the conjugates of §12 and §15, and the second asks only that a
  particular sum of polyhedral functions be polyhedral, which is §19 verbatim. Neither is cited
  anywhere in §§30–39. The section's one *theoretically* load-bearing example, the indicator
  bifunction of a linear transformation (11639), **is** here.
* **The reduction of a generalized program to an ordinary one with linear equality constraints**
  (11833–11859). Rockafellar states it as a remark and then argues against using it ("this would
  not be very natural … would consequently lead to a seriously restrictive theory"). It needs
  §28's `(m + 3)`-tuple, so it belongs in `Part6/Section28.lean` if anywhere.
* **The exercise at 11929**: for an *ordinary* convex program, strong consistency is
  `∃ x ∈ ri C` with `fᵢ(x) < 0` for the inequality constraints and `fᵢ(x) = 0` for the affine
  ones. The book leaves it to the reader, and it is a statement about the ordinary-program
  bifunction, hence §28's. The *general* characterisation of strict consistency it is contrasted
  with (11941) is here, as `strictlyConsistent_iff`.
* **The generalization of Theorem 28.4**, which Rockafellar explicitly leaves as an exercise
  (12105) — "we shall leave this as an exercise at present, since the result will be obvious from
  the theory of dual programs". It is §30's, and it is not a numbered result of §29.

**Nothing is deferred by scope, and nothing is blocked.** Both gates `part6.md` records for
§29 — the `negFst (prodPairing Bu Bx)` instances (remediation §4.2) and the `ℝᵐ × ℝⁿ ≃ ℝᵐ⁺ⁿ`
transport (§4.8) — are closed, and neither is used here: §29 never conjugates against the
sign-flipped product pairing (that is §30's adjoint) and never needs `ℝᵐ⁺ⁿ` as a type, because the
backbone states the whole bifunction theory on the *product* `U × X`.

## Backbone gaps

**None.** Every one of the twelve results is a specialisation, and the longest proof in the file is
the counterexample. The one thing that looked like a gap was not: Corollary 29.1.3 needs "a
subgradient at a point of finiteness makes the function proper", and
`Tdaf/Analysis/Convex/Subgradient/Defs.lean` already has it as `proper_of_mem_subgradient`,
Theorem 23.3's first half. It was written `private` here first and the pre-commit duplicate grep
(`gotchas.md` BLD17) caught it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §29 (lines 11597–12152),
  reading §7 (Theorems 7.2, 7.4, 7.5 and the definition of `cl f` at line 2177), §23 (Theorems
  23.1–23.4 and 23.10), §25 (Theorems 25.1 and 25.2), §27 (Corollary 27.3.2) and §19
  (Corollary 19.3.1).
-/

open Filter Topology
open scoped Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The section's vocabulary

Rockafellar's definitions of §29, in the order he gives them. Everything but the three declarations
below is the backbone's under the book's own name; the module docstring has the dictionary. -/

section Vocabulary

variable {m n : ℕ}

/-- The **graph domain** of a bifunction (line 11637): the effective domain of its graph function,
a convex subset of `ℝᵐ × ℝⁿ`. -/
def graphDomain (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n) := dom (graphFn F)

theorem graphDomain_eq (F : Bifun (Rn m) (Rn n)) : graphDomain F = dom (graphFn F) := rfl

@[simp] theorem mem_graphDomain {F : Bifun (Rn m) (Rn n)} {u : Rn m} {x : Rn n} :
    (u, x) ∈ graphDomain F ↔ F u x < ⊤ := Iff.rfl

/-- **`dom F` is the projection of the graph domain on `ℝᵐ`** (line 11637), and is therefore a
convex set. This is the identification every relative-interior step of Theorem 29.4 runs on. -/
theorem domBifun_eq_image_graphDomain (F : Bifun (Rn m) (Rn n)) :
    domBifun F = LinearMap.fst ℝ (Rn m) (Rn n) '' graphDomain F :=
  domBifun_eq_image_dom_graphFn F

/-- The graph domain of a convex bifunction is convex (line 11637). -/
theorem convex_graphDomain {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F) :
    Convex ℝ (graphDomain F) :=
  ConvexFn.convex_dom hF

/-- An **optimal solution** to the convex program `(P)` associated with `F` (line 11715): a vector
`x` at which `(F0)(x)` is *finite* and equal to the optimal value in `(P)`.

This is deliberately not `argmin (F 0)`. Rockafellar is explicit that "we do not speak of optimal
solutions to `(P)` when `(P)` is inconsistent, even though in that case `(F0)(x)` is the optimal
value `+∞` in `(P)` for every `x`", and an optimal value of `-∞` is excluded by the same clause.
`isOptimalSolution_iff_mem_argmin` is the bridge to the backbone's minimum set. -/
def IsOptimalSolution (F : Bifun (Rn m) (Rn n)) (x : Rn n) : Prop :=
  F 0 x ≠ ⊤ ∧ F 0 x ≠ ⊥ ∧ F 0 x = infBifun F 0

/-- **The bridge to the backbone's minimum set** (line 11717): "the set of all optimal solutions to
`(P)` is empty unless `F0` is proper; when `F0` is proper it is the minimum set of `F0`". The
second hypothesis is consistency, which is what rules out the `+∞` case. -/
theorem isOptimalSolution_iff_mem_argmin {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (hb : ∀ y, F 0 y ≠ ⊥) (ht : infBifun F 0 ≠ ⊤) :
    IsOptimalSolution F x ↔ x ∈ argmin (F 0) := by
  constructor
  · rintro ⟨-, -, hx⟩
    intro z
    rw [hx, infBifun_apply]
    exact iInf_le _ z
  · intro hx
    have hval : F 0 x = infBifun F 0 := by
      rw [infBifun_apply]
      exact le_antisymm (le_iInf hx) (iInf_le _ x)
    exact ⟨by rw [hval]; exact ht, hb x, hval⟩

/-- A program whose optimal value is `-∞` has no optimal solutions, whatever else is true of it:
the book's definition asks for a *finite* value. -/
theorem not_isOptimalSolution_of_infBifun_eq_bot {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (h : infBifun F 0 = ⊥) : ¬ IsOptimalSolution F x := by
  rintro ⟨-, hne, hval⟩
  exact hne (by rw [hval, h])

/-- **The saddle-point condition of Theorem 29.3, written as the book writes it** (line 12037):
`L(u*, x̄) ≤ L(ū*, x̄) ≤ L(ū*, x)` for every `u*` and every `x`. This is the backbone's
`IsSaddlePoint` of the Lagrangian read as a function on `ℝᵐ × ℝⁿ`, by definition. -/
theorem isSaddlePoint_lagrangian_iff_forall (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔
      (∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y :=
  Iff.rfl

end Vocabulary

/-! ### The indicator bifunction of a linear transformation

Line 11639: "A simple example of a convex bifunction which will be very important to us
theoretically … is the `(+∞)` indicator bifunction of a linear transformation `A`". It is the
bridge between linear algebra and the theory of convex bifunctions, and §30's adjoint is stated
against it. -/

section LinearIndicator

variable {m n : ℕ}

/-- The **`(+∞)` indicator bifunction of a linear transformation `A`** (line 11639):
`(Fu)(x) = δ(x | Au)`, which is `0` when `x = Au` and `+∞` otherwise. It is the backbone's
indicator bifunction of the convex process `ofLinearMap A`. -/
noncomputable def linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) : Bifun (Rn m) (Rn n) :=
  (ConvexProcess.ofLinearMap A).indicatorBifun

/-- The bridge: `(Fu)(x) = δ(x | Au)`. -/
theorem linearIndicatorBifun_apply (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) (x : Rn n) :
    linearIndicatorBifun A u x = indicatorFn {A u} x := by
  rw [linearIndicatorBifun, ConvexProcess.indicatorBifun_apply, ConvexProcess.eval_ofLinearMap]

/-- The graph function of `linearIndicatorBifun A` is the indicator of the graph of `A`, "which
happens to be a convex set (a subspace) in `ℝᵐ⁺ⁿ`" (line 11645). -/
theorem graphFn_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    graphFn (linearIndicatorBifun A) = indicatorFn {p : Rn m × Rn n | p.2 = A p.1} :=
  ConvexProcess.graphFn_indicatorBifun _

/-- **Line 11645**: the indicator bifunction of a linear transformation is convex. -/
theorem convexBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ConvexBifun (linearIndicatorBifun A) :=
  ConvexProcess.convexBifun_indicatorBifun _

/-- **Line 11645**: it is closed. -/
theorem closedBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ClosedBifun (linearIndicatorBifun A) := by
  rw [ClosedBifun, graphFn_linearIndicatorBifun]
  refine closedFn_indicatorFn ?_
  have hker : {p : Rn m × Rn n | p.2 = A p.1}
      = LinearMap.ker ((LinearMap.snd ℝ (Rn m) (Rn n)) - A ∘ₗ LinearMap.fst ℝ (Rn m) (Rn n)) := by
    ext p
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hker]
  exact (LinearMap.ker _).closed_of_finiteDimensional

/-- **Line 11645**: it is proper. -/
theorem proper_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    Proper (graphFn (linearIndicatorBifun A)) := by
  rw [graphFn_linearIndicatorBifun]
  exact ⟨⟨(0, A 0), by simp⟩, indicatorFn_ne_bot _⟩

/-- **Line 11645**: `dom F = ℝᵐ`. -/
@[simp] theorem domBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    domBifun (linearIndicatorBifun A) = Set.univ := by
  rw [linearIndicatorBifun, ConvexProcess.domBifun_indicatorBifun,
    ConvexProcess.dom_ofLinearMap]

end LinearIndicator

/-! ### Theorem 29.1

Line 11863. The fundamental fact about the perturbation function of any convex program, ordinary or
generalized. -/

section Theorem291

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m}

/-- **Rockafellar, Theorem 29.1** (line 11863), first assertion: the perturbation function `inf F`
of the convex program `(P)` associated with a convex bifunction `F` is a convex function on `ℝᵐ`.

Rockafellar's proof is Theorem 5.7 at the projection `(u, x) ↦ u`, and that is the backbone's
proof too: `inf F` *is* the image of the graph function under that projection. -/
theorem theorem_29_1_convexFn (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_infBifun hF

/-- **Rockafellar, Theorem 29.1**, first assertion, second half: the effective domain of `inf F` is
`dom F`. The value of `inf F` at `u` is `+∞` only if `Fu` is the constant `+∞`, so this needs no
hypothesis on `F` at all. -/
theorem theorem_29_1_dom (F : Bifun (Rn m) (Rn n)) : dom (infBifun F) = domBifun F :=
  dom_infBifun F

/-- **Rockafellar, line 11738**, the reformulation of the definition of a Kuhn–Tucker vector that
he records immediately after giving it: since `⟨u*, u⟩ + inf Fu` equals `inf F0` at `u = 0`, the
condition is that `inf F0` be finite and that `inf Fu + ⟨u*, u⟩ ≥ inf F0` for every `u`. -/
theorem theorem_29_1_forall_le :
    v ∈ KuhnTucker (pairing m) F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u : Rn m, infBifun F 0 ≤ ((pairing m u v : ℝ) : EReal) + infBifun F u :=
  mem_kuhnTucker_iff_forall_le

/-- **Rockafellar, Theorem 29.1**, second assertion (line 11863): when the optimal value in `(P)`
is finite, the Kuhn–Tucker vectors for `(P)` are precisely the `u*` with `-u* ∈ ∂(inf F)(0)`.

**No convexity is used.** Rockafellar states the whole theorem for a convex bifunction, and the
first assertion does need it; this one is a rearrangement of the definition, valid for every
bifunction. -/
theorem theorem_29_1 (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker (pairing m) F ↔ -v ∈ subgradient (pairing m) (infBifun F) 0 :=
  mem_kuhnTucker_iff_neg_mem_subgradient ht hb

/-- **Rockafellar, Theorem 29.1**, second assertion, as an equation between sets: the Kuhn–Tucker
set is the reflection of `∂(inf F)(0)`. Every property of subdifferentials transfers through it,
which is what Corollaries 29.1.1–29.1.5 are. -/
theorem theorem_29_1_set (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = -(subgradient (pairing m) (infBifun F) 0) :=
  kuhnTucker_eq_neg_subgradient ht hb

end Theorem291

/-! ### Corollary 29.1.1

Line 11885: Theorems 23.1 and 23.2 applied to `inf F`. -/

section Corollary2911

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 29.1.1** (line 11885), first clause: the one-sided directional
derivative `(inf F)'(0; u)` *exists* for every `u`.

The backbone defines `dirDeriv` as the infimum of the difference quotient over `λ > 0`, where the
book defines it as the limit as `λ ↓ 0`; this is Theorem 23.1's monotonicity, which says the two
agree, specialised to `inf F` at the origin. -/
theorem corollary_29_1_1_monotone {r : ℝ} (hF : ConvexBifun F) (hr : infBifun F 0 = (r : EReal))
    (u : Rn m) :
    MonotoneOn (fun a : ℝ => (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal))
      (Set.Ioi 0) :=
  monotoneOn_sub_div (convexFn_infBifun hF) hr u

/-- **Rockafellar, Corollary 29.1.1**, the formula for the directional derivative it is stated
with (line 11888). In the backbone this is the definition of `dirDeriv`. -/
theorem corollary_29_1_1_iInf (F : Bifun (Rn m) (Rn n)) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = ⨅ a ∈ Set.Ioi (0 : ℝ), (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal) :=
  dirDeriv_apply _ 0 u

/-- **Rockafellar, Corollary 29.1.1**, first clause: `(inf F)'(0; ·)` is positively homogeneous.
This clause needs nothing at all — it is a reindexing of the infimum. -/
theorem corollary_29_1_1_posHomogeneous (F : Bifun (Rn m) (Rn n)) :
    PosHomogeneous (dirDeriv (infBifun F) 0) :=
  posHomogeneous_dirDeriv_infBifun F

/-- **Rockafellar, Corollary 29.1.1**, first clause: `(inf F)'(0; ·)` is a convex function of the
direction. -/
theorem corollary_29_1_1_convexFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : ConvexFn (dirDeriv (infBifun F) 0) :=
  convexFn_dirDeriv_infBifun hF ht hb

/-- **Rockafellar, Corollary 29.1.1**, second clause: the Kuhn–Tucker vectors form a convex set. -/
theorem corollary_29_1_1_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  convex_kuhnTucker ht hb

/-- **Rockafellar, Corollary 29.1.1**, second clause: the Kuhn–Tucker vectors form a closed set. -/
theorem corollary_29_1_1_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  isClosed_kuhnTucker ht hb

/-- **Rockafellar, Corollary 29.1.1**, last clause (line 11891): the support function of the
Kuhn–Tucker set is the closure of `u ↦ (inf F)'(0; -u)`.

This is Theorem 23.2 at the origin, composed with the sign flip of Theorem 29.1. -/
theorem corollary_29_1_1_supportFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    supportFn (pairing m) (KuhnTucker (pairing m) F) u
      = clFn (dirDeriv (infBifun F) 0) (-u) := by
  rw [← supportFn_flip_pairing]
  exact supportFn_kuhnTucker hF ht hb u

end Corollary2911

/-! ### Corollary 29.1.2

Line 11899: Theorem 23.3 applied to `inf F`. -/

section Corollary2912

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 29.1.2** (line 11899): for a convex program with a finite optimal
value, a Kuhn–Tucker vector fails to exist exactly when some direction of perturbation makes the
*two-sided* directional derivative of the optimal value equal to `-∞`.

"Two-sided and equal to `-∞`" is spelled out as the book means it: the derivative from the right is
`(inf F)'(0; u) = -∞`, and the one from the left is `-(inf F)'(0; -u) = -∞`, i.e.
`(inf F)'(0; -u) = +∞`.

This is the definitive existence criterion for Kuhn–Tucker vectors from the equilibrium-price point
of view (line 11909): the program has one unless perturbation in some direction is "infinitely
advantageous", which obviously precludes an equilibrium. -/
theorem corollary_29_1_2 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = ∅ ↔
      ∃ u : Rn m, dirDeriv (infBifun F) 0 u = ⊥ ∧ dirDeriv (infBifun F) 0 (-u) = ⊤ :=
  kuhnTucker_eq_empty_iff hF ht hb

end Corollary2912

/-! ### Corollary 29.1.3

Line 11913: Theorem 29.1 and Theorem 25.1. -/

section Corollary2913

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {b : Rn m}

/-- **Rockafellar, Corollary 29.1.3** (line 11913): for a convex program with a finite optimal
value, `(P)` has a *unique* Kuhn–Tucker vector exactly when the perturbation function is
differentiable at the origin.

Rockafellar's proof is "immediate from Theorem 29.1 and Theorem 25.1", and so is this one; the
properness that Theorem 25.1 wants is supplied on each side of the equivalence rather than
assumed. See `## Where the book's hypotheses had to change`. -/
theorem corollary_29_1_3 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (∃ v : Rn m, KuhnTucker (pairing m) F = {v}) ↔ DifferentiableAtFn (infBifun F) 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hsub : subgradient (pairing m) (infBifun F) 0 = {-v} := by
      have h := theorem_29_1_set (F := F) ht hb
      rw [hv] at h
      have h2 : subgradient (pairing m) (infBifun F) 0 = -({v} : Set (Rn m)) := by
        rw [h, neg_neg]
      rw [h2, Set.neg_singleton]
    have hmem : -v ∈ subgradient (pairing m) (infBifun F) 0 := by rw [hsub]; rfl
    have hp : Proper (infBifun F) := proper_of_mem_subgradient ht hb hmem
    exact (theorem_25_1_differentiableAtFn (convexFn_infBifun hF) hp).2 ⟨-v, hsub⟩
  · intro hd
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
    have hp : Proper (infBifun F) := corollary_25_1_1_proper (convexFn_infBifun hF) hc
    refine ⟨-c, ?_⟩
    rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) hc,
      Set.neg_singleton]

/-- **Rockafellar, Corollary 29.1.3**, the formula: where the perturbation function is
differentiable at the origin with gradient `b`, the unique Kuhn–Tucker vector is `-b`. -/
theorem corollary_29_1_3_eq (hF : ConvexBifun F) (h : HasGradientVecAt (infBifun F) b 0)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = {-b} := by
  rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) h, Set.neg_singleton]

/-- **Rockafellar, Corollary 29.1.3**, the book's coordinate formula (line 11916):
`vᵢ* = -∂(inf F)/∂vᵢ` at `u = 0`.

The `i`-th partial derivative is the directional derivative along the `i`-th coordinate vector
`eᵢ`, which is Theorem 25.2 read at a basis vector. -/
theorem corollary_29_1_3_partial (hF : ConvexBifun F) {v : Rn m}
    (hv : v ∈ KuhnTucker (pairing m) F) (hd : DifferentiableAtFn (infBifun F) 0) (i : Fin m) :
    dirDeriv (infBifun F) 0 (EuclideanSpace.single i (1 : ℝ)) = ((-(v i) : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
  have hset : KuhnTucker (pairing m) F = {-c} :=
    corollary_29_1_3_eq hF hc hv.1 hv.2.1
  have hvc : v = -c := by rw [hset] at hv; exact hv
  rw [theorem_25_2_dirDeriv (convexFn_infBifun hF) hc, hvc]
  congr 1
  rw [pairing_apply, EuclideanSpace.inner_single_left]
  simp

end Corollary2913

/-! ### Strong and strict consistency

Line 11929. `Consistent`, `StronglyConsistent` and `StrictlyConsistent` are the backbone's, defined
as `0 ∈ dom F`, `0 ∈ ri (dom F)` and `0 ∈ int (dom F)`; what is here is the general
characterisation of strict consistency that Rockafellar records at line 11941. -/

section Consistency

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, line 11941**: a convex program `(P)` is strictly consistent if and only if, for
every `u ∈ ℝᵐ`, there is a `λ > 0` with `λu ∈ dom F` — informally, a consistent program is strictly
consistent unless some direction of perturbation empties the feasible set immediately.

The book cites Corollary 6.4.1; the backbone's form of it is
`mem_interior_iff_forall_exists_smul_mem`, which is where the convexity of `dom F` is used. -/
theorem strictlyConsistent_iff (hF : ConvexBifun F) :
    StrictlyConsistent F ↔ ∀ u : Rn m, ∃ a : ℝ, 0 < a ∧ a • u ∈ domBifun F := by
  rw [StrictlyConsistent, Convex.mem_interior_iff_absorbs (convex_domBifun hF)]
  exact forall_congr' fun u => exists_congr fun a => by rw [zero_add]

end Consistency

/-! ### Corollary 29.1.4

Line 11943: Theorem 23.4 applied to `inf F`, whose properness comes from Theorem 7.2. -/

section Corollary2914

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- Negating an infimum of real values over a set turns it into a supremum: this is the one
`EReal` step between the backbone's support function and the book's `-inf {⟨u*, u⟩ | u* ∈ U*}`. -/
private theorem iSup_coe_neg_eq (S : Set (Rn m)) (g : Rn m → ℝ) :
    (⨆ v ∈ S, ((-(g v) : ℝ) : EReal)) = -(⨅ v ∈ S, ((g v : ℝ) : EReal)) := by
  rw [Tdaf.EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [Tdaf.EReal.neg_iInf]
  exact iSup_congr fun _ => (_root_.EReal.coe_neg (g v)).symm

/-- **Rockafellar, Corollary 29.1.4** (line 11943), existence half: a strongly (or strictly)
consistent convex program with a finite optimal value has at least one Kuhn–Tucker vector.

Rockafellar applies Theorem 23.4 to `inf F`, noting that Theorem 7.2 makes `inf F` proper because
it is finite at `0` and `0` is a relative interior point of its effective domain. That is exactly
`proper_infBifun_of_stronglyConsistent`. -/
theorem corollary_29_1_4_nonempty (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_stronglyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs hb) hs ht

/-- **Rockafellar, Corollary 29.1.4**, the derivative formula (line 11946):

`(inf F)'(0; u) = -inf {⟨u*, u⟩ | u* ∈ U*}`,

where `U*` is the set of all Kuhn–Tucker vectors for `(P)`. This is the complete interpretation of
Kuhn–Tucker vectors as rates of change of the optimal value under the given perturbations. -/
theorem corollary_29_1_4_dirDeriv (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = -(⨅ v ∈ KuhnTucker (pairing m) F, ((pairing m u v : ℝ) : EReal)) := by
  have hp : Proper (infBifun F) := proper_infBifun_of_stronglyConsistent hF hs hb
  rw [dirDeriv_infBifun_eq (B := pairing m) hF hp hs u, supportFn_flip_pairing, supportFn_apply,
    ← iSup_coe_neg_eq]
  refine iSup_congr fun v => iSup_congr fun _ => ?_
  rw [map_neg, pairing_comm v u]

end Corollary2914

/-! ### Corollary 29.1.5

Line 11951 (a **mixed-case** label, invisible to a case-sensitive scan for `COROLLARY`): Theorems
7.2, 10.1 and 23.4 applied to `inf F`. -/

section Corollary2915

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 29.1.5** (line 11951), first clause: for a strictly consistent convex
program with a finite optimal value there is an **open convex neighbourhood of `0`** on which
`inf F` is finite and continuous.

The neighbourhood is `int (dom F)` itself, which is what Rockafellar's proof produces: `dom F` is
the effective domain of `inf F` by Theorem 29.1, `inf F` is proper by Theorem 7.2, and a proper
convex function is finite and continuous throughout the interior of its effective domain
(Theorem 10.1). -/
theorem corollary_29_1_5_nbhd (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) :
    ∃ V : Set (Rn m), IsOpen V ∧ Convex ℝ V ∧ (0 : Rn m) ∈ V ∧
      (∀ u ∈ V, infBifun F u ≠ ⊤ ∧ infBifun F u ≠ ⊥) ∧ ContinuousOn (infBifun F) V := by
  have hp : Proper (infBifun F) :=
    proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb
  refine ⟨interior (domBifun F), isOpen_interior, (convex_domBifun hF).interior, hs,
    fun u hu => ⟨infBifun_ne_top_of_mem_domBifun (interior_subset hu), hp.ne_bot u⟩,
    continuousOn_infBifun_interior hF hp⟩

/-- **Rockafellar, Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **non-empty**
set. -/
theorem corollary_29_1_5_nonempty (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

/-- **Rockafellar, Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **closed**
set. -/
theorem corollary_29_1_5_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  isClosed_kuhnTucker ht hb

/-- **Rockafellar, Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **bounded**
set. This is the one clause of §29 that is genuinely finite-dimensional in the *dual* variable:
Theorem 23.4 bounds `∂f(x)` only in the pairing sense of Corollary 13.2.2, and the upgrade to
`Bornology.IsBounded` is a coordinate estimate against a finite basis. It is also the clause that
distinguishes Corollary 29.1.5 from Corollary 29.1.4, which has no boundedness assertion at all —
under mere *strong* consistency the Kuhn–Tucker set need not be bounded, because Theorem 23.4
bounds `∂f x` only at *interior* points of `dom f`. -/
theorem corollary_29_1_5_isBounded (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) : Bornology.IsBounded (KuhnTucker (pairing m) F) :=
  isBounded_kuhnTucker_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs

/-- **Rockafellar, Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **convex**
set. -/
theorem corollary_29_1_5_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  convex_kuhnTucker ht hb

/-- **Rockafellar, Corollary 29.1.5**, last clause, in one piece: for a strictly consistent program
with a finite optimal value the Kuhn–Tucker set is non-empty, compact and convex. Compactness is
Heine–Borel applied to the closedness and boundedness clauses. -/
theorem corollary_29_1_5_isCompact (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsCompact (KuhnTucker (pairing m) F) :=
  isCompact_kuhnTucker_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

end Corollary2915

/-! ### Corollary 29.1.6

Line 11955: Theorem 7.2 applied to `inf F`. -/

section Corollary2916

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Corollary 29.1.6** (line 11955): if `inf Fu = -∞` for *some* `u`, then
`inf Fu = -∞` for *every* `u ∈ ri (dom F)`. -/
theorem corollary_29_1_6_bot (hF : ConvexBifun F) (h : ∃ u : Rn m, infBifun F u = ⊥) {u : Rn m}
    (hu : u ∈ ri (domBifun F)) : infBifun F u = ⊥ :=
  infBifun_eq_bot_of_mem_relint hF h hu

/-- **Rockafellar, Corollary 29.1.6**, the parenthesis: `inf Fu = +∞` for every `u ∉ dom F`. This
needs neither convexity nor the hypothesis of the corollary; it is Theorem 29.1's identification of
`dom (inf F)` with `dom F`. -/
theorem corollary_29_1_6_top {u : Rn m} (hu : u ∉ domBifun F) : infBifun F u = ⊤ :=
  infBifun_eq_top_of_notMem_domBifun hu

end Corollary2916

/-! ### Theorem 29.2

Line 12029: the special properties of polyhedral convex programs, from Corollary 19.3.1,
Corollary 27.3.2 and Theorem 23.10. -/

section Theorem292

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, Theorem 29.2** (line 12029), first clause: every slice `Fu` of a polyhedral
convex bifunction — in particular the objective function `F0` — is a polyhedral convex
function. -/
theorem theorem_29_2_objective (hF : PolyhedralBifun F) (u : Rn m) : PolyhedralFn (F u) :=
  hF.polyhedralFn_apply u

/-- **Rockafellar, Theorem 29.2**, second clause: the perturbation function of a polyhedral convex
program is polyhedral. This is Corollary 19.3.1 at the projection `(u, x) ↦ u`, which is the only
step of the theorem that is not immediate. -/
theorem theorem_29_2_infBifun (hF : PolyhedralBifun F) : PolyhedralFn (infBifun F) :=
  hF.polyhedralFn_infBifun

/-- **Rockafellar, Theorem 29.2**, third clause: a polyhedral convex program with a finite optimal
value has at least one **optimal solution**.

The proof needs less than the book asks: `inf F0 ≠ -∞` alone makes `F0` bounded below, and
Corollary 27.3.2 then attains the infimum. Finiteness is what the *polyhedrality* of the minimum
set below needs. -/
theorem theorem_29_2_argmin_nonempty (hF : PolyhedralBifun F) (hb : infBifun F 0 ≠ ⊥) :
    (argmin (F 0)).Nonempty :=
  argmin_nonempty_of_polyhedralBifun hF hb

/-- **Rockafellar, Theorem 29.2**, third clause: a polyhedral convex program with a finite optimal
value has at least one **Kuhn–Tucker vector**. This is Theorem 23.10 applied to `inf F` at the
origin, through Theorem 29.1. -/
theorem theorem_29_2_kuhnTucker_nonempty (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_polyhedralBifun hF ht hb

/-- **Rockafellar, Theorem 29.2**, last clause: the optimal solutions form a polyhedral convex set,
being a sublevel set of the polyhedral function `F0` at the optimal value. -/
theorem theorem_29_2_polyhedral_argmin (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (argmin (F 0)) :=
  polyhedral_argmin_of_polyhedralBifun hF ht hb

/-- **Rockafellar, Theorem 29.2**, last clause: the Kuhn–Tucker vectors form a polyhedral convex
set. -/
theorem theorem_29_2_polyhedral_kuhnTucker (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (KuhnTucker (pairing m) F) :=
  polyhedral_kuhnTucker_of_polyhedralBifun hF ht hb

end Theorem292

/-! ### Theorem 29.3

Line 12035: the Lagrangian characterisation of Kuhn–Tucker vectors and optimal solutions.

**The route is direct, not through §36.** `Saddle/Minimax.lean` is where the backbone states this,
because that is where `IsSaddlePoint` and the Lagrangian-as-a-saddle-function are defined; but
nothing in the proof is a minimax theorem. It is Rockafellar's own argument —
`⨅ y L(v, y) ≤ inf F0 ≤ (F0)(x) = ⨆ w L(w, x)`, with the outer terms `≠ +∞` and `≠ -∞` by
properness — and its one non-trivial ingredient is Fenchel–Moreau read at the origin
(`clFn_zero_eq_iSup_iInf`, Theorem 12.2), which is §12. The book's forward reference to §36 at
line 12103 is about the *interpretation* of the saddle-point problem, not about this proof. -/

section Theorem293

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m} {x : Rn n}

/-- **Rockafellar, Theorem 29.3** (line 12035), as the book displays it (line 12037): for a closed
proper convex bifunction `F`, `ū*` is a Kuhn–Tucker vector for `(P)` and `x̄` is an optimal
solution to `(P)` if and only if

`L(u*, x̄) ≤ L(ū*, x̄) ≤ L(ū*, x)` for all `u*` and all `x`,

i.e. `(ū*, x̄)` is a saddle-point of the Lagrangian. -/
theorem theorem_29_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) :
    ((∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [← isSaddlePoint_lagrangian_iff_forall, isSaddlePoint_lagrangian_iff hF hcl hpr]
  refine and_congr_right fun hv => ?_
  exact (isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) hv.1).symm

/-- **Rockafellar, Theorem 29.3**, in the backbone's bundled form. -/
theorem theorem_29_3_isSaddlePoint (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [isSaddlePoint_lagrangian_iff_forall]
  exact theorem_29_3 hF hcl hpr

end Theorem293

/-! ### Corollary 29.3.1

Line 12097: the generalized Kuhn–Tucker theorem. -/

section Corollary2931

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- The common core of Corollary 29.3.1's three constraint qualifications: whenever the
qualification supplies a Kuhn–Tucker vector at a finite optimal value, optimality of `x̄` is
equivalent to `x̄` completing some `ū*` to a saddle-point.

The `-∞` branch is where the book's "polyhedral and merely consistent" needs care: an optimal value
of `-∞` leaves a closed proper program with no optimal solutions and no Kuhn–Tucker vectors, so the
equivalence holds with both sides false. -/
private theorem corollary_29_3_1_aux (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F)
    (hkt : infBifun F 0 ≠ ⊥ → (KuhnTucker (pairing m) F).Nonempty) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) := by
  by_cases hb : infBifun F 0 = ⊥
  · refine ⟨fun h => absurd h (not_isOptimalSolution_of_infBifun_eq_bot hb), ?_⟩
    rintro ⟨v, hv⟩
    exact absurd ((theorem_29_3_isSaddlePoint hF hcl hpr).1 hv).1.2.1 (not_not.2 hb)
  · have ht : infBifun F 0 ≠ ⊤ := infBifun_ne_top_of_mem_domBifun hc
    rw [isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) ht]
    exact mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr (hkt hb)

/-- **Rockafellar, Corollary 29.3.1** (line 12097), the strongly consistent case: for a strongly
consistent closed proper convex program, `x̄` is an optimal solution to `(P)` if and only if there
is a `ū*` making `(ū*, x̄)` a saddle-point of the Lagrangian.

This is the generalization of the Kuhn–Tucker Theorem (Corollary 28.3.1), and Rockafellar restates
it as Theorem 36.6. -/
theorem corollary_29_3_1_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF hcl hpr hs.consistent fun hb =>
    corollary_29_1_4_nonempty hF hs (infBifun_ne_top_of_mem_domBifun hs.consistent) hb

/-- **Rockafellar, Corollary 29.3.1**, the strictly consistent case. A strictly consistent program
is strongly consistent, so this is the previous corollary verbatim. -/
theorem corollary_29_3_1_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Rockafellar, Corollary 29.3.1**, the polyhedral case: for a *polyhedral* closed proper convex
program no more than plain consistency is needed, because Theorem 29.2 supplies a Kuhn–Tucker
vector without any interiority hypothesis. -/
theorem corollary_29_3_1_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF.convexBifun hcl hpr hc fun hb =>
    theorem_29_2_kuhnTucker_nonempty hF (infBifun_ne_top_of_mem_domBifun hc) hb

end Corollary2931

/-! ### Theorem 29.4

Line 12109: the closure of a bifunction, slice by slice. The operation `cl F` — the bifunction
whose graph function is `cl (graph F)` — is introduced at line 12107 in order to regularize a
program before applying Theorem 29.3 or the duality theory of §30. -/

section Theorem294

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Line 12107**: `cl F` is a closed convex bifunction. -/
theorem clBifun_convex (hF : ConvexBifun F) : ConvexBifun (clBifun F) :=
  ConvexBifun.clBifun hF

/-- **Line 12107**: `cl F` is closed. -/
theorem clBifun_closed (F : Bifun (Rn m) (Rn n)) : ClosedBifun (clBifun F) :=
  closedBifun_clBifun F

/-- **Line 12107**: `cl F` is proper when `F` is. -/
theorem clBifun_proper (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    Proper (graphFn (clBifun F)) :=
  ConvexFn.proper_clFn hF hp

/-- **Rockafellar, Theorem 29.4** (line 12109), first assertion: for each `u ∈ ri (dom F)`,

`(cl F)u = cl (Fu)`.

**The printed proof is correct, and this repository's records said otherwise.** `part6.md`,
`inventory.md` and `00-overview.md` all record a defect at line 12139: "it claims
`((cl F)u)(y) = -∞` for *all* `y` in the improper case, but `cl f` is `+∞` outside `cl (dom f)`".
That is a description of the lower semicontinuous hull `f̄`, not of `cl f`. Rockafellar's closure is
defined by cases at line 2177 — "the closure of `f` is defined to be the constant function `-∞` if
`f` is an improper convex function such that `f(x) = -∞` for some `x`" — and line 2231 states the
contrast explicitly: "`f̄(x)` is `-∞` on `cl (dom f)` and `+∞` outside `cl (dom f)`, whereas
`(cl f)(x)` is `-∞` **everywhere**, for such a function `f`." The step at 12137–12141 is therefore
sound, and the backbone's proof takes exactly the same route through `clFn_of_exists_eq_bot`.
(The cited line 12139 is in any case a display-math delimiter; the claim itself is on 12140.) -/
theorem theorem_29_4_apply (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (domBifun F)) :
    clBifun F u = clFn (F u) :=
  clBifun_apply_eq_clFn hF hu

/-- **Rockafellar, Theorem 29.4**, second assertion: `inf (cl F)u = inf Fu` for `u ∈ ri (dom F)`.
A convex function and its closure have the same infimum, so the content is the first assertion. -/
theorem theorem_29_4_inf (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (domBifun F)) :
    infBifun (clBifun F) u = infBifun F u :=
  infBifun_clBifun_eq hF hu

/-- **Rockafellar, Theorem 29.4**, third assertion, first inclusion: `dom F ⊆ dom (cl F)` for
proper `F`. -/
theorem theorem_29_4_dom_subset (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun F ⊆ domBifun (clBifun F) :=
  domBifun_subset_domBifun_clBifun hF hp

/-- **Rockafellar, Theorem 29.4**, third assertion, second inclusion:
`dom (cl F) ⊆ cl (dom F)` for proper `F`. Properness is not decoration here: the counterexample
`originBifun` below has `dom F = {0}` and `dom (cl F) = ℝ¹`. -/
theorem theorem_29_4_dom_subset_closure (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun (clBifun F) ⊆ closure (domBifun F) :=
  domBifun_clBifun_subset_closure hF hp

end Theorem294

/-! ### Corollary 29.4.1

Line 12151. Printed with no proof at all, and stated without the properness hypothesis its own
Theorem 29.4 carries; see `## Where the book is defective` in the module docstring. Every clause
below is proved; the one that needs properness is `corollary_29_4_1_eventually`, and
`corollary_29_4_1_perturbation_false` shows it cannot be dropped. -/

section Corollary2941

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- **Rockafellar, Corollary 29.4.1**, the underlying domain fact: closing a proper convex
bifunction leaves the relative interior of its effective domain alone. Theorem 29.4's two
inclusions sandwich `dom (cl F)` between `dom F` and `cl (dom F)`, and Corollary 6.3.1 says such a
sandwich has the same relative interior. -/
theorem corollary_29_4_1_relint (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    ri (domBifun (clBifun F)) = ri (domBifun F) :=
  relint_domBifun_clBifun hF hp

/-- **Rockafellar, Corollary 29.4.1**, first clause: if `(P)` is strongly consistent then so is
`(cl P)`.

**This clause does survive without properness**, unlike the perturbation clause below, and it is
stated here as the book states it. The improper case is not the sandwich of Theorem 29.4 but its
opposite: an improper `F` whose graph function is somewhere `-∞` has `cl (graph F)` the *constant*
`-∞`, so `dom (cl F)` is all of `ℝᵐ` and the conclusion is immediate; and an improper `F` with an
empty graph domain is not consistent at all, so the hypothesis is vacuous. -/
theorem corollary_29_4_1_stronglyConsistent (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    StronglyConsistent (clBifun F) := by
  by_cases hp : Proper (graphFn F)
  · exact stronglyConsistent_clBifun hF hp hs
  · have hne : (dom (graphFn F)).Nonempty := by
      have h0 : (0 : Rn m) ∈ domBifun F := intrinsicInterior_subset hs
      obtain ⟨x, hx⟩ := h0
      exact ⟨(0, x), mem_dom.2 (lt_of_le_of_ne le_top hx)⟩
    have hbot : ∃ p, graphFn F p = ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hp ⟨hne, hcon⟩
    obtain ⟨p, hpbot⟩ := hbot
    have hlsc : lscHull (graphFn F) p = ⊥ :=
      le_bot_iff.1 (le_trans (lscHull_le (graphFn F) p) (le_of_eq hpbot))
    have hcl : clFn (graphFn F) = fun _ => ⊥ := clFn_of_exists_eq_bot ⟨p, hlsc⟩
    have hdom : domBifun (clBifun F) = Set.univ := by
      ext u
      simp only [mem_domBifun, Set.mem_univ, iff_true]
      exact ⟨0, by rw [clBifun_apply, hcl]; simp⟩
    change (0 : Rn m) ∈ ri (domBifun (clBifun F))
    rw [hdom]
    exact interior_subset_intrinsicInterior (by simp)

/-- **Rockafellar, Corollary 29.4.1**, second clause: the objective function for `(cl P)` is the
closure of the objective function for `(P)`. This is Theorem 29.4 read at the origin. -/
theorem corollary_29_4_1_objective (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    clBifun F 0 = clFn (F 0) :=
  clBifun_zero_eq_clFn hF hs

/-- **Rockafellar, Corollary 29.4.1**, third clause: `(P)` and `(cl P)` have the same optimal
value. -/
theorem corollary_29_4_1_optimalValue (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (clBifun F) 0 = infBifun F 0 :=
  infBifun_clBifun_zero_eq hF hs

/-- **Rockafellar, Corollary 29.4.1**, fourth clause, in the backbone's vocabulary: every minimiser
of the objective function of `(P)` minimises that of `(cl P)`. The inclusion is strict in general —
closing can create new minimisers. -/
theorem corollary_29_4_1_argmin (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (clBifun F 0) :=
  argmin_subset_argmin_clBifun hF hs

/-- **Rockafellar, Corollary 29.4.1**, fourth clause, in the book's own vocabulary: every optimal
solution to `(P)` is an optimal solution to `(cl P)`. -/
theorem corollary_29_4_1_optimalSolution (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (h : IsOptimalSolution F x) : IsOptimalSolution (clBifun F) x := by
  have hval : infBifun (clBifun F) 0 = infBifun F 0 := infBifun_clBifun_zero_eq hF hs
  have hge : infBifun (clBifun F) 0 ≤ clBifun F 0 x := by
    rw [infBifun_apply]
    exact iInf_le _ x
  have hle : clBifun F 0 x ≤ infBifun (clBifun F) 0 := by
    rw [hval, ← h.2.2]
    exact clBifun_le F 0 x
  have heq : clBifun F 0 x = infBifun (clBifun F) 0 := le_antisymm hle hge
  refine ⟨?_, ?_, heq⟩
  · rw [heq, hval, ← h.2.2]; exact h.1
  · rw [heq, hval, ← h.2.2]; exact h.2.1

/-- **Rockafellar, Corollary 29.4.1**, fifth clause, **with the properness hypothesis the book
omits**: the perturbation functions of `(P)` and `(cl P)` agree on a neighbourhood of `0`.

Theorem 29.4 supplies agreement on `ri (dom F)`, which is only a *relative* neighbourhood; what
upgrades it is that `ri C` is relatively open together with
`dom (cl F) ⊆ cl (dom F) ⊆ aff (dom F)`, so a small enough ball around the origin meets no point
except those of `ri (dom F)` — where Theorem 29.4 applies — and those outside `aff (dom F)`, where
both perturbation functions are `+∞`. The second inclusion is where properness enters, and
`corollary_29_4_1_perturbation_false` shows the clause is false without it. -/
theorem corollary_29_4_1_eventually (hF : ConvexBifun F) (hp : Proper (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (clBifun F) u = infBifun F u :=
  eventually_infBifun_clBifun_eq hF hp hs

/-- **Rockafellar, Corollary 29.4.1**, last clause: `(P)` and `(cl P)` have the same Kuhn–Tucker
vectors.

The book deduces this from the agreement of the two perturbation functions near `0`, which is the
clause that needs properness; the backbone's route does not, because the adjoint bifunction never
sees the closure at all (`adjointBifun_clBifun`) and a Kuhn–Tucker vector is a point where the dual
objective attains the optimal value. So this clause holds under the book's own hypotheses. -/
theorem corollary_29_4_1_kuhnTucker (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    KuhnTucker (pairing m) (clBifun F) = KuhnTucker (pairing m) F :=
  kuhnTucker_clBifun_eq (Bu := pairing m) (pairing n) hF hs

end Corollary2941

/-! ### Corollary 29.4.1 as printed is false

The *stated and refuted* category of the alignment checklist. `corollary_29_4_1_perturbation` is
the corollary's fifth clause transcribed with the hypotheses the book prints — a convex bifunction
and a strongly consistent program, and no properness — and `corollary_29_4_1_perturbation_false`
refutes it on `ℝ¹`. -/

section Counterexample

/-- The counterexample to Corollary 29.4.1 as printed: the bifunction on `ℝ¹` that is `-∞` when
`u = 0` and `+∞` otherwise.

This is the `ℝ¹` degeneration of the recorded `ℝ²` example — `F u x = -∞` for `u` on a line `L`
through the origin and `+∞` off it — with `L` the origin itself. Nothing two-dimensional is needed:
what the example must do is make `dom F` a proper affine subset containing the origin in its
relative interior, and `{0} ⊆ ℝ¹` is the cheapest such set.

The `⨆ _ : p, c` encoding keeps `Decidable` out of the definition; see `gotchas.md` ER6. -/
noncomputable def originBifun : Bifun (Rn 1) (Rn 1) := fun u _ => ⨆ _ : u ≠ 0, (⊤ : EReal)

@[simp] theorem originBifun_zero (x : Rn 1) : originBifun 0 x = ⊥ := by
  rw [originBifun, iSup_neg (by simp)]

@[simp] theorem originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) (x : Rn 1) :
    originBifun u x = ⊤ := by
  rw [originBifun, iSup_pos hu]

/-- `originBifun` is convex: its epigraph is the preimage of `{0}` under a linear map, hence a
linear subspace of `(ℝ¹ × ℝ¹) × ℝ`. -/
theorem convexBifun_originBifun : ConvexBifun originBifun := by
  refine ⟨?_⟩
  have hepi : epi (graphFn originBifun)
      = ((LinearMap.fst ℝ (Rn 1) (Rn 1)) ∘ₗ
          (LinearMap.fst ℝ (Rn 1 × Rn 1) ℝ)) ⁻¹' ({0} : Set (Rn 1)) := by
    ext q
    obtain ⟨⟨u, y⟩, a⟩ := q
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · simp [hu]
  rw [hepi]
  exact (convex_singleton (0 : Rn 1)).linear_preimage _

/-- `dom F = {0}`. -/
@[simp] theorem domBifun_originBifun : domBifun originBifun = ({0} : Set (Rn 1)) := by
  ext u
  simp only [mem_domBifun, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy⟩
    by_contra hu
    exact hy (originBifun_of_ne_zero hu y)
  · rintro rfl
    exact ⟨0, by simp⟩

/-- `(P)` is strongly consistent: `ri {0} = {0}` contains the origin. -/
theorem stronglyConsistent_originBifun : StronglyConsistent originBifun := by
  change (0 : Rn 1) ∈ ri (domBifun originBifun)
  rw [domBifun_originBifun, intrinsicInterior_singleton]
  exact rfl

/-- `cl F` is the constant `-∞`: the graph function takes the value `-∞`, so Rockafellar's closure
convention (line 2177) makes its closure the constant `-∞` everywhere. -/
theorem clBifun_originBifun (u x : Rn 1) : clBifun originBifun u x = ⊥ := by
  have hlsc : lscHull (graphFn originBifun) ((0 : Rn 1), (0 : Rn 1)) = ⊥ := by
    refine le_bot_iff.1 (le_trans (lscHull_le (graphFn originBifun) _) (le_of_eq ?_))
    rw [graphFn_apply, originBifun_zero]
  rw [clBifun_apply, clFn_of_exists_eq_bot ⟨_, hlsc⟩]

/-- `inf (cl F) ≡ -∞`. -/
theorem infBifun_clBifun_originBifun (u : Rn 1) : infBifun (clBifun originBifun) u = ⊥ := by
  rw [infBifun_apply]
  exact le_bot_iff.1 (le_trans (iInf_le _ 0) (le_of_eq (clBifun_originBifun u 0)))

/-- `inf F = +∞` away from the origin. -/
theorem infBifun_originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) : infBifun originBifun u = ⊤ := by
  rw [infBifun_apply]
  simp [originBifun_of_ne_zero hu]

/-- **Corollary 29.4.1's perturbation clause, transcribed with the hypotheses the book prints**
(line 12151): "Let `F` be a convex bifunction from `Rᵐ` to `Rⁿ`. … Assume that `(P)` is strongly
consistent. … The perturbation functions for `(P)` and `(cl P)` agree on a neighborhood of `0`."

No properness hypothesis appears anywhere in the corollary, although its own Theorem 29.4 carries
one for the domain inclusions the clause rests on. -/
def corollary_29_4_1_perturbation : Prop :=
  ∀ (m n : ℕ) (F : Bifun (Rn m) (Rn n)), ConvexBifun F → StronglyConsistent F →
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (clBifun F) u = infBifun F u

/-- **Corollary 29.4.1 is false as Rockafellar states it.**

Take `F = originBifun` on `ℝ¹`: `(Fu)(x) = -∞` for `u = 0` and `+∞` for `u ≠ 0`. It is convex, and
`dom F = {0}` has `0` in its relative interior, so `(P)` is strongly consistent. But its graph
function takes the value `-∞`, so `cl (graph F)` is the constant `-∞` by Rockafellar's own
convention, `inf (cl F) ≡ -∞`, while `inf F = +∞` at every `u ≠ 0`. The two perturbation functions
therefore agree at the single point `0`, and `{0}` is not a neighbourhood of `0` in `ℝ¹`.

**Root cause.** Every other clause of the corollary is Theorem 29.4 read at the origin, where
`0 ∈ ri (dom F)` is available; the perturbation clause is the one that needs agreement at points
*outside* `ri (dom F)`, and the only thing that gives it there is Theorem 29.4's third assertion
`dom (cl F) ⊆ cl (dom F)`, which is stated for proper `F`. With `F` proper the clause is
`corollary_29_4_1_eventually`. -/
theorem corollary_29_4_1_perturbation_false : ¬ corollary_29_4_1_perturbation := by
  intro hcor
  have hev := hcor 1 1 originBifun convexBifun_originBifun stronglyConsistent_originBifun
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : Rn 1),
      infBifun (clBifun originBifun) u = infBifun originBifun u :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨u, hu, hune⟩ := (h1.and (eventually_mem_nhdsWithin (a := (0 : Rn 1)))).exists
  have hune' : u ≠ 0 := hune
  rw [infBifun_clBifun_originBifun u, infBifun_originBifun_of_ne_zero hune'] at hu
  exact absurd hu (by simp)

end Counterexample

end Rockafellar
