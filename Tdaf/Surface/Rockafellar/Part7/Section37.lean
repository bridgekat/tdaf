/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Conjugate
import Tdaf.Analysis.Convex.Saddle.Existence
import Tdaf.Analysis.Convex.Saddle.Monotone
import Tdaf.Surface.Rockafellar.Part7.Section34
import Tdaf.Surface.Rockafellar.Part7.Section35
import Tdaf.Surface.Rockafellar.Part7.Section36

/-!
# Rockafellar, §37: Conjugate Saddle-Functions and Minimax Theorems

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §37, pp. 388–400: the **lower conjugate**
`K̲*` and the **upper conjugate** `K̄*` of a saddle-function, the conjugacy correspondence among
equivalence classes of closed saddle-functions, the effective domain `C* × D*` of the conjugate
class, the existence theorems for the saddle-value and for a saddle-point, and — as their special
cases — Rockafellar's two finite-dimensional minimax theorems.

This is the last section of Part VII and the section that pays for the whole Part: minimax theory
is the conjugacy correspondence of §§33–34 read at the origin.

## The three orientation conventions, all in force

1. `cl₁` closes the **concave/first** argument, `cl₂` the **convex/second** one (§33).
2. **Minimisation takes place in the convex argument and maximisation in the concave one**
   (§36, the sentence at 15449). `Section36.lean`'s docstring carries the table; every statement
   below is false verbatim under the opposite reading.
3. The **lower** conjugate is `sup_v inf_u` and the **upper** is `inf_u sup_v` (15763, 15769), with
   `K̲* ≤ K̄*` by Lemma 36.1 (`lowerConj_le_upperConj`). Swapping the extrema swaps the two
   conjugates.

Two places where the sign is explicit and is *not* re-derived from the shape of a statement:

* **Corollary 37.5.2 inserts `u* ↦ −u*`.** `∂K = ∂₁K × ∂₂K` mixes a concave superdifferential in
  the first argument with a convex subdifferential in the second, and §35 exports the reason as
  `mem_subgrad₁_iff_neg_mem_subgradient_neg`. Without the insertion `∂K` is monotone in one
  variable and antitone in the other, and `ρ` is what repairs it.
* **Corollary 37.5.1's homeomorphism is the asymmetric `(u − u*, v + v*)`**, not a symmetric sum,
  for the same reason.

## Conjugacy is a property of the class, not of a representative

Corollary 37.1.1 says the two conjugates depend only on the equivalence class of `K`. Following
§34, everything here is therefore stated for a member of `Ω (F)` — `Rockafellar.Ω` of
`Part7/Section34.lean` — or for a closed (proper) concave-convex function, from which
`exists_mem_Ω_of_closed` recovers the bifunction by Theorem 34.2. No statement quantifies over a
bare saddle-function where the class is what matters.

## Contents

| label | declaration |
|---|---|
| §37 definitions, 15753–15775 | `lowerConj`, `upperConj`, `lowerConj_le_upperConj`, `domSubgrad` |
| Theorem 37.1 | `theorem_37_1_upper`, `theorem_37_1_lower`, `theorem_37_1_conj_upper`,
  `theorem_37_1_conj_lower` |
| Corollary 37.1.1 | `corollary_37_1_1_lower_concaveConvex`, `corollary_37_1_1_lower_lowerClosed`,
  `corollary_37_1_1_upper_concaveConvex`, `corollary_37_1_1_upper_upperClosed`,
  `corollary_37_1_1_equiv`, `corollary_37_1_1_closed_lower`, `corollary_37_1_1_closed_upper`,
  `corollary_37_1_1_lower_class`, `corollary_37_1_1_upper_class`, `corollary_37_1_1_proper_upper`,
  `corollary_37_1_1_proper_lower`, `corollary_37_1_1_biconj_lower`,
  `corollary_37_1_1_biconj_upper` |
| Corollary 37.1.2 | `corollary_37_1_2_cl₁`, `corollary_37_1_2_cl₂`, `corollary_37_1_2_dom`,
  `corollary_37_1_2_structure`, `corollary_37_1_2_eq_of_mem_relint_dom₁`,
  `corollary_37_1_2_eq_of_mem_relint_dom₂` |
| §37, 15833–15849 | `minimax_eq_neg_lowerConj_zero`, `maximin_eq_neg_upperConj_zero` |
| Corollary 37.1.3 | `corollary_37_1_3_dom₁`, `corollary_37_1_3_dom₂`, `corollary_37_1_3_finite` |
| Theorem 37.2 | `theorem_37_2_dom₂`, `theorem_37_2_dom₂_recessionFn` |
| Corollary 37.2.1 | `corollary_37_2_1_dom₂`, `corollary_37_2_1_dom₁` |
| Theorem 37.3 (a), (b) | `theorem_37_3_a`, `theorem_37_3_b`, `theorem_37_3_finite` |
| Corollary 37.3.1 | `corollary_37_3_1_dom₂`, `corollary_37_3_1_dom₁` |
| Corollary 37.3.2 | `corollary_37_3_2_right`, `corollary_37_3_2_left` |
| Theorem 37.4 | `theorem_37_4`, `theorem_37_4_relint`, `theorem_37_4_dom`,
  `theorem_37_4_convex`, `theorem_37_4_isClosed` |
| Corollary 37.4.1 | `corollary_37_4_1_subgrad`, `corollary_37_4_1_eq` |
| Theorem 37.5 (a)–(d) | `theorem_37_5_f`, `theorem_37_5_a`, `theorem_37_5_b`, `theorem_37_5_c`,
  `theorem_37_5_d` |
| Corollary 37.5.1 | `corollary_37_5_1_isClosed`, `corollary_37_5_1_homeomorph`,
  `corollary_37_5_1_homeomorph_apply`, `corollary_37_5_1_exists_homeomorph` |
| Corollary 37.5.2 | `corollary_37_5_2`, `corollary_37_5_2_gradient` |
| Corollary 37.5.3 | `corollary_37_5_3`, `corollary_37_5_3_convex`, `corollary_37_5_3_isClosed`,
  `corollary_37_5_3_exists_iff`, `corollary_37_5_3_exists_of_relint` |
| Theorem 37.6 | `theorem_37_6`, `theorem_37_6_mem_dom` |
| Corollary 37.6.1 | `corollary_37_6_1`, `corollary_37_6_1_finite` |
| Corollary 37.6.2 | `corollary_37_6_2` |

## Where the book diverges, or is defective

**Corollary 37.1.3 is printed with no proof at all** (15851). It is closed here from
`hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle` and its mirror, which is exactly the argument
the two displays before the statement sketch.

**Corollaries 37.3.2 and 37.6.2 are Rockafellar's finite-dimensional minimax theorems**, and their
hypothesis is that `C` or `D` be **closed and bounded**. In infinite dimensions the corresponding
theorems — Kneser–Fan and Sion — require **compactness**, which is strictly stronger there; the
substitution is invisible in `ℝⁿ` by Heine–Borel and is flagged in each docstring. The backbone
proves Corollary 37.6.2 from Rockafellar's *own* unbounded machinery (Corollary 37.6.1 applied to
the lower simple extension) rather than from Mathlib's `Topology/Sion.lean`, because the unbounded
theorems it specialises are wanted anyway.

**Corollaries 37.3.2 and 37.6.2 weaken "continuous finite concave-convex function on `C × D`"**
from joint to *separate* continuity and convexity of each slice on its own set — the same
weakening §33 recorded for Corollary 33.3.3 and §34 for Corollary 34.2.4, and it is what the
backbone's `exists_bifunSaddleClass_lowerSimpleExt` actually uses.

**Corollary 37.3.2 cannot be stated with real-valued extrema.** With only one of `C`, `D` bounded
both iterated extrema can be infinite (`C = {0}`, `D = ℝ`, `K (u, v) = v` gives `sup inf = -∞`), so
the equality is in `EReal`. Corollary 37.6.2, where both are bounded, keeps the book's real
inequalities.

**Corollary 37.5.1's homeomorphism is parametrised by the bifunction.** The book's `K` is a closed
proper saddle-function and the map is built from the graph function of the `F` of Theorem 34.2;
`F` is unique but is produced by an existential, and a `Homeomorph` is data. So
`corollary_37_5_1_homeomorph` takes `F` and `corollary_37_5_1_exists_homeomorph` states the
book's `Nonempty` form.

**Corollary 37.4.1 is proved from Theorem 37.5, not from Theorem 37.4.** Rockafellar tilts by
`(u*, v*)` and appeals to Theorem 36.4; that route needs `cl₁ (K − ℓ) = cl₁ K − ℓ`, which the
backbone does not have. Theorem 37.5's (a) ⇔ (d) says `∂K` *is* the relation
`IsBifunSubgradientPair F` of the class, which gives the corollary directly — at the cost of
closedness and properness hypotheses the book does not state. See `corollary_37_4_1_subgrad`.

## What is not here

* **The `C*` half of Theorem 37.2** — the formula `−δ*(−z | C*) = inf_{v ∈ ri D} inf_{u ∈ C}
  {K (u + z, v) − K (u, v)}`. *Backbone gap*: `Saddle/Existence.lean` carries the `C*` half of
  Corollary 37.2.1 (`zero_mem_interior_dom₁_lowerConjSaddle_iff`) but not the support-function
  identity it is read off from. `Saddle/Conjugate.lean` has the `D*` identity
  (`supportFn_dom₂_upperConjSaddle`); the `C*` mirror wants
  `supportFn_dom₁_lowerConjSaddle` beside `zero_mem_interior_dom₁_lowerConjSaddle_iff`. Everything
  §37 uses Theorem 37.2 *for* is present, so nothing downstream is affected.
* **The motivating computation at 15697–15721** — `⟨u*, F_* x⟩ = inf_u {⟨u, u*⟩ + (Fu)(x)}` and its
  `inf_u sup_x*` form. *Deferred by scope*: the first display is §36's
  `inverseBifunBracket_apply`, and the second is Theorem 37.1 itself.
* **The closing remark at 16171** — every finite saddle-function on a bounded relatively open
  `C₀ × D₀` extends to a closed proper saddle-function with a saddle-point. *Deferred by scope*:
  it is `corollary_34_5_1` composed with `corollary_37_6_1` and Theorem 36.3, with no new content.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §37.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The two conjugates of a saddle-function (15753–15775) -/

section Defs

variable {m n : ℕ}

/-- **Rockafellar's lower conjugate `K̲*`** (15763):

`K̲* (u*, v*) = sup_v inf_u {⟨u, u*⟩ + ⟨v, v*⟩ − K (u, v)}`.

A reducible `abbrev` for the backbone's `lowerConjSaddle` at the two Euclidean pairings, so this
*is* that object. Note the order of the extrema: the supremum over the **convex** variable is
outermost. -/
noncomputable abbrev lowerConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  lowerConjSaddle (pairing m) (pairing n) K

/-- **Rockafellar's upper conjugate `K̄*`** (15769):

`K̄* (u*, v*) = inf_u sup_v {⟨u, u*⟩ + ⟨v, v*⟩ − K (u, v)}`,

with the infimum over the **concave** variable outermost. -/
noncomputable abbrev upperConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  upperConjSaddle (pairing m) (pairing n) K

/-- The book's defining formula for `K̲*` (15763). -/
theorem lowerConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    lowerConj K q
      = ⨆ v : Rn n, ⨅ u : Rn m, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- The book's defining formula for `K̄*` (15769). -/
theorem upperConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    upperConj K q
      = ⨅ u : Rn m, ⨆ v : Rn n, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- **Rockafellar, §37**, the sentence after the two definitions (15775): `K̲* ≤ K̄*`, "of course,
by Lemma 36.1". Specialises `lowerConjSaddle_le_upperConjSaddle`; no hypotheses. -/
theorem lowerConj_le_upperConj (K : Rn m × Rn n → EReal) : lowerConj K ≤ upperConj K :=
  lowerConjSaddle_le_upperConjSaddle (pairing m) (pairing n) K

/-- **Rockafellar's `dom ∂K = {(u, v) | ∂K (u, v) ≠ ∅}`** (15959). A reducible `abbrev` for
`domSaddleSubgradient` at the two Euclidean pairings. -/
abbrev domSubgrad (K : Rn m × Rn n → EReal) : Set (Rn m × Rn n) :=
  domSaddleSubgradient (pairing m) (pairing n) K

theorem mem_domSubgrad {K : Rn m × Rn n → EReal} {p : Rn m × Rn n} :
    p ∈ domSubgrad K ↔ (subgrad K p).Nonempty := Iff.rfl

/-- **`pairing n` separates on the left.** The mirror of `separatingRight_pairing`, which
`Surface/Common/Euclidean.lean` asserts; several `C*`-side backbone theorems ask for this one
instead, and on a self-paired space it is one line from `inner_self_eq_zero`. -/
theorem separatingLeft_pairing (n : ℕ) : (pairing n).SeparatingLeft :=
  fun _ hx => inner_self_eq_zero.1 (hx _)

/-- **Theorem 34.2, packaged for §37**: a closed concave-convex function on `ℝᵐ × ℝⁿ` belongs to
the class `Ω (F)` of a closed convex bifunction `F`, and `F` is unique.

Every result of §37 that the book states for a "closed (proper) concave-convex function `K`" is
proved by producing this `F` and quoting a backbone theorem about `Ω (F)`. Properness of `K` is
*not* needed here — the constant functions `±∞` are closed saddle-functions too — but properness of
the graph function of `F` is exactly `ProperSaddleFn K`
(`proper_graphFn_of_properSaddleFn`). -/
theorem exists_mem_Ω_of_closed {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K)
    (hcl : ClosedSaddleFn K) :
    ∃ F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧ K ∈ Ω F := by
  obtain ⟨F, ⟨hFconv, hFcl, hlow, hup⟩, -⟩ := theorem_34_2_converse hK hcl
  exact ⟨F, hFconv, hFcl, theorem_34_2_mem_self hK hlow hup⟩

end Defs

/-! ### Theorem 37.1 -/

section Thm371

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.1**, first equation (15737): for a closed convex bifunction `F` and
any `K ∈ Ω (F)`,

`inf_u sup_x* {⟨u, u*⟩ + ⟨x, x*⟩ − K (u, x*)} = ⟨u*, F_* x⟩`.

Specialises `upperConjSaddle_eq_saddleLagrangian` composed with §36's
`saddleLagrangian_eq_inverseBifunBracket`: the upper conjugate *is* the Lagrangian, and the
Lagrangian is the concave bracket of the inverse bifunction. -/
theorem theorem_37_1_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    upperConj K = inverseBifunBracket F :=
  (upperConjSaddle_eq_saddleLagrangian (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)).trans (saddleLagrangian_eq_inverseBifunBracket F)

/-- **Rockafellar, Theorem 37.1**, second equation (15739): for the same `F` and `K`,

`sup_x* inf_u {⟨u, u*⟩ + ⟨x, x*⟩ − K (u, x*)} = ⟨F_*^* u*, x⟩`.

Specialises `lowerConjSaddle_eq_bracket_inverseBifun`. `F_*^*` is `inverseBifun (dualProgram F)`,
the bifunction of the conjugate class. -/
theorem theorem_37_1_lower (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    lowerConj K = bifunBracket (inverseBifun (dualProgram F)) := by
  have h := lowerConjSaddle_eq_bracket_inverseBifun (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK)
  simp only [flip_pairing] at h
  exact h

/-- The class conjugate to `Ω (F)` is `Ω (F_*^*)`, and it is a class of the same kind: `F_*^*` is a
closed convex bifunction from `ℝᵐ` to `ℝⁿ`. -/
theorem convexBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ConvexBifun (inverseBifun (dualProgram F)) :=
  convexBifun_inverseBifun_adjointBifun (pairing m) (pairing n) F

/-- The companion of `convexBifun_conjBifun`: `F_*^*` is closed. -/
theorem closedBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ClosedBifun (inverseBifun (dualProgram F)) :=
  closedBifun_inverseBifun_adjointBifun (pairing m) (pairing n) F

/-- `(F_*^*)_* = F^*`: the inverse operation is an involution, so the adjoint bifunction of the
conjugate class is the adjoint of `F` again. -/
theorem inverseBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun (dualProgram F)) = dualProgram F :=
  inverseBifun_inverseBifun _

/-- **The biadjoint identity `(F_*^*)^* = F_*`** (the book's remark before Corollary 37.1.2, 15791)
for a closed convex bifunction. Specialises `adjointBifun_flip_inverseBifun_adjointBifun`. -/
theorem dualProgram_conjBifun (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    dualProgram (inverseBifun (dualProgram F)) = inverseBifun F := by
  have h := adjointBifun_flip_inverseBifun_adjointBifun (pairing m) (pairing n) hF hcl
  simpa only [flip_pairing] using h

/-- **Rockafellar, Theorem 37.1**, third equation (15745): for any `K* ∈ Ω (F_*)` — that is, any
concave-convex function with `⟨F_*^* u*, x⟩ ≤ K* (u*, x) ≤ ⟨u*, F_* x⟩` —

`inf_u* sup_x {⟨u, u*⟩ + ⟨x, x*⟩ − K* (u*, x)} = ⟨u, F* x*⟩`.

This is the first equation applied to the closed convex bifunction `F_*^*`, whose inverse is `F^*`
by `inverseBifun_conjBifun`. -/
theorem theorem_37_1_conj_upper (F : Bifun (Rn m) (Rn n))
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : upperConj L = adjointBracket F := by
  have h := theorem_37_1_upper (convexBifun_conjBifun F) (closedBifun_conjBifun F) hL
  have h2 : inverseBifunBracket (inverseBifun (dualProgram F)) = adjointBracket F := by
    change concaveBifunBracket (inverseBifun (inverseBifun (dualProgram F))) = adjointBracket F
    rw [inverseBifun_conjBifun]
  exact h.trans h2

/-- **Rockafellar, Theorem 37.1**, fourth equation (15747): for the same `K* ∈ Ω (F_*)`,

`sup_x inf_u* {⟨u, u*⟩ + ⟨x, x*⟩ − K* (u*, x)} = ⟨Fu, x*⟩`.

The second equation applied to `F_*^*`, using the biadjoint identity `(F_*^*)^* = F_*` — this is
where closedness of `F` is spent. -/
theorem theorem_37_1_conj_lower (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : lowerConj L = bifunBracket F := by
  have h := theorem_37_1_lower (convexBifun_conjBifun F) hL
  rw [dualProgram_conjBifun hF hcl, inverseBifun_inverseBifun] at h
  exact h

end Thm371

/-! ### Corollary 37.1.1 -/

section Cor3711

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- The upper conjugate of a member of `Ω (F)` lies in the conjugate class `Ω (F_*^*)`. This is the
membership every "the conjugates of `K*` …" statement runs on. -/
theorem upperConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    upperConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (inverseBifun (adjointBifun (pairing m) (pairing n) F)) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_right (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simpa only [flip_pairing] using hmem
  exact hmem'

/-- The lower conjugate of a member of `Ω (F)` lies in the conjugate class `Ω (F_*^*)` as well. -/
theorem lowerConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    lowerConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (inverseBifun (adjointBifun (pairing m) (pairing n) F)) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_left (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simpa only [flip_pairing] using hmem
  exact hmem'

/-- **Rockafellar, Corollary 37.1.1**: `K̲*` is a concave-convex function. -/
theorem corollary_37_1_1_lower_concaveConvex (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    ConcaveConvexFn (lowerConj K) :=
  concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**: `K̲*` is **lower closed** — `cl₂ cl₁ K̲* = K̲*`. This is
Theorem 33.3 applied to `F_*^*`. -/
theorem corollary_37_1_1_lower_lowerClosed (hF : ConvexBifun F) (_hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : LowerClosedFn (lowerConj K) :=
  lowerClosedFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**: `K̄*` is a concave-convex function. -/
theorem corollary_37_1_1_upper_concaveConvex (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : ConcaveConvexFn (upperConj K) :=
  concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**: `K̄*` is **upper closed** — `cl₁ cl₂ K̄* = K̄*`. -/
theorem corollary_37_1_1_upper_upperClosed (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : UpperClosedFn (upperConj K) :=
  upperClosedFn_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**: `K̲*` and `K̄*` are **equivalent** saddle-functions, so by
Theorem 36.4 they have the same iterated extrema and the same saddle-points. -/
theorem corollary_37_1_1_equiv (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj K) (upperConj K) :=
  saddleEquiv_lowerConjSaddle_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**: both conjugates are closed saddle-functions — they are the
two ends of the closure pair of `Ω (F_*^*)`. -/
theorem corollary_37_1_1_closed_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn (lowerConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedBifun_conjBifun F)
    (lowerConj_mem_Ω hF hcl hK)

/-- **Rockafellar, Corollary 37.1.1**: the upper conjugate is a closed saddle-function. -/
theorem corollary_37_1_1_closed_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn (upperConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedBifun_conjBifun F)
    (upperConj_mem_Ω hF hcl hK)

/-- **Rockafellar, Corollary 37.1.1**: the lower conjugate **depends only on the equivalence
class** — two members of `Ω (F)` have the same lower conjugate, on the nose. -/
theorem corollary_37_1_1_lower_class (hF : ConvexBifun F) (hK : K ∈ Ω F) (hL : L ∈ Ω F) :
    lowerConj K = lowerConj L :=
  (theorem_37_1_lower hF hK).trans (theorem_37_1_lower hF hL).symm

/-- **Rockafellar, Corollary 37.1.1**: and so does the upper conjugate. -/
theorem corollary_37_1_1_upper_class (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : upperConj K = upperConj L :=
  (theorem_37_1_upper hF hcl hK).trans (theorem_37_1_upper hF hcl hL).symm

/-- **Rockafellar, §37**, the remark after Corollary 37.1.1 (15789): a saddle-function conjugate to
a closed **proper** saddle-function is proper — the only improper closed saddle-functions are the
constants `±∞`, and those are conjugate to each other. Specialises
`properSaddleFn_upperConjSaddle`. -/
theorem corollary_37_1_1_proper_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (upperConj K) :=
  properSaddleFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, §37**, the same for the lower conjugate. -/
theorem corollary_37_1_1_proper_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (lowerConj K) :=
  properSaddleFn_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.1**, last sentence: the conjugacy correspondence is involutive up
to equivalence — the **lower** conjugate of a conjugate `K*` of `K` is equivalent to `K`.

`lowerConj (upperConj K)` is `⟨Fu, x*⟩`, the lower end of `Ω (F)`, and every member of `Ω (F)` is
equivalent to it (Theorem 34.2). -/
theorem corollary_37_1_1_biconj_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj (upperConj K)) K := by
  rw [theorem_37_1_conj_lower hF hcl (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_lower_mem hF hcl) hK

/-- **Rockafellar, Corollary 37.1.1**, last sentence: and so is the **upper** conjugate of `K*`.
`upperConj (upperConj K)` is `⟨u, F*x*⟩`, the upper end of `Ω (F)`. -/
theorem corollary_37_1_1_biconj_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (upperConj (upperConj K)) K := by
  rw [theorem_37_1_conj_upper F (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_upper_mem hF hcl) hK

end Cor3711

/-! ### Corollary 37.1.2 -/

section Cor3712

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 37.1.2**, first equation: `cl₁ K̲* = K̄*`. Specialises
`partialCl₁_lowerConjSaddle`. -/
theorem corollary_37_1_2_cl₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₁ (lowerConj K) = upperConj K :=
  partialCl₁_lowerConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.2**, second equation: `cl₂ K̄* = K̲*`. -/
theorem corollary_37_1_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₂ (upperConj K) = lowerConj K :=
  partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.2**: `C* × D*` is the effective domain of **both** conjugates. -/
theorem corollary_37_1_2_dom (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : domSaddle (lowerConj K) = domSaddle (upperConj K) :=
  domSaddle_conjSaddle_eq (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.1.2**, first sentence: the conjugates of a closed proper
saddle-function have the **structural properties of Theorem 34.3** with respect to the non-empty
convex product set `C* × D*`. Read off from Theorem 34.3 through `corollary_37_1_1_closed_upper`
and `corollary_37_1_1_proper_upper`. -/
theorem corollary_37_1_2_structure (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : SaddleStructure (upperConj K) :=
  (theorem_34_3 (corollary_37_1_1_upper_concaveConvex hF hcl hK)
    (corollary_37_1_1_proper_upper hF hcl hK hp)).1 (corollary_37_1_1_closed_upper hF hcl hK)

/-- **Rockafellar, Corollary 37.1.2**, last clause: `K̲* (u*, v*) = K̄* (u*, v*)` whenever
`u* ∈ ri C*`. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (dom₁ (lowerConj K)))
    (v : Rn n) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hu v

/-- **Rockafellar, Corollary 37.1.2**, last clause: and whenever `v* ∈ ri D*`. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {v : Rn n} (hv : v ∈ ri (dom₂ (lowerConj K)))
    (u : Rn m) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hv u

end Cor3712

/-! ### The saddle-value read at the origin (15833–15849), and Corollary 37.1.3 -/

section Cor3713

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, §37** (15839): `inf_v sup_u K (u, v) = −K̲* (0, 0)`. No hypotheses. -/
theorem minimax_eq_neg_lowerConj_zero (K : Rn m × Rn n → EReal) :
    minimax K = -(lowerConj K 0) :=
  minimax_eq_neg_lowerConjSaddle_zero (pairing m) (pairing n) K

/-- **Rockafellar, §37** (15841): `sup_u inf_v K (u, v) = −K̄* (0, 0)`. No hypotheses. -/
theorem maximin_eq_neg_upperConj_zero (K : Rn m × Rn n → EReal) :
    maximin K = -(upperConj K 0) :=
  maximin_eq_neg_upperConjSaddle_zero (pairing m) (pairing n) K

/-- **Rockafellar, Corollary 37.1.3** (15851, **printed with no proof**): if the origin of `ℝᵐ`
lies in `ri C*`, then `inf_v sup_u K = sup_u inf_v K`.

By the two displays above, the saddle-value exists exactly when the two conjugates agree at the
origin, and Corollary 37.1.2's last clause makes them agree throughout `ri C* × ℝⁿ`. Specialises
`hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle`. -/
theorem corollary_37_1_3_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Rockafellar, Corollary 37.1.3**: the same when the origin of `ℝⁿ` lies in `ri D*`. -/
theorem corollary_37_1_3_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Rockafellar, Corollary 37.1.3**, last sentence: if **both** conditions hold, the saddle-value
is finite. Specialises `exists_maximin_eq_coe_of_mem_relint_domSaddle`. -/
theorem corollary_37_1_3_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)))
    (h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_mem_relint_domSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h1 h2

end Cor3713

/-! ### Theorem 37.2 and Corollary 37.2.1 -/

section Thm372

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.2**, the `D*` formula (15869): for a closed proper concave-convex `K`
with effective domain `C × D`,

`δ*(w | D*) = sup_{u ∈ ri C} sup_{v ∈ D} {K (u, v + w) − K (u, v)}`.

Specialises `supportFn_dom₂_upperConjSaddle`. The `C*` formula is **not** carried; see the module
docstring under `## What is not here`. -/
theorem theorem_37_2_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), ⨆ v ∈ dom₂ K, (K (u, v + w) - K (u, v)) :=
  supportFn_dom₂_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Rockafellar, Theorem 37.2**, the `D*` formula in recession-function form: `δ*(· | D*)` is the
pointwise supremum over `u ∈ ri C` of the recession functions of the convex slices `K (u, ·)`.
This is the shape Corollary 37.2.1 consumes (Theorem 8.5). -/
theorem theorem_37_2_dom₂_recessionFn (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), recessionFn (fun v => K (u, v)) w :=
  supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Rockafellar, Corollary 37.2.1**, first half: `0 ∈ int D*` if and only if the convex functions
`K (u, ·)`, `u ∈ ri C`, have **no common direction of recession**. Specialises
`zero_mem_interior_dom₂_upperConjSaddle_iff`; `separatingRight_pairing` discharges the
`SeparatingRight` hypothesis, which on a self-paired space is automatic. -/
theorem corollary_37_2_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn n) ∈ interior (dom₂ (upperConj K)) ↔
      ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w :=
  zero_mem_interior_dom₂_upperConjSaddle_iff (pairing m) (pairing n) (separatingRight_pairing n)
    hF hcl (proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
      (mem_bifunSaddleClass_of_mem_Ω hK) hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1
    hp.dom₂_nonempty ((theorem_34_3 hK.1 hp).1 hcls).1

/-- **Rockafellar, Corollary 37.2.1**, second half: `0 ∈ int C*` if and only if the convex
functions `−K (·, v)`, `v ∈ ri D`, have no common direction of recession. Specialises
`zero_mem_interior_dom₁_lowerConjSaddle_iff`, the `saddleSwap` reading of the first half. -/
theorem corollary_37_2_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn m) ∈ interior (dom₁ (lowerConj K)) ↔
      ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z :=
  zero_mem_interior_dom₁_lowerConjSaddle_iff (pairing m) (pairing n) (separatingLeft_pairing m)
    hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls)

end Thm372

/-! ### Theorem 37.3 and its two corollaries -/

section Thm373

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.3 (a)** (15931): if the convex functions `K (u, ·)` for `u ∈ ri C`
have no common direction of recession, the saddle-value of `K` exists.

Combines Corollaries 37.1.3 and 37.2.1, exactly as the book's one-line proof says. Specialises
`hasSaddleValue_of_no_common_direction_of_recession`. -/
theorem theorem_37_3_a (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession (pairing m) (pairing n)
    (separatingRight_pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 hrec

/-- **Rockafellar, Theorem 37.3 (b)** (15933): if the convex functions `−K (·, v)` for `v ∈ ri D`
have no common direction of recession, the saddle-value of `K` exists. Specialises
`hasSaddleValue_of_no_common_direction_of_recession_neg`. -/
theorem theorem_37_3_b (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_neg (pairing m) (pairing n)
    (separatingLeft_pairing m) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hrec

/-- **Rockafellar, Theorem 37.3**, last sentence: if **both** conditions hold, the saddle-value is
finite. Corollary 37.2.1 turns them into `0 ∈ int C*` and `0 ∈ int D*`, hence into membership of
the two relative interiors, and Corollary 37.1.3's last clause concludes. -/
theorem theorem_37_3_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  have hpr := proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
    (mem_bifunSaddleClass_of_mem_Ω hK) hp
  have h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)) :=
    interior_subset_intrinsicInterior ((corollary_37_2_1_dom₁ hF hcl hK hp hcls).2 hrec₁)
  have h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K)) := by
    rw [dom₂_conjSaddle_eq (pairing m) (pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact interior_subset_intrinsicInterior ((corollary_37_2_1_dom₂ hF hcl hK hp hcls).2 hrec₂)
  exact corollary_37_1_3_finite hF hcl hK hp h1 h2

/-- **Rockafellar, Corollary 37.3.1**, the half where `D` is bounded: the effective domain of
`K (u, ·)` is `D` for every `u ∈ ri C` (Theorem 34.3), so a bounded `D` fulfils condition (a).
Specialises `hasSaddleValue_of_isBounded_dom₂`. -/
theorem corollary_37_3_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₂ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₂ (pairing m) (pairing n) (separatingRight_pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty hp.dom₁_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 hbd

/-- **Rockafellar, Corollary 37.3.1**, the half where `C` is bounded: condition (b) is fulfilled.
Specialises `hasSaddleValue_of_isBounded_dom₁`. -/
theorem corollary_37_3_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₁ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁ (pairing m) (pairing n) (separatingLeft_pairing m) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hbd

end Thm373

/-! ### Corollary 37.3.2: the minimax theorem for a finite continuous saddle-function -/

section Cor3732

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Rockafellar, Corollary 37.3.2** (15943): for non-empty closed convex `C ⊆ ℝᵐ`, `D ⊆ ℝⁿ` and
a continuous finite concave-convex `K` on `C × D`, if `D` is **bounded** then

`inf_{v ∈ D} sup_{u ∈ C} K (u, v) = sup_{u ∈ C} inf_{v ∈ D} K (u, v)`.

Specialises `biSup_biInf_eq_biInf_biSup_of_isBounded_right`, which applies Corollary 37.3.1 to the
lower simple extension of `K` (a closed proper concave-convex function with effective domain
`C × D`, by Corollary 34.2.4) and reads the two extrema back by Theorem 36.3.

**Two divergences.** (i) This is Rockafellar's finite-dimensional minimax theorem; its
infinite-dimensional analogues (Kneser–Fan, Sion) require **compactness** of `D`, not boundedness,
and the two coincide here only by Heine–Borel. (ii) The extrema are stated in `EReal`: with only
`D` bounded both can be infinite (`C = {0}`, `D = ℝ`, `K (u, v) = v`), so the book's implicit
finiteness is not available. Continuity and convexity are asked slice by slice, which is what the
proof uses. -/
theorem corollary_37_3_2_right (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_right (pairing m) (pairing n)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbd

/-- **Rockafellar, Corollary 37.3.2**, the half where `C` is bounded. Same divergences as
`corollary_37_3_2_right`. -/
theorem corollary_37_3_2_left (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_left (pairing m) (pairing n)
    (separatingLeft_pairing m) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbd

end Cor3732

/-! ### Theorem 37.4: subgradients are saddle-points of the tilted function -/

section Thm374

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.4**, first sentence (15963): `(u*, v*) ∈ ∂K (u, v)` exactly when
`(u, v)` is a saddle-point of the tilted function `K − ⟨·, u*⟩ − ⟨·, v*⟩`.

That tilt is the backbone's `saddleTilt (pairing m) (pairing n) K (u*, v*)`, whose value at `(u, v)`
is `K (u, v) − (⟨u, u*⟩ + ⟨v, v*⟩)` (`saddleTilt_apply`); the two inner products are combined into
one real coercion so that no `∞ − ∞` can arise. Specialises
`mem_saddleSubgradient_iff_isSaddlePoint`, which has **no hypotheses at all** — not concavity, not
convexity, not properness. -/
theorem theorem_37_4 (K : Rn m × Rn n → EReal) (p q : Rn m × Rn n) :
    q ∈ subgrad K p ↔ IsSaddlePoint (saddleTilt (pairing m) (pairing n) K q) p :=
  mem_saddleSubgradient_iff_isSaddlePoint

/-- **Rockafellar, §37** (15949): `∂K (u, v)` is a **convex** set, with no hypothesis on `K` — it
is the product `∂₁K (u, v) × ∂₂K (u, v)` of two convex sets. -/
theorem theorem_37_4_convex (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    Convex ℝ (subgrad K p) := convex_saddleSubgradient

private theorem isClosed_subgrad₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subgrad₁ K p) := by
  have h : subgrad₁ K p
      = (fun y : Rn m => -y) ⁻¹' subgradient (pairing m) (fun u => -(K (u, p.2))) p.1 := by
    ext y
    exact mem_subgrad₁_iff_neg_mem_subgradient_neg
  rw [h]
  exact (isClosed_subgradient _ _).preimage continuous_neg

/-- **Rockafellar, §37** (15949): `∂K (u, v)` is a **closed** set. The convex half is
`convex_saddleSubgradient`; the closed half has no backbone counterpart for the concave factor
(`isClosed_concaveSubgradient` does not exist), so it is assembled here from the sign dictionary
`mem_subgrad₁_iff_neg_mem_subgradient_neg` of §35 and `isClosed_subgradient`. -/
theorem theorem_37_4_isClosed (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subgrad K p) :=
  (isClosed_subgrad₁ K p).prod (isClosed_subgradient _ _)

/-- **Rockafellar, Theorem 37.4**, left-hand inclusion: `ri (dom K) ⊆ dom ∂K` for a closed proper
concave-convex function. Over `ri C` the convex slice `K (u, ·)` is proper with effective domain
`D` (Theorem 34.3), so Theorem 23.4 produces a subgradient; the concave half is the same statement
for `saddleSwap K`. Specialises `kernelSet_subset_domSaddleSubgradient`. -/
theorem theorem_37_4_relint (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) : ri (domSaddle K) ⊆ domSubgrad K := by
  have h := kernelSet_subset_domSaddleSubgradient (Bu := pairing m) (Bx := pairing n) hK
    ((theorem_34_3 hK hp).1 hcl)
  rwa [kernelSet_eq_relint_domSaddle] at h

/-- **Rockafellar, Theorem 37.4**, right-hand inclusion: `dom ∂K ⊆ dom K`. Only **properness** is
used — a subgradient pair at `p` makes `p` a saddle-point of the tilt, the tilt is again proper,
and the saddle-points of a proper saddle-function lie in its effective domain (Corollary 36.3.1).
Specialises `domSaddleSubgradient_subset_domSaddle`. -/
theorem theorem_37_4_dom (hp : ProperSaddleFn K) : domSubgrad K ⊆ domSaddle K :=
  domSaddleSubgradient_subset_domSaddle hp

end Thm374

/-! ### Corollary 37.4.1 -/

section Cor3741

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 37.4.1** (15993): equivalent saddle-functions have the same
subdifferential, `∂K = ∂L`. So one may speak of the subdifferential of an *equivalence class*.

**Divergence from the book's proof.** Rockafellar tilts both functions by `(u*, v*)`, observes that
the tilts are equivalent, and appeals to Theorem 36.4. That route needs `cl₁ (K − ℓ) = cl₁ K − ℓ`
for a linear `ℓ`, which the backbone does not have. The route taken here is Theorem 37.5's
(a) ⇔ (d): `∂K` *is* the relation `IsBifunSubgradientPair F` attached to the class, and by
Theorem 34.2 an equivalent concave-convex function belongs to the same class
(`theorem_34_2_maximal`). The price is the closedness hypothesis, which the book's statement does
not carry. -/
theorem corollary_37_4_1_subgrad (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : subgrad K = subgrad L := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  have hpair : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → ∀ p q : Rn m × Rn n,
      (q ∈ subgrad M p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q) := by
    intro M hM p q
    have hb := mem_saddleSubgradient_iff_isBifunSubgradientPair (pairing m) (pairing n) hFconv
      hFcl (mem_bifunSaddleClass_of_mem_Ω hM) p q
    simpa only [flip_pairing] using hb
  funext p
  ext q
  exact (hpair K hKmem p q).trans (hpair L hLmem p q).symm

/-- **Rockafellar, Corollary 37.4.1**, second sentence: equivalent saddle-functions moreover
**agree in value** on `dom ∂K = dom ∂L`.

A subgradient pair at `p` says that the conjugate of the convex slice is attained
(`mem_subgradient_iff_conj_eq`), and that conjugate is `F p.1` for every member of the class
(`bifunOfSaddle_eq_of_mem_bifunSaddleClass`); so both `K p` and `L p` equal the same
`⟨v, v*⟩ − (F u)(v*)`. -/
theorem corollary_37_4_1_eq (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) {p : Rn m × Rn n} (hp : p ∈ domSubgrad K) :
    K p = L p := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  obtain ⟨q, hq⟩ := hp
  have hqL : q ∈ subgrad L p := by
    rw [← corollary_37_4_1_subgrad hK hcl hL h]
    exact hq
  have key : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → q ∈ subgrad M p →
      ((pairing n p.2 q.2 : ℝ) : EReal) - F p.1 q.2 = M p := by
    intro M hM hqM
    have hA : conj (pairing n).flip (fun v => M (p.1, v)) = F p.1 :=
      congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hFconv hFcl
        (mem_bifunSaddleClass_of_mem_Ω hM)) p.1
    rw [conj_flip_pairing] at hA
    have hsub : conj (pairing n) (fun v => M (p.1, v)) q.2
        = ((pairing n p.2 q.2 : ℝ) : EReal) - M (p.1, p.2) :=
      mem_subgradient_iff_conj_eq.1 hqM.2
    rw [hA] at hsub
    exact eq_coe_sub_iff_coe_sub_eq.1 hsub
  exact (key K hKmem hq).symm.trans (key L hLmem hqL)

end Cor3741

/-! ### Theorem 37.5 -/

section Thm375

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.5**, the definition of `f` (16015): the graph function of the `F` of
Theorem 34.2 is `f (u, v*) = sup_v {⟨v, v*⟩ − K (u, v)}`, the conjugate of the convex slice
`K (u, ·)`.

`f` is a closed proper convex function on `ℝᵐ⁺ⁿ`, read here as a function on `ℝᵐ × ℝⁿ`; the two
readings are identified by `pairingProd_euclideanProdEquiv`. -/
theorem theorem_37_5_f (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) (u : Rn m)
    (w : Rn n) : graphFn F (u, w) = ⨆ v : Rn n, (((pairing n v w : ℝ) : EReal) - K (u, v)) := by
  have hA : conj (pairing n).flip (fun v => K (u, v)) = F u :=
    congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK)) u
  rw [conj_flip_pairing] at hA
  have hg : graphFn F (u, w) = F u w := rfl
  rw [hg, ← hA, conj_apply]

/-- **Rockafellar, Theorem 37.5 (a)** (16019), read against condition (d): `(u*, v*) ∈ ∂K (u, v)`
holds exactly when the pair satisfies the class-level condition `IsBifunSubgradientPair`, i.e.
`(Fu)(v*) − ⟨v, v*⟩ = (F*v)(u*) − ⟨u, u*⟩`.

Because the right-hand side mentions only `F`, this *is* the statement that `∂K` depends only on
the equivalence class. Specialises `mem_saddleSubgradient_iff_isBifunSubgradientPair`. -/
theorem theorem_37_5_a (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    q ∈ subgrad K p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubgradient_iff_isBifunSubgradientPair (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Rockafellar, Theorem 37.5 (b)** (16021), read against condition (d):
`(u, v) ∈ ∂K* (u*, v*)`, where `K*` is a conjugate of `K` — here the canonical upper one.

With (a) this says that the subdifferentials of conjugate equivalence classes are **inverse to each
other** as multivalued mappings, exactly as `∂(f*) = (∂f)⁻¹` for convex functions (Corollary
23.5.1). Specialises `mem_saddleSubgradient_upperConjSaddle_iff`. -/
theorem theorem_37_5_b (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    p ∈ subgrad (upperConj K) q ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubgradient_upperConjSaddle_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Rockafellar, Theorem 37.5 (c)** (16023), read against condition (d):
`(−u*, v) ∈ ∂f (u, v*)`, where `f` is the graph function of `F`.

**The sign and the exchange are both real.** `∂K` is the **partial inversion** of `∂f`: the second
components of point and gradient are swapped, and the first component of the gradient is negated.
That is what makes every geometric fact about `∂f` — closedness, the Minty parametrisation,
maximal monotonicity — transfer to `∂K`, and it is the source of the asymmetry in Corollaries
37.5.1 and 37.5.2. Specialises `isBifunSubgradientPair_iff_mem_subgradient_graphFn`; it needs no
hypothesis on `F` at all. -/
theorem theorem_37_5_c (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      (-q.1, p.2) ∈ subgradient (pairingProd m n) (graphFn F) (p.1, q.2) :=
  isBifunSubgradientPair_iff_mem_subgradient_graphFn (pairing m) (pairing n) F p q

/-- **Rockafellar, Theorem 37.5 (d)** (16025): the condition

`(Fu)(v*) − ⟨v, v*⟩ = (F*v)(u*) − ⟨u, u*⟩`,

the equality case of the chain
`⟨v, v*⟩ − (Fu)(v*) ≤ ⟨Fu, v⟩ ≤ K (u, v) ≤ ⟨u, F*v⟩ ≤ ⟨u, u*⟩ − (F*v)(u*)`. It mentions no
representative of the class, which is why the backbone names it and states (a), (b) and (c)
against it. -/
theorem theorem_37_5_d (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      F p.1 q.2 - ((pairing n q.2 p.2 : ℝ) : EReal)
        = dualProgram F p.2 q.1 - ((pairing m p.1 q.1 : ℝ) : EReal) := Iff.rfl

end Thm375

/-! ### Corollaries 37.5.1 and 37.5.2 -/

section Cor3751

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

private theorem continuous_pairing (n : ℕ) :
    Continuous fun r : Rn n × Rn n => pairing n r.1 r.2 := continuous_inner

/-- **Rockafellar, Corollary 37.5.1**, closedness clause (16093): the graph of `∂K` is closed.

Theorem 37.5 (c) identifies that graph with the preimage of the graph of `∂f` under the linear
homeomorphism `(u, v, u*, v*) ↦ ((u, v*), (−u*, v))`, and Theorem 24.4 says the graph of `∂f` is
closed. Specialises `isClosed_setOf_mem_saddleSubgradient`. -/
theorem corollary_37_5_1_isClosed (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F) :
    IsClosed {r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} := by
  have h := isClosed_setOf_mem_saddleSubgradient (pairing m) (pairing n) (continuous_pairing m)
    (continuous_pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Rockafellar, Corollary 37.5.1**, homeomorphism clause (16097): the graph of `∂K` is
homeomorphic to `ℝᵐ × ℝⁿ` under

`(u, v, u*, v*) ↦ (u − u*, v + v*)`.

**The map is asymmetric, and deliberately so.** It is Corollary 31.5.1's Minty parametrisation
`(z, z*) ↦ z + z*` composed with the partial inversion of Theorem 37.5 (c), whose sign sits on the
first dual component; a symmetric `(u + u*, v + v*)` is *not* a homeomorphism here. Specialises
`saddleSubgradientHomeomorph` at `prodPairing (innerₗ (Rn m)) (innerₗ (Rn n))`.

The book's `K` is a closed proper saddle-function; `F` is then unique by Theorem 34.2 but is
produced by an existential, and a `Homeomorph` is data, so `F` is an explicit argument here.
`corollary_37_5_1_exists_homeomorph` is the book's own form. -/
noncomputable def corollary_37_5_1_homeomorph (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F) :
    ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} ≃ₜ (Rn m × Rn n) :=
  saddleSubgradientHomeomorph hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.5.1**: the homeomorphism is the book's map `(u − u*, v + v*)`,
with the two summands of the second component in the other order. -/
theorem corollary_37_5_1_homeomorph_apply (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F)
    (r : ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1}) :
    corollary_37_5_1_homeomorph hF hcl hpr hK r = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) :=
  saddleSubgradientHomeomorph_apply hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) r

/-- **Rockafellar, Corollary 37.5.1** in the book's own quantification: for a closed proper
concave-convex `K` the graph of `∂K` is homeomorphic to `ℝᵐ × ℝⁿ`. The bifunction is recovered by
Theorem 34.2 (`exists_mem_Ω_of_closed`). -/
theorem corollary_37_5_1_exists_homeomorph (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    Nonempty (↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} ≃ₜ (Rn m × Rn n)) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_mem_Ω_of_closed hK hcl
  exact ⟨corollary_37_5_1_homeomorph hFconv hFcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
      (mem_bifunSaddleClass_of_mem_Ω hmem) hp) hmem⟩

/-- **Rockafellar, Corollary 37.5.2** (16101): the mapping

`ρ : (u, v) ↦ {(−u*, v*) | (u*, v*) ∈ ∂K (u, v)}`

is a **maximal monotone** mapping from `ℝᵐ × ℝⁿ` to `ℝᵐ × ℝⁿ`.

**The `u* ↦ −u*` is inserted, not derived.** `∂K = ∂₁K × ∂₂K` carries a *super*differential in the
first argument and a subdifferential in the second (§35,
`mem_subgrad₁_iff_neg_mem_subgradient_neg`), so `∂K` itself is monotone in one variable and
antitone in the other; negating the first dual component is exactly what repairs it, and it is the
same sign as Theorem 37.5 (c). Specialises `isMaximalMonotoneRel_saddleMonotoneRel`, which is
Corollary 31.5.2 at `prodPairing (innerₗ (Rn m)) (innerₗ (Rn n))`. -/
theorem corollary_37_5_2 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hK : K ∈ Ω F) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subgrad K r.1} := by
  have h := isMaximalMonotoneRel_saddleMonotoneRel hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  have he : saddleMonotoneRel (pairing m) (pairing n) K
      = {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subgrad K r.1} := by
    ext r
    simp only [mem_saddleMonotoneRel, flip_pairing, Set.mem_ofPred_eq]
  rwa [he] at h

/-- **Rockafellar, Corollary 37.5.2**, "in particular" clause: if `K` is everywhere finite and
differentiable, `(u, v) ↦ (−∇₁K (u, v), ∇₂K (u, v))` is maximal monotone.

Theorem 35.8 collapses `∂K` to the single point `(∇₁K, ∇₂K)`, and over the whole space §35's
real-valued `subgradientSaddle` and §37's `EReal`-valued `saddleSubgradient` are the same set
(`saddleSubgradient_eq_subgradientSaddle`). The gradient is a **pair**, not a vector of `ℝᵐ⁺ⁿ`,
because Mathlib gives a product of inner-product spaces the supremum norm; that is what
`HasSaddleGradientAt` records. Specialises `isMaximalMonotoneRel_setOf_hasSaddleGradientAt`. -/
theorem corollary_37_5_2_gradient {K : Rn m × Rn n → ℝ}
    (hK : ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K)
    (hdiff : ∀ p : Rn m × Rn n, DifferentiableAt ℝ K p) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} :=
  isMaximalMonotoneRel_setOf_hasSaddleGradientAt hK hdiff

end Cor3751

/-! ### Corollary 37.5.3 -/

section Cor3753

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 37.5.3** (16131): `∂K* (0, 0)` **is** the set of saddle-points of `K`.

Theorem 37.5 (b) at `(u*, v*) = (0, 0)` composed with Theorem 37.4, whose tilt by the origin is
`K` itself. Specialises `mem_saddleSubgradient_upperConjSaddle_zero_iff`. -/
theorem corollary_37_5_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p : Rn m × Rn n) : p ∈ subgrad (upperConj K) 0 ↔ IsSaddlePoint K p := by
  have h := mem_saddleSubgradient_upperConjSaddle_zero_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p
  simpa only [flip_pairing] using h

/-- **Rockafellar, Corollary 37.5.3**, second sentence: the saddle-points of `K` form a **convex
product set** — they are a value of a subdifferential, and `∂K* = ∂₁K* × ∂₂K*`. -/
theorem corollary_37_5_3_convex (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    Convex ℝ {p : Rn m × Rn n | IsSaddlePoint K p} :=
  convex_setOf_isSaddlePoint (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Rockafellar, Corollary 37.5.3**, second sentence: and they form a **closed** set. -/
theorem corollary_37_5_3_isClosed (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    IsClosed {p : Rn m × Rn n | IsSaddlePoint K p} := by
  have hset : {p : Rn m × Rn n | IsSaddlePoint K p} = subgrad (upperConj K) 0 := by
    ext p
    exact (corollary_37_5_3 hF hcl hK p).symm
  rw [hset]
  exact theorem_37_4_isClosed _ _

/-- **Rockafellar, Corollary 37.5.3**, last sentence: a saddle-point exists **if and only if**
`(0, 0) ∈ dom ∂K*`. Specialises `exists_isSaddlePoint_iff_zero_mem_domSaddleSubgradient`. -/
theorem corollary_37_5_3_exists_iff (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    (∃ p, IsSaddlePoint K p) ↔ (0 : Rn m × Rn n) ∈ domSubgrad (upperConj K) := by
  have h := exists_isSaddlePoint_iff_zero_mem_domSaddleSubgradient (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Rockafellar, Corollary 37.5.3**, "in particular": `K` has a saddle-point as soon as
`(0, 0) ∈ ri (dom K*)`, by Theorem 37.4 applied to `K*`. Specialises
`exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle`. -/
theorem corollary_37_5_3_exists_of_relint (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F)
    (h0 : (0 : Rn m × Rn n) ∈ ri (domSaddle (upperConj K))) : ∃ p, IsSaddlePoint K p := by
  refine exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle (pairing m) (pairing n) hF
    hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) ?_
  rwa [← kernelSet_eq_relint_domSaddle] at h0

end Cor3753

/-! ### Theorem 37.6 and its two corollaries -/

section Thm376

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 37.6** (16151): if conditions (a) **and** (b) of Theorem 37.3 both
hold, `K` has a saddle-point.

Corollary 37.2.1 turns the two recession conditions into `0 ∈ int C*` and `0 ∈ int D*`, hence
`(0, 0) ∈ ri (dom K*)`, and Corollary 37.5.3 produces the point. Specialises
`exists_isSaddlePoint_of_no_common_direction_of_recession`. -/
theorem theorem_37_6 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_no_common_direction_of_recession (pairing m) (pairing n)
    (separatingLeft_pairing m) (separatingRight_pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hrec₂ hrec₁

/-- **Rockafellar, Theorem 37.6**, parenthesis: a saddle-point of a proper saddle-function
necessarily lies in `C × D = dom K` (Corollary 36.3.1). -/
theorem theorem_37_6_mem_dom (hp : ProperSaddleFn K) {q : Rn m × Rn n} (hq : IsSaddlePoint K q) :
    q ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp hq

/-- **Rockafellar, Corollary 37.6.1** (16155): if `C` **and** `D` are bounded, `K` has a
saddle-point. Both conditions of Theorem 37.3 hold, because the slices over the relative interiors
have effective domains exactly `D` and `C` (Theorem 34.3). Specialises
`exists_isSaddlePoint_of_isBounded_domSaddle`. -/
theorem corollary_37_6_1 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

/-- **Rockafellar, Corollary 37.6.1**, second clause: the saddle-value is then **finite**. It is a
value of `K` at a saddle-point, and a proper saddle-function is finite on its effective domain
(Corollary 36.3.1). Specialises `exists_maximin_eq_coe_of_isBounded_domSaddle`. -/
theorem corollary_37_6_1_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

end Thm376

/-! ### Corollary 37.6.2: the minimax theorem -/

section Cor3762

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Rockafellar, Corollary 37.6.2** (16159), the classical minimax theorem: let `C ⊆ ℝᵐ` and
`D ⊆ ℝⁿ` be non-empty closed **bounded** convex sets and `K` a continuous finite concave-convex
function on `C × D`. Then `K` has a saddle-point relative to `C × D`: there are `ū ∈ C`, `v̄ ∈ D`
with

`K (u, v̄) ≤ K (ū, v̄) ≤ K (ū, v)` for all `u ∈ C`, `v ∈ D`.

Proof route: the lower simple extension of `K` is a closed proper concave-convex function with
effective domain `C × D` (Corollary 34.2.4); Corollary 37.6.1 gives it a saddle-point, Corollary
36.3.1 places that point in `C × D`, and there the extension agrees with `K`. Specialises
`exists_saddlePoint_of_isBounded`.

**Two divergences.** (i) This is Rockafellar's finite-dimensional minimax theorem. Its
infinite-dimensional analogues — Kneser–Fan and Sion — require `C` and `D` to be **compact**, not
merely closed and bounded; in `ℝⁿ` the two coincide by Heine–Borel, and the substitution is
invisible. The backbone proves this corollary from Rockafellar's *own* unbounded machinery rather
than from Mathlib's `Topology/Sion.lean`, because Theorem 37.6 and Corollary 37.6.1 are wanted in
their own right. (ii) "Continuous finite concave-convex on `C × D`" is asked here **slice by
slice** — convexity, concavity and continuity of each one-variable section on its own set — which
is weaker than the book's joint hypothesis and is what the proof uses. -/
theorem corollary_37_6_2 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : Rn m × Rn n, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ v ∈ D, K q ≤ K (q.1, v) :=
  exists_saddlePoint_of_isBounded (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbdC hbdD

end Cor3762

end Rockafellar
