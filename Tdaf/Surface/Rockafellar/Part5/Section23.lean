/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Tdaf.Analysis.Convex.Polyhedral.Duality
import Tdaf.Analysis.Convex.Recession.ConeHull
import Tdaf.Analysis.Convex.Subgradient.Approx
import Tdaf.Analysis.Convex.Subgradient.Calculus
import Tdaf.Analysis.Convex.Subgradient.Existence
import Tdaf.Surface.Rockafellar.Part3.Section16

/-!
# Rockafellar, §23: Directional Derivatives and Subgradients

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §23, pp. 213–222: the one-sided
directional derivative `f'(x; y)`, the subdifferential `∂f(x)`, and the duality
`x* ∈ ∂f(x) ⟺ f(x) + f*(x*) = ⟨x, x*⟩` that makes the two calculable.

This is the first section of Part V, and it is where Parts II and III are cashed in: Theorem 23.2
is Corollary 13.2.1 applied to `f'(x; ·)`, Theorem 23.4 is Theorem 7.2 plus Corollary 7.4.2,
Theorem 23.8 is Theorem 16.4 (or the Alternative Proof's Theorem 11.3), and Theorem 23.9 is
Theorem 16.3.

## Contents

| label | declaration |
|---|---|
| Theorem 23.1 | `theorem_23_1_monotone`, `theorem_23_1_iInf`, `theorem_23_1_posHomogeneous`,
  `theorem_23_1_convex`, `theorem_23_1_zero`, `theorem_23_1_neg_le` |
| Theorem 23.2 | `theorem_23_2`, `theorem_23_2_closure` |
| Theorem 23.3 | `theorem_23_3_proper`, `theorem_23_3_two_sided`, `theorem_23_3_relint` |
| Theorem 23.4 | `theorem_23_4_notMem_dom`, `theorem_23_4_nonempty`, `theorem_23_4_proper`,
  `theorem_23_4_closed`, `theorem_23_4_supportFn`, `theorem_23_4_isBounded_iff`,
  `theorem_23_4_finite_iff` |
| Theorem 23.5 | `theorem_23_5_a`, `theorem_23_5_b`, `theorem_23_5_c`, `theorem_23_5_d`,
  `theorem_23_5_a_star`, `theorem_23_5_b_star`, `theorem_23_5_a_star_star` |
| Corollary 23.5.1 | `corollary_23_5_1`, `corollary_23_5_1_mem` |
| Corollary 23.5.2 | `corollary_23_5_2_clFn`, `corollary_23_5_2_subgradient` |
| Corollary 23.5.3 | `corollary_23_5_3` |
| Corollary 23.5.4 | `corollary_23_5_4`, `corollary_23_5_4_inv` |
| Theorem 23.6 | `theorem_23_6` |
| Theorem 23.7 | `theorem_23_7` |
| Corollary 23.7.1 | `corollary_23_7_1`, `corollary_23_7_1_smul` |
| Theorem 23.8 | `theorem_23_8_subset`, `theorem_23_8`, `theorem_23_8_polyhedral` |
| Corollary 23.8.1 | `corollary_23_8_1_subset`, `corollary_23_8_1` |
| Theorem 23.9 | `theorem_23_9_subset`, `theorem_23_9` |
| Theorem 23.10 | `theorem_23_10_nonempty`, `theorem_23_10_polyhedral`,
  `theorem_23_10_dirDeriv_polyhedral`, `theorem_23_10_dirDeriv_proper`,
  `theorem_23_10_supportFn` |

## The section's definitions

Both of the section's objects are backbone definitions and are used without a surface copy.

* `Tdaf.ConvexAnalysis.dirDeriv f x y` is Rockafellar's `f'(x; y)`, defined as the infimum of the
  difference quotient over `λ > 0`. The book defines it as the limit as `λ ↓ 0` and *proves* in
  Theorem 23.1 that the two agree; the backbone takes the infimum as the definition, and
  `theorem_23_1_monotone` supplies the monotonicity that identifies it with the limit.
* `Tdaf.ConvexAnalysis.subgradient (pairing n) f x` is `∂f(x)`, and
  `Tdaf.ConvexAnalysis.subgradientRel (pairing n) f` is the multivalued mapping `∂f` itself, as a
  `SetRel`. Corollary 23.5.1 is `SetRel.inv` applied to the latter, which is what the book's "in
  the sense of multivalued mappings" means.
* `Tdaf.ConvexAnalysis.normalCone (pairing n) C x` is `N_C(x)`, and
  `Tdaf.ConvexAnalysis.epsSubgradient (pairing n) ε f x` is `∂_ε f(x)`. The unnumbered facts the
  book records about `∂_ε` — it is closed and convex, it shrinks with `ε`, and its intersection
  over `ε > 0` is `∂f(x)` — are `epsSubgradient_convex_closed` and
  `epsSubgradient_iInter` below.

## Where the book's hypotheses had to change

**Theorem 23.5, clauses (a), (b) and (c), need neither convexity nor properness.** The book states
the whole theorem for a proper convex `f`. Clauses (a)–(c) are three readings of one system of weak
linear inequalities, and the backbone proves their equivalence with no hypothesis at all
(`mem_subgradient_iff_forall_sub_le`, `mem_subgradient_iff_conj_le`,
`mem_subgradient_iff_add_conj_le`); only the passage from the inequality (c) to the *equality* (d)
consumes `Proper`, because `f x + f* x*` can otherwise be `⊥`. The declarations below carry the
hypotheses that are used and record the difference here rather than re-adding them.

**Theorem 23.6 asks `IsClosed (epi f)` where the book says "closed".** For a proper convex function
those are the same condition; the backbone spells it as the epigraph because `ClosedFn` is defined
as the fixed-point equation `cl f = f`, whose unification behaviour is a known hazard
(`gotchas.md` EL13).

**Theorem 23.6 is an infimum, not a limit.** The book writes `lim_{ε ↓ 0} δ*(y | ∂_ε f(x))`. The
sets `∂_ε f(x)` increase with `ε`, so the limit is a monotone infimum and the backbone states it as
one; nothing is lost, and no filter is needed.

**Corollary 23.7.1 is stated twice.** `corollary_23_7_1` gives the normal cone as the convex cone
generated by `∂f(x)`, which is the backbone's conclusion, and `corollary_23_7_1_smul` gives the
book's own reading `∃ λ ≥ 0, x* ∈ λ ∂f(x)`. The two agree by Corollary 9.6.1's description of the
cone generated by a *convex* set (`mem_coe_hull_iff_of_convex`), plus the non-emptiness of `∂f(x)`
that the hypothesis `x ∈ int (dom f)` supplies.

**Theorem 23.9 is stated for a closed proper convex `h`, and then for a proper convex one.** The
backbone's constructor `IsExactImage.of_relint` asks for `ClosedProperConvexFn`; §16 already pays
the reduction to the closed case (`theorem_16_3_exact`, `theorem_16_3_attained`), and
`theorem_23_9` is stated with the book's hypotheses by rebuilding the `IsExactImage` from those two
results. See **Backbone gaps** below.

## What is not here

* **The polyhedral clause of Theorem 23.9** — *omitted with a reason*: it needs
  `IsExactImage.of_polyhedral`, the polyhedral constructor of Theorem 16.3, and
  `Tdaf/Analysis/Convex/Polyhedral/Duality.lean` supplies only the *sum* constructors
  (`IsExactSum.of_polyhedral`, `IsExactFinsetSum.of_polyhedral`). Recorded as a backbone gap
  below. The relative-interior clause and the unconditional inclusion are both here, so the label
  is covered.
* **`rec (∂f(x)) = N_{dom f}(x)`** (book, p. 218, line 8477) — *omitted with a reason*: the book
  leaves it "as an exercise" and verifies it only later, inside the proof of Theorem 25.6. It is
  unnumbered, and it is **not** assumed anywhere in this file. What the backbone does have is the
  one-sided fact `subgradient_add_normalCone_dom_subset` (`∂f(x) + N_{dom f}(x) ⊆ ∂f(x)`, with no
  hypothesis), which is the easy half; the converse is §25's obligation, and §25 should discharge
  it rather than inherit it.
* **The complementary-slackness description of `∂δ(· | ℝⁿ₊)`** (book, p. 222) — *omitted with a
  reason*: it is unnumbered, and it is the instance of `corollary_23_5_4` at the non-negative
  orthant. What it needs beyond this file is the identification of the orthant's polar with the
  non-positive orthant, which belongs to §14 and not here.

## Backbone gaps

Each of the following is proved as a `private` lemma below and should move.

1. **`IsExactFinsetSum.subgradient_finsetSum`**, in
   `Tdaf/Analysis/Convex/Subgradient/Calculus.lean`. Wanted:
   `IsExactFinsetSum B s f → ∀ x, subgradient B (∑ i ∈ s, f i) x = ∑ i ∈ s, subgradient B (f i) x`,
   with `subgradient_finsetSum_subset` (the unconditional inclusion, no hypothesis) beside it.
   `Calculus.lean` has only the binary `IsExactSum.subgradient_add`, although §16's
   `IsExactFinsetSum` interface — and its constructors `of_relint` and `of_polyhedral` — are
   `m`-ary throughout. The `m`-ary form is what Rockafellar states, and it is what Corollary 23.8.1
   needs; going through the binary rule would mean re-deriving properness and the relative-interior
   condition of each partial sum at every step, which is exactly what `IsExactFinsetSum.cons`
   exists to avoid.
2. **`Tdaf.EReal.le_coe_of_sum_le_coe_sum`**, in `Tdaf/Order/EReal.lean`. Wanted: from
   `∀ i ∈ s, (c i : EReal) ≤ u i` and `∑ i ∈ s, u i ≤ ↑(∑ i ∈ s, c i)`, conclude `u j ≤ ↑(c j)` for
   every `j ∈ s`. This is the `m`-ary form of `Tdaf.EReal.le_coe_of_add_le_coe_add`, whose
   docstring already names Theorem 23.8 as its consumer; the `m`-ary theorem needs the `m`-ary
   lemma, and the two-summand version does not iterate (there is no subtraction to peel a summand
   off with).
3. **`IsExactImage.of_relint` without closedness**, in `Tdaf/Analysis/Convex/Duality/Relint.lean`.
   Wanted: `ConvexFn g → Proper g → A x₀ ∈ ri (dom g) → IsExactImage B B' A A' hA g`. The existing
   constructor asks for `ClosedProperConvexFn g`, so §16 pays a closure reduction
   (`clFn_compLin` plus `ConvexFn.relint_dom_clFn`) inside `theorem_16_3_exact` and again inside
   `theorem_16_3_attained`, and §23 has to pay it a third time to reach Theorem 23.9 with the
   book's hypotheses. One backbone constructor removes all three.
4. **`indicatorFn_finsetSum`**, in `Tdaf/Analysis/Convex/Indicator.lean`. Wanted:
   `∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i)`, the `m`-ary `indicatorFn_add`.
   `indicatorFn_add`'s own docstring says that "every intersection corollary in the book is the
   indicator instance of a statement about sums"; Corollary 23.8.1 is the `m`-ary one, and it is
   the sum over a `Finset` that it needs.

Mathlib's `Set.finsetSum_mem_finsetSum` — the `m`-ary `Set.add_mem_add` — was written here first
and then found: it is `to_additive`-generated, so a grep of Mathlib's source for the name returns
nothing (`gotchas.md` DEP3). Only the multiplicative `finsetProd_mem_finsetProd` occurs.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §23.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {m n : ℕ}

/-! ### Theorem 23.1: the one-sided directional derivative -/

/-- **Rockafellar, Theorem 23.1**, first assertion. For a convex `f` finite at `x`, the difference
quotient `[f(x + λy) - f(x)] / λ` is a non-decreasing function of `λ > 0`.

This is what identifies the book's `lim_{λ ↓ 0}` with the backbone's `⨅_{λ > 0}`: a monotone
function's limit at the left endpoint is its infimum. Specialises `monotoneOn_sub_div`. -/
theorem theorem_23_1_monotone {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (y : Rn n) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Ioi 0) :=
  monotoneOn_sub_div hf hr y

/-- **Rockafellar, Theorem 23.1**, the formula `f'(x; y) = inf_{λ > 0} [f(x + λy) - f(x)] / λ`.

In the backbone this is the *definition* of `dirDeriv`, so the content of the book's sentence is
`theorem_23_1_monotone`, which says the infimum is a limit. -/
theorem theorem_23_1_iInf (f : Rn n → EReal) (x y : Rn n) :
    dirDeriv f x y = ⨅ a ∈ Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) :=
  dirDeriv_apply f x y

/-- **Rockafellar, Theorem 23.1**: `f'(x; ·)` is positively homogeneous.

This clause needs nothing at all — neither convexity of `f` nor finiteness at `x` — because it is a
reindexing of the infimum. Specialises `posHomogeneous_dirDeriv`. -/
theorem theorem_23_1_posHomogeneous (f : Rn n → EReal) (x : Rn n) :
    PosHomogeneous (dirDeriv f x) :=
  posHomogeneous_dirDeriv f x

/-- **Rockafellar, Theorem 23.1**: `f'(x; ·)` is a convex function of `y`.

Specialises `convexFn_dirDeriv`. The finiteness of `f` at `x` is not removable: off `dom f` the
difference quotient is `⊤ - ⊤ = ⊥` in every direction. -/
theorem theorem_23_1_convex {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) : ConvexFn (dirDeriv f x) :=
  convexFn_dirDeriv hf ht hb

/-- **Rockafellar, Theorem 23.1**: `f'(x; 0) = 0`.

Specialises `dirDeriv_zero`. -/
theorem theorem_23_1_zero {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x 0 = 0 :=
  dirDeriv_zero ht hb

/-- **Rockafellar, Theorem 23.1**, last assertion: `-f'(x; -y) ≤ f'(x; y)` for every `y`.

Specialises `neg_dirDeriv_neg_le`. -/
theorem theorem_23_1_neg_le {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (y : Rn n) : -dirDeriv f x (-y) ≤ dirDeriv f x y :=
  neg_dirDeriv_neg_le hf ht hb y

/-! ### Theorem 23.2: subgradients and directional derivatives -/

/-- **Rockafellar, Theorem 23.2.** For a convex `f` finite at `x`, a vector `x*` is a subgradient
of `f` at `x` if and only if `f'(x; y) ≥ ⟨x*, y⟩` for every `y`.

Specialises `mem_subgradient_iff_le_dirDeriv`; convexity of `f` is not used, because the
subgradient inequality and the infimum of difference quotients are two spellings of the same
system. -/
theorem theorem_23_2 {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      ∀ v : Rn n, ((pairing n v y : ℝ) : EReal) ≤ dirDeriv f x v :=
  mem_subgradient_iff_le_dirDeriv ht hb

/-- **Rockafellar, Theorem 23.2**, second assertion: the closure of `f'(x; ·)` as a convex function
of `y` is the support function of the closed convex set `∂f(x)`.

Specialises `clFn_dirDeriv`, which is Corollary 13.2.1 applied to the positively homogeneous convex
function `f'(x; ·)`. The `.flip` the backbone hands back is `pairing n` again
(`supportFn_flip_pairing`). -/
theorem theorem_23_2_closure {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) :
    clFn (dirDeriv f x) = supportFn (pairing n) (subgradient (pairing n) f x) := by
  have h := clFn_dirDeriv (B := pairing n) hf ht hb
  rwa [supportFn_flip_pairing] at h

/-! ### Theorem 23.3: when subgradients exist -/

/-- **Rockafellar, Theorem 23.3**, first assertion: if `f` is subdifferentiable at a point where it
is finite, then `f` is proper.

Specialises `proper_of_subgradient_nonempty`: a subgradient exhibits an affine minorant, and a
convex function with an affine minorant cannot take the value `-∞`. -/
theorem theorem_23_3_proper {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subgradient (pairing n) f x).Nonempty) : Proper f :=
  proper_of_subgradient_nonempty ht hb h

/-- **Rockafellar, Theorem 23.3**, second assertion: if `f` is *not* subdifferentiable at `x`,
there is an infinite two-sided directional derivative there — some `y` with
`f'(x; y) = -f'(x; -y) = -∞`.

Specialises `exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top`. The book's `-f'(x; -y) = -∞` is
`f'(x; -y) = +∞`, which is how it is stated here. -/
theorem theorem_23_3_two_sided {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subgradient (pairing n) f x = ∅) :
    ∃ y : Rn n, dirDeriv f x y = ⊥ ∧ dirDeriv f x (-y) = ⊤ :=
  exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top hf ht hb hsub

/-- **Rockafellar, Theorem 23.3**, last assertion: if `f` is not subdifferentiable at `x` then
`f'(x; z - x) = -∞` for *every* `z ∈ ri (dom f)`.

Specialises `dirDeriv_eq_bot_of_subgradient_eq_empty`. -/
theorem theorem_23_3_relint {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subgradient (pairing n) f x = ∅) {z : Rn n} (hz : z ∈ ri (dom f)) :
    dirDeriv f x (z - x) = ⊥ :=
  dirDeriv_eq_bot_of_subgradient_eq_empty hf ht hb hsub hz

/-! ### Theorem 23.4: existence, closedness and boundedness -/

/-- **Rockafellar, Theorem 23.4**, first assertion: for a proper convex `f` and `x ∉ dom f`, the
set `∂f(x)` is empty.

Specialises `subgradient_eq_empty_of_notMem_dom`; convexity is not used. -/
theorem theorem_23_4_notMem_dom {f : Rn n → EReal} (hp : Proper f) {x : Rn n} (hx : x ∉ dom f) :
    subgradient (pairing n) f x = ∅ :=
  subgradient_eq_empty_of_notMem_dom hp hx

/-- **Rockafellar, Theorem 23.4**: a proper convex function is subdifferentiable at every point of
`ri (dom f)`.

Specialises `subgradient_nonempty_of_mem_relint_dom`. -/
theorem theorem_23_4_nonempty {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : (subgradient (pairing n) f x).Nonempty :=
  subgradient_nonempty_of_mem_relint_dom hf hp hx

/-- **Rockafellar, Theorem 23.4**: for `x ∈ ri (dom f)`, `f'(x; ·)` is proper.

Specialises `proper_dirDeriv_of_mem_relint_dom`, which is Theorem 7.2 applied to `f'(x; ·)`: its
effective domain is the subspace parallel to `aff (dom f)`, and it vanishes at the origin. -/
theorem theorem_23_4_proper {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : Proper (dirDeriv f x) :=
  proper_dirDeriv_of_mem_relint_dom hf hp hx

/-- **Rockafellar, Theorem 23.4**: for `x ∈ ri (dom f)`, `f'(x; ·)` is closed.

Specialises `closedFn_dirDeriv_of_mem_relint_dom`, which is Corollary 7.4.2. -/
theorem theorem_23_4_closed {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : ClosedFn (dirDeriv f x) :=
  closedFn_dirDeriv_of_mem_relint_dom hf hp hx

/-- **Rockafellar, Theorem 23.4**: for `x ∈ ri (dom f)`,
`f'(x; y) = sup {⟨x*, y⟩ | x* ∈ ∂f(x)} = δ*(y | ∂f(x))`.

Specialises `dirDeriv_eq_supportFn_of_mem_relint_dom`. Because `f'(x; ·)` is already closed there,
no closure operation appears — this is the sharpening of Theorem 23.2 that the relative interior
buys. -/
theorem theorem_23_4_supportFn {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) :
    dirDeriv f x = supportFn (pairing n) (subgradient (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_mem_relint_dom (B := pairing n) hf hp hx
  rwa [supportFn_flip_pairing] at h

/-- **Rockafellar, Theorem 23.4**, last assertion: `∂f(x)` is a non-empty *bounded* set if and only
if `x ∈ int (dom f)`.

Specialises `isBounded_subgradient_iff_mem_interior_dom`; the non-emptiness is
`theorem_23_4_nonempty`, so only the boundedness is at issue. -/
theorem theorem_23_4_isBounded_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    {x : Rn n} (hx : x ∈ ri (dom f)) :
    Bornology.IsBounded (subgradient (pairing n) f x) ↔ x ∈ interior (dom f) :=
  isBounded_subgradient_iff_mem_interior_dom hf hp hx

/-- **Rockafellar, Theorem 23.4**, last clause: in that case `f'(x; y)` is finite for every `y`.

Specialises `dom_dirDeriv_eq_univ_iff_mem_interior_dom`; "finite for every `y`" is
`dom (f'(x; ·)) = ℝⁿ` together with properness (`theorem_23_4_proper`), which rules out `-∞`. -/
theorem theorem_23_4_finite_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    (hx : x ∈ ri (dom f)) : dom (dirDeriv f x) = univ ↔ x ∈ interior (dom f) :=
  dom_dirDeriv_eq_univ_iff_mem_interior_dom hf hp hx

/-! ### Theorem 23.5: the four conditions, and the three starred ones -/

/-- **Rockafellar, Theorem 23.5**, condition (a): `x* ∈ ∂f(x)`, i.e. the subgradient inequality
`f(z) ≥ f(x) + ⟨x*, z - x⟩` for every `z`.

This is the definition of `subgradient`, recorded as a clause so that the seven conditions can be
read off one list. -/
theorem theorem_23_5_a {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      ∀ z : Rn n, f x + ((pairing n (z - x) y : ℝ) : EReal) ≤ f z :=
  mem_subgradient

/-- **Rockafellar, Theorem 23.5**, condition (b): `⟨z, x*⟩ - f(z)` achieves its supremum in `z` at
`z = x`.

Specialises `mem_subgradient_iff_forall_sub_le`. Neither convexity nor properness is used: this is
the subgradient inequality with the terms moved across, and `⟨z, x*⟩ - f(z)` is finite-minus-`EReal`
so no `∞ - ∞` can arise. -/
theorem theorem_23_5_b {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      ∀ z : Rn n, ((pairing n z y : ℝ) : EReal) - f z ≤ ((pairing n x y : ℝ) : EReal) - f x :=
  mem_subgradient_iff_forall_sub_le

/-- **Rockafellar, Theorem 23.5**, condition (c): `f(x) + f*(x*) ≤ ⟨x, x*⟩`.

Specialises `mem_subgradient_iff_add_conj_le`. Since the supremum in (b) *is* `f*(x*)`, this is (b)
restated; again no hypothesis is needed. -/
theorem theorem_23_5_c {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      f x + conj (pairing n) f y ≤ ((pairing n x y : ℝ) : EReal) :=
  mem_subgradient_iff_add_conj_le

/-- **Rockafellar, Theorem 23.5**, condition (d): `f(x) + f*(x*) = ⟨x, x*⟩`.

Specialises `Proper.mem_subgradient_iff_add_conj_eq`. This is the one clause of (a)–(d) that
genuinely consumes properness: Fenchel's inequality `⟨x, x*⟩ ≤ f(x) + f*(x*)` is false for
`f ≡ +∞`, since `⊤ + ⊥ = ⊥` in `EReal`. -/
theorem theorem_23_5_d {f : Rn n → EReal} (hp : Proper f) {x y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      f x + conj (pairing n) f y = ((pairing n x y : ℝ) : EReal) :=
  hp.mem_subgradient_iff_add_conj_eq

/-- **Rockafellar, Theorem 23.5**, condition (a*): `x ∈ ∂f*(x*)`, available when
`(cl f)(x) = f(x)`.

Specialises `mem_subgradient_conj_iff`, whose hypothesis is `f** x = f x`; for convex `f` that is
`(cl f)(x) = f(x)` by Fenchel–Moreau (`biconj_eq_clFn`). -/
theorem theorem_23_5_a_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : clFn f x = f x) {y : Rn n} :
    x ∈ subgradient (pairing n) (conj (pairing n) f) y ↔ y ∈ subgradient (pairing n) f x := by
  have hbi : biconj (pairing n) f x = f x := by rw [biconj_eq_clFn hf]; exact hx
  have h := mem_subgradient_conj_iff (B := pairing n) (f := f) (x := x) (y := y) hbi
  rwa [subgradient_flip_pairing] at h

/-- **Rockafellar, Theorem 23.5**, condition (b*): `⟨x, z*⟩ - f*(z*)` achieves its supremum in `z*`
at `z* = x*`, available when `(cl f)(x) = f(x)`.

This is condition (b) for `f*` at the point `x`, reached through (a*). -/
theorem theorem_23_5_b_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : clFn f x = f x) {y : Rn n} :
    y ∈ subgradient (pairing n) f x ↔
      ∀ w : Rn n, ((pairing n x w : ℝ) : EReal) - conj (pairing n) f w
        ≤ ((pairing n x y : ℝ) : EReal) - conj (pairing n) f y := by
  rw [← theorem_23_5_a_star hf hx, theorem_23_5_b]
  exact forall_congr' fun w => by rw [pairing_comm w x, pairing_comm y x]

/-- **Rockafellar, Theorem 23.5**, condition (a**): `x* ∈ ∂(cl f)(x)`, available when
`(cl f)(x) = f(x)`.

Specialises `mem_subgradient_clFn_iff`. -/
theorem theorem_23_5_a_star_star {f : Rn n → EReal} {x : Rn n} (hx : clFn f x = f x)
    {y : Rn n} :
    y ∈ subgradient (pairing n) (clFn f) x ↔ y ∈ subgradient (pairing n) f x :=
  mem_subgradient_clFn_iff hx

/-- **Rockafellar, Corollary 23.5.1.** For a closed proper convex `f`, the multivalued mapping
`∂f*` is the inverse of `∂f`.

`subgradientRel` is `∂f` as a `SetRel ℝⁿ ℝⁿ`, so the corollary is literally `SetRel.inv` applied to
it — which is why the backbone bundles the graph as well as the pointwise sets.

**The book states this corollary with no proof at all.** It follows from the equivalence of (a) and
(a*) in Theorem 23.5, whose hypothesis `(cl f)(x) = f(x)` is automatic for a closed `f`. -/
theorem corollary_23_5_1 {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    subgradientRel (pairing n) (conj (pairing n) f) = (subgradientRel (pairing n) f).inv := by
  have h := subgradientRel_conj_eq_inv (B := pairing n) hf hc
  rwa [flip_pairing] at h

/-- **Rockafellar, Corollary 23.5.1**, pointwise: `x ∈ ∂f*(x*)` if and only if `x* ∈ ∂f(x)`.

**Stated without proof in the book**; see `corollary_23_5_1`. -/
theorem corollary_23_5_1_mem {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedFn f)
    {x y : Rn n} :
    x ∈ subgradient (pairing n) (conj (pairing n) f) y ↔ y ∈ subgradient (pairing n) f x := by
  have h := mem_subgradient_conj_iff_of_closedFn (B := pairing n) (x := x) (y := y) hf hc
  rwa [subgradient_flip_pairing] at h

/-- **Rockafellar, Corollary 23.5.2**, first assertion: if the proper convex `f` is
subdifferentiable at `x` then `(cl f)(x) = f(x)`.

Specialises `clFn_eq_of_mem_subgradient`. Properness is not needed: a subgradient already forces
the biconjugate to agree with `f` at `x`. -/
theorem corollary_23_5_2_clFn {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subgradient (pairing n) f x) : clFn f x = f x :=
  clFn_eq_of_mem_subgradient hf hy

/-- **Rockafellar, Corollary 23.5.2**, second assertion: and then `∂(cl f)(x) = ∂f(x)`.

Specialises `subgradient_clFn`, which is the equivalence of (a) and (a**) in Theorem 23.5. -/
theorem corollary_23_5_2_subgradient {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subgradient (pairing n) f x) :
    subgradient (pairing n) (clFn f) x = subgradient (pairing n) f x :=
  subgradient_clFn hf hy

/-- **Rockafellar, Corollary 23.5.3.** For a non-empty closed convex `C` and any `x*`, the set
`∂δ*(x* | C)` consists of the points `x` (if any) at which the linear function `⟨·, x*⟩` achieves
its maximum over `C`.

Specialises `subgradient_supportFn`, which is the equivalence of (a*) and (b) at
`f = δ(· | C)`. -/
theorem corollary_23_5_3 {C : Set (Rn n)} (hC : IsClosed C) (hCc : Convex ℝ C)
    (hCne : C.Nonempty) (y : Rn n) :
    subgradient (pairing n) (supportFn (pairing n) C) y
      = {x ∈ C | ∀ z ∈ C, pairing n z y ≤ pairing n x y} := by
  have h := subgradient_supportFn (B := pairing n) hC hCc hCne y
  rwa [subgradient_flip_pairing] at h

/-- The normal cone to a set at the origin is its polar cone. -/
private theorem normalCone_zero (C : Set (Rn n)) :
    normalCone (pairing n) C 0 = polarCone (pairing n) C := by
  ext y
  simp only [mem_normalCone, mem_polarCone, sub_zero]

/-- **Rockafellar, Corollary 23.5.4.** For a convex cone `K`, one has `x* ∈ ∂δ(x | K)` if and only
if `x ∈ K`, `x* ∈ K°` and `⟨x, x*⟩ = 0` — the complementary-slackness form.

Specialises `mem_subgradient_indicatorFn_pointedCone`. **Rockafellar assumes `K` non-empty and
closed and neither hypothesis is used**: he derives the corollary from `δ(· | K)* = δ(· | K°)`,
which needs closedness, while the direct argument — put `z = 0` and `z = x + x` into the subgradient
inequality — does not. -/
theorem corollary_23_5_4 (K : PointedCone ℝ (Rn n)) {x y : Rn n} :
    y ∈ subgradient (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ K ∧ y ∈ polarCone (pairing n) (K : Set (Rn n)) ∧ pairing n x y = 0 := by
  rw [mem_subgradient_indicatorFn_pointedCone, normalCone_zero]

/-- **Rockafellar, Corollary 23.5.4**, the duality: for a closed convex cone `K`,
`x* ∈ ∂δ(x | K)` if and only if `x ∈ ∂δ(x* | K°)`.

Both sides unfold by `corollary_23_5_4` to the same three conditions, once `K°° = K`
(**Theorem 14.1**) has identified the polar of `K°` with `K`. Closedness and non-emptiness are used
here, and only here. -/
theorem corollary_23_5_4_inv {K : PointedCone ℝ (Rn n)} (hK : IsClosed (K : Set (Rn n)))
    {x y : Rn n} :
    y ∈ subgradient (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ subgradient (pairing n)
        (indicatorFn (polarPointedCone (pairing n) (K : Set (Rn n)) : Set (Rn n))) y := by
  have hbi : polarCone (pairing n) (polarCone (pairing n) (K : Set (Rn n)))
      = (K : Set (Rn n)) := by
    have h := polarCone_polarCone_pointedCone (B := pairing n) K hK
    rwa [polarCone_flip_pairing] at h
  rw [corollary_23_5_4, corollary_23_5_4 (polarPointedCone (pairing n) (K : Set (Rn n)))]
  rw [coe_polarPointedCone, hbi]
  constructor
  · rintro ⟨hx, hy, h0⟩
    exact ⟨hy, hx, by rw [Tdaf.Surface.pairing_comm]; exact h0⟩
  · rintro ⟨hy, hx, h0⟩
    exact ⟨hx, hy, by rw [Tdaf.Surface.pairing_comm]; exact h0⟩

/-! ### Theorem 23.6: `ε`-subgradients -/

/-- The unnumbered facts the book records about `∂_ε f(x)` immediately before Theorem 23.6: it is a
closed convex set for every `ε`.

`epsSubgradient` is the backbone's `∂_ε f(x)`, and the description
`∂_ε f(x) = {x* | h*(x*) ≤ ε}` with `h(y) = f(x + y) - f(x)` is `epsSubgradient_eq_setOf_conj_le`,
from which both clauses follow. -/
theorem epsSubgradient_convex_closed {f : Rn n → EReal} {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (ε : ℝ) :
    Convex ℝ (epsSubgradient (pairing n) ε f x) ∧
      IsClosed (epsSubgradient (pairing n) ε f x) :=
  ⟨convex_epsSubgradient hr ε, isClosed_epsSubgradient hr ε⟩

/-- The other unnumbered fact: the nest `∂_ε f(x)`, `ε > 0`, has intersection `∂f(x)`.

Specialises `iInter_epsSubgradient`. -/
theorem epsSubgradient_iInter (f : Rn n → EReal) (x : Rn n) :
    ⋂ ε ∈ Ioi (0 : ℝ), epsSubgradient (pairing n) ε f x = subgradient (pairing n) f x :=
  iInter_epsSubgradient (pairing n) f x

/-- **Rockafellar, Theorem 23.6.** For a closed proper convex `f` finite at `x`,
`f'(x; y) = lim_{ε ↓ 0} δ*(y | ∂_ε f(x))`.

Specialises `dirDeriv_eq_iInf_supportFn_epsSubgradient`. Two departures from the printed statement,
both recorded in the module docstring: the limit is written as the infimum it is (the sets increase
with `ε`), and "closed" is spelled as `IsClosed (epi f)`. -/
theorem theorem_23_6 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f)
    (hc : IsClosed (epi f)) {x : Rn n} {r : ℝ} (hr : f x = (r : EReal)) (v : Rn n) :
    ⨅ ε ∈ Ioi (0 : ℝ), supportFn (pairing n) (epsSubgradient (pairing n) ε f x) v
      = dirDeriv f x v := by
  have h := dirDeriv_eq_iInf_supportFn_epsSubgradient (B := pairing n) hf hp hc hr v
  simpa only [supportFn_flip_pairing] using h

/-! ### Theorem 23.7: normals to a level set -/

/-- **Rockafellar, Theorem 23.7.** Let `f` be a proper convex function and let `x` be a point at
which `f` is subdifferentiable but does not achieve its minimum. Then the normal cone to
`C = {z | f(z) ≤ f(x)}` at `x` is the closure of the convex cone generated by `∂f(x)`.

Specialises `normalCone_setOf_le_eq_closure_coe_hull_subgradient`. The hypothesis
`⨅ z, f z < f x` is the book's "f does not achieve its minimum at `x`". -/
theorem theorem_23_7 {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hne : (subgradient (pairing n) f x).Nonempty) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = closure ((PointedCone.hull ℝ (subgradient (pairing n) f x) : Set (Rn n))) :=
  normalCone_setOf_le_eq_closure_coe_hull_subgradient hf hr hinf hne

/-- **Rockafellar, Corollary 23.7.1.** If `x` is an interior point of `dom f` at which `f` does not
achieve its minimum, the closure in Theorem 23.7 is unnecessary: the normal cone to
`C = {z | f(z) ≤ f(x)}` at `x` is the convex cone generated by `∂f(x)`.

Specialises `normalCone_setOf_le_eq_coe_hull_subgradient_of_mem_interior_dom`; what makes the
closure redundant is that `∂f(x)` is then non-empty, closed, bounded and misses the origin, so
Corollary 9.6.1 applies. -/
theorem corollary_23_7_1 {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal)) (hx : x ∈ interior (dom f)) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = (PointedCone.hull ℝ (subgradient (pairing n) f x) : Set (Rn n)) :=
  normalCone_setOf_le_eq_coe_hull_subgradient_of_mem_interior_dom hf hp hr hinf hx

/-- **Rockafellar, Corollary 23.7.1** in the book's own words: `x*` is normal to
`C = {z | f(z) ≤ f(x)}` at `x` if and only if there exists a `λ ≥ 0` with `x* ∈ λ ∂f(x)`.

The convex cone generated by a *convex* set is the union of its non-negative multiples
(`mem_coe_hull_iff_of_convex`, Corollary 9.6.1); `∂f(x)` is convex with no hypothesis, and it is
non-empty because `x ∈ int (dom f) ⊆ ri (dom f)`, which is what turns `λ > 0` into `λ ≥ 0`. -/
theorem corollary_23_7_1_smul {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) {x : Rn n}
    {r : ℝ} (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hx : x ∈ interior (dom f)) {y : Rn n} :
    y ∈ normalCone (pairing n) {z | f z ≤ (r : EReal)} x ↔
      ∃ a : ℝ, 0 ≤ a ∧ y ∈ a • subgradient (pairing n) f x := by
  have hri : x ∈ ri (dom f) := interior_subset_intrinsicInterior hx
  obtain ⟨y₀, hy₀⟩ := theorem_23_4_nonempty hf hp hri
  rw [corollary_23_7_1 hf hp hr hinf hx,
    mem_coe_hull_iff_of_convex (convex_subgradient (pairing n) f x)]
  constructor
  · rintro (rfl | ⟨t, ht, hmem⟩)
    · exact ⟨0, le_rfl, ⟨y₀, hy₀, by simp⟩⟩
    · exact ⟨t, ht.le, hmem⟩
  · rintro ⟨a, ha, hmem⟩
    rcases eq_or_lt_of_le ha with rfl | ha'
    · obtain ⟨w, -, hw⟩ := hmem
      exact Or.inl (by rw [← hw]; simp)
    · exact Or.inr ⟨a, ha', hmem⟩

/-! ### Theorem 23.8: the sum rule -/

/-- **Backbone gap 1**, unconditional half: the `m`-ary form of `subgradient_add_subset`. -/
private theorem subgradient_finsetSum_subset {ι : Type*} (f : ι → Rn n → EReal) (x : Rn n) :
    ∀ s : Finset ι,
      ∑ i ∈ s, subgradient (pairing n) (f i) x ⊆ subgradient (pairing n) (∑ i ∈ s, f i) x := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro y hy
      simp only [Finset.sum_empty, Set.mem_zero] at hy
      subst hy
      simp [mem_subgradient]
  | cons i t hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (Set.add_subset_add_left ih).trans (subgradient_add_subset (pairing n) (f i) _ x)

/-- **Backbone gap 2**: the `m`-ary form of `Tdaf.EReal.le_coe_of_add_le_coe_add`. If each `u i`
dominates the real `c i` and the sum of the `u i` is dominated by the sum of the `c i`, then every
one of the inequalities is tight.

There is no subtraction on `EReal` to peel a summand off with, so the two-summand lemma does not
iterate; what does work is to split `s` as `{j} ∪ (s \ {j})` and apply the two-summand lemma once,
with the *sums* over `s.erase j` as the second pair. -/
private theorem le_coe_of_sum_le_coe_sum {ι : Type*} {s : Finset ι} {c : ι → ℝ} {u : ι → EReal}
    (hle : ∀ i ∈ s, ((c i : ℝ) : EReal) ≤ u i)
    (hsum : ∑ i ∈ s, u i ≤ ((∑ i ∈ s, c i : ℝ) : EReal)) {j : ι} (hj : j ∈ s) :
    u j ≤ ((c j : ℝ) : EReal) := by
  classical
  have hq : ((∑ i ∈ s.erase j, c i : ℝ) : EReal) ≤ ∑ i ∈ s.erase j, u i := by
    rw [Tdaf.EReal.coe_sum]
    exact Finset.sum_le_sum fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have hadd : u j + ∑ i ∈ s.erase j, u i
      ≤ ((c j + ∑ i ∈ s.erase j, c i : ℝ) : EReal) := by
    rw [Finset.add_sum_erase s u hj, Finset.add_sum_erase s c hj]
    exact hsum
  exact Tdaf.EReal.le_coe_of_add_le_coe_add (hle j hj) hq hadd

/-- **Backbone gap 1**, exact half: `∂(∑ᵢ fᵢ)(x) = ∑ᵢ ∂fᵢ(x)` for an exactly-adding family.

The argument is Rockafellar's own, run once for the family rather than iterated: exactness hands
back a splitting `y = ∑ yᵢ` whose conjugate values already sum to `(∑ fᵢ)* y`, Fenchel's
inequality gives `⟨x, yᵢ⟩ ≤ fᵢ x + fᵢ* yᵢ` for each `i`, and the assumption `y ∈ ∂(∑ fᵢ)(x)` makes
the *sum* of those inequalities tight — so `le_coe_of_sum_le_coe_sum` makes each of them tight. -/
private theorem subgradient_finsetSum {ι : Type*} {s : Finset ι} {f : ι → Rn n → EReal}
    (h : IsExactFinsetSum (pairing n) s f) (x : Rn n) :
    subgradient (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subgradient (pairing n) (f i) x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subgradient_finsetSum_subset f x s)
  obtain ⟨y', hy', hle⟩ := h.exact_le y
  have hfen : ∀ i ∈ s, ((pairing n x (y' i) : ℝ) : EReal)
      ≤ f i x + conj (pairing n) (f i) (y' i) :=
    fun i hi => (h.proper i hi).le_add_conj x (y' i)
  have hsum : ∑ i ∈ s, (f i x + conj (pairing n) (f i) (y' i))
      ≤ ((∑ i ∈ s, pairing n x (y' i) : ℝ) : EReal) := by
    calc ∑ i ∈ s, (f i x + conj (pairing n) (f i) (y' i))
        = (∑ i ∈ s, f i) x + ∑ i ∈ s, conj (pairing n) (f i) (y' i) := by
          rw [Finset.sum_add_distrib, Finset.sum_apply]
      _ ≤ (∑ i ∈ s, f i) x + conj (pairing n) (∑ i ∈ s, f i) y := add_le_add le_rfl hle
      _ ≤ ((pairing n x y : ℝ) : EReal) := mem_subgradient_iff_add_conj_le.1 hy
      _ = ((∑ i ∈ s, pairing n x (y' i) : ℝ) : EReal) := by rw [← hy', map_sum]
  have hmem : ∀ i ∈ s, y' i ∈ subgradient (pairing n) (f i) x := fun i hi =>
    mem_subgradient_iff_add_conj_le.2
      (le_coe_of_sum_le_coe_sum (c := fun i => pairing n x (y' i))
        (u := fun i => f i x + conj (pairing n) (f i) (y' i)) hfen hsum hi)
  have hgoal :=
    Set.finsetSum_mem_finsetSum s (fun i => subgradient (pairing n) (f i) x) y' hmem
  rwa [hy'] at hgoal

/-- **Rockafellar, Theorem 23.8**, the unconditional inclusion: for proper convex `f₁, …, fₘ` and
`f = f₁ + ⋯ + fₘ`, one has `∂f(x) ⊇ ∂f₁(x) + ⋯ + ∂fₘ(x)` for every `x`.

No hypothesis at all — the `m` subgradient inequalities simply add. -/
theorem theorem_23_8_subset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) (x : Rn n) :
    ∑ i ∈ s, subgradient (pairing n) (f i) x ⊆ subgradient (pairing n) (∑ i ∈ s, f i) x :=
  subgradient_finsetSum_subset f x s

/-- **Rockafellar, Theorem 23.8.** If the convex sets `ri (dom fᵢ)`, `i = 1, …, m`, have a point in
common, then `∂(f₁ + ⋯ + fₘ)(x) = ∂f₁(x) + ⋯ + ∂fₘ(x)` for every `x`.

Stated for a `Finset` of summands, as the book states it, and **not** by induction on `m`:
`IsExactFinsetSum.of_relint` is Theorem 16.4 in the same `m`-ary form, so the constraint
qualification is discharged once.

The book gives two proofs. The printed one goes through Theorem 16.4, which is the route taken
here; the ALTERNATIVE PROOF (p. 220) uses only proper separation of the two convex sets
`{(x, μ) | μ ≥ f₁ x}` and `{(x, μ) | μ ≤ -f₂ x}` in `ℝⁿ⁺¹`, and reduces `m` to `2` by induction on
Theorem 6.5. It is the more elementary argument, but it is also the one that *needs* the induction:
the backbone's `IsExactFinsetSum` interface already carries the `m`-ary statement, and running the
separation argument instead would put the induction back. -/
theorem theorem_23_8 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → Rn n → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n}
    (hx₀ : ∀ i ∈ s, x₀ ∈ ri (dom (f i))) (x : Rn n) :
    subgradient (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subgradient (pairing n) (f i) x :=
  subgradient_finsetSum (IsExactFinsetSum.of_relint hs hf hpf hx₀) x

/-- **Rockafellar, Theorem 23.8**, last sentence: the condition for equality weakens when some of
the `fᵢ` are polyhedral. If `f₁, …, f_k` are polyhedral it is enough that
`dom f₁, …, dom f_k, ri (dom f_{k+1}), …, ri (dom fₘ)` have a point in common.

`t` is the book's `{1, …, k}` and `u` its complement; the index set is split membership-wise so
that no `DecidableEq` instance reaches the statement (`gotchas.md` SET11). Specialises
`IsExactFinsetSum.of_polyhedral`, which is Theorem 20.1. The book's ALTERNATIVE PROOF explicitly
does *not* cover this clause. -/
theorem theorem_23_8_polyhedral {ι : Type*} {s t u : Finset ι} (hs : s.Nonempty)
    (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u) {f : ι → Rn n → EReal}
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ dom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (f i))) (x : Rn n) :
    subgradient (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subgradient (pairing n) (f i) x :=
  subgradient_finsetSum
    (IsExactFinsetSum.of_polyhedral hs hdisj hmem hpoly hconv hpf hxt hxu) x

/-! ### Corollary 23.8.1: normals to an intersection -/

/-- Splitting off one index from an intersection over a `Finset`. -/
private theorem biInter_cons {ι : Type*} {i : ι} {t : Finset ι} (hi : i ∉ t)
    (C : ι → Set (Rn n)) : (⋂ j ∈ Finset.cons i t hi, C j) = C i ∩ ⋂ j ∈ t, C j := by
  ext z
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_cons]
  constructor
  · intro hz
    exact ⟨hz i (Or.inl rfl), fun j hj => hz j (Or.inr hj)⟩
  · rintro ⟨h₁, h₂⟩ j (rfl | hj)
    · exact h₁
    · exact h₂ j hj

/-- **Backbone gap 4**: the `m`-ary `indicatorFn_add`. -/
private theorem indicatorFn_finsetSum {ι : Type*} (C : ι → Set (Rn n)) :
    ∀ s : Finset ι, ∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i) := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      funext z
      simp
  | cons i t hi ih =>
      rw [Finset.sum_cons, ih, indicatorFn_add, biInter_cons hi C]

/-- **Rockafellar, Corollary 23.8.1**, the unconditional inclusion: the sum of the normal cones is
contained in the normal cone to the intersection.

Proved directly rather than through indicators, so that it needs no hypothesis on the sets or on
the point. -/
theorem corollary_23_8_1_subset {ι : Type*} (C : ι → Set (Rn n)) (x : Rn n) :
    ∀ s : Finset ι,
      ∑ i ∈ s, normalCone (pairing n) (C i) x ⊆ normalCone (pairing n) (⋂ i ∈ s, C i) x := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro y hy
      simp only [Finset.sum_empty, Set.mem_zero] at hy
      subst hy
      simp
  | cons i t hi ih =>
      rw [Finset.sum_cons, biInter_cons hi C]
      exact (Set.add_subset_add_left ih).trans (normalCone_add_subset (pairing n) (C i) _ x)

/-- **Rockafellar, Corollary 23.8.1.** Let `C₁, …, Cₘ` be convex sets whose relative interiors have
a point in common. Then the normal cone to `C₁ ∩ ⋯ ∩ Cₘ` at any `x` is `K₁ + ⋯ + Kₘ`, where `Kᵢ` is
the normal cone to `Cᵢ` at `x`.

The indicator instance of Theorem 23.8, via `indicatorFn_finsetSum`
(`δ(·|C₁) + ⋯ + δ(·|Cₘ) = δ(·| ⋂ Cᵢ)`, with no side condition) and `subgradient_indicatorFn`. The
hypothesis `x ∈ Cᵢ` is what `subgradient_indicatorFn` asks for; off the intersection both sides are
empty and the sum is `∅` too, which is why Rockafellar can leave it unsaid. -/
theorem corollary_23_8_1 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) {x : Rn n}
    (hx : ∀ i ∈ s, x ∈ C i) :
    normalCone (pairing n) (⋂ i ∈ s, C i) x = ∑ i ∈ s, normalCone (pairing n) (C i) x := by
  have hconv : ∀ i ∈ s, ConvexFn (indicatorFn (C i)) :=
    fun i hi => convexFn_indicatorFn.2 (hC i hi)
  have hprop : ∀ i ∈ s, Proper (indicatorFn (C i)) := fun i hi =>
    ⟨⟨x, by rw [dom_indicatorFn]; exact hx i hi⟩, indicatorFn_ne_bot (C i)⟩
  have hri : ∀ i ∈ s, x₀ ∈ ri (dom (indicatorFn (C i))) := by
    intro i hi
    rw [dom_indicatorFn]
    exact hx₀ i hi
  have hsum := theorem_23_8 hs hconv hprop hri x
  rw [indicatorFn_finsetSum C s,
    subgradient_indicatorFn (Set.mem_iInter₂.2 hx)] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i hi => subgradient_indicatorFn (hx i hi)

/-! ### Theorem 23.9: composition with a linear transformation -/

/-- **Rockafellar, Theorem 23.9**, the unconditional inclusion: for `f(x) = h(Ax)` one has
`∂f(x) ⊇ A*∂h(Ax)` for every `x`.

Specialises `image_subgradient_subset`; `h` is arbitrary and only the adjointness is used. -/
theorem theorem_23_9_subset (A : Rn n →ₗ[ℝ] Rn m) (h : Rn m → EReal) (x : Rn n) :
    LinearMap.adjoint A '' subgradient (pairing m) h (A x)
      ⊆ subgradient (pairing n) (compLin h A) x :=
  image_subgradient_subset (isAdjointPair_adjoint A) h x

/-- **Backbone gap 3**: `IsExactImage` for a *proper convex* `h` whose effective domain's relative
interior meets the range of `A`. The backbone's `IsExactImage.of_relint` asks for
`ClosedProperConvexFn h`; the reduction to the closed case is Theorem 9.5 plus Corollary 7.4.1, and
§16 already pays it inside `theorem_16_3_exact` and `theorem_16_3_attained`. This lemma reads the
interface back off those two. -/
private theorem isExactImage_of_relint_proper (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal}
    (hg : ConvexFn g) (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom g)) :
    IsExactImage (pairing n) (pairing m) A (LinearMap.adjoint A)
      (isAdjointPair_adjoint A) g where
  proper := hp
  exact_le y hy := by
    obtain ⟨z, hz, heq⟩ := theorem_16_3_attained A hg hp hx₀ hy
    exact ⟨z, hz, le_of_eq heq⟩

/-- **Rockafellar, Theorem 23.9.** Let `f(x) = h(Ax)` with `h` a proper convex function on `ℝᵐ` and
`A` a linear transformation from `ℝⁿ` to `ℝᵐ`. If the range of `A` contains a point of
`ri (dom h)`, then `∂f(x) = A*∂h(Ax)` for every `x`.

Specialises `IsExactImage.subgradient_compLin`, which is Theorem 23.5 applied to the exact
conjugacy formula of Theorem 16.3. Rockafellar's `A*` is `LinearMap.adjoint A`; on `ℝⁿ` the
adjointness hypothesis the backbone carries as data is `isAdjointPair_adjoint`.

**The polyhedral clause is not here**; see the module docstring. -/
theorem theorem_23_9 (A : Rn n →ₗ[ℝ] Rn m) {h : Rn m → EReal} (hh : ConvexFn h) (hp : Proper h)
    {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom h)) (x : Rn n) :
    subgradient (pairing n) (compLin h A) x
      = LinearMap.adjoint A '' subgradient (pairing m) h (A x) :=
  (isExactImage_of_relint_proper A hh hp hx₀).subgradient_compLin x

/-! ### Theorem 23.10: the polyhedral case -/

/-- **Rockafellar, Theorem 23.10**, first assertion: a polyhedral convex function is
subdifferentiable at every point where it is finite.

Specialises `subgradient_nonempty_of_polyhedralFn`. No relative interior is needed: the cone
generated by `epi f - (x, f x)` is polyhedral, hence closed (Corollary 19.7.1), so `f'(x; ·)` is
already closed and Theorem 23.2 gives a subgradient. -/
theorem theorem_23_10_nonempty {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : (subgradient (pairing n) f x).Nonempty :=
  subgradient_nonempty_of_polyhedralFn hf ht hb

/-- **Rockafellar, Theorem 23.10**: and `∂f(x)` is a polyhedral convex set.

Specialises `polyhedral_subgradient_of_polyhedralFn` (Corollary 19.2.1). -/
theorem theorem_23_10_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : Polyhedral (subgradient (pairing n) f x) :=
  polyhedral_subgradient_of_polyhedralFn hf ht hb

/-- **Rockafellar, Theorem 23.10**: `f'(x; ·)` is a polyhedral convex function.

Specialises `polyhedralFn_dirDeriv`. -/
theorem theorem_23_10_dirDeriv_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : PolyhedralFn (dirDeriv f x) :=
  polyhedralFn_dirDeriv hf ht hb

/-- **Rockafellar, Theorem 23.10**: `f'(x; ·)` is proper.

Specialises `proper_dirDeriv_of_polyhedralFn`. The book's reason is worth keeping: `f'(x; 0) = 0`,
and a polyhedral convex function taking the value `-∞` somewhere has no finite values at all. -/
theorem theorem_23_10_dirDeriv_proper {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : Proper (dirDeriv f x) :=
  proper_dirDeriv_of_polyhedralFn hf ht hb

/-- **Rockafellar, Theorem 23.10**, last assertion: `f'(x; ·)` is the support function of `∂f(x)`,
with no closure operation.

Specialises `dirDeriv_eq_supportFn_of_polyhedralFn`. -/
theorem theorem_23_10_supportFn {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x = supportFn (pairing n) (subgradient (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_polyhedralFn (B := pairing n) hf ht hb
  rwa [supportFn_flip_pairing] at h

end Rockafellar
