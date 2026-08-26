/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.ConeDuality
import Tdaf.Analysis.Convex.Optimization.MoreauGradient
import Tdaf.Analysis.Convex.Optimization.Normal
import Tdaf.Analysis.Convex.Polyhedral.Duality
import Tdaf.Surface.Rockafellar.Part3.Section12
import Tdaf.Surface.Rockafellar.Part3.Section16
import Tdaf.Surface.Rockafellar.Part4.Section19

/-!
# Rockafellar, §31: Fenchel's Duality Theorem

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §31, pp. 327–341 (book lines
13137–13916): Fenchel's Duality Theorem and the version of it a linear transformation `A` allows,
the same pair of extremum problems read as a convex program and its dual in the sense of §§29–30,
the two dual-cone corollaries, and Moreau's decomposition theorem.

This is where Part III's conjugacy and Part V's programs meet. Almost every declaration below is a
one-line specialisation of a backbone theorem from
`Tdaf/Analysis/Convex/Optimization/{Fenchel, Moreau, MoreauGradient, Prox, ConeDuality}.lean`; the
exceptions are the two places where the book leaves work undone, listed under **What the book
leaves undone** below.

## Contents

| label | declaration |
|---|---|
| Theorem 31.1 | `theorem_31_1_weak`, `theorem_31_1_a`, `theorem_31_1_a_attained`,
  `theorem_31_1_a_isGreatest`, `theorem_31_1_b`, `theorem_31_1_b_attained`,
  `theorem_31_1_finite` |
| Theorem 31.1, polyhedral (13167) | `theorem_31_1_a_polyhedral_left`,
  `theorem_31_1_a_polyhedral_left_attained`, `theorem_31_1_a_polyhedral_right`,
  `theorem_31_1_a_polyhedral_right_attained`, `theorem_31_1_b_polyhedral_left`,
  `theorem_31_1_b_polyhedral_right` |
| Theorem 31.2 | `fenchelBifun`, `fenchelBifun_apply`, `theorem_31_2_convex`,
  `theorem_31_2_proper`, `theorem_31_2_closed`, `theorem_31_2_infBifun`,
  `theorem_31_2_domBifun`, `theorem_31_2_relint_domBifun`,
  `theorem_31_2_stronglyConsistent_iff`, `theorem_31_2_adjoint`,
  `theorem_31_2_supBifun_adjoint`, `theorem_31_2_domConcaveBifun_adjoint`,
  `theorem_31_2_concaveStronglyConsistent_iff` |
| Corollary 31.2.1 | `corollary_31_2_1_a`, `corollary_31_2_1_a_attained`, `corollary_31_2_1_b`,
  `corollary_31_2_1_b_attained` |
| Corollary 31.2.1, polyhedral (13379) | `corollary_31_2_1_a_polyhedral_left`,
  `corollary_31_2_1_a_polyhedral_right` |
| Theorem 31.3 | `theorem_31_3_weak`, `theorem_31_3`, `theorem_31_3_kuhnTucker_concave`,
  `theorem_31_3_iInf`, `theorem_31_3_iSup`, `theorem_31_3_id` |
| Corollary 31.3.1 | `corollary_31_3_1`, `corollary_31_3_1_id` |
| Theorem 31.4 | `theorem_31_4_dualCone`, `theorem_31_4_weak`, `theorem_31_4_a`,
  `theorem_31_4_a_attained`, `theorem_31_4_b`, `theorem_31_4_b_attained`,
  `theorem_31_4_optimality`, `theorem_31_4_optimality_primal`,
  `theorem_31_4_optimality_dual` |
| Theorem 31.4, polyhedral (13595) | `theorem_31_4_a_polyhedral`,
  `theorem_31_4_a_polyhedral_attained`, `theorem_31_4_b_polyhedral`,
  `theorem_31_4_b_polyhedral_attained` |
| Corollary 31.4.1 | `neg_polarCone_nonnegOrthant`, `corollary_31_4_1_a`,
  `corollary_31_4_1_a_attained`, `corollary_31_4_1_b`, `corollary_31_4_1_b_attained`,
  `corollary_31_4_1_optimality` |
| Corollary 31.4.2 | `polarCone_coe_submodule_eq_orthogonal`, `corollary_31_4_2_a`,
  `corollary_31_4_2_a_attained`, `corollary_31_4_2_b_attained`,
  `corollary_31_4_2_optimality` |
| Corollary 31.4.3 | `corollary_31_4_3`, `corollary_31_4_3_iInf_eq_coe`,
  `corollary_31_4_3_iInf_dual_eq_coe`, `corollary_31_4_3_attained`,
  `corollary_31_4_3_dual_attained` |
| Theorem 31.5 | `theorem_31_5_quadFn`, `theorem_31_5`, `theorem_31_5_apply`,
  `theorem_31_5_finite`, `theorem_31_5_finite_conj`, `theorem_31_5_existsUnique`,
  `theorem_31_5_argmin_iff`, `theorem_31_5_argmin_eq`, `theorem_31_5_gradient`,
  `theorem_31_5_gradient_conj` |
| §31, the proximation (13820–13849) | `prox_eq_iff_sub_mem_subgradient`,
  `prox_add_prox_conj_eq`, `prox_conj_eq_sub`, `prox_continuous`, `prox_contraction`,
  `prox_lipschitzWith_one`, `range_prox` |
| Corollary 31.5.1 | `corollary_31_5_1`, `corollary_31_5_1_apply`,
  `corollary_31_5_1_symm_apply` |
| Corollary 31.5.2 | `corollary_31_5_2` |

## The section's definitions

Two objects are introduced here; both come with a bridge lemma back to the book's formula.

* `Rockafellar.ClosedProperConcaveFn g` is Rockafellar's "closed proper concave function", the
  standing hypothesis on `g` from Corollary 31.2.1 onwards. The backbone spells the same condition
  as `ClosedProperConvexFn fun x => -(g x)`; `closedProperConcaveFn_iff_neg` is the bridge and
  `ClosedProperConcaveFn.neg` the projection used at every call site.
* `Rockafellar.fenchelBifun A f g` is the bifunction `(F u)(x) = f x - g (A x + u)` of
  Theorem 31.2 (13260) — the Fenchel problem perturbed by translating the concave function.
  `fenchelBifun_apply` is the bridge, and `theorem_31_2_infBifun` is the statement that its convex
  program really is the Fenchel problem.

Everything else is a backbone object used without a surface copy: `conj`, `concaveConj`,
`subgradient`, `subgradientRel`, `polarCone` (the book's `K°`; `K* = -K°` is
`theorem_31_4_dualCone`), `quadFn`, `infConv`, `moreauObj`, `prox`, `argmin`,
`IsMaximalMonotoneRel`, and, for Theorem 31.2, the §29–§30 vocabulary `Bifun`, `graphFn`,
`infBifun`, `domBifun`, `ConvexBifun`, `ClosedBifun`, `StronglyConsistent`, `adjointBifun`,
`supBifun`, `domConcaveBifun`, `ConcaveStronglyConsistent`, `Normal`.

Rockafellar's `A*` is written `LinearMap.adjoint A` throughout and **no adjointness hypothesis is
carried anywhere in this file**: on `ℝⁿ` the transpose is canonical, and
`Tdaf.ConvexAnalysis.isAdjointPair_adjoint A` supplies the `IsAdjointPair` datum that the
pairing-parametrised backbone asks for. This is design decision **D3**, and it is what makes a
bundled adjoint unnecessary here.

## Where the book's hypotheses had to change

**Theorem 31.1's finiteness clause needs only the domains, not their relative interiors.**
The book says "if (a) and (b) both hold, the infimum and supremum are necessarily finite"
(13167). Only a point of `dom f ∩ dom g` and a point of `dom g* ∩ dom f*` are used —
`theorem_31_1_finite` asks for exactly those, and conditions (a) and (b) supply them by
`intrinsicInterior_subset`.

**Closedness is not needed under condition (a).** Corollary 31.2.1 is stated for closed proper `f`
and `g`; `corollary_31_2_1_a` and `corollary_31_2_1_a_attained` assume `f` only convex and proper.
The same happens in Theorem 31.3 and Corollary 31.3.1, where the book assumes both functions
closed and the proof is Theorem 23.5 twice plus a squeeze between two Fenchel inequalities.

**Theorem 31.2's properness clause needs no relative-interior hypothesis at all.**
`theorem_31_2_proper` holds for any proper convex `f` and proper concave `g`: one point of `dom f`
and one point of `dom g` suffice, because the perturbation `u` is free to move `A x` onto `dom g`.

**Corollary 31.4.1 goes through the polyhedral form of Theorem 31.4.** The book's conditions for
the non-negative orthant are `x ∈ ri (dom f)` with `x ≥ 0`, and `x* ∈ ri (dom f*)` with `x* ≥ 0` —
no relative interior of the orthant appears. That is Theorem 31.4's polyhedral strengthening
(13595) rather than its plain form, so `corollary_31_4_1_*` is derived from
`theorem_31_4_*_polyhedral` together with the private `polyhedral_nonnegOrthant`.

**Corollary 31.4.3 does not need `K` closed for most of what it says.** The book assumes `K` is a
closed convex cone; closedness is used only for the attainment of the *first* infimum
(`corollary_31_4_3_attained`). The identity and both finiteness clauses hold for any non-empty
convex cone.

**Theorem 6.6 is taken in its backbone form.** Surface §6's `theorem_6_6_ri` is stated only for
maps `Rn n →ₗ[ℝ] Rn m`. The map `(w, x) ↦ w - A x` that turns Rockafellar's `dom g - A (dom f)`
into a single linear image goes out of a *product*, so `relint_sub_image` uses
`Convex.relint_image` and `intrinsicInterior_prod_eq` directly.

## What the book leaves undone

**Corollary 31.2.1's polyhedral strengthening is asserted with the proof withheld.** The book
(13379) says: "It can be shown that in Corollary 31.2.1, just as in Theorem 31.1, `ri` can be
omitted whenever the corresponding function `f` or `g` is actually polyhedral. However, the proof
will not be given here." Both halves are proved here, as `corollary_31_2_1_a_polyhedral_right`
(`g` polyhedral) and `corollary_31_2_1_a_polyhedral_left` (`f` polyhedral). Condition (a) has two
jobs in the composed setting — an exact *sum* on `ℝⁿ` and an exact *image* along `A` — and the
polyhedral form has to replace both. `IsExactSum.of_polyhedral` covers the first, once
`polyhedralFn_neg_comp` says that `-(g ∘ A)` is polyhedral; the second has no backbone constructor
at all and is built here as `isExactImage_of_polyhedralFn` out of Theorem 19.2, Corollary 19.3.1
and Theorem 16.3's closure formula.

**Corollary 31.5.1 is stated with no proof.** Rockafellar gives the statement (13889) and moves on,
exactly as with Corollary 23.5.1. `corollary_31_5_1` proves it: bijectivity is Theorem 31.5, and
continuity of the inverse `z ↦ (prox (z ∣ f), z - prox (z ∣ f))` is the unnumbered contraction
property of the proximation (13851–13885), which is named here as `prox_contraction`. Theorem 24.4
— closedness of the graph of `∂f` — is not needed.

## What is not here

* **The linear-programming example (13381–13411)** — *an instance, not a statement*. Rockafellar
  substitutes `f = ⟨a*, ·⟩ + δ(· ∣ x ≥ 0)` and `g = -δ(· ∣ u ≥ a)` into Theorem 31.2 and reads off
  the dual linear program. Nothing is asserted that Theorem 31.2 does not already give; the
  orthant instance that *is* a numbered statement is Corollary 31.4.1, and it is here. Formalising
  the substitution would be an exercise in the `δ` calculus of §12 with no new content.
* **The positively-homogeneous example (13413–13419)** — same reason: `f` positively homogeneous
  with `g* = -δ*(· ∣ D)` is another substitution into Theorem 31.2.
* **The subgradient preview of Theorem 31.3 (13421–13463)** — *superseded by what is here*. The
  book's `0 ∈ ∂(f - gA)(x)` discussion, its inclusion `∂(f - gA)(x) ⊇ ∂f(x) - A*∂g(Ax)` and the
  "usually necessary" hedging are Theorems 23.8 and 23.9, which live in §23; line 13465 says the
  Kuhn–Tucker conditions "can also be stated and proved more directly, as follows" and then states
  Theorem 31.3, which is `theorem_31_3` and `corollary_31_3_1` below.
* **The §29–§30 commentary on the perturbation function `p` (13325–13363)** — *deferred by
  scope*: it is a reading of Corollaries 29.1.2, 29.1.3 and 30.2.3 and of Theorem 30.5 for this
  particular `F`, and those belong to the surface §§29–30 files. Its one operative consequence,
  "Theorem 30.4 and Corollary 30.5.2 yield a generalization of Fenchel's Duality Theorem" (13363),
  *is* here: it is exactly how `corollary_31_2_1_b` and `corollary_31_2_1_b_attained` are proved.
* **The Gale–Kuhn–Tucker remark (13691) and Tucker representations (13693)** — *omitted with a
  reason*: both are forward references with no proof and no statement of their own.
* **The separable case and Problems (I) and (II) (13695–13733)** — *deferred by scope*. Problems
  (I) and (II) are Corollary 31.4.2 with `f (ξ₁, …, ξₙ) = f₁ ξ₁ + ⋯ + fₙ ξₙ`, so the only content
  is the two separability facts the book recalls in passing: `f* = f₁* + ⋯ + fₙ*` (13704) and
  `x* ∈ ∂f(x) ⟺ ξⱼ* ∈ ∂fⱼ(ξⱼ) for every j` (13726, which the book itself sets "as an exercise").
  Both are §16/§23 statements about a finite direct sum, and the backbone has no separable
  conjugate at all — `Duality/FiniteProduct.lean` carries the product *pairing* and the relative
  interior of a product, not a `conj` of a sum. Recorded under **Backbone gaps**.
* **The proximation of an indicator function and Moreau's cone decomposition (13841–13847)** —
  *deferred by scope*: `prox (z ∣ δ(· ∣ C))` is the projection on `C`, and for a cone `K` the
  decomposition `z = x + x*` with `x ∈ K`, `x* ∈ K°` and `⟨x, x*⟩ = 0` follows. The backbone's
  `Prox.lean` has no projection-on-a-convex-set operator, so this needs a definition first; the
  §31 content it rests on (`prox_add_prox_conj_eq`, `prox_conj_eq_sub`) is here.

## Backbone gaps

Three of the six private declarations this file once carried are now in the backbone, and the
lemma the sixth item asked for exists there too. Items 4 and 5 are still open. The numbering is
unchanged.

1. **Corollary 30.5.2** — **done**. `exists_infBifun_eq_of_concaveStronglyConsistent` is public in
   `Tdaf/Analysis/Convex/Optimization/Normal.lean`, and `corollary_31_2_1_b_attained` cites it.
2. **Theorem 30.5, concave side** — **done**. The mirror
   `mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq` is public in the same module, with `Bu`
   and `Bx` explicit, and the dual assertion of Theorem 30.5
   itself (`mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin`) is beside it.
3. **An `EReal` infimum over a product splits** — **done**. `Tdaf.EReal.iInf_prod_add` is public in
   `Tdaf/Order/EReal.lean`, together with `coe_add_iInf`, `add_iInf_of_ne_bot` and
   `iInf_add_of_ne_bot`. It is stated under `⨅ ψ ≠ ⊤` and `⨅ φ ≠ ⊤` rather than under the
   witness-value hypotheses proposed here — strictly more general, since it *handles* the `⊥`
   corners instead of excluding them — so the call site derives the two hypotheses from one finite
   value on each side.
4. **A polyhedral constructor for `IsExactImage`.** `isExactImage_of_polyhedralFn` is Theorem
   20.1's companion for the image rule; `Tdaf/Analysis/Convex/Polyhedral/Duality.lean` has
   `IsExactSum.of_polyhedral` and `IsExactFinsetSum.of_polyhedral` but nothing for images. Wanted
   there as

       theorem IsExactImage.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B']
           {h : G → EReal} (hA : IsAdjointPair B B' A A') (hh : PolyhedralFn h) (hp : Proper h)
           {x₀ : E} (hx₀ : A x₀ ∈ dom h) : IsExactImage B B' A A' hA h

   `Tdaf/Surface/Rockafellar/Part5/Section23.lean` proves the same lemma privately for Theorem
   23.9; the two are now duplicated.
5. **A polyhedral function composed with a linear map is polyhedral.** `polyhedralFn_neg_comp` is
   `Polyhedral.comap` applied to `epi_compLin`. The public `polyhedralFn_compLin` in
   `Tdaf/Analysis/Convex/Saddle/Correspondence.lean` says the same thing, and its own docstring
   says it belongs in `Optimization/Perturbation.lean`; §31 must not import a §37 module, so it is
   restated here. Wanted in `Tdaf/Analysis/Convex/Optimization/Perturbation.lean`, next to
   `polyhedralFn_mapLin`.
6. **A separable conjugate** — the backbone half is **done**. `conj_piFn` is public in
   `Tdaf/Analysis/Convex/Duality/FiniteProduct.lean` (which is already in this file's import
   closure), as

       theorem conj_piFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : ι → E → EReal) (hf : ∀ i, Proper (f i))
           (y : ι → F) :
           conj (piPairing B) (fun x => ∑ i, f i (x i)) y = ∑ i, conj B (f i) (y i)

   What is still not carried is the *surface* statement: Problems (I) and (II) of 13695–13733 also
   need the separable subgradient rule `x* ∈ ∂f(x) ⟺ ξⱼ* ∈ ∂fⱼ(ξⱼ) for every j` (13726), which the
   book itself sets as an exercise, and a `Rn n ≃ (Fin s → Rn nⱼ)` decomposition — remediation
   §12.31's `s`-fold product, still open.

Two smaller local proofs are surface-level rather than backbone gaps: `polyhedral_nonnegOrthant`
and `smul_nonnegOrthant` describe `Rockafellar.nonnegOrthant` from §12 and belong with it, and
`relint_sub_image` is Theorem 6.6 for a map out of a product (see above).

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31.
* J.-J. Moreau, *Proximité et dualité dans un espace hilbertien*, Bull. Soc. Math. France **93**
  (1965), 273–299 — Theorem 31.5 and Corollary 31.5.2.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {m n : ℕ}

/-! ### Concave functions in the book's vocabulary -/

/-- Rockafellar's **closed proper concave function** on `ℝⁿ`: the concave mirror of
`ClosedProperConvexFn`, which is the standing hypothesis on `g` from Corollary 31.2.1 onwards.

The backbone spells this as `ClosedProperConvexFn fun x => -(g x)`; the bridge is
`closedProperConcaveFn_iff_neg`, and every theorem below is derived through it. -/
structure ClosedProperConcaveFn (g : Rn n → EReal) : Prop where
  /-- The hypograph is convex. -/
  concave : ConcaveFn g
  /-- `g` equals its own concave closure. -/
  closed : ClosedConcaveFn g
  /-- `g` is finite somewhere and never `+∞`. -/
  proper : ProperConcave g

/-- **The bridge to the backbone**: `g` is closed proper concave exactly when `-g` is closed proper
convex. This is Rockafellar's own definition of the concave notions (§30, and §12's sign
dictionary), taken clause by clause. -/
theorem closedProperConcaveFn_iff_neg {g : Rn n → EReal} :
    ClosedProperConcaveFn g ↔ ClosedProperConvexFn fun x => -(g x) :=
  ⟨fun h => ⟨concaveFn_iff_convexFn_neg.1 h.concave, closedConcaveFn_iff.1 h.closed,
      properConcave_iff_proper_neg.1 h.proper⟩,
    fun h => ⟨concaveFn_iff_convexFn_neg.2 h.convex, closedConcaveFn_iff.2 h.closed,
      properConcave_iff_proper_neg.2 h.proper⟩⟩

/-- The bridge, in the direction every proof below uses. -/
theorem ClosedProperConcaveFn.neg {g : Rn n → EReal} (hg : ClosedProperConcaveFn g) :
    ClosedProperConvexFn fun x => -(g x) :=
  closedProperConcaveFn_iff_neg.1 hg

/-! ### Theorem 31.1: Fenchel's duality theorem

Rockafellar's two conditions (a) and (b) are two sufficient conditions for one interface, the
backbone's `IsExactSum`; the polyhedral weakenings the theorem's last paragraph announces are two
more. The four private constructors below are exactly those four, and the numbered statements are
one line each after them. -/

/-- Rockafellar's condition **(a)** of Theorem 31.1: `ri (dom f) ∩ ri (dom g) ≠ ∅` makes `f` and
`-g` add exactly (Theorem 16.4). -/
private theorem isExactSum_neg_of_relint {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (domConcave g)) : IsExactSum (pairing n) f fun x => -(g x) :=
  IsExactSum.of_relint hf hpf (concaveFn_iff_convexFn_neg.1 hg)
    (properConcave_iff_proper_neg.1 hpg) hxf (by rwa [← domConcave_eq_dom_neg])

/-- Rockafellar's condition **(b)** of Theorem 31.1, on the dual pair: `ri (dom g*) ∩ ri (dom f*)`
non-empty makes `f*` and `-g*` add exactly. -/
private theorem isExactSum_conj_of_relint {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyg : y₀ ∈ ri (domConcave (concaveConj (pairing n) g))) :
    IsExactSum (pairing n).flip (conj (pairing n) f)
      fun y => -(concaveConj (pairing n) g y) := by
  refine IsExactSum.of_relint (convexFn_conj (pairing n) f) (proper_conj (B := pairing n) hf)
    (concaveFn_iff_convexFn_neg.1 (concaveFn_concaveConj (pairing n) g))
    (properConcave_iff_proper_neg.1 ⟨⟨y₀, intrinsicInterior_subset hyg⟩,
      fun y => concaveConj_ne_top hg.proper.domConcave_nonempty y⟩)
    hyf ?_
  rwa [← domConcave_eq_dom_neg]

/-- **Rockafellar, Theorem 31.1** (13153), the inequality the proof opens with: every dual value
`g*(x*) - f*(x*)` is below every primal value `f(x) - g(x)`.

It is Fenchel's inequality used twice, and Rockafellar states it in the proof rather than in the
theorem. Specialises `concaveConj_sub_conj_le_sub`, which carries **no hypothesis at all**: both
`∞ - ∞` collisions are absorbed on the correct side. -/
theorem theorem_31_1_weak (f g : Rn n → EReal) (x y : Rn n) :
    concaveConj (pairing n) g y - conj (pairing n) f y ≤ f x - g x :=
  concaveConj_sub_conj_le_sub (pairing n) f g x y

/-- **Rockafellar, Theorem 31.1** (13153) under condition **(a)** (13161): for a proper convex `f`
and a proper concave `g` whose effective domains have relative interiors meeting,

`inf {f(x) - g(x)} = sup {g*(x*) - f*(x*)}`.

Specialises `fenchel_duality`; condition (a) enters only through Theorem 16.4
(`IsExactSum.of_relint`). -/
theorem theorem_31_1_a {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (domConcave g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13165): under condition (a) the supremum is attained at some
`x*`. Specialises `exists_concaveConj_sub_conj_eq`. -/
theorem theorem_31_1_a_attained {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (domConcave g)) :
    ∃ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_conj_eq (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13165), the attainment clause packaged: under condition (a) the
common value is the *greatest* dual value. Specialises `isGreatest_concaveConj_sub_conj`. -/
theorem theorem_31_1_a_isGreatest {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (domConcave g)) :
    IsGreatest (Set.range fun y : Rn n =>
      concaveConj (pairing n) g y - conj (pairing n) f y) (⨅ x, f x - g x) :=
  isGreatest_concaveConj_sub_conj (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13153) under condition **(b)** (13163): `f` and `g` closed, with
`ri (dom g*)` meeting `ri (dom f*)`. The equality is the same one.

Specialises `fenchel_duality_of_closed`, which is condition (a) read on the dual pair together with
Fenchel–Moreau. -/
theorem theorem_31_1_b {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyg : y₀ ∈ ri (domConcave (concaveConj (pairing n) g))) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y :=
  fenchel_duality_of_closed hf hg.neg (isExactSum_conj_of_relint hf hg hyf hyg)

/-- **Rockafellar, Theorem 31.1** (13165): under condition (b) the *infimum* is attained at some
`x`. Specialises `exists_sub_eq_iInf`. -/
theorem theorem_31_1_b_attained {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyg : y₀ ∈ ri (domConcave (concaveConj (pairing n) g))) :
    ∃ x : Rn n, f x - g x = ⨅ z, f z - g z :=
  exists_sub_eq_iInf hf hg.neg (isExactSum_conj_of_relint hf hg hyf hyg)

/-! ### Theorem 31.1: the polyhedral strengthening

"If `g` is actually polyhedral, `ri (dom g)` and `ri (dom g*)` can be replaced by `dom g` and
`dom g*` in (a) and (b), respectively (and the closure assumption in (b) is superfluous). Similarly
if `f` is polyhedral" (13167). All four readings are Theorem 20.1 (`IsExactSum.of_polyhedral`) in
place of Theorem 16.4, and the closure assumption really is superfluous, because a proper polyhedral
convex function is closed (Corollary 19.1.2). -/

/-- Condition (a) with `f` polyhedral: `dom f` in place of `ri (dom f)`. -/
private theorem isExactSum_neg_of_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : Proper f) (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : x₀ ∈ ri (domConcave g)) : IsExactSum (pairing n) f fun x => -(g x) :=
  IsExactSum.of_polyhedral hf hpf (concaveFn_iff_convexFn_neg.1 hg)
    (properConcave_iff_proper_neg.1 hpg) hxf (by rwa [← domConcave_eq_dom_neg])

/-- Condition (a) with `g` polyhedral: `dom g` in place of `ri (dom g)`. -/
private theorem isExactSum_neg_of_polyhedral_right {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : Proper f) (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ domConcave g) :
    IsExactSum (pairing n) f fun x => -(g x) :=
  (IsExactSum.of_polyhedral hg (properConcave_iff_proper_neg.1 hpg) hf hpf
    (by rwa [← domConcave_eq_dom_neg]) hxf).symm

/-- **`-g*` is polyhedral when `-g` is.** The concave conjugate is the convex conjugate of `-g`
read at `-y` (`neg_concaveConj`), the conjugate of a polyhedral function is polyhedral
(**Theorem 19.2**), and precomposing with `-id` is a linear substitution, which `Polyhedral.comap`
carries through the epigraph. -/
private theorem polyhedralFn_neg_concaveConj {g : Rn n → EReal}
    (hg : PolyhedralFn fun x => -(g x)) :
    PolyhedralFn fun y : Rn n => -(concaveConj (pairing n) g y) := by
  have hfun : (fun y : Rn n => -(concaveConj (pairing n) g y))
      = compLin (conj (pairing n) fun x => -(g x)) (-LinearMap.id) := by
    funext y
    rw [neg_concaveConj, compLin_apply]
    rfl
  rw [hfun]
  change Polyhedral (epi _)
  rw [epi_compLin]
  exact Polyhedral.comap (PolyhedralFn.conj (B := pairing n) hg) _

/-- A polyhedral proper concave function is closed (**Corollary 19.1.2** on the concave side), so
the closure assumption of Theorem 31.1(b) really is superfluous for it. -/
private theorem closedProperConcaveFn_of_polyhedral {g : Rn n → EReal}
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) : ClosedProperConcaveFn g := by
  have hp : Proper fun x => -(g x) := properConcave_iff_proper_neg.1 hpg
  exact closedProperConcaveFn_iff_neg.2 ⟨hg.convexFn, hg.closedFn hp.ne_bot, hp⟩

/-- **Rockafellar, Theorem 31.1** (13167), the polyhedral strengthening of condition (a) with `f`
polyhedral: `ri (dom f)` may be replaced by `dom f`. -/
theorem theorem_31_1_a_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : x₀ ∈ ri (domConcave g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_polyhedral_left hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13167): under the polyhedral form of (a) with `f` polyhedral,
the supremum is still attained. -/
theorem theorem_31_1_a_polyhedral_left_attained {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : Proper f) (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : x₀ ∈ ri (domConcave g)) :
    ∃ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_conj_eq (isExactSum_neg_of_polyhedral_left hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13167), the polyhedral strengthening of condition (a) with `g`
polyhedral: `ri (dom g)` may be replaced by `dom g`. -/
theorem theorem_31_1_a_polyhedral_right {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ domConcave g) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_polyhedral_right hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13167): under the polyhedral form of (a) with `g` polyhedral,
the supremum is still attained. -/
theorem theorem_31_1_a_polyhedral_right_attained {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : Proper f) (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ domConcave g) :
    ∃ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_conj_eq (isExactSum_neg_of_polyhedral_right hf hpf hg hpg hxf hxg)

/-- **Rockafellar, Theorem 31.1** (13167), the polyhedral strengthening of condition (b) with `f`
polyhedral: `ri (dom f*)` may be replaced by `dom f*`, and `f` is not assumed closed — a proper
polyhedral convex function is closed automatically. -/
theorem theorem_31_1_b_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n} (hyf : y₀ ∈ dom (conj (pairing n) f))
    (hyg : y₀ ∈ ri (domConcave (concaveConj (pairing n) g))) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y := by
  have hfc : ClosedProperConvexFn f := ⟨hf.convexFn, hf.closedFn hpf.ne_bot, hpf⟩
  refine fenchel_duality_of_closed hfc hg.neg (IsExactSum.of_polyhedral
    (PolyhedralFn.conj (B := pairing n) hf) (proper_conj (B := pairing n) hfc)
    (concaveFn_iff_convexFn_neg.1 (concaveFn_concaveConj (pairing n) g))
    (properConcave_iff_proper_neg.1 ⟨⟨y₀, intrinsicInterior_subset hyg⟩,
      fun y => concaveConj_ne_top hg.proper.domConcave_nonempty y⟩) hyf ?_)
  change y₀ ∈ ri (dom fun y => -(concaveConj (pairing n) g y))
  rwa [← domConcave_eq_dom_neg]

/-- **Rockafellar, Theorem 31.1** (13167), the polyhedral strengthening of condition (b) with `g`
polyhedral: `ri (dom g*)` may be replaced by `dom g*`, and `g` is not assumed closed. -/
theorem theorem_31_1_b_polyhedral_right {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyg : y₀ ∈ domConcave (concaveConj (pairing n) g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - conj (pairing n) f y := by
  refine fenchel_duality_of_closed hf (closedProperConcaveFn_of_polyhedral hg hpg).neg
    (IsExactSum.of_polyhedral (polyhedralFn_neg_concaveConj hg)
      (properConcave_iff_proper_neg.1 ⟨⟨y₀, hyg⟩,
        fun y => concaveConj_ne_top hpg.domConcave_nonempty y⟩)
      (convexFn_conj (pairing n) f) (proper_conj (B := pairing n) hf) ?_ hyf).symm
  rwa [← domConcave_eq_dom_neg]

/-- **Rockafellar, Theorem 31.1** (13167): "if (a) and (b) both hold, the infimum and supremum are
necessarily finite".

Only the *closures* of the two conditions are used: a point of `dom f ∩ dom g` bounds the infimum
above, and a point of `dom g* ∩ dom f*` bounds it below through weak duality
(`theorem_31_1_weak`). Neither relative interior is needed, so the hypotheses below are weaker than
the book's; (a) and (b) imply them by `intrinsicInterior_subset`. -/
theorem theorem_31_1_finite {f g : Rn n → EReal} (hpf : Proper f) (hpg : ProperConcave g)
    {x₀ : Rn n} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ domConcave g) {y₀ : Rn n}
    (hyf : y₀ ∈ dom (conj (pairing n) f))
    (hyg : y₀ ∈ domConcave (concaveConj (pairing n) g)) :
    ∃ r : ℝ, (⨅ x, f x - g x) = (r : EReal) := by
  have hgy : (⊥ : EReal) < concaveConj (pairing n) g y₀ := hyg
  have hfy : conj (pairing n) f y₀ < ⊤ := hyf
  obtain ⟨c, hc⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hgy.ne'
    (lt_top_iff_ne_top.2 (concaveConj_ne_top hpg.domConcave_nonempty y₀))
  obtain ⟨d, hd⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top
    (conj_ne_bot hpf.dom_nonempty y₀) hfy
  have hlow : ((c - d : ℝ) : EReal) ≤ ⨅ x, f x - g x := by
    refine le_iInf fun x => ?_
    have h := theorem_31_1_weak f g x y₀
    rwa [hc, hd, ← _root_.EReal.coe_sub] at h
  have hbot : (⨅ x, f x - g x) ≠ ⊥ := by
    intro hcon
    rw [hcon, le_bot_iff] at hlow
    exact _root_.EReal.coe_ne_bot _ hlow
  have htop : (⨅ x, f x - g x) < ⊤ := by
    refine lt_of_le_of_lt (iInf_le (fun x => f x - g x) x₀) ?_
    have h1 : f x₀ < ⊤ := hxf
    have h2 : (⊥ : EReal) < g x₀ := hxg
    have h3 : -(g x₀) ≠ ⊤ := by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact h2.ne'
    exact _root_.EReal.add_lt_top h1.ne h3
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hbot htop
  exact ⟨r, hr⟩

/-! ### Corollary 31.2.1: a linear transformation between the two functions

Rockafellar's condition (a) — some `x ∈ ri (dom f)` with `A x ∈ ri (dom g)` — does two jobs at
once, and the backbone separates them: it makes `f` and `-(g A)` add exactly (Theorem 16.4,
`IsExactSum`) and it makes `-g` pull back exactly along `A` (Theorem 16.3, `IsExactImage`). The
two private constructors below are those two jobs; the polyhedral versions further down are the
strengthening whose proof the book declines to give. -/

/-- Condition (a) of Corollary 31.2.1, the exact-pullback half: **Theorem 16.3**. -/
private theorem isExactImage_neg_of_relint {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hg : ClosedProperConcaveFn g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (domConcave g)) :
    IsExactImage (pairing n) (pairing m) A (LinearMap.adjoint A) (isAdjointPair_adjoint A)
      fun w => -(g w) :=
  IsExactImage.of_relint_closed (isAdjointPair_adjoint A) hg.neg (by rwa [← domConcave_eq_dom_neg])

/-- Condition (a) of Corollary 31.2.1, the exact-sum half: **Theorem 16.4**, with the relative
interior of `dom (-(g A)) = A⁻¹ (dom (-g))` computed by **Theorem 6.7**. -/
private theorem isExactSum_neg_comp_of_relint {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : ConvexFn f) (hpf : Proper f) (hg : ConcaveFn g)
    (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : A x₀ ∈ ri (domConcave g)) : IsExactSum (pairing n) f fun x => -(g (A x)) := by
  have hgn : ConvexFn fun w => -(g w) := concaveFn_iff_convexFn_neg.1 hg
  have hpgn : Proper fun w => -(g w) := properConcave_iff_proper_neg.1 hpg
  have hxg' : A x₀ ∈ ri (dom fun w => -(g w)) := by rwa [← domConcave_eq_dom_neg]
  have hcomp : ConvexFn (compLin (fun w => -(g w)) A) := convexFn_compLin A hgn
  have hpcomp : Proper (compLin (fun w => -(g w)) A) :=
    ⟨⟨x₀, by rw [dom_compLin]; exact Set.mem_preimage.2 (intrinsicInterior_subset hxg')⟩,
      fun x => hpgn.ne_bot (A x)⟩
  have hri : x₀ ∈ ri (dom (compLin (fun w => -(g w)) A)) := by
    rw [dom_compLin, Convex.relint_preimage hgn.convex_dom A ⟨x₀, hxg'⟩]
    exact hxg'
  exact IsExactSum.of_relint hf hpf hcomp hpcomp hxf hri

/-- **Composing with a linear map keeps a polyhedral concave function polyhedral.**
`epi (-(g A))` is `epi (-g)` pulled back along `(x, μ) ↦ (A x, μ)`. -/
private theorem polyhedralFn_neg_comp {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hg : PolyhedralFn fun w => -(g w)) : PolyhedralFn fun x => -(g (A x)) := by
  change Polyhedral (epi (compLin (fun w => -(g w)) A))
  rw [epi_compLin]
  exact Polyhedral.comap hg _

/-- **The polyhedral constructor for `IsExactImage`** — Theorem 20.1's companion for the image
rule, which the backbone does not have (see `## Backbone gaps`).

The route is entirely §19's, and it is the one Rockafellar points at for Theorem 23.9: `h*` is
polyhedral (**Theorem 19.2**), so `A*h*` is polyhedral with its infimum attained
(**Corollary 19.3.1**), and a proper polyhedral convex function is closed, so Theorem 16.3's
closure formula has nothing left to close. -/
private theorem isExactImage_of_polyhedralFn {h : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hh : PolyhedralFn h) (hp : Proper h) {x₀ : Rn n} (hx₀ : A x₀ ∈ dom h) :
    IsExactImage (pairing n) (pairing m) A (LinearMap.adjoint A)
      (isAdjointPair_adjoint A) h := by
  have hhcl : ClosedFn h := hh.closedFn hp.ne_bot
  have hconjpoly : PolyhedralFn (conj (pairing m) h) := PolyhedralFn.conj (B := pairing m) hh
  have hmappoly : PolyhedralFn (mapLin (LinearMap.adjoint A) (conj (pairing m) h)) :=
    polyhedralFn_mapLin hconjpoly _
  have hne : (dom (compLin h A)).Nonempty := ⟨x₀, by rwa [mem_dom, compLin_apply]⟩
  have hbot : ∀ y, conj (pairing n) (compLin h A) y ≠ ⊥ := fun y => conj_ne_bot hne y
  have hmapbot : ∀ y, mapLin (LinearMap.adjoint A) (conj (pairing m) h) y ≠ ⊥ := by
    intro y hy
    exact hbot y
      (le_bot_iff.1 (hy ▸ conj_compLin_le_mapLin (isAdjointPair_adjoint A) h y))
  have hmapcl : ClosedFn (mapLin (LinearMap.adjoint A) (conj (pairing m) h)) :=
    hmappoly.closedFn hmapbot
  have heq : conj (pairing n) (compLin h A)
      = mapLin (LinearMap.adjoint A) (conj (pairing m) h) := by
    have hstep := theorem_16_3_closure A hh.convexFn
    rwa [show clFn h = h from hhcl,
      show clFn (mapLin (LinearMap.adjoint A) (conj (pairing m) h))
        = mapLin (LinearMap.adjoint A) (conj (pairing m) h) from hmapcl] at hstep
  refine ⟨hp, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hmapbot y) hy
  obtain ⟨z, hz, hzeq⟩ := corollary_19_3_1_attained hconjpoly (LinearMap.adjoint A) hμ
  exact ⟨z, hz, le_of_eq hzeq⟩

/-- **Rockafellar, Corollary 31.2.1** (13365) under condition **(a)** (13373): for a proper convex
`f` on `ℝⁿ`, a closed proper concave `g` on `ℝᵐ` and a linear `A : ℝⁿ → ℝᵐ`,

`inf {f(x) - g(Ax)} = sup {g*(u*) - f*(A*u*)}`

as soon as some `x ∈ ri (dom f)` has `Ax ∈ ri (dom g)`.

Rockafellar's `A*` is `LinearMap.adjoint A`, and no adjointness hypothesis is carried: on `ℝⁿ` the
transpose is canonical and `isAdjointPair_adjoint` supplies the datum (design decision **D3**).
Closedness of `f` is assumed in the book but is not used under (a). Specialises
`fenchel_duality_comp`. -/
theorem corollary_31_2_1_a {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : Proper f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : A x₀ ∈ ri (domConcave g)) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - conj (pairing n) f (LinearMap.adjoint A z) :=
  fenchel_duality_comp (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg)

/-- **Rockafellar, Corollary 31.2.1** (13377): under (a) the supremum is attained at some `u*`.
Specialises `exists_concaveConj_sub_conj_comp_eq`. -/
theorem corollary_31_2_1_a_attained {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : Proper f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : A x₀ ∈ ri (domConcave g)) :
    ∃ z : Rn m, concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z)
      = ⨅ x, f x - g (A x) :=
  exists_concaveConj_sub_conj_comp_eq (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg)

/-- **Rockafellar, Corollary 31.2.1** (13379), the polyhedral strengthening with `g` polyhedral —
*the clause whose proof the book explicitly declines to give*: "It can be shown that in Corollary
31.2.1, just as in Theorem 31.1, `ri` can be omitted whenever the corresponding function `f` or `g`
is actually polyhedral. However, the proof will not be given here."

Here is the proof for `g`. Both of condition (a)'s jobs have polyhedral constructors: `-(g A)` is
polyhedral (`polyhedralFn_neg_comp`), so **Theorem 20.1** replaces Theorem 16.4 in the sum, and
`isExactImage_of_polyhedralFn` — Corollary 19.3.1 in place of Theorem 16.3 — replaces the pullback.
Neither needs a relative interior on the `g` side, and closedness of `g` is automatic
(Corollary 19.1.2). -/
theorem corollary_31_2_1_a_polyhedral_right {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : ConvexFn f) (hpf : Proper f)
    (hg : PolyhedralFn fun w => -(g w)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : A x₀ ∈ domConcave g) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - conj (pairing n) f (LinearMap.adjoint A z) := by
  have hpgn : Proper fun w => -(g w) := properConcave_iff_proper_neg.1 hpg
  have hxg' : A x₀ ∈ dom fun w => -(g w) := by rwa [← domConcave_eq_dom_neg]
  refine fenchel_duality_comp (isAdjointPair_adjoint A)
    ((IsExactSum.of_polyhedral (polyhedralFn_neg_comp A hg)
      ⟨⟨x₀, hxg'⟩, fun x => hpgn.ne_bot (A x)⟩ hf hpf hxg' hxf).symm)
    (isExactImage_of_polyhedralFn A hg hpgn hxg')

/-- **Rockafellar, Corollary 31.2.1** (13379), the polyhedral strengthening with `f` polyhedral,
the other half of the clause the book leaves unproved: `ri (dom f)` may be replaced by `dom f`.

Only the sum half changes here — **Theorem 20.1** with the polyhedral summand on the left — because
the pullback is a statement about `g` alone and keeps its relative interior. -/
theorem corollary_31_2_1_a_polyhedral_left {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ClosedProperConcaveFn g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : A x₀ ∈ ri (domConcave g)) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - conj (pairing n) f (LinearMap.adjoint A z) := by
  have hgn : ConvexFn fun w => -(g w) := concaveFn_iff_convexFn_neg.1 hg.concave
  have hpgn : Proper fun w => -(g w) := properConcave_iff_proper_neg.1 hg.proper
  have hxg' : A x₀ ∈ ri (dom fun w => -(g w)) := by rwa [← domConcave_eq_dom_neg]
  have hpcomp : Proper (compLin (fun w => -(g w)) A) :=
    ⟨⟨x₀, by rw [dom_compLin]; exact Set.mem_preimage.2 (intrinsicInterior_subset hxg')⟩,
      fun x => hpgn.ne_bot (A x)⟩
  have hri : x₀ ∈ ri (dom (compLin (fun w => -(g w)) A)) := by
    rw [dom_compLin, Convex.relint_preimage hgn.convex_dom A ⟨x₀, hxg'⟩]
    exact hxg'
  exact fenchel_duality_comp (isAdjointPair_adjoint A)
    (IsExactSum.of_polyhedral hf hpf (convexFn_compLin A hgn) hpcomp hxf hri)
    (isExactImage_neg_of_relint A hg hxg)

/-! ### Theorem 31.3: the Kuhn–Tucker conditions -/

/-- **Rockafellar, Theorem 31.3** (13467), weak duality for the transformed pair, which the proof
uses as its "general inequality" (13496): every value of `g* - f*A*` is below every value of
`f - gA`. No hypothesis at all. -/
theorem theorem_31_3_weak {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (x : Rn n) (z : Rn m) :
    concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z) ≤ f x - g (A x) :=
  concaveConj_sub_conj_comp_le_sub (isAdjointPair_adjoint A) x z

/-- **Rockafellar, Theorem 31.3** (13467). For `f` proper convex on `ℝⁿ`, `g` proper concave on
`ℝᵐ` and `A` linear, the primal and dual values agree at `(x, u*)` if and only if `x` and `u*`
satisfy the **Kuhn–Tucker conditions** `A*u* ∈ ∂f(x)` and `Ax ∈ ∂g*(u*)`.

The book's second condition uses the *super*differential of the concave `g*`. That
superdifferential is `-∂(-g)`, so it is spelled `-u* ∈ ∂(-g)(Ax)` here and no new notion is needed;
`theorem_31_3_kuhnTucker_concave` is the dictionary back to the book's Fenchel-equality form.

Closedness of `f` and `g` is assumed by the book and is not used: the theorem is Theorem 23.5 twice
plus the squeeze between the two Fenchel inequalities. Specialises
`sub_comp_eq_concaveConj_sub_conj_iff`. -/
theorem theorem_31_3 {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hpf : Proper f) (hpg : ProperConcave g) {x : Rn n} {z : Rn m} :
    f x - g (A x)
        = concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z) ↔
      LinearMap.adjoint A z ∈ subgradient (pairing n) f x ∧
        -z ∈ subgradient (pairing m) (fun w => -(g w)) (A x) :=
  sub_comp_eq_concaveConj_sub_conj_iff (isAdjointPair_adjoint A) hpf
    (properConcave_iff_proper_neg.1 hpg)

/-- **Rockafellar, Theorem 31.3** (13486), the book's own reading of the second Kuhn–Tucker
condition: `Ax ∈ ∂g*(u*)` says that Fenchel's inequality for the concave pair holds with equality,
`g(Ax) + g*(u*) = ⟨Ax, u*⟩` (**Theorem 23.5** on the concave side).

Specialises `neg_mem_subgradient_neg_iff_add_concaveConj_eq`. -/
theorem theorem_31_3_kuhnTucker_concave {g : Rn m → EReal} (hpg : ProperConcave g) (w z : Rn m) :
    -z ∈ subgradient (pairing m) (fun v => -(g v)) w ↔
      g w + concaveConj (pairing m) g z = ((pairing m w z : ℝ) : EReal) :=
  neg_mem_subgradient_neg_iff_add_concaveConj_eq (properConcave_iff_proper_neg.1 hpg)

/-- **Rockafellar, Theorem 31.3** (13467), first consequence: a pair at which the two values agree
already minimises `f - gA`. Only weak duality is used. -/
theorem theorem_31_3_iInf {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    {x : Rn n} {z : Rn m}
    (h : f x - g (A x)
      = concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z)) :
    (⨅ w, f w - g (A w)) = f x - g (A x) :=
  iInf_sub_comp_eq_of_sub_eq (isAdjointPair_adjoint A) h

/-- **Rockafellar, Theorem 31.3** (13467), second consequence: the same pair maximises
`g* - f*A*`. -/
theorem theorem_31_3_iSup {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    {x : Rn n} {z : Rn m}
    (h : f x - g (A x)
      = concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z)) :
    (⨆ w : Rn m, concaveConj (pairing m) g w - conj (pairing n) f (LinearMap.adjoint A w))
      = concaveConj (pairing m) g z - conj (pairing n) f (LinearMap.adjoint A z) :=
  iSup_sub_comp_eq_of_sub_eq (isAdjointPair_adjoint A) h

/-- **Rockafellar, Theorem 31.3** (13567), the case of Fenchel's duality theorem itself: with `A`
the identity the Kuhn–Tucker conditions reduce to `x* ∈ ∂f(x)` and `x ∈ ∂g*(x*)`.

Specialises `sub_eq_concaveConj_sub_conj_iff`. -/
theorem theorem_31_3_id {f g : Rn n → EReal} (hpf : Proper f) (hpg : ProperConcave g)
    {x y : Rn n} :
    f x - g x = concaveConj (pairing n) g y - conj (pairing n) f y ↔
      y ∈ subgradient (pairing n) f x ∧ -y ∈ subgradient (pairing n) (fun z => -(g z)) x :=
  sub_eq_concaveConj_sub_conj_iff hpf (properConcave_iff_proper_neg.1 hpg)

/-- **Rockafellar, Corollary 31.3.1** (13517): assume the notation of Theorem 31.3 and that the
image of `ri (dom f)` under `A` meets `ri (dom g)`. Then `x` minimises `f - gA` if and only if some
`u*` makes `(x, u*)` a Kuhn–Tucker pair.

The book's one-line proof is "Apply Corollary 31.2.1", and that is literally what happens: the
forward direction consumes the *attainment* clause of Corollary 31.2.1(a), the backward direction
only weak duality. Specialises `iInf_sub_comp_eq_iff_exists_kuhnTucker`. -/
theorem corollary_31_3_1 {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : Proper f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxg : A x₀ ∈ ri (domConcave g)) (x : Rn n) :
    (⨅ w, f w - g (A w)) = f x - g (A x) ↔
      ∃ z : Rn m, LinearMap.adjoint A z ∈ subgradient (pairing n) f x ∧
        -z ∈ subgradient (pairing m) (fun w => -(g w)) (A x) :=
  iInf_sub_comp_eq_iff_exists_kuhnTucker (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg) x

/-- **Rockafellar, Corollary 31.3.1** (13517) at the identity, which is the statement Fenchel's
duality theorem itself carries: `x` minimises `f - g` exactly when it carries a Kuhn–Tucker pair.

Specialises `iInf_sub_eq_iff_exists_kuhnTucker`. -/
theorem corollary_31_3_1_id {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (domConcave g)) (x : Rn n) :
    (⨅ z, f z - g z) = f x - g x ↔
      ∃ y : Rn n, y ∈ subgradient (pairing n) f x ∧
        -y ∈ subgradient (pairing n) (fun z => -(g z)) x :=
  iInf_sub_eq_iff_exists_kuhnTucker (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg) x

/-! ### Theorem 31.4: minimising a convex function over a convex cone

Rockafellar's `K*` is `-(polarCone (pairing n) K)`. `Set` negation is a preimage, so `y ∈ -K°`
unfolds to `-y ∈ K°`; `theorem_31_4_dualCone` states the useful form. There is no separate name for
`K*` here: the backbone writes it out, and inventing one would put a surface definition between
every statement and the lemma that proves it. -/

/-- **Rockafellar, Theorem 31.4** (13578), the definition of the dual cone:
`K* = {x* | ⟨x*, x⟩ ≥ 0 for all x ∈ K}` is the negative of the polar cone `K°`.

Specialises `mem_neg_polarCone`; the arguments are in the backbone's orientation, and
`pairing_comm` turns them round. -/
theorem theorem_31_4_dualCone {K : Set (Rn n)} {y : Rn n} :
    y ∈ -(polarCone (pairing n) K) ↔ ∀ z ∈ K, (0 : ℝ) ≤ pairing n z y :=
  mem_neg_polarCone

/-- Rockafellar's condition (a) of Theorem 31.4 makes `f` and `δ(· | K)` add exactly. -/
private theorem isExactSum_indicatorFn_of_relint {B : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ}
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ConvexFn f) (hpf : Proper f) (hK : Convex ℝ K) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxK : x₀ ∈ ri K) : IsExactSum B f (indicatorFn K) :=
  IsExactSum.of_relint hf hpf (convexFn_indicatorFn.2 hK)
    ⟨⟨x₀, by rw [dom_indicatorFn]; exact intrinsicInterior_subset hxK⟩, indicatorFn_ne_bot K⟩
    hxf (by rwa [dom_indicatorFn])

/-- Rockafellar's condition (a) of Theorem 31.4 for a **polyhedral** `K`: `ri K` becomes `K`. -/
private theorem isExactSum_indicatorFn_of_polyhedral {B : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ}
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ConvexFn f) (hpf : Proper f) (hK : Polyhedral K) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxK : x₀ ∈ K) : IsExactSum B f (indicatorFn K) :=
  (IsExactSum.of_polyhedral (polyhedralFn_indicatorFn hK)
    ⟨⟨x₀, by rwa [dom_indicatorFn]⟩, indicatorFn_ne_bot K⟩ hf hpf
    (by rwa [dom_indicatorFn]) hxf).symm

/-- The negative of a polyhedral set is polyhedral: `-S` is `S` pulled back along `-id`. -/
private theorem polyhedral_neg_set {S : Set (Rn n)} (hS : Polyhedral S) : Polyhedral (-S) := by
  have h : (-S) = (-LinearMap.id : Rn n →ₗ[ℝ] Rn n) ⁻¹' S := rfl
  rw [h]
  exact Polyhedral.comap hS _

/-- **`K*` is polyhedral when `K` is** — for a cone, the polar cone is the polar *set*
(`polarCone_eq_polarSet_of_isCone`), which is polyhedral by **Corollary 19.2.2**, and negation
preserves polyhedrality. -/
private theorem polyhedral_neg_polarCone {K : Set (Rn n)} (hK : Polyhedral K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) : Polyhedral (-(polarCone (pairing n) K)) := by
  rw [polarCone_eq_polarSet_of_isCone hcone]
  exact polyhedral_neg_set (corollary_19_2_2 hK)

/-- **Rockafellar, Theorem 31.4** (13575) under condition **(a)** (13589): for a closed proper
convex `f` and a nonempty convex cone `K` whose relative interior meets `ri (dom f)`,

`inf {f(x) | x ∈ K} = -inf {f*(x*) | x* ∈ K*}`.

Closedness of `f` and of `K` are not used here; they belong to condition (b). Specialises
`iInf_mem_eq_neg_iInf_mem_neg_polarCone`. -/
theorem theorem_31_4_a {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f) (hpf : Proper f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hxK : x₀ ∈ ri K) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w) :=
  iInf_mem_eq_neg_iInf_mem_neg_polarCone
    (isExactSum_indicatorFn_of_relint (B := pairing n) hf hpf hK hxf hxK) hcone hne

/-- **Rockafellar, Theorem 31.4** (13595): under (a) the infimum of `f*` over `K*` is attained.
Specialises `exists_mem_neg_polarCone_conj_eq_iInf`. -/
theorem theorem_31_4_a_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : Proper f) (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hxK : x₀ ∈ ri K) :
    ∃ y ∈ -(polarCone (pairing n) K), conj (pairing n) f y
      = ⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w :=
  exists_mem_neg_polarCone_conj_eq_iInf
    (isExactSum_indicatorFn_of_relint (B := pairing n) hf hpf hK hxf hxK) hcone hne

/-- **Rockafellar, Theorem 31.4** (13595), the polyhedral strengthening of (a): "if `K` is
polyhedral, `ri K` and `ri K*` can be replaced by `K` and `K*` in (a) and (b)". -/
theorem theorem_31_4_a_polyhedral {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : Proper f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hxK : x₀ ∈ K) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w) :=
  iInf_mem_eq_neg_iInf_mem_neg_polarCone
    (isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf hK hxf hxK) hcone hne

/-- **Rockafellar, Theorem 31.4** (13595): under the polyhedral form of (a) the dual infimum is
still attained. -/
theorem theorem_31_4_a_polyhedral_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : Proper f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hxK : x₀ ∈ K) :
    ∃ y ∈ -(polarCone (pairing n) K), conj (pairing n) f y
      = ⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w :=
  exists_mem_neg_polarCone_conj_eq_iInf
    (isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf hK hxf hxK) hcone hne

/-- **Rockafellar, Theorem 31.4** (13575) under condition **(b)** (13591): the same equality, with
`ri (dom f*)` meeting `ri K*`.

This is condition (a) read on the dual pair: Theorem 31.4 applied to `f*` and `K*`, closed up by
`K** = K` (**Theorem 14.1**, `neg_polarCone_neg_polarCone`) and `f** = f` (Fenchel–Moreau). Both
are where `f` closed and `K` closed are used. -/
theorem theorem_31_4_b {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K)
    {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyK : y₀ ∈ ri (-(polarCone (pairing n) K))) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w) := by
  have hex : IsExactSum (pairing n).flip (conj (pairing n) f)
      (indicatorFn (-(polarCone (pairing n) K))) :=
    isExactSum_indicatorFn_of_relint (B := (pairing n).flip) (convexFn_conj (pairing n) f)
      (proper_conj (B := pairing n) hf) (convex_neg_polarCone (pairing n) K) hyf hyK
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex
    (fun a ha => smul_neg_polarCone (pairing n) K a ha) (neg_polarCone_nonempty (pairing n) K)
  rw [neg_polarCone_neg_polarCone hK hcone hne hcl,
    show conj (pairing n).flip (conj (pairing n) f) = f from biconj_eq_self hf.convex hf.closed]
    at h
  rw [h, neg_neg]

/-- **Rockafellar, Theorem 31.4** (13595): under (b) the infimum of `f` over `K` is attained.
Specialises `exists_mem_eq_iInf_of_isExactSum_conj`. -/
theorem theorem_31_4_b_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K)
    {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyK : y₀ ∈ ri (-(polarCone (pairing n) K))) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z :=
  exists_mem_eq_iInf_of_isExactSum_conj (biconj_eq_self hf.convex hf.closed)
    (isExactSum_indicatorFn_of_relint (B := (pairing n).flip) (convexFn_conj (pairing n) f)
      (proper_conj (B := pairing n) hf) (convex_neg_polarCone (pairing n) K) hyf hyK)
    hK hcone hne hcl

/-- **Rockafellar, Theorem 31.4** (13595), the polyhedral strengthening of (b): `ri K*` becomes
`K*`. Polyhedrality of `K` is what makes `K*` polyhedral (`polyhedral_neg_polarCone`), and a
polyhedral set is closed, so the closedness hypothesis is free. -/
theorem theorem_31_4_b_polyhedral {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (dom (conj (pairing n) f))) (hyK : y₀ ∈ -(polarCone (pairing n) K)) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), conj (pairing n) f w) := by
  have hex : IsExactSum (pairing n).flip (conj (pairing n) f)
      (indicatorFn (-(polarCone (pairing n) K))) :=
    isExactSum_indicatorFn_of_polyhedral (B := (pairing n).flip) (convexFn_conj (pairing n) f)
      (proper_conj (B := pairing n) hf) (polyhedral_neg_polarCone hK hcone) hyf hyK
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex
    (fun a ha => smul_neg_polarCone (pairing n) K a ha) (neg_polarCone_nonempty (pairing n) K)
  rw [neg_polarCone_neg_polarCone hK.convex hcone hne (Polyhedral.isClosed hK),
    show conj (pairing n).flip (conj (pairing n) f) = f from biconj_eq_self hf.convex hf.closed]
    at h
  rw [h, neg_neg]

/-- **Rockafellar, Theorem 31.4** (13595): under the polyhedral form of (b) the primal infimum is
still attained. -/
theorem theorem_31_4_b_polyhedral_attained {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ClosedProperConvexFn f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyK : y₀ ∈ -(polarCone (pairing n) K)) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z :=
  exists_mem_eq_iInf_of_isExactSum_conj (biconj_eq_self hf.convex hf.closed)
    (isExactSum_indicatorFn_of_polyhedral (B := (pairing n).flip) (convexFn_conj (pairing n) f)
      (proper_conj (B := pairing n) hf) (polyhedral_neg_polarCone hK hcone) hyf hyK)
    hK.convex hcone hne (Polyhedral.isClosed hK)

/-- **Rockafellar, Theorem 31.4** (13603), the optimality conditions: for `x ∈ K` and `x* ∈ K*`,
the primal and dual values agree — `f(x) = -f*(x*)` — exactly when `x* ∈ ∂f(x)` and
`⟨x, x*⟩ = 0`.

Rockafellar reads this off Theorem 31.3's Kuhn–Tucker conditions at `g = -δ(· | K)`, where
`x ∈ ∂g*(x*)` unfolds into the three conditions `x ∈ K`, `x* ∈ K*`, `⟨x, x*⟩ = 0`. Specialises
`add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero`. -/
theorem theorem_31_4_optimality {f : Rn n → EReal} {K : Set (Rn n)} (hpf : Proper f) {x y : Rn n}
    (hxK : x ∈ K) (hyK : y ∈ -(polarCone (pairing n) K)) :
    f x + conj (pairing n) f y = 0 ↔
      y ∈ subgradient (pairing n) f x ∧ (pairing n x y : ℝ) = 0 :=
  add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero hpf hxK hyK

/-- **Rockafellar, Theorem 31.4** (13603): the optimality conditions make `x` optimal for the
primal cone program. -/
theorem theorem_31_4_optimality_primal {f : Rn n → EReal} {K : Set (Rn n)} {x y : Rn n}
    (hyK : y ∈ -(polarCone (pairing n) K)) (hy : y ∈ subgradient (pairing n) f x)
    (hxy : (pairing n x y : ℝ) = 0) {z : Rn n} (hz : z ∈ K) : f x ≤ f z :=
  forall_le_of_mem_subgradient_of_pairing_eq_zero hyK hy hxy hz

/-- **Rockafellar, Theorem 31.4** (13603): the optimality conditions make `x*` optimal for the dual
cone program. -/
theorem theorem_31_4_optimality_dual {f : Rn n → EReal} {K : Set (Rn n)} (hpf : Proper f)
    {x y : Rn n} (hxK : x ∈ K) (hy : y ∈ subgradient (pairing n) f x)
    (hxy : (pairing n x y : ℝ) = 0) {w : Rn n} (hwK : w ∈ -(polarCone (pairing n) K)) :
    conj (pairing n) f y ≤ conj (pairing n) f w :=
  conj_le_conj_of_mem_subgradient_of_pairing_eq_zero hpf hxK hy hxy hwK

/-- **Rockafellar, Theorem 31.4**, weak duality: every dual value is below every primal value.
No hypothesis beyond `x ∈ K` and `x* ∈ K*`. -/
theorem theorem_31_4_weak {f : Rn n → EReal} {K : Set (Rn n)} {x : Rn n} (hxK : x ∈ K) {w : Rn n}
    (hwK : w ∈ -(polarCone (pairing n) K)) : -(conj (pairing n) f w) ≤ f x :=
  neg_conj_le_of_mem_neg_polarCone hxK hwK

/-! ### Corollary 31.4.1: the non-negative orthant

`Rockafellar.nonnegOrthant n` is the set `{z | z ≥ 0}` of §12. Rockafellar states Corollary 31.4.1's
conditions without a relative interior on the orthant side, which is the *polyhedral* form of
Theorem 31.4; `polyhedral_nonnegOrthant` is what licenses it. -/

/-- The non-negative orthant is polyhedral: it is cut out by the `n` inequalities `-ξⱼ ≤ 0`.
The coordinate functionals are produced inside the proof, so that no new name for them reaches the
statement. -/
private theorem polyhedral_nonnegOrthant (n : ℕ) : Polyhedral (nonnegOrthant n) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin n → (Rn n →ₗ[ℝ] ℝ), ∀ (j : Fin n) (x : Rn n), c j x = x j :=
    ⟨fun j => ⟨⟨fun x => x j, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine ⟨(Finset.univ : Finset (Fin n)).image fun j => (-(c j), (0 : ℝ)), ?_⟩
  ext x
  constructor
  · intro hx q hq
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    simpa [hc j x] using hx j
  · intro hx j
    have h := hx (-(c j), (0 : ℝ)) (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩)
    simpa [hc j x] using h

/-- The non-negative orthant is invariant under positive scaling, which is Rockafellar's cone
condition. -/
private theorem smul_nonnegOrthant (n : ℕ) {a : ℝ} (ha : 0 < a) :
    a • nonnegOrthant n = nonnegOrthant n := by
  ext z
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact mul_nonneg ha.le (hu j)
  · intro hz
    exact ⟨a⁻¹ • z, fun j => mul_nonneg (inv_nonneg.2 ha.le) (hz j),
      by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩

/-- **The orthant is self-dual**: `K* = -K° = {y | y ≥ 0}` for `K` the non-negative orthant.
`polarCone_nonnegOrthant` (**Theorem 14.1**, §14) gives `K°` as the *non-positive* orthant, and the
sign flip of Rockafellar's `K*` turns it back. -/
theorem neg_polarCone_nonnegOrthant (n : ℕ) :
    -(polarCone (pairing n) (nonnegOrthant n)) = nonnegOrthant n := by
  have h : polarCone (pairing n) (nonnegOrthant n) = {y : Rn n | ∀ i, y i ≤ 0} :=
    polarCone_nonnegOrthant
  rw [h]
  ext y
  constructor
  · intro hy j
    simpa using (Set.mem_neg.1 hy) j
  · intro hy
    exact Set.mem_neg.2 fun j => by simpa using hy j

/-- On the orthant the inner product vanishes exactly when every product of coordinates does: this
is the complementary-slackness reading of `⟨x, x*⟩ = 0` in Corollary 31.4.1. -/
private theorem pairing_eq_zero_iff_of_mem_nonnegOrthant {x y : Rn n} (hx : x ∈ nonnegOrthant n)
    (hy : y ∈ nonnegOrthant n) : (pairing n x y : ℝ) = 0 ↔ ∀ j, x j * y j = 0 := by
  rw [pairing_apply, inner_rn,
    Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hx j) (hy j)]
  exact ⟨fun h j => h j (Finset.mem_univ j), fun h j _ => h j⟩

/-- **Rockafellar, Corollary 31.4.1** (13623) under condition **(a)** (13633): for a closed proper
convex `f` on `ℝⁿ` with some `x ∈ ri (dom f)` satisfying `x ≥ 0`,

`inf {f(x) | x ≥ 0} = -inf {f*(x*) | x* ≥ 0}`.

This is Theorem 31.4 at the non-negative orthant, whose dual cone is itself
(`neg_polarCone_nonnegOrthant`). Rockafellar's condition asks only `x ≥ 0`, not `x ∈ ri K`, which
is the *polyhedral* form of Theorem 31.4 — the orthant is polyhedral. -/
theorem corollary_31_4_1_a {f : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (dom f)) (hx₀ : x₀ ∈ nonnegOrthant n) :
    (⨅ z ∈ nonnegOrthant n, f z)
      = -(⨅ w ∈ nonnegOrthant n, conj (pairing n) f w) := by
  have h := theorem_31_4_a_polyhedral hf hpf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hxf hx₀
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Rockafellar, Corollary 31.4.1** (13635): under (a) the second infimum is attained. -/
theorem corollary_31_4_1_a_attained {f : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hx₀ : x₀ ∈ nonnegOrthant n) :
    ∃ y ∈ nonnegOrthant n, conj (pairing n) f y
      = ⨅ w ∈ nonnegOrthant n, conj (pairing n) f w := by
  have h := theorem_31_4_a_polyhedral_attained hf hpf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hxf hx₀
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Rockafellar, Corollary 31.4.1** (13623) under condition **(b)** (13635): the same equality
from a point `x* ∈ ri (dom f*)` with `x* ≥ 0`. -/
theorem corollary_31_4_1_b {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (dom (conj (pairing n) f))) (hy₀ : y₀ ∈ nonnegOrthant n) :
    (⨅ z ∈ nonnegOrthant n, f z)
      = -(⨅ w ∈ nonnegOrthant n, conj (pairing n) f w) := by
  have h := theorem_31_4_b_polyhedral hf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hyf
    (by rw [neg_polarCone_nonnegOrthant]; exact hy₀)
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Rockafellar, Corollary 31.4.1** (13635): under (b) the *first* infimum is attained. -/
theorem corollary_31_4_1_b_attained {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (dom (conj (pairing n) f))) (hy₀ : y₀ ∈ nonnegOrthant n) :
    ∃ x ∈ nonnegOrthant n, f x = ⨅ z ∈ nonnegOrthant n, f z := by
  refine theorem_31_4_b_polyhedral_attained hf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ (y₀ := y₀) hyf ?_
  rw [neg_polarCone_nonnegOrthant]
  exact hy₀

/-- **Rockafellar, Corollary 31.4.1** (13641), the complementary-slackness conditions: the two
infima are the negatives of each other and attained at `x` and `x*` exactly when `x* ∈ ∂f(x)` and
`ξⱼ ≥ 0`, `ξⱼ* ≥ 0`, `ξⱼ ξⱼ* = 0` for every `j`.

Theorem 31.4's `⟨x, x*⟩ = 0` becomes the coordinatewise condition because both vectors are
non-negative (`pairing_eq_zero_iff_of_mem_nonnegOrthant`). -/
theorem corollary_31_4_1_optimality {f : Rn n → EReal} (hpf : Proper f) {x y : Rn n}
    (hx : x ∈ nonnegOrthant n) (hy : y ∈ nonnegOrthant n) :
    f x + conj (pairing n) f y = 0 ↔
      y ∈ subgradient (pairing n) f x ∧ ∀ j, x j * y j = 0 := by
  have hyK : y ∈ -(polarCone (pairing n) (nonnegOrthant n)) := by
    rw [neg_polarCone_nonnegOrthant]; exact hy
  rw [theorem_31_4_optimality hpf hx hyK, pairing_eq_zero_iff_of_mem_nonnegOrthant hx hy]

/-! ### Corollary 31.4.2: a subspace -/

/-- **The polar cone of a subspace is its orthogonal complement.** Rockafellar writes `L⊥`; the
backbone's `polarCone` of a subspace is the annihilator (`polarCone_coe_submodule'`), and on `ℝⁿ`
the annihilator *is* `Lᗮ`. -/
theorem polarCone_coe_submodule_eq_orthogonal (M : Submodule ℝ (Rn n)) :
    polarCone (pairing n) (M : Set (Rn n)) = ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
  rw [polarCone_coe_submodule' (pairing n) M]
  ext y
  constructor
  · intro h
    exact (Submodule.mem_orthogonal M y).2 fun u hu => by
      have hu' : pairing n u y = 0 := h u hu
      rwa [pairing_apply] at hu'
  · intro h u hu
    have h' := (Submodule.mem_orthogonal M y).1 h u hu
    rwa [← pairing_apply] at h'

/-- **Rockafellar, Corollary 31.4.2** (13643) under condition **(a)** (13653): for a closed proper
convex `f` and a subspace `L` meeting `ri (dom f)`,

`inf {f(x) | x ∈ L} = -inf {f*(x*) | x* ∈ L⊥}`.

This is Theorem 31.4 with `K = L`, where the dual cone `K* = -K°` collapses to `L⊥`. A subspace is
polyhedral, which is why Rockafellar's condition needs no relative interior on the `L` side. -/
theorem corollary_31_4_2_a {f : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    {M : Submodule ℝ (Rn n)} {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hxM : x₀ ∈ M) :
    (⨅ z ∈ (M : Set (Rn n)), f z)
      = -(⨅ w ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), conj (pairing n) f w) := by
  have hex := isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf
    (polyhedral_coe_submodule M) hxf hxM
  have h := iInf_mem_submodule_eq_neg_iInf_mem_polarCone hex
  rwa [polarCone_coe_submodule_eq_orthogonal] at h

/-- **Rockafellar, Corollary 31.4.2** (13655): under (a) the infimum of `f*` on `L⊥` is
attained. -/
theorem corollary_31_4_2_a_attained {f : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    {M : Submodule ℝ (Rn n)} {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f)) (hxM : x₀ ∈ M) :
    ∃ y ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), conj (pairing n) f y
      = ⨅ w ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), conj (pairing n) f w := by
  have h := theorem_31_4_a_polyhedral_attained hf hpf (polyhedral_coe_submodule M)
    (fun a ha => smul_coe_submodule M ha) ⟨0, M.zero_mem⟩ hxf hxM
  rwa [neg_polarCone_coe_submodule, polarCone_coe_submodule_eq_orthogonal] at h

/-- **Rockafellar, Corollary 31.4.2** (13655): under condition **(b)** (13655) the infimum of `f`
on `L` is attained. -/
theorem corollary_31_4_2_b_attained {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    {M : Submodule ℝ (Rn n)} {y₀ : Rn n} (hyf : y₀ ∈ ri (dom (conj (pairing n) f)))
    (hyM : y₀ ∈ Mᗮ) :
    ∃ x ∈ (M : Set (Rn n)), f x = ⨅ z ∈ (M : Set (Rn n)), f z := by
  refine theorem_31_4_b_polyhedral_attained hf (polyhedral_coe_submodule M)
    (fun a ha => smul_coe_submodule M ha) ⟨0, M.zero_mem⟩ (y₀ := y₀) hyf ?_
  rw [neg_polarCone_coe_submodule, polarCone_coe_submodule_eq_orthogonal]
  exact hyM

/-- **Rockafellar, Corollary 31.4.2** (13658), the optimality conditions: over a subspace the
orthogonality `⟨x, x*⟩ = 0` of Theorem 31.4 is automatic, so `x` and `x*` are jointly optimal
exactly when `x ∈ L`, `x* ∈ L⊥` and `x* ∈ ∂f(x)`. -/
theorem corollary_31_4_2_optimality {f : Rn n → EReal} (hpf : Proper f)
    {M : Submodule ℝ (Rn n)} {x y : Rn n} (hxM : x ∈ M) (hyM : y ∈ Mᗮ) :
    f x + conj (pairing n) f y = 0 ↔ y ∈ subgradient (pairing n) f x := by
  refine add_conj_eq_zero_iff_mem_subgradient_of_mem_submodule hpf hxM ?_
  rw [polarCone_coe_submodule_eq_orthogonal]
  exact hyM

/-! ### Corollary 31.4.3: the duality between a co-finite `h` and `h*` -/

/-- **Rockafellar, Corollary 31.4.3** (13673): for `h` convex on `ℝⁿ`, finite everywhere and
co-finite, and `K` a nonempty convex cone,

`inf_{x ∈ K} {h(z + x) - ⟨z*, x⟩} + inf_{x* ∈ K*} {h*(z* + x*) - ⟨z, x*⟩} = ⟨z, z*⟩`.

The whole proof is **Theorem 12.3** followed by Theorem 31.4: `f = h(z + ·) - ⟨·, z*⟩` has
`dom f = ℝⁿ` and `dom f* = ℝⁿ`, so both of Rockafellar's conditions hold in their strongest form.
Specialises `iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing`.

Closedness of `K` — which the book assumes for the whole corollary — is needed only for the
attainment of the *first* infimum; the identity and both finiteness clauses hold for any nonempty
convex cone. -/
theorem corollary_31_4_3 {h : Rn n → EReal} (hcof : Cofinite h) (hdom : dom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (z z' : Rn n) :
    (⨅ x ∈ K, (h (z + x) - ((pairing n x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone (pairing n) K),
            (conj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal)))
      = ((pairing n z z' : ℝ) : EReal) :=
  iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing hcof hdom hconv hcone hne z z'

/-- **Rockafellar, Corollary 31.4.3** (13673): the first infimum is finite. -/
theorem corollary_31_4_3_iInf_eq_coe {h : Rn n → EReal} (hcof : Cofinite h) (hdom : dom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (z z' : Rn n) :
    ∃ s : ℝ, (⨅ x ∈ K, (h (z + x) - ((pairing n x z' : ℝ) : EReal))) = (s : EReal) :=
  exists_iInf_mem_eq_coe_of_cofinite hcof hdom hconv hcone hne z z'

/-- **Rockafellar, Corollary 31.4.3** (13673): the second infimum is finite. -/
theorem corollary_31_4_3_iInf_dual_eq_coe {h : Rn n → EReal} (hcof : Cofinite h)
    (hdom : dom h = univ) {K : Set (Rn n)} (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z z' : Rn n) :
    ∃ r : ℝ, (⨅ w ∈ -(polarCone (pairing n) K),
      (conj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal))) = (r : EReal) :=
  exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite hcof hdom hconv hcone hne z z'

/-- **Rockafellar, Corollary 31.4.3** (13673): the first infimum is attained. This is the clause
that needs `K` closed. -/
theorem corollary_31_4_3_attained {h : Rn n → EReal} (hcof : Cofinite h) (hdom : dom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (hcl : IsClosed K) (z z' : Rn n) :
    ∃ x ∈ K, h (z + x) - ((pairing n x z' : ℝ) : EReal)
      = ⨅ u ∈ K, (h (z + u) - ((pairing n u z' : ℝ) : EReal)) :=
  exists_iInf_mem_eq_of_cofinite hcof hdom hconv hcone hne hcl z z'

/-- **Rockafellar, Corollary 31.4.3** (13673): the second infimum is attained. Co-finiteness is not
needed for this half, nor is closedness of `K`. -/
theorem corollary_31_4_3_dual_attained {h : Rn n → EReal} (hcof : Cofinite h)
    (hdom : dom h = univ) {K : Set (Rn n)} (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z z' : Rn n) :
    ∃ w ∈ -(polarCone (pairing n) K),
      conj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal)
        = ⨅ v ∈ -(polarCone (pairing n) K),
            (conj (pairing n) h (z' + v) - ((pairing n z v : ℝ) : EReal)) :=
  exists_iInf_mem_neg_polarCone_eq_of_cofinite hcof hdom hconv hcone hne z z'

/-! ### Theorem 31.5 (Moreau), proximations, and the two corollaries

`w` is the backbone's `quadFn (pairing n)`, and `theorem_31_5_quadFn` is the bridge to
Rockafellar's `w(z) = ½|z|²`. `□` is `infConv`, `prox (z ∣ f)` is `prox (pairing n) f z`, and
`moreauObj (pairing n) f z` is the objective `x ↦ f(x) + w(z - x)` whose infimum defines
`(f □ w)(z)`. -/

/-- **Rockafellar, Theorem 31.5** (13735): `w(z) = ½|z|²`, in the book's own notation. Specialises
`quadFn_innerL`. -/
theorem theorem_31_5_quadFn (z : Rn n) : quadFn (pairing n) z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal) :=
  quadFn_innerL z

/-- **Rockafellar, Theorem 31.5 (Moreau)** (13735), the identity `(f □ w) + (f* □ w) = w` as an
equation between functions.

The backbone's proof is Theorem 27.1(a) applied to `f + w(z - ·)`, with `IsExactSum.conj_add_apply`
splitting the conjugate of that sum at the origin — no separation and no `ri`. Specialises
`moreau_add`. -/
theorem theorem_31_5 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    infConv f (quadFn (pairing n)) + infConv (conj (pairing n) f) (quadFn (pairing n))
      = quadFn (pairing n) :=
  funext fun z => moreau_add hf z

/-- **Rockafellar, Theorem 31.5** (13741), the identity written out at a point:
`inf_x {f(x) + w(z - x)} + inf_{x*} {f*(x*) + w(z - x*)} = w(z)`. -/
theorem theorem_31_5_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    (⨅ x, (f x + quadFn (pairing n) (z - x)))
        + (⨅ y, (conj (pairing n) f y + quadFn (pairing n) (z - y)))
      = quadFn (pairing n) z := by
  rw [← infConv_quadFn_apply hf.proper.ne_bot z,
    ← infConv_quadFn_apply (conj_ne_bot hf.proper.dom_nonempty) z]
  exact moreau_add hf z

/-- **Rockafellar, Theorem 31.5** (13741): "both infima are finite". Specialises
`infConv_quadFn_ne_bot` and `infConv_quadFn_ne_top`. -/
theorem theorem_31_5_finite {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃ r : ℝ, infConv f (quadFn (pairing n)) z = (r : EReal) :=
  Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (infConv_quadFn_ne_bot hf z)
    (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- **Rockafellar, Theorem 31.5** (13741): the dual infimum is finite too. -/
theorem theorem_31_5_finite_conj {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃ r : ℝ, infConv (conj (pairing n) f) (quadFn (pairing n)) z = (r : EReal) :=
  Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (infConv_conj_quadFn_ne_bot hf z)
    (lt_top_iff_ne_top.2 (infConv_conj_quadFn_ne_top hf z))

/-- **Rockafellar, Theorem 31.5** (13747): the two infima are *uniquely* attained, and the unique
minimisers are the unique pair with `z = x + x*` and `x* ∈ ∂f(x)`.

The backbone's uniqueness is monotonicity of `∂f` (Theorem 24.8) at the two pairs, not strict
convexity of `w`; attainment is Theorem 27.2, through the recession function of `f + w(z - ·)`.
Specialises `existsUnique_sub_mem_subgradient`. -/
theorem theorem_31_5_existsUnique {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃! p : Rn n × Rn n, p.1 + p.2 = z ∧ p.2 ∈ subgradient (pairing n) f p.1 := by
  obtain ⟨x, hx, huniq⟩ := existsUnique_sub_mem_subgradient (B := pairing n) hf z
  refine ⟨(x, z - x), ⟨by module, hx⟩, ?_⟩
  rintro ⟨u, v⟩ ⟨hsum, hmem⟩
  have hsum' : u + v = z := hsum
  have hv : v = z - u := by rw [← hsum']; abel
  subst hv
  have hu : u = x := huniq u hmem
  subst hu
  rfl

/-- **Rockafellar, Theorem 31.5** (13750), the characterisation of the minimiser: `x` attains
`inf_x {f(x) + w(z - x)}` exactly when `z - x ∈ ∂f(x)`. Specialises
`mem_argmin_moreauObj_iff`. -/
theorem theorem_31_5_argmin_iff {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z x : Rn n) :
    x ∈ argmin (moreauObj (pairing n) f z) ↔ z - x ∈ subgradient (pairing n) f x :=
  mem_argmin_moreauObj_iff hf z x

/-- **Rockafellar, Theorem 31.5** (13823): `prox (z ∣ f)` is the unique minimiser, so the minimum
set is a singleton. Specialises `argmin_moreauObj_eq_singleton`. -/
theorem theorem_31_5_argmin_eq {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    argmin (moreauObj (pairing n) f z) = {prox (pairing n) f z} :=
  argmin_moreauObj_eq_singleton hf z

/-- **Rockafellar, §31** (13823), the defining property of the **proximation**: `prox (z ∣ f)` is
the unique `x` with `z - x ∈ ∂f(x)`. Specialises `prox_eq_iff`. -/
theorem prox_eq_iff_sub_mem_subgradient {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (z x : Rn n) : prox (pairing n) f z = x ↔ z - x ∈ subgradient (pairing n) f x :=
  prox_eq_iff hf z x

/-- **Rockafellar, §31** (13820): the decomposition `z = prox (z ∣ f) + prox (z ∣ f*)`. -/
theorem prox_add_prox_conj_eq {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    prox (pairing n) f z + prox (pairing n) (conj (pairing n) f) z = z :=
  prox_add_prox_conj hf z

/-- **Rockafellar, §31** (13838): `prox (z ∣ f*) = z - prox (z ∣ f)`. Specialises
`prox_conj_eq`. -/
theorem prox_conj_eq_sub {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    prox (pairing n) (conj (pairing n) f) z = z - prox (pairing n) f z :=
  prox_conj_eq hf z

/-- **Rockafellar, Theorem 31.5** (13756): `x* = ∇(f □ w)(z)`, the gradient formula for the
Moreau envelope of `f`. The subdifferential of `f □ w` is the single point `prox (z ∣ f*)`, so
Theorem 25.1's converse upgrades it to a gradient. Specialises `gradient_infConv_quadFn`. -/
theorem theorem_31_5_gradient {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    gradient (fun u => (infConv f (quadFn (pairing n)) u).toReal) z
      = z - prox (pairing n) f z :=
  gradient_infConv_quadFn hf z

/-- **Rockafellar, Theorem 31.5** (13756): `x = ∇(f* □ w)(z)`. Specialises
`gradient_infConv_conj_quadFn`. -/
theorem theorem_31_5_gradient_conj {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    gradient (fun u => (infConv (conj (pairing n) f) (quadFn (pairing n)) u).toReal) z
      = prox (pairing n) f z :=
  gradient_infConv_conj_quadFn hf z

/-- **Rockafellar, §31** (13841): `prox (· ∣ f)` is the gradient mapping of the differentiable
convex function `f* □ w`, hence continuous (Corollary 25.5.1). Specialises `continuous_prox`. -/
theorem prox_continuous {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Continuous (prox (pairing n) f) :=
  continuous_prox hf

/-- **The contraction property of `prox`** (13851–13885). Rockafellar states and proves it in
*unnumbered running text*, and it is what Corollary 31.5.2 is built on, so it gets a name here:

`|prox (z₁ ∣ f) - prox (z₀ ∣ f)| ≤ |z₁ - z₀|` for all `z₀`, `z₁`.

The book's argument is exactly the backbone's: with `xᵢ = prox (zᵢ ∣ f)` and `xᵢ* = zᵢ - xᵢ`,
expanding `|z₁ - z₀|²` and using monotonicity of `∂f` (end of §24) to drop the cross term gives
`|z₁ - z₀|² ≥ |x₁ - x₀|²`. Specialises `dist_prox_prox_le`, which is
`pairingNorm_prox_sub_le` read at the inner product, where the pairing norm *is* the norm. -/
theorem prox_contraction {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z₀ z₁ : Rn n) :
    ‖prox (pairing n) f z₁ - prox (pairing n) f z₀‖ ≤ ‖z₁ - z₀‖ := by
  have h := dist_prox_prox_le (E := Rn n) hf z₁ z₀
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- **The contraction property of `prox`** (13851–13885), packaged as a Lipschitz bound with
constant `1`. Specialises `lipschitzWith_prox`. -/
theorem prox_lipschitzWith_one {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    LipschitzWith 1 (prox (pairing n) f) :=
  lipschitzWith_prox hf

/-- **Rockafellar, §31** (13849): "the range of `prox (· ∣ f)` is of course `dom ∂f`". Unnumbered,
and one line in each direction: `z - prox (z ∣ f) ∈ ∂f (prox (z ∣ f))` gives `⊆`, and a subgradient
`y ∈ ∂f(x)` exhibits `x` as `prox (x + y ∣ f)`. -/
theorem range_prox {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Set.range (prox (pairing n) f) = {x : Rn n | (subgradient (pairing n) f x).Nonempty} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z - prox (pairing n) f z, sub_prox_mem_subgradient hf z⟩
  · rintro ⟨y, hy⟩
    refine ⟨x + y, prox_eq_of_sub_mem_subgradient hf ?_⟩
    rwa [add_sub_cancel_left]

/-- **Rockafellar, Corollary 31.5.1** (13889) — *stated in the book with no proof at all*, like
Corollary 23.5.1. The mapping `(x, x*) ↦ x + x*` is one-to-one from the graph of `∂f` onto `ℝⁿ`
and continuous in both directions, so the graph of `∂f` is homeomorphic to `ℝⁿ`.

A `Homeomorph` *is* that statement: bijective, continuous, with continuous inverse. Bijectivity is
Theorem 31.5 (`theorem_31_5_existsUnique`); continuity of the inverse
`z ↦ (prox (z ∣ f), z - prox (z ∣ f))` is the contraction property `prox_contraction`, and that is
the whole analytic content — Theorem 24.4 (closedness of the graph) is not used. Specialises
`subgradientRelHomeomorph`. -/
noncomputable def corollary_31_5_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    ↥(subgradientRel (pairing n) f) ≃ₜ Rn n :=
  subgradientRelHomeomorph hf

@[simp] theorem corollary_31_5_1_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (p : ↥(subgradientRel (pairing n) f)) : corollary_31_5_1 hf p = p.1.1 + p.1.2 := rfl

@[simp] theorem corollary_31_5_1_symm_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (z : Rn n) :
    (corollary_31_5_1 hf).symm z
      = ⟨(prox (pairing n) f z, z - prox (pairing n) f z), sub_prox_mem_subgradient hf z⟩ :=
  rfl

/-- **Rockafellar, Corollary 31.5.2** (13897): `∂f` is a *maximal monotone* mapping from `ℝⁿ` to
`ℝⁿ`.

Rockafellar's proof is the one the backbone runs: given `(y, y*)` outside the graph, Theorem 31.5
produces `(x, x*)` in the graph with `x + x* = y + y*`, and then
`⟨y - x, y* - x*⟩ = -|y - x|² < 0`. This is *monotone* maximality, not the *cyclically* monotone
maximality of Theorem 24.9; neither implies the other, and line 9631 of the book warns explicitly
that this one does not follow from that one. Specialises
`isMaximalMonotoneRel_subgradientRel`. -/
theorem corollary_31_5_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    IsMaximalMonotoneRel (pairing n) (subgradientRel (pairing n) f) :=
  isMaximalMonotoneRel_subgradientRel hf
/-! ### Theorem 31.2: Fenchel's problem as a convex program

Rockafellar (13257) exhibits the Fenchel problem as the convex program of §29 attached to the
bifunction `(F u)(x) = f x - g (A x + u)`: the perturbation translates the concave function. The
whole machinery of §§29–30 then applies, and Corollary 31.2.1 is what Theorem 30.4 and
Corollary 30.5.2 give back. -/

/-- The **Fenchel bifunction** `(F u)(x) = f x - g (A x + u)` of Rockafellar's line 13260: the
Fenchel problem `inf (f - g ∘ A)` perturbed by translating the concave function.

`fenchelBifun_apply` is the bridge back to the displayed formula. -/
noncomputable def fenchelBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal) :
    Bifun (Rn m) (Rn n) := fun u x => f x - g (A x + u)

@[simp] theorem fenchelBifun_apply (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal)
    (u : Rn m) (x : Rn n) : fenchelBifun A f g u x = f x - g (A x + u) := rfl

/-- The linear map `(u, x) ↦ A x + u` whose preimage of `-g` is the second summand of
`graphFn (fenchelBifun A f g)`. -/
private def shiftLin (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) →ₗ[ℝ] Rn m :=
  A ∘ₗ LinearMap.snd ℝ (Rn m) (Rn n) + LinearMap.fst ℝ (Rn m) (Rn n)

private theorem shiftLin_apply (A : Rn n →ₗ[ℝ] Rn m) (p : Rn m × Rn n) :
    shiftLin A p = A p.2 + p.1 := rfl

/-- The graph function of the Fenchel bifunction is a sum of two linear preimages: `f` pulled back
along the projection, and `-g` pulled back along `(u, x) ↦ A x + u`. -/
private theorem graphFn_fenchelBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal)
    (g : Rn m → EReal) :
    graphFn (fenchelBifun A f g)
      = compLin f (LinearMap.snd ℝ (Rn m) (Rn n)) + compLin (fun w => -(g w)) (shiftLin A) := rfl

/-- **Rockafellar, Theorem 31.2** (13263), first assertion: `F` is a convex bifunction. -/
theorem theorem_31_2_convex (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ConvexFn f) (hpf : Proper f) (hg : ConcaveFn g) (hpg : ProperConcave g) :
    ConvexBifun (fenchelBifun A f g) := by
  rw [convexBifun_iff, graphFn_fenchelBifun]
  refine ConvexFn.add (convexFn_compLin _ hf)
    (convexFn_compLin _ (concaveFn_iff_convexFn_neg.1 hg)) (fun p => hpf.ne_bot _) fun p => ?_
  simpa using hpg.ne_top (shiftLin A p)

/-- **Rockafellar, Theorem 31.2** (13263), second assertion: `F` is proper. Properness is
automatic — it needs no relative-interior hypothesis, only a point of `dom f` and a point of
`dom g`, which `Proper` and `ProperConcave` supply. -/
theorem theorem_31_2_proper (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : Proper f) (hpg : ProperConcave g) : Proper (graphFn (fenchelBifun A f g)) := by
  obtain ⟨x₀, hx₀⟩ := hpf.dom_nonempty
  obtain ⟨w₀, hw₀⟩ := hpg.domConcave_nonempty
  refine ⟨⟨(w₀ - A x₀, x₀), ?_⟩, fun p => ?_⟩
  · obtain ⟨a, ha⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x₀) hx₀
    obtain ⟨b, hb⟩ :=
      Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hw₀) (lt_top_iff_ne_top.2 (hpg.ne_top w₀))
    have hA : A x₀ + (w₀ - A x₀) = w₀ := by abel
    have hval : graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) = ((a - b : ℝ) : EReal) := by
      have hg0 : graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) = f x₀ - g w₀ := by
        simp only [graphFn, fenchelBifun, hA]
      rw [hg0, ha, hb, ← EReal.coe_sub]
    change graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) < ⊤
    rw [hval]
    exact EReal.coe_lt_top _
  · exact _root_.EReal.add_ne_bot_iff.2 ⟨hpf.ne_bot p.2, by simpa using hpg.ne_top (A p.2 + p.1)⟩

/-- **Rockafellar, Theorem 31.2** (13263), third assertion: `F` is closed when `f` and `g` are. -/
theorem theorem_31_2_closed (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) :
    ClosedBifun (fenchelBifun A f g) := by
  have hgn : ClosedProperConvexFn fun w => -(g w) := hg.neg
  rw [closedBifun_iff, graphFn_fenchelBifun]
  refine (ClosedProperConvexFn.add
    ⟨convexFn_compLin _ hf.convex,
      closedFn_compLin hf.closed (LinearMap.continuous_of_finiteDimensional _),
      ⟨?_, fun p => hf.proper.ne_bot _⟩⟩
    ⟨convexFn_compLin _ hgn.convex,
      closedFn_compLin hgn.closed (LinearMap.continuous_of_finiteDimensional _),
      ⟨?_, fun p => hgn.proper.ne_bot _⟩⟩ ?_).closed
  · obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
    exact ⟨(0, x₀), hx₀⟩
  · obtain ⟨w₀, hw₀⟩ := hgn.proper.dom_nonempty
    exact ⟨(w₀, 0), by simpa [shiftLin_apply] using hw₀⟩
  · obtain ⟨p, hp⟩ := (theorem_31_2_proper A hf.proper hg.proper).dom_nonempty
    exact ⟨p, hp⟩

/-- The linear map `(w, x) ↦ w - A x`, whose image of `dom g ×ˢ dom f` is `dom F`. Writing the
book's `dom g - A (dom f)` as one linear image is what lets Theorem 6.6 and the product formula
for relative interiors do the whole job at once. -/
private def subLin (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) →ₗ[ℝ] Rn m :=
  LinearMap.fst ℝ (Rn m) (Rn n) - A ∘ₗ LinearMap.snd ℝ (Rn m) (Rn n)

private theorem subLin_apply (A : Rn n →ₗ[ℝ] Rn m) (p : Rn m × Rn n) :
    subLin A p = p.1 - A p.2 := rfl

private theorem sub_image_eq_subLin_image (A : Rn n →ₗ[ℝ] Rn m) (S : Set (Rn m))
    (T : Set (Rn n)) : S - A '' T = subLin A '' (S ×ˢ T) := by
  ext u
  constructor
  · rintro ⟨w, hw, -, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(w, x), ⟨hw, hx⟩, rfl⟩
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
    exact ⟨w, hw, A x, ⟨x, hx, rfl⟩, rfl⟩

/-- **Rockafellar, Theorem 6.6 and Corollary 6.6.2** in the combination this section needs:
`ri (S - A T) = ri S - A (ri T)`.  Surface §6's `theorem_6_6_ri` is stated only for maps
`Rn n →ₗ[ℝ] Rn m`, and the map here goes out of a product, so Theorem 6.6 is taken in its backbone
form `Convex.relint_image`.  Stating this once, with the two sets opaque, also keeps the elaborator
away from the conjugates it is applied to. -/
private theorem relint_sub_image (A : Rn n →ₗ[ℝ] Rn m) {S : Set (Rn m)} {T : Set (Rn n)}
    (hS : Convex ℝ S) (hT : Convex ℝ T) : ri (S - A '' T) = ri S - A '' ri T := by
  rw [sub_image_eq_subLin_image, sub_image_eq_subLin_image,
    Convex.relint_image (hS.prod hT) (subLin A), intrinsicInterior_prod_eq]

/-- `F u` is `+∞` at `x` unless `x ∈ dom f` and `A x + u ∈ dom g` (13283). -/
private theorem fenchelBifun_ne_top_iff {f : Rn n → EReal} {g : Rn m → EReal} (hpf : Proper f)
    (hpg : ProperConcave g) (A : Rn n →ₗ[ℝ] Rn m) (u : Rn m) (x : Rn n) :
    fenchelBifun A f g u x ≠ ⊤ ↔ x ∈ dom f ∧ A x + u ∈ domConcave g := by
  have hb : -(g (A x + u)) ≠ ⊥ := by simpa using hpg.ne_top (A x + u)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (_root_.EReal.add_ne_top_iff_ne_top₂ (hpf.ne_bot x) hb).1 h
    have h2' : g (A x + u) ≠ ⊥ := by simpa using h2
    exact ⟨lt_top_iff_ne_top.2 h1, bot_lt_iff_ne_bot.2 h2'⟩
  · rintro ⟨h1, h2⟩
    refine (_root_.EReal.add_ne_top_iff_ne_top₂ (hpf.ne_bot x) hb).2
      ⟨lt_top_iff_ne_top.1 h1, ?_⟩
    simpa using (ne_of_gt h2)

/-- **Rockafellar, Theorem 31.2** (13266): the optimal value of the convex program attached
to `F` is the Fenchel infimum `inf {f x - g (A x)}`. -/
theorem theorem_31_2_infBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal) :
    infBifun (fenchelBifun A f g) 0 = ⨅ x, f x - g (A x) :=
  iInf_congr fun x => by rw [fenchelBifun_apply, add_zero]

/-- **Rockafellar, Theorem 31.2** (13286): `dom F = dom g - A (dom f)`. -/
theorem theorem_31_2_domBifun (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : Proper f) (hpg : ProperConcave g) :
    domBifun (fenchelBifun A f g) = domConcave g - A '' dom f := by
  rw [sub_image_eq_subLin_image]
  ext u
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hx1, hx2⟩ := (fenchelBifun_ne_top_iff hpf hpg A u x).1 hx
    refine ⟨(A x + u, x), ⟨hx2, hx1⟩, ?_⟩
    change A x + u - A x = u
    abel
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
    refine ⟨x, (fenchelBifun_ne_top_iff hpf hpg A _ x).2 ⟨hx, ?_⟩⟩
    have hAx : A x + subLin A (w, x) = w := by change A x + (w - A x) = w; abel
    rwa [hAx]

/-- **Rockafellar, Theorem 31.2** (13292): `ri (dom F) = ri (dom g) - A (ri (dom f))`, by
Theorem 6.6 and Corollary 6.6.2 (`relint_sub_image`). -/
theorem theorem_31_2_relint_domBifun (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ConvexFn f) (hpf : Proper f) (hg : ConcaveFn g) (hpg : ProperConcave g) :
    ri (domBifun (fenchelBifun A f g)) = ri (domConcave g) - A '' ri (dom f) := by
  rw [theorem_31_2_domBifun A hpf hpg,
    relint_sub_image A hg.convex_domConcave hf.convex_dom]

/-- **Rockafellar, Theorem 31.2** (13269): the primal program is strongly consistent exactly
when `A (ri (dom f))` meets `ri (dom g)` — condition (a) of Theorem 31.1, in program form. -/
theorem theorem_31_2_stronglyConsistent_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hf : ConvexFn f) (hpf : Proper f) (hg : ConcaveFn g)
    (hpg : ProperConcave g) :
    StronglyConsistent (fenchelBifun A f g) ↔ ∃ x ∈ ri (dom f), A x ∈ ri (domConcave g) := by
  have key : ri (domBifun (fenchelBifun A f g))
      = subLin A '' (ri (domConcave g) ×ˢ ri (dom f)) := by
    rw [theorem_31_2_relint_domBifun A hf hpf hg hpg, sub_image_eq_subLin_image]
  have h0 : StronglyConsistent (fenchelBifun A f g)
      ↔ (0 : Rn m) ∈ subLin A '' (ri (domConcave g) ×ˢ ri (dom f)) := by
    change (0 : Rn m) ∈ ri (domBifun (fenchelBifun A f g)) ↔ _
    rw [key]
  rw [h0]
  constructor
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, hz⟩
    have hz' : w - A x = 0 := hz
    exact ⟨x, hx, (sub_eq_zero.1 hz') ▸ hw⟩
  · rintro ⟨x, hx, hAx⟩
    refine ⟨(A x, x), ⟨hAx, hx⟩, ?_⟩
    change A x - A x = 0
    exact sub_self _

/-! #### The adjoint of the Fenchel bifunction

Rockafellar's calculation (13301–13320) is a change of variable `w = A x + u` followed by a split
of one infimum over a product into two independent infima.  The split is where `EReal` bites: it
is *false* without a side condition (take `ψ i = -i` on `ℕ` and `φ ≡ ⊤`; then `⨅ ψ = ⊥`,
`⨅ φ = ⊤`, the sum is `⊥`, but every `ψ i + φ j` is `⊤`, so the joint infimum is `⊤`).
`Tdaf.EReal.iInf_prod_add` supplies it under `⨅ ψ ≠ ⊤` and `⨅ φ ≠ ⊤`, which properness gives at a
single point of each effective domain. -/

/-- Regrouping the five terms of Rockafellar's third display.  Both sides are sums of the same
`EReal`s, so `AddCommMonoid` associativity and commutativity settle it — no finiteness needed. -/
private theorem ereal_regroup (a b : EReal) (P K : ℝ) :
    a - b + ((P - K : ℝ) : EReal) = ((P : ℝ) : EReal) - b + (a - ((K : ℝ) : EReal)) := by
  rw [EReal.coe_sub, sub_eq_add_neg a b, sub_eq_add_neg ((P : ℝ) : EReal) ((K : ℝ) : EReal),
    sub_eq_add_neg ((P : ℝ) : EReal) b, sub_eq_add_neg a ((K : ℝ) : EReal)]
  simp only [add_comm, add_left_comm, add_assoc]

/-- Rockafellar's substitution `y = A x + u`, as a bijection of `Rᵐ × Rⁿ`. -/
private def shiftEquiv (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) ≃ (Rn m × Rn n) where
  toFun q := (q.1 - A q.2, q.2)
  invFun p := (A p.2 + p.1, p.2)
  left_inv := by rintro ⟨w, x⟩; simp
  right_inv := by rintro ⟨u, x⟩; simp

/-- **Rockafellar, Theorem 31.2** (13272): the adjoint of the Fenchel bifunction is
`(F* x*)(u*) = g*(u*) - f*(A* u* + x*)`. -/
theorem theorem_31_2_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : Proper f) (hpg : ProperConcave g) (y : Rn n) (v : Rn m) :
    adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v
      = concaveConj (pairing m) g v - conj (pairing n) f (LinearMap.adjoint A v + y) := by
  obtain ⟨x₀, hx₀⟩ := hpf.dom_nonempty
  obtain ⟨w₀, hw₀⟩ := hpg.domConcave_nonempty
  obtain ⟨fa, hfa⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x₀) hx₀
  obtain ⟨gb, hgb⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hw₀) (lt_top_iff_ne_top.2 (hpg.ne_top w₀))
  have hpair : ∀ (x : Rn n) (w : Rn m),
      (pairing m (w - A x) v - pairing n x y : ℝ)
        = (pairing m w v : ℝ) - (pairing n x (LinearMap.adjoint A v + y) : ℝ) := by
    intro x w
    have hA : (pairing m (A x) v : ℝ) = (pairing n x (LinearMap.adjoint A v) : ℝ) :=
      isAdjointPair_adjoint A x v
    simp only [map_sub, LinearMap.sub_apply, map_add, hA]
    ring
  have hsplit : adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v
      = ⨅ q : Rn m × Rn n,
          ((((pairing m q.1 v : ℝ) : EReal) - g q.1)
            + (f q.2 - ((pairing n q.2 (LinearMap.adjoint A v + y) : ℝ) : EReal))) := by
    rw [adjointBifun_apply, ← (shiftEquiv A).iInf_comp]
    refine iInf_congr fun q => ?_
    obtain ⟨w, x⟩ := q
    have hAx : A x + (w - A x) = w := by abel
    have h1 : fenchelBifun A f g (w - A x) x = f x - g w := by
      rw [fenchelBifun_apply, hAx]
    change fenchelBifun A f g (w - A x) x
        + ((pairing m (w - A x) v - pairing n x y : ℝ) : EReal)
      = (((pairing m w v : ℝ) : EReal) - g w)
        + (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal))
    rw [h1, hpair x w]
    exact ereal_regroup (f x) (g w) _ _
  have hb1 : ((pairing m w₀ v : ℝ) : EReal) - g w₀ ≠ ⊤ := by
    rw [hgb, ← EReal.coe_sub]; exact EReal.coe_ne_top _
  have hb3 : f x₀ - ((pairing n x₀ (LinearMap.adjoint A v + y) : ℝ) : EReal) ≠ ⊤ := by
    rw [hfa, ← EReal.coe_sub]; exact EReal.coe_ne_top _
  have ht1 : (⨅ w : Rn m, (((pairing m w v : ℝ) : EReal) - g w)) ≠ ⊤ := by
    intro hcon
    exact hb1 (top_le_iff.1 (by rw [← hcon]; exact iInf_le _ w₀))
  have ht2 : (⨅ x : Rn n, (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)))
      ≠ ⊤ := by
    intro hcon
    exact hb3 (top_le_iff.1 (by rw [← hcon]; exact iInf_le _ x₀))
  have hsp := Tdaf.EReal.iInf_prod_add
      (fun w : Rn m => (((pairing m w v : ℝ) : EReal) - g w))
      (fun x : Rn n => f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)) ht1 ht2
  have hc1 : (⨅ w : Rn m, (((pairing m w v : ℝ) : EReal) - g w))
      = concaveConj (pairing m) g v := rfl
  have hc2 : (⨅ x : Rn n, (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)))
      = -(conj (pairing n) f (LinearMap.adjoint A v + y)) := by
    rw [conj_apply, Tdaf.EReal.neg_iSup]
    exact (iInf_congr fun x => Tdaf.EReal.neg_coe_sub _ _).symm
  rw [hsplit, hsp, hc1, hc2, ← sub_eq_add_neg]

/-- **Rockafellar, Theorem 31.2** (13278): the optimal value of the dual concave program is
`sup {g*(u*) - f*(A* u*)}`. -/
theorem theorem_31_2_supBifun_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : Proper f) (hpg : ProperConcave g) :
    supBifun (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) 0
      = ⨆ v, concaveConj (pairing m) g v - conj (pairing n) f (LinearMap.adjoint A v) :=
  iSup_congr fun v => by rw [theorem_31_2_adjoint A hpf hpg 0 v, add_zero]

/-- `F* y` is identically `-∞` unless some `u*` has both `g* u*` and `f* (A* u* + y)` finite. -/
private theorem adjointBifun_fenchelBifun_ne_bot_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : Proper f) (hpg : ProperConcave g) (y : Rn n) (v : Rn m) :
    adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v ≠ ⊥
      ↔ v ∈ domConcave (concaveConj (pairing m) g)
        ∧ LinearMap.adjoint A v + y ∈ dom (conj (pairing n) f) := by
  rw [theorem_31_2_adjoint A hpf hpg y v, sub_eq_add_neg]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := _root_.EReal.add_ne_bot_iff.1 h
    have h2' : conj (pairing n) f (LinearMap.adjoint A v + y) ≠ ⊤ := by simpa using h2
    exact ⟨bot_lt_iff_ne_bot.2 h1, lt_top_iff_ne_top.2 h2'⟩
  · rintro ⟨h1, h2⟩
    refine _root_.EReal.add_ne_bot_iff.2 ⟨ne_of_gt h1, ?_⟩
    simpa using (lt_top_iff_ne_top.1 h2)

/-- The concave effective domain of `F*` is `dom f* - A* (dom g*)`: the mirror of
`theorem_31_2_domBifun`. -/
theorem theorem_31_2_domConcaveBifun_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : Proper f) (hpg : ProperConcave g) :
    domConcaveBifun (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      = dom (conj (pairing n) f)
        - LinearMap.adjoint A '' domConcave (concaveConj (pairing m) g) := by
  rw [sub_image_eq_subLin_image]
  ext y
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨h1, h2⟩ := (adjointBifun_fenchelBifun_ne_bot_iff A hpf hpg y v).1 hv
    refine ⟨(LinearMap.adjoint A v + y, v), ⟨h2, h1⟩, ?_⟩
    change LinearMap.adjoint A v + y - LinearMap.adjoint A v = y
    abel
  · rintro ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
    refine ⟨v, (adjointBifun_fenchelBifun_ne_bot_iff A hpf hpg _ v).2 ⟨hv, ?_⟩⟩
    have hz : LinearMap.adjoint A v + subLin (LinearMap.adjoint A) (w, v) = w := by
      change LinearMap.adjoint A v + (w - LinearMap.adjoint A v) = w
      abel
    rwa [hz]

/-- **Rockafellar, Theorem 31.2** (13281): the dual program is strongly consistent exactly
when `A* (ri (dom g*))` meets `ri (dom f*)` — condition (b) of Corollary 31.2.1, in program
form. -/
theorem theorem_31_2_concaveStronglyConsistent_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : Proper f) (hpg : ProperConcave g) :
    ConcaveStronglyConsistent (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      ↔ ∃ v ∈ ri (domConcave (concaveConj (pairing m) g)),
          LinearMap.adjoint A v ∈ ri (dom (conj (pairing n) f)) := by
  have hcf : Convex ℝ (dom (conj (pairing n) f)) := (convexFn_conj (pairing n) f).convex_dom
  have hcg : Convex ℝ (domConcave (concaveConj (pairing m) g)) :=
    (concaveFn_concaveConj (pairing m) g).convex_domConcave
  have key : ri (domConcaveBifun (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g)))
      = subLin (LinearMap.adjoint A)
          '' (ri (dom (conj (pairing n) f))
            ×ˢ ri (domConcave (concaveConj (pairing m) g))) := by
    rw [theorem_31_2_domConcaveBifun_adjoint A hpf hpg,
      relint_sub_image (LinearMap.adjoint A) hcf hcg, sub_image_eq_subLin_image]
  have h0 : ConcaveStronglyConsistent (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      ↔ (0 : Rn n) ∈ subLin (LinearMap.adjoint A)
          '' (ri (dom (conj (pairing n) f))
            ×ˢ ri (domConcave (concaveConj (pairing m) g))) := by
    change (0 : Rn n)
      ∈ ri (domConcaveBifun (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g))) ↔ _
    rw [key]
  rw [h0]
  constructor
  · rintro ⟨⟨w, v⟩, ⟨hw, hv⟩, hz⟩
    have hz' : w - LinearMap.adjoint A v = 0 := hz
    exact ⟨v, hv, (sub_eq_zero.1 hz') ▸ hw⟩
  · rintro ⟨v, hv, hAv⟩
    refine ⟨(LinearMap.adjoint A v, v), ⟨hAv, hv⟩, ?_⟩
    change LinearMap.adjoint A v - LinearMap.adjoint A v = 0
    exact sub_self _

/-! ### Corollary 31.2.1 under condition (b)

Rockafellar derives Corollary 31.2.1 from Theorem 31.2 by way of Theorem 30.4 and
Corollary 30.5.2, and under condition (b) that is the only route available: condition (b) is a
statement about `ri (dom g*)` and `ri (dom f*)`, and the composite `g ∘ A` it would have to be
turned into never appears in it. -/

/-- **Rockafellar, Corollary 31.2.1** under condition (b) (13375): if `ri (dom g*)` contains
a `u*` with `A* u* ∈ ri (dom f*)` then the Fenchel duality equation holds.

This is Theorem 31.2 followed by Theorem 30.4(b) (a convex program whose dual is strongly
consistent is normal) and Theorem 30.3 (normality is the absence of a duality gap). -/
theorem corollary_31_2_1_b (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) {v₀ : Rn m}
    (hv : v₀ ∈ ri (domConcave (concaveConj (pairing m) g)))
    (hAv : LinearMap.adjoint A v₀ ∈ ri (dom (conj (pairing n) f))) :
    (⨅ x, f x - g (A x))
      = ⨆ v : Rn m, concaveConj (pairing m) g v - conj (pairing n) f (LinearMap.adjoint A v) := by
  have hF : ConvexBifun (fenchelBifun A f g) :=
    theorem_31_2_convex A hf.convex hf.proper hg.concave hg.proper
  have hcl : ClosedBifun (fenchelBifun A f g) := theorem_31_2_closed A hf hg
  have hs : ConcaveStronglyConsistent
      (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) :=
    (theorem_31_2_concaveStronglyConsistent_iff A hf.proper hg.proper).2 ⟨v₀, hv, hAv⟩
  have hnorm : Normal (fenchelBifun A f g) :=
    normal_of_concaveStronglyConsistent_adjointBifun hF hcl hs
  have hgap := (normal_iff_iSup_adjointBifun_eq (Bu := pairing m) (pairing n) hF).1 hnorm
  rw [← theorem_31_2_infBifun A f g, ← hgap]
  exact theorem_31_2_supBifun_adjoint A hf.proper hg.proper

/-- **Rockafellar, Corollary 31.2.1** under condition (b), attainment clause (13377): the
*infimum* is attained at some `x`. -/
theorem corollary_31_2_1_b_attained (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) {v₀ : Rn m}
    (hv : v₀ ∈ ri (domConcave (concaveConj (pairing m) g)))
    (hAv : LinearMap.adjoint A v₀ ∈ ri (dom (conj (pairing n) f))) :
    ∃ x, f x - g (A x) = ⨅ z, f z - g (A z) := by
  have hF : ConvexBifun (fenchelBifun A f g) :=
    theorem_31_2_convex A hf.convex hf.proper hg.concave hg.proper
  have hcl : ClosedBifun (fenchelBifun A f g) := theorem_31_2_closed A hf hg
  have hs : ConcaveStronglyConsistent
      (adjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) :=
    (theorem_31_2_concaveStronglyConsistent_iff A hf.proper hg.proper).2 ⟨v₀, hv, hAv⟩
  have hinf : infBifun (fenchelBifun A f g) 0 = ⨅ x, f x - g (A x) :=
    theorem_31_2_infBifun A f g
  by_cases hc : Consistent (fenchelBifun A f g)
  · have hnorm : Normal (fenchelBifun A f g) :=
      normal_of_concaveStronglyConsistent_adjointBifun hF hcl hs
    have hgap : (⨆ v, adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v)
        = infBifun (fenchelBifun A f g) 0 :=
      (normal_iff_iSup_adjointBifun_eq (Bu := pairing m) (pairing n) hF).1 hnorm
    have hv0 : adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v₀ ≠ ⊥ := by
      refine (adjointBifun_fenchelBifun_ne_bot_iff A hf.proper hg.proper 0 v₀).2
        ⟨intrinsicInterior_subset hv, ?_⟩
      rw [add_zero]
      exact intrinsicInterior_subset hAv
    have hbot : infBifun (fenchelBifun A f g) 0 ≠ ⊥ := by
      rw [← hgap]
      intro h
      exact hv0 (le_bot_iff.1 (h ▸ le_iSup
        (fun v => adjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v) v₀))
    obtain ⟨x, hx⟩ := exists_infBifun_eq_of_concaveStronglyConsistent (Bu := pairing m)
      (Bx := pairing n) hF hcl hc hbot hs
    refine ⟨x, ?_⟩
    rw [← hinf, ← hx, fenchelBifun_apply, add_zero]
  · have h1 : ∀ x : Rn n, f x - g (A x) = ⊤ := by
      intro x
      by_contra hx
      refine hc ⟨x, ?_⟩
      rw [fenchelBifun_apply, add_zero]
      exact hx
    refine ⟨0, ?_⟩
    rw [h1 0]
    simp only [h1, iInf_const]

end Rockafellar
