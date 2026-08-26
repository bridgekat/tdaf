/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.LinearProcess
import Tdaf.Analysis.Convex.Bifunction.ProcessDuality
import Tdaf.Analysis.Convex.Polyhedral.Ops
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §39: Convex Processes

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §39, pp. 413–424: the last section of the
book. A **convex process** from `ℝᵐ` to `ℝⁿ` is a multivalued map whose graph is a convex cone
containing the origin; it sits between a linear transformation and a convex bifunction, and it
inherits a full duality theory from §§30–38.

All nine numbered results are here.

## Contents

| label | declaration |
|---|---|
| Theorem 39.1 (16817) | `theorem_39_1`, `theorem_39_1_isBounded` |
| Theorem 39.2 (17017) | `theorem_39_2_orientation`, `theorem_39_2_isClosed`, `theorem_39_2`,
  `theorem_39_2_eq_self_iff`, `theorem_39_2_indicatorBifun` |
| Theorem 39.3 (17049) | `theorem_39_3_posHomogeneous`, `theorem_39_3_convexFn`,
  `theorem_39_3_closedFn`, `theorem_39_3_concaveFn`, `theorem_39_3_closedConcaveFn`,
  `theorem_39_3_posHomogeneous_arg`, `theorem_39_3_concaveFn_arg`, `theorem_39_3_convexFn_arg`,
  `theorem_39_3_cl`, `theorem_39_3_cl_inf`, `theorem_39_3_cl_adjoint`,
  `theorem_39_3_relint_dom`, `theorem_39_3_relint_dom_adjoint` |
| Theorem 39.4 (17071) | `theorem_39_4`, `theorem_39_4_eval` |
| Theorem 39.5 (17155) | `theorem_39_5`, `theorem_39_5_isClosed`, `theorem_39_5_closure` |
| Theorem 39.6 (17165) | `theorem_39_6` |
| Theorem 39.7 (17169) | `theorem_39_7`, `theorem_39_7_attained`, `theorem_39_7_closedFn`,
  `theorem_39_7_attained_image`, `theorem_39_7_closure` |
| Corollary 39.7.1 (17181) | `corollary_39_7_1`, `corollary_39_7_1_isBounded` |
| Theorem 39.8 (17191) | `theorem_39_8`, `theorem_39_8_isClosed`, `theorem_39_8_closure` |

The section's unnumbered running text is transcribed too: the elementary properties of `A u`,
`dom A`, `range A` and `A⁻¹` (`eval_convex`, `dom_convex`, `range_convex`, `dom_inv`, `range_inv`),
the algebra `λA`, `A + B`, `AC`, `Af`, `BA` (`dom_add`, `image_convex`, `imageFn`, `inv_comp`,
`comp_assoc`, `id_comp`, `comp_id`), the failure of `A⁻¹A = I` (`inv_comp_ne_id`), the
complete-lattice structure (`convexProcessCompleteLattice`, taken from Mathlib through
`convexProcessEquivGraph`), and the remark that a linear transformation read as a convex process has
the adjoint linear transformation for its adjoint (`adjoint_ofLinearMap`).

## The section's definitions

**Orientation is data, not a convention.** Rockafellar is explicit (16945): "an oriented convex set
is a pair consisting of a convex set and one of the words *supremum* or *infimum*". Theorems 39.5
and 39.8 require two processes to carry the **same** orientation, and Theorem 39.2 **flips** it, so
both orientations must be simultaneously expressible and a global convention — of the kind §36
imposes on saddle-functions — cannot even state Theorem 39.5. The surface therefore carries the
pair:

* `Rockafellar.Orientation` — the formal word, `sup` or `inf`, with `Orientation.flip`.
* `Rockafellar.OrientedProcess m n` — the pair `⟨process, orientation⟩`.
* `Rockafellar.Orientation.bracketSet` — `⟨C, x*⟩`, the supremum or the infimum of `⟨·, x*⟩` over
  `C` according to the orientation. `bracketSet_sup_eq_supportFn` is its bridge to the backbone.
* `Rockafellar.OrientedProcess.bracket` — `⟨Au, x*⟩`, with bridges `bracket_sup` (the §33 bracket
  of the indicator bifunction) and `bracket_inf` (`ConvexProcess.coBracket`).
* `Rockafellar.OrientedProcess.adjoint` — `A*`, dispatching to `ConvexProcess.adjointProcess` or
  `ConvexProcess.coadjointProcess` and flipping the orientation.
* `Rockafellar.OrientedProcess.inv`, and the `Add`, `SMul` and `comp` operations, which take the
  orientation of their (left) argument, as the book's "the sum or product of convex processes with
  like orientation is given this same orientation" (16963) prescribes.
* `Rockafellar.PolyhedralConvexProcess` — "a convex process is said to be polyhedral if its graph
  is a polyhedral convex cone" (16871). No numbered result of §39 needs it, and the backbone has
  no counterpart; `polyhedral_graph_of_polyhedral` is the bridge to `Polyhedral`.
* `Rockafellar.imageFn` — `Af`, "the image of a convex function under a convex process",
  `(Af)(x) = inf {f u | u ∈ A⁻¹x}` (16913). `imageFn_apply` is the bridge to `imageBifun`.

## Where the book's hypotheses had to change

**Theorem 39.1 is stated with `A0 = {0}`, not with `A0` bounded.** Rockafellar's hypothesis is that
`A0` is a bounded set, and the first line of his proof is "since `A0` is a convex cone containing
the origin, boundedness implies that `A0` consists of the origin alone". Nothing after that line
uses boundedness. `A0 = {0}` is therefore the hypothesis the theorem actually has, it is strictly
weaker than the book's, and — unlike boundedness — it makes sense with no norm and no finite
dimension. `theorem_39_1` is stated that way and `theorem_39_1_isBounded` recovers the book's
literal form from it, so nothing is lost. This follows the precedent of Corollary 32.3.3
(`Part6/Section32.lean`), where the divergence is recorded in the docstring rather than hidden.

**Theorems 39.5, 39.7 and 39.8 carry an `IsExactSum` where the book carries a relative-interior
condition.** Rockafellar's hypotheses are `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`,
`ri (dom f) ∩ ri (dom A) ≠ ∅` and `ri (range A) ∩ ri (dom B) ≠ ∅`. The backbone states each of the
three as the exactness of the relevant sum (Theorem 16.4's conclusion), one instance per dual
vector, and the surface transcribes that hypothesis verbatim.

That hypothesis is **strictly stronger** than the book's, not a restatement of it, and the gap is
not closable by `IsExactSum.of_relint`. `IsExactSum` demands **proper** summands, and the summands
here are `u ↦ -⟨Aᵢ u, x*⟩`, which take the value `-∞` at every `u` where `Aᵢ u` is unbounded in
the direction `x*`. Quantified over *all* `x*`, as Theorems 39.5 and 39.8 are, this forces
`dom Aᵢ* = ℝⁿ` — and it already fails for §39's own running example
`Au = {x | x ≤ Bu} if u ≥ 0`, whose `A0 = {x | x ≤ 0}` has `⟨A0, x*⟩ = +∞` at every `x*` with a
negative coordinate. So `theorem_39_5` and `theorem_39_8` are true but do not cover the section's
motivating example. This is a backbone defect, recorded in the report; the surface neither invents
a weaker statement and numbers it as the book's, nor pretends the hypothesis is the book's.

**Theorem 39.3's last assertion is stated without closedness on the `u` side.** The book prefixes
both halves with "if `A` is closed"; the `u` half is Corollary 33.2.1, whose only input is that a
concave function agrees with its concave closure on the relative interior of its effective domain.
`theorem_39_3_relint_dom` therefore carries no closedness hypothesis, which is a strengthening.
`theorem_39_3_relint_dom_adjoint`, the `x*` half, does need it.

## What is not here

* **The infimum-oriented half of Theorem 39.2's last assertion.** For a supremum-oriented `A` the
  adjoint of the indicator bifunction of `A` is the indicator bifunction of `A*`
  (`theorem_39_2_indicatorBifun`, from `ConvexProcess.adjointBifun_indicatorBifun`). The mirror
  needs `concaveAdjointBifun` of the *concave* indicator bifunction `-δ(· | Au)` of an
  infimum-oriented process, and the backbone has no lemma for it; the book itself says only "the
  case of an infimum oriented convex process is argued similarly". Recorded as a backbone gap:
  `ConvexProcess.concaveAdjointBifun_neg_indicatorBifun` belongs in
  `Tdaf/Analysis/Convex/Bifunction/Process.lean`.
* **The infimum-oriented mirrors of Theorem 39.3's fourth and last assertions.**
  `Bifunction/Process.lean`'s own `## What is not here` records them as absent, and they are
  absent here for the same reason. The supremum-oriented forms are `theorem_39_3_cl_adjoint`,
  `theorem_39_3_relint_dom` and `theorem_39_3_relint_dom_adjoint`.
* **The infimum-oriented mirror of Theorem 39.4.** Rockafellar states the correspondence for
  supremum-oriented processes and remarks that upper closed convex-concave functions correspond to
  infimum-oriented ones; `Bifunction/ProcessDuality.lean` records that mirror as not obtainable by
  `simp`-normalising through negation, so it is a separate piece of backbone work.
* **The closing material, lines 17199–17268.** It sketches an algebra of oriented processes and a
  proposed duality for multivalued maps, entirely without proof. It is the end of the book, not a
  section of results, and nothing in it is a numbered result.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39.
-/

namespace Rockafellar

open Pointwise Set Tdaf.ConvexAnalysis Tdaf.Surface

variable {m n p : ℕ}

/-! ### Convex processes: the elementary properties (16741–16869) -/

/-- **Rockafellar, §39** (16791): each value `A u` of a convex process is a convex set.

Specialises `ConvexProcess.convex_eval`. -/
theorem eval_convex (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) : Convex ℝ (A.eval u) :=
  A.convex_eval u

/-- **Rockafellar, §39** (16791): `A 0` consists precisely of the vectors `y` with
`A u + y ⊆ A u` for every `u`.

Specialises `ConvexProcess.add_eval_zero_subset`. -/
theorem add_eval_zero_subset (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    A.eval u + A.eval 0 ⊆ A.eval u :=
  A.add_eval_zero_subset u

/-- **Rockafellar, §39** (16799): `dom A = {u | A u ≠ ∅}` is a convex cone containing the origin.

Specialises `ConvexProcess.convex_dom`. -/
theorem dom_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.dom := A.convex_dom

/-- **Rockafellar, §39** (16807): `range A = ⋃ {A u | u ∈ ℝᵐ}` is a convex cone containing the
origin.

Specialises `ConvexProcess.convex_range`. -/
theorem range_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.range := A.convex_range

/-- **Rockafellar, §39** (16813): `dom A⁻¹ = range A`.

Specialises `ConvexProcess.dom_inv`. -/
theorem dom_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.dom = A.range := A.dom_inv

/-- **Rockafellar, §39** (16813): `range A⁻¹ = dom A`.

Specialises `ConvexProcess.range_inv`. -/
theorem range_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.range = A.dom := A.range_inv

/-! ### Theorem 39.1 (16817) -/

/-- **Rockafellar, Theorem 39.1.** If `A` is a convex process from `ℝᵐ` to `ℝⁿ` such that
`dom A = ℝᵐ` and `A 0 = {0}`, then `A` is a linear transformation.

**Divergence from the book, deliberate.** Rockafellar's hypothesis is that `A 0` is *bounded*, and
the first line of his proof turns it into `A 0 = {0}`: "since `A 0` is a convex cone containing the
origin, boundedness implies that `A 0` consists of the origin alone". Nothing later in the proof
uses boundedness. `A 0 = {0}` is therefore the hypothesis the theorem actually has; it is strictly
weaker than the book's, and it needs neither a norm nor finite dimension.
`theorem_39_1_isBounded` recovers the book's literal statement, so the generalisation costs
nothing. This follows the precedent of Corollary 32.3.3 in `Part6/Section32.lean`.

Specialises `ConvexProcess.exists_linearMap_of_isBounded`. -/
theorem theorem_39_1 (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hzero : A.eval 0 = {0}) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  A.exists_linearMap_of_isBounded hdom (by rw [hzero]; exact Bornology.isBounded_singleton)

/-- **Rockafellar, Theorem 39.1**, in the book's literal form: `A 0` bounded rather than
`A 0 = {0}`. The two hypotheses coincide, `A 0` being a convex cone containing the origin
(`ConvexProcess.eval_zero_eq_zero_of_isBounded`), which is exactly the reduction the book's proof
opens with. -/
theorem theorem_39_1_isBounded (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  theorem_39_1 A hdom (A.eval_zero_eq_zero_of_isBounded hb)

/-! ### Polyhedral convex processes (16871) -/

/-- **Rockafellar, §39** (16871): a convex process is **polyhedral** if its graph is a polyhedral
convex cone.

The backbone has no `PolyhedralConvexProcess`, and no numbered result of §39 needs one — all nine
are proved without it — so this is a surface definition, with `PolyhedralCone` from
`Tdaf/Analysis/Convex/Polyhedral/Cone.lean`. `polyhedral_graph_of_polyhedral` is the bridge to
`Polyhedral` (`Tdaf/Analysis/Convex/Polyhedral/Defs.lean`). -/
def PolyhedralConvexProcess (A : ConvexProcess (Rn m) (Rn n)) : Prop :=
  PolyhedralCone (A.graph : Set (Rn m × Rn n))

/-- The graph of a polyhedral convex process is a polyhedral convex set.

Specialises `PolyhedralCone.polyhedral`. -/
theorem polyhedral_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : Polyhedral (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.polyhedral hA

/-- **Rockafellar, §39** (16871): a polyhedral convex process is closed, a polyhedral convex cone
being closed.

Specialises `PolyhedralCone.isClosed`. -/
theorem isClosed_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : IsClosed (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.isClosed hA

/-! ### The algebra of convex processes (16879–16943) -/

/-- **Rockafellar, §39** (16893): `dom (A₁ + A₂) = dom A₁ ∩ dom A₂`.

Specialises `ConvexProcess.dom_add`. -/
theorem dom_add (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    (A₁ + A₂).dom = A₁.dom ∩ A₂.dom :=
  ConvexProcess.dom_add A₁ A₂

/-- **Rockafellar, §39** (16903): the image `A C` of a convex set under a convex process is
convex.

Specialises `ConvexProcess.convex_image`. -/
theorem image_convex (A : ConvexProcess (Rn m) (Rn n)) {C : Set (Rn m)} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) :=
  A.convex_image hC

/-- **Rockafellar, §39** (16913): the **image of a convex function under a convex process**,
`(Af)(x) = inf {f u | u ∈ A⁻¹x}`.

This is `imageBifun` at the indicator bifunction of `A`; `imageFn_apply` is the bridge that turns
the unrestricted infimum of `imageBifun` into the book's restricted one. -/
noncomputable def imageFn (A : ConvexProcess (Rn m) (Rn n)) (f : Rn m → EReal) : Rn n → EReal :=
  imageBifun A.indicatorBifun f

/-- **Rockafellar, §39** (16913): `(Af)(x) = inf {f u | u ∈ A⁻¹x}`, the book's own formula.

The hypothesis `f u ≠ ⊥` is what turns the summand `f u + δ(x | A u)` into `⊤` off the fibre; it is
automatic for the proper convex `f` of Theorem 39.7. -/
theorem imageFn_apply (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal}
    (hf : ∀ u, f u ≠ ⊥) (x : Rn n) :
    imageFn A f x = ⨅ u ∈ A.inv.eval x, f u := by
  have hunfold : imageFn A f x = ⨅ u, f u + A.indicatorBifun u x := rfl
  rw [hunfold]
  refine iInf_congr fun u => ?_
  by_cases hu : u ∈ A.inv.eval x
  · rw [ConvexProcess.indicatorBifun_apply, indicatorFn_of_mem (show x ∈ A.eval u from hu),
      add_zero, iInf_pos hu]
  · rw [ConvexProcess.indicatorBifun_apply,
      indicatorFn_of_notMem (show x ∉ A.eval u from hu), iInf_neg hu]
    exact _root_.EReal.add_top_of_ne_bot (hf u)

/-- **Rockafellar, §39** (16929): `(BA)⁻¹ = A⁻¹B⁻¹`.

Specialises `ConvexProcess.inv_comp`. -/
theorem inv_comp (B : ConvexProcess (Rn n) (Rn p)) (A : ConvexProcess (Rn m) (Rn n)) :
    (B.comp A).inv = A.inv.comp B.inv :=
  ConvexProcess.inv_comp B A

/-- **Rockafellar, §39** (16939): multiplication of convex processes is associative, so the convex
processes from `ℝⁿ` to itself form a semigroup under multiplication. -/
theorem comp_assoc {q : ℕ} (C : ConvexProcess (Rn p) (Rn q)) (B : ConvexProcess (Rn n) (Rn p))
    (A : ConvexProcess (Rn m) (Rn n)) : (C.comp B).comp A = C.comp (B.comp A) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  constructor
  · rintro ⟨x, hx, z, hz, hw⟩
    exact ⟨z, ⟨x, hx, hz⟩, hw⟩
  · rintro ⟨z, ⟨x, hx, hz⟩, hw⟩
    exact ⟨x, hx, z, hz, hw⟩

/-- **Rockafellar, §39** (16939): the identity linear transformation `I` is a left identity for
multiplication of convex processes. -/
theorem id_comp (A : ConvexProcess (Rn m) (Rn n)) :
    (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn n))).comp A = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hz' : x = w := hz
    rwa [hz']
  · intro hr
    exact ⟨x, hr, rfl⟩

/-- **Rockafellar, §39** (16939): the identity linear transformation `I` is a right identity for
multiplication of convex processes. -/
theorem comp_id (A : ConvexProcess (Rn m) (Rn n)) :
    A.comp (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn m))) = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hw' : w = u := hw
    rwa [hw'] at hz
  · intro hr
    exact ⟨u, rfl, hr⟩

/-- **Rockafellar, §39** (16929): `A⁻¹A` is in general a multivalued mapping and **not** the
identity transformation.

The witness is the zero linear transformation on `ℝ¹`: `A u = {0}` for every `u`, so `A⁻¹0 = ℝ¹`
and `(A⁻¹A) u = ℝ¹`, whereas the identity process has `I u = {u}`. This is why the convex
processes from `ℝⁿ` to itself form a semigroup and not a group. -/
theorem inv_comp_ne_id :
    ∃ A : ConvexProcess (Rn 1) (Rn 1),
      A.inv.comp A ≠ ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn 1)) := by
  refine ⟨ConvexProcess.ofLinearMap 0, fun hc => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Rn 1)
  have hmem : ((0 : Rn 1), v) ∈
      ((ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1)).inv.comp
        (ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1))).graph := ⟨0, rfl, rfl⟩
  rw [hc] at hmem
  exact hv hmem

/-- **Rockafellar, §39** (16933), the first distributive inequality: `A(A₁ + A₂) ⊇ AA₁ + AA₂`,
inclusion being in the sense of graphs. -/
theorem comp_add_le (A : ConvexProcess (Rn n) (Rn p)) (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    ((A.comp A₁) + (A.comp A₂)).graph ≤ (A.comp (A₁ + A₂)).graph := by
  rintro ⟨u, z⟩ ⟨z₁, ⟨x₁, hx₁, hz₁⟩, z₂, ⟨x₂, hx₂, hz₂⟩, hz⟩
  refine ⟨x₁ + x₂, ⟨x₁, hx₁, x₂, hx₂, rfl⟩, ?_⟩
  have hz' : z = z₁ + z₂ := hz
  rw [hz']
  exact A.add_mem_graph hz₁ hz₂

/-- **Rockafellar, §39** (16933), the second distributive inequality: `(A₁ + A₂)A ⊆ A₁A + A₂A`. -/
theorem add_comp_le (A : ConvexProcess (Rn m) (Rn n)) (A₁ A₂ : ConvexProcess (Rn n) (Rn p)) :
    ((A₁ + A₂).comp A).graph ≤ ((A₁.comp A) + (A₂.comp A)).graph := by
  rintro ⟨u, z⟩ ⟨x, hx, z₁, hz₁, z₂, hz₂, hz⟩
  exact ⟨z₁, ⟨x, hx, hz₁⟩, z₂, ⟨x, hx, hz₂⟩, hz⟩

/-! ### The complete lattice of convex processes (16943)

"The collection of all convex processes from `ℝᵐ` to `ℝⁿ` is, of course, a complete lattice under
the partial ordering defined by inclusion (inasmuch as the collection of all convex cones containing
the origin in `ℝᵐ⁺ⁿ` is a complete lattice under inclusion)." That parenthesis is the whole proof,
and the lattice of pointed cones is Mathlib's `Submodule` lattice: the surface transports it along
the graph bijection rather than rebuilding it (design decision D12). -/

/-- A convex process **is** its graph: the bijection between convex processes and pointed convex
cones in the product, which is what the lattice structure is transported along. -/
def convexProcessEquivGraph (m n : ℕ) :
    ConvexProcess (Rn m) (Rn n) ≃ PointedCone ℝ (Rn m × Rn n) where
  toFun A := A.graph
  invFun K := ⟨K⟩
  left_inv A := by cases A; rfl
  right_inv _ := rfl

/-- **Rockafellar, §39** (16943): the convex processes from `ℝᵐ` to `ℝⁿ` form a **complete
lattice** under inclusion.

Everything is Mathlib's: `PointedCone ℝ (ℝᵐ × ℝⁿ)` is a `Submodule`, `Submodule` is a
`CompleteLattice`, and `Equiv.completeLattice` transports the structure along
`convexProcessEquivGraph`. -/
noncomputable instance convexProcessCompleteLattice :
    CompleteLattice (ConvexProcess (Rn m) (Rn n)) :=
  (convexProcessEquivGraph m n).completeLattice

/-- The order of the lattice is inclusion of graphs, which is Rockafellar's `A ⊇ B` read the other
way round. -/
theorem convexProcess_le_iff {A B : ConvexProcess (Rn m) (Rn n)} :
    A ≤ B ↔ (A.graph : Set (Rn m × Rn n)) ⊆ B.graph :=
  Iff.rfl

/-! ### Orientation (16945–16965) -/

/-- **Rockafellar's orientation** (16945): "an oriented convex set is a pair consisting of a convex
set and one of the words *supremum* or *infimum*". This is that word. -/
inductive Orientation where
  /-- The supremum orientation: `C` is identified with `δ(· | C)`. -/
  | sup : Orientation
  /-- The infimum orientation: `C` is identified with `-δ(· | C)`. -/
  | inf : Orientation
  deriving DecidableEq

/-- The opposite orientation. "The inverse of an oriented convex process is given the opposite
orientation" (16963), and so is its adjoint (Theorem 39.2). -/
def Orientation.flip : Orientation → Orientation
  | Orientation.sup => Orientation.inf
  | Orientation.inf => Orientation.sup

@[simp] theorem Orientation.flip_sup : Orientation.sup.flip = Orientation.inf := rfl

@[simp] theorem Orientation.flip_inf : Orientation.inf.flip = Orientation.sup := rfl

@[simp] theorem Orientation.flip_flip (o : Orientation) : o.flip.flip = o := by cases o <;> rfl

/-- **Rockafellar, §39** (16949): the inner product `⟨C, x*⟩ = ⟨x*, C⟩` of an **oriented convex
set** with a vector: the supremum of `⟨x, x*⟩` over `C` when `C` is supremum oriented, the infimum
when it is infimum oriented. -/
noncomputable def Orientation.bracketSet (o : Orientation) (C : Set (Rn n)) (y : Rn n) : EReal :=
  match o with
  | Orientation.sup => ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal)
  | Orientation.inf => ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal)

@[simp] theorem Orientation.bracketSet_sup (C : Set (Rn n)) (y : Rn n) :
    Orientation.sup.bracketSet C y = ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

@[simp] theorem Orientation.bracketSet_inf (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

/-- **Rockafellar, §39** (16955): for a supremum-oriented convex set, `⟨C, ·⟩` is the support
function of `C`, the convex conjugate of `δ(· | C)`.

Specialises `supportFn_apply`. -/
theorem bracketSet_sup_eq_supportFn (C : Set (Rn n)) :
    Orientation.sup.bracketSet C = supportFn (pairing n) C :=
  funext fun y => (supportFn_apply (pairing n) C y).symm

/-- **Rockafellar, §39** (16957): for an infimum-oriented convex set,
`⟨C, x*⟩ = -δ*(-x* | C)`, i.e. `⟨C, ·⟩` is the concave conjugate of `-δ(· | C)`. -/
theorem bracketSet_inf_eq_neg_supportFn (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = -(supportFn (pairing n) C (-y)) := by
  rw [Orientation.bracketSet_inf, supportFn_apply, Tdaf.EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [Tdaf.EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [← _root_.EReal.coe_neg, map_neg (pairing n x) y, _root_.neg_neg]

/-- **Rockafellar, §39** (16959): an **oriented convex process** is a convex process together with
an orientation, `A u` carrying that orientation for every `u`.

This is Rockafellar's formal pair, and it must be a pair: Theorems 39.5 and 39.8 require two
processes to carry the *same* orientation, and Theorem 39.2 flips it, so no global convention can
state them. -/
@[ext] structure OrientedProcess (m n : ℕ) where
  /-- The underlying convex process. -/
  process : ConvexProcess (Rn m) (Rn n)
  /-- The orientation, one of the two words. -/
  orientation : Orientation

/-- The **adjoint of a convex process in a given orientation**: `A*` is `adjointProcess` for the
supremum orientation and `coadjointProcess` for the infimum orientation, the two differing only in
the direction of the defining inequality (16991). -/
noncomputable def Orientation.adjointProcess (o : Orientation)
    (A : ConvexProcess (Rn m) (Rn n)) : ConvexProcess (Rn n) (Rn m) :=
  match o with
  | Orientation.sup => ConvexProcess.adjointProcess (pairing m) (pairing n) A
  | Orientation.inf => ConvexProcess.coadjointProcess (pairing m) (pairing n) A

@[simp] theorem Orientation.adjointProcess_sup (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.sup.adjointProcess A
      = ConvexProcess.adjointProcess (pairing m) (pairing n) A := rfl

@[simp] theorem Orientation.adjointProcess_inf (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.inf.adjointProcess A
      = ConvexProcess.coadjointProcess (pairing m) (pairing n) A := rfl

namespace OrientedProcess

/-- **Rockafellar, §39** (16963): the inverse of an oriented convex process, with the opposite
orientation. -/
def inv (A : OrientedProcess m n) : OrientedProcess n m := ⟨A.process.inv, A.orientation.flip⟩

@[simp] theorem inv_process (A : OrientedProcess m n) : A.inv.process = A.process.inv := rfl

@[simp] theorem inv_orientation (A : OrientedProcess m n) :
    A.inv.orientation = A.orientation.flip := rfl

/-- **Rockafellar, §39** (16991): the **adjoint** `A*` of an oriented convex process, an oriented
convex process from `ℝⁿ` to `ℝᵐ` with the opposite orientation. -/
noncomputable def adjoint (A : OrientedProcess m n) : OrientedProcess n m :=
  ⟨A.orientation.adjointProcess A.process, A.orientation.flip⟩

@[simp] theorem adjoint_process (A : OrientedProcess m n) :
    A.adjoint.process = A.orientation.adjointProcess A.process := rfl

@[simp] theorem adjoint_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := rfl

/-- **Rockafellar, §39** (16963): the sum of two convex processes with like orientation, given that
same orientation. Only sums of processes with like orientation are considered, which is why every
theorem about a sum below carries the hypothesis that the two orientations agree. -/
instance : Add (OrientedProcess m n) where
  add A₁ A₂ := ⟨A₁.process + A₂.process, A₁.orientation⟩

@[simp] theorem add_process (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).process = A₁.process + A₂.process := rfl

@[simp] theorem add_orientation (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).orientation = A₁.orientation := rfl

/-- **Rockafellar, §39** (16879, 16963): the scalar multiple `λA`, with the same orientation. -/
instance : SMul ℝ (OrientedProcess m n) where
  smul a A := ⟨a • A.process, A.orientation⟩

@[simp] theorem smul_process (a : ℝ) (A : OrientedProcess m n) :
    (a • A).process = a • A.process := rfl

@[simp] theorem smul_orientation (a : ℝ) (A : OrientedProcess m n) :
    (a • A).orientation = A.orientation := rfl

/-- **Rockafellar, §39** (16921, 16963): the product `BA` of two convex processes with like
orientation, given that same orientation. -/
def comp (B : OrientedProcess n p) (A : OrientedProcess m n) : OrientedProcess m p :=
  ⟨B.process.comp A.process, A.orientation⟩

@[simp] theorem comp_process (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).process = B.process.comp A.process := rfl

@[simp] theorem comp_orientation (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).orientation = A.orientation := rfl

/-- **Rockafellar, §39** (17041): the inner product `⟨Au, x*⟩` of an oriented convex process, the
value `A u` being read with `A`'s orientation. -/
noncomputable def bracket (A : OrientedProcess m n) (u : Rn m) (y : Rn n) : EReal :=
  A.orientation.bracketSet (A.process.eval u) y

/-- The supremum-oriented inner product is §33's bracket of the indicator bifunction of `A`, which
is where every clause of Theorem 39.3 about a supremum-oriented process comes from.

Specialises `ConvexProcess.bracket_indicatorBifun_apply`. -/
theorem bracket_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = Tdaf.ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  (ConvexProcess.bracket_indicatorBifun_apply (pairing n) A u y).symm

/-- The infimum-oriented inner product is the backbone's `ConvexProcess.coBracket`. -/
theorem bracket_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).bracket u y
      = ConvexProcess.coBracket (pairing n) A u y := rfl

/-- `bracket_sup` as an equation between functions of the dual variable. -/
theorem bracket_sup_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.sup).bracket u
      = Tdaf.ConvexAnalysis.bracket (pairing n) A.indicatorBifun u :=
  funext fun y => bracket_sup A u y

/-- `bracket_inf` as an equation between functions of the dual variable. -/
theorem bracket_inf_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.inf).bracket u
      = ConvexProcess.coBracket (pairing n) A u := rfl

/-- `bracket_sup` as an equation between functions of the primal variable. -/
theorem bracket_sup_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).bracket u y)
      = fun u => Tdaf.ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  funext fun u => bracket_sup A u y

/-- `bracket_sup` as an equation between functions on the product, the shape Theorems 39.3 and
39.4 state their closure identities in. -/
theorem bracket_sup_prod (A : ConvexProcess (Rn m) (Rn n)) :
    (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
      = fun q : Rn m × Rn n =>
          Tdaf.ConvexAnalysis.bracket (pairing n) A.indicatorBifun q.1 q.2 :=
  funext fun q => bracket_sup A q.1 q.2

end OrientedProcess

/-- **Rockafellar, §39** (17005): when `A` is a linear transformation, the adjoint of `A` as a
convex process — in **either** orientation — is the adjoint linear transformation.

Specialises `ConvexProcess.adjointProcess_ofLinearMap` and
`ConvexProcess.coadjointProcess_ofLinearMap` (`Bifunction/LinearProcess.lean`). -/
theorem adjoint_ofLinearMap (T : Rn m →ₗ[ℝ] Rn n) (o : Orientation) :
    (OrientedProcess.mk (ConvexProcess.ofLinearMap T) o).adjoint.process
      = ConvexProcess.ofLinearMap (LinearMap.adjoint T) := by
  cases o
  · exact ConvexProcess.adjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)
  · exact ConvexProcess.coadjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)

/-! ### Theorem 39.2 (17017) -/

/-- **Rockafellar, Theorem 39.2**, first assertion: `A*` has the **opposite orientation** to `A`.
This is by construction — it is the definition of `OrientedProcess.adjoint` — and it is the clause
that forces the orientation to be data. -/
theorem theorem_39_2_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := rfl

/-- **Rockafellar, Theorem 39.2**, first assertion: `A*` is a **closed** convex process from `ℝⁿ`
to `ℝᵐ`, in either orientation, being an intersection of homogeneous closed half-spaces.

Specialises `ConvexProcess.isClosed_graph_adjointProcess` and
`ConvexProcess.isClosed_graph_coadjointProcess`. -/
theorem theorem_39_2_isClosed (A : OrientedProcess m n) :
    IsClosed (A.adjoint.process.graph : Set (Rn n × Rn m)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact ConvexProcess.isClosed_graph_adjointProcess (pairing m) (pairing n) A
  · exact ConvexProcess.isClosed_graph_coadjointProcess (pairing m) (pairing n) A

/-- The second adjoint of a supremum-oriented process is the bipolar of its graph. -/
private theorem graph_biadjoint_sup (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.coadjointProcess (pairing n) (pairing m)
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- The second adjoint of an infimum-oriented process is the same bipolar. -/
private theorem graph_biadjoint_inf (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.adjointProcess (pairing n) (pairing m)
        (ConvexProcess.coadjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_adjointProcess_coadjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- **Rockafellar, Theorem 39.2**, second assertion: `A** = cl A`.

Read through the graph this is the bipolar theorem `K°° = cl K` of §14; the two sign flips cancel
exactly because the second adjoint is taken in the *opposite* orientation, which is what
`OrientedProcess.adjoint` arranges.

Specialises `ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure` and
`ConvexProcess.graph_adjointProcess_coadjointProcess_eq_closure`. -/
theorem theorem_39_2 (A : OrientedProcess m n) :
    (A.adjoint.adjoint.process.graph : Set (Rn m × Rn n))
      = closure (A.process.graph : Set (Rn m × Rn n)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact graph_biadjoint_sup A
  · exact graph_biadjoint_inf A

/-- **Rockafellar, Theorem 39.2**: a convex process is closed exactly when it is its own second
adjoint, `A** = A`.

Specialises `ConvexProcess.coadjointProcess_adjointProcess_eq_self_iff` and
`ConvexProcess.adjointProcess_coadjointProcess_eq_self_iff`. -/
theorem theorem_39_2_eq_self_iff (A : OrientedProcess m n) :
    A.adjoint.adjoint = A ↔ IsClosed (A.process.graph : Set (Rn m × Rn n)) := by
  rw [← closure_eq_iff_isClosed, ← theorem_39_2 A]
  constructor
  · intro h
    rw [h]
  · intro h
    refine OrientedProcess.ext ?_ (by simp)
    exact ConvexProcess.ext (SetLike.ext' h)

/-- **Rockafellar, Theorem 39.2**, last assertion: the adjoint of the indicator bifunction of a
supremum-oriented convex process `A` is the indicator bifunction of `A*`. The indicator appears
negated because `A*` carries the opposite orientation, and an infimum-oriented set is identified
with `-δ(· | ·)`.

Specialises `ConvexProcess.adjointBifun_indicatorBifun`. The infimum-oriented mirror is a backbone
gap; see the module docstring. -/
theorem theorem_39_2_indicatorBifun (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    adjointBifun (pairing m) (pairing n) A.indicatorBifun y v
      = -((OrientedProcess.mk A Orientation.sup).adjoint.process.indicatorBifun y v) :=
  ConvexProcess.adjointBifun_indicatorBifun (pairing m) (pairing n) A y v

/-! ### Theorem 39.3 (17049) -/

/-- The second extremum problem of Theorem 39.3 for a supremum-oriented `A`:
`⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}` is the concave bracket of the adjoint bifunction. -/
private theorem bracket_adjoint_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u
      = concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) u y := by
  rw [ConvexProcess.concaveBracket_adjointBifun_indicatorBifun]
  change (⨅ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iInf_congr fun v => iInf_congr fun _ => by rw [pairing_comm]

/-- The second extremum problem of Theorem 39.3 for an infimum-oriented `A`:
`⟨u, A* x*⟩ = sup {⟨u, u*⟩ | u* ∈ A* x*}`. -/
private theorem bracket_adjoint_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u
      = ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) := by
  change (⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iSup_congr fun v => iSup_congr fun _ => by rw [pairing_comm]

/-- **Rockafellar, Theorem 39.3**, first assertion: `⟨Au, x*⟩` is a **positively homogeneous**
function of `x*` for each `u`, in either orientation.

Specialises `ConvexProcess.posHomogeneous_bracket_indicatorBifun` and
`ConvexProcess.posHomogeneous_coBracket`. -/
theorem theorem_39_3_posHomogeneous (A : OrientedProcess m n) (u : Rn m) :
    PosHomogeneous (A.bracket u) := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_fn]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun (pairing n) A u
  · rw [OrientedProcess.bracket_inf_fn]
    exact ConvexProcess.posHomogeneous_coBracket (pairing n) A u

/-- **Rockafellar, Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is a
**convex** function of `x*`, being the support function of `A u`.

Specialises `ConvexProcess.convexFn_bracket_indicatorBifun`. -/
theorem theorem_39_3_convexFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConvexFn ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.convexFn_bracket_indicatorBifun (pairing n) A u

/-- **Rockafellar, Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is a
**closed** function of `x*`.

Specialises `ConvexProcess.closedFn_bracket_indicatorBifun`. -/
theorem theorem_39_3_closedFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedFn ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.closedFn_bracket_indicatorBifun (Bx := pairing n) A u

/-- **Rockafellar, Theorem 39.3**, "likewise when `A` is infimum oriented, except that then
convexity and concavity are reversed": `⟨Au, x*⟩` is a **concave** function of `x*`.

Specialises `ConvexProcess.concaveFn_coBracket`. -/
theorem theorem_39_3_concaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConcaveFn ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.concaveFn_coBracket (pairing n) A u

/-- **Rockafellar, Theorem 39.3**, infimum-oriented mirror: `⟨Au, x*⟩` is a **closed concave**
function of `x*`.

Specialises `ConvexProcess.closedConcaveFn_coBracket`. -/
theorem theorem_39_3_closedConcaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedConcaveFn ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.closedConcaveFn_coBracket (Bx := pairing n) A u

/-- **Rockafellar, Theorem 39.3**, first assertion: `⟨Au, x*⟩` is a **positively homogeneous**
function of `u` for each `x*`, in either orientation. This is the one clause that uses the
definition of a convex process rather than §33: it is axiom (b), `A(λu) = λ(Au)`.

Specialises `ConvexProcess.posHomogeneous_bracket_indicatorBifun_arg` and
`ConvexProcess.posHomogeneous_coBracket_arg`. -/
theorem theorem_39_3_posHomogeneous_arg (A : OrientedProcess m n) (y : Rn n) :
    PosHomogeneous fun u => A.bracket u y := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_arg]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun_arg (pairing n) A y
  · exact ConvexProcess.posHomogeneous_coBracket_arg (pairing n) A y

/-- **Rockafellar, Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is a
**concave** function of `u` for each `x*`.

Specialises `ConvexProcess.concaveFn_bracket_indicatorBifun`. -/
theorem theorem_39_3_concaveFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConcaveFn fun u => (OrientedProcess.mk A Orientation.sup).bracket u y := by
  rw [OrientedProcess.bracket_sup_arg]
  exact ConvexProcess.concaveFn_bracket_indicatorBifun (pairing n) A y

/-- **Rockafellar, Theorem 39.3**, infimum-oriented mirror: `⟨Au, x*⟩` is a **convex** function of
`u` for each `x*`. Reversing the orientation exchanges convexity and concavity in both variables at
once.

Specialises `ConvexProcess.convexFn_coBracket_arg`. -/
theorem theorem_39_3_convexFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConvexFn fun u => (OrientedProcess.mk A Orientation.inf).bracket u y :=
  ConvexProcess.convexFn_coBracket_arg (pairing n) A y

/-- **Rockafellar, Theorem 39.3**, third assertion: `⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩` for a
supremum-oriented `A`, the closure being the **concave** one because `⟨A ·, x*⟩` is concave. No
closedness of `A` is needed.

Specialises `ConvexProcess.concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁`. -/
theorem theorem_39_3_cl (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => partialCl₁
          (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
          (u, y) := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) u y :=
    funext fun u => bracket_adjoint_sup A u y
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁
    (Bu := pairing m) (Bx := pairing n) A y

/-- **Rockafellar, Theorem 39.3**, third assertion, infimum-oriented mirror:
`⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`, the closure now being the ordinary **convex** one because
`⟨A ·, x*⟩` is convex.

Specialises `ConvexProcess.iSup_coadjointProcess_eq_clFn`. -/
theorem theorem_39_3_cl_inf (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => clFn (fun u' => (OrientedProcess.mk A Orientation.inf).bracket u' y) u := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) :=
    funext fun u => bracket_adjoint_inf A u y
  rw [hL]
  exact ConvexProcess.iSup_coadjointProcess_eq_clFn (Bu := pairing m) (Bx := pairing n) A y

/-- **Rockafellar, Theorem 39.3**, fourth assertion: if `A` is closed then
`⟨Au, x*⟩ = cl_{x*} ⟨u, A* x*⟩`, the closure in the dual variable being the ordinary convex one.
Closedness of `A` is genuinely needed here: it is Theorem 33.2's *second* equation.

Specialises `ConvexProcess.partialCl₂_concaveBracket_adjointBifun_indicatorBifun`. -/
theorem theorem_39_3_cl_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) :
    partialCl₂ (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2 := by
  have hL : (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) q.1 q.2 :=
    funext fun q => bracket_adjoint_sup A q.1 q.2
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.partialCl₂_concaveBracket_adjointBifun_indicatorBifun
    (Bu := pairing m) (Bx := pairing n) A hA

/-- **Rockafellar, Theorem 39.3**, last assertion: `⟨Au, x*⟩ = ⟨u, A* x*⟩` whenever
`u ∈ ri (dom A)`.

**Divergence, a strengthening.** The book prefixes this and its dual with "if `A` is closed". The
`u` half is Corollary 33.2.1, whose only input is that a concave function agrees with its concave
closure on the relative interior of its effective domain, so no closedness is needed.

Specialises `ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom`. -/
theorem theorem_39_3_relint_dom (A : ConvexProcess (Rn m) (Rn n)) {u : Rn m}
    (hu : u ∈ ri A.dom) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom
    (Bu := pairing m) (Bx := pairing n) A hu y

/-- **Rockafellar, Theorem 39.3**, last assertion, dual half: for a **closed** `A`,
`⟨Au, x*⟩ = ⟨u, A* x*⟩` whenever `x* ∈ ri (dom A*)`.

Specialises `ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint`. -/
theorem theorem_39_3_relint_dom_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (OrientedProcess.mk A Orientation.sup).adjoint.process.dom) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint
    (Bu := pairing m) (Bx := pairing n) A hA u hy

/-! ### Theorem 39.4 (17071) -/

/-- **Rockafellar, Theorem 39.4.** The relations `K (u, x*) = ⟨Au, x*⟩` and
`Au = {x | ⟨x, x*⟩ ≤ K (u, x*) ∀ x*}` define a **one-to-one correspondence** between the lower
closed concave-convex functions `K` on `ℝᵐ × ℝⁿ` with `K (0, 0) = 0` that are positively
homogeneous in each variable separately, and the supremum-oriented **closed** convex processes `A`
from `ℝᵐ` to `ℝⁿ`.

Closedness sits inside the `∃!` rather than in the hypotheses, because the correspondence is with
closed processes and uniqueness is uniqueness among them.

Specialises `exists_unique_convexProcess_bracket_indicatorBifun_eq`. -/
theorem theorem_39_4 {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K)
    (hK₀ : K (0, 0) = 0)
    (hhu : ∀ y : Rn n, PosHomogeneous fun u : Rn m => K (u, y))
    (hhy : ∀ u : Rn m, PosHomogeneous fun y : Rn n => K (u, y)) :
    ∃! A : ConvexProcess (Rn m) (Rn n), IsClosed (A.graph : Set (Rn m × Rn n)) ∧
      (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2) = K := by
  simp only [OrientedProcess.bracket_sup_prod]
  exact exists_unique_convexProcess_bracket_indicatorBifun_eq (pairing m) (pairing n)
    hK hlc hK₀ hhu hhy

/-- **Rockafellar, Theorem 39.4**, the second displayed relation: a closed convex process is
recovered from its inner product by `Au = {x | ⟨x, x*⟩ ≤ K (u, x*) for every x*}`.

Specialises `ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun`. -/
theorem theorem_39_4_eval (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) :
    A.eval u = {x : Rn n | ∀ y : Rn n,
      ((pairing n x y : ℝ) : EReal) ≤ (OrientedProcess.mk A Orientation.sup).bracket u y} := by
  have h := ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun (Bx := pairing n) A hA u
  rw [flip_pairing] at h
  rw [h]
  ext x
  simp only [mem_supportSet, mem_ofPred_eq, OrientedProcess.bracket_sup]
  exact forall_congr' fun y => by rw [pairing_comm]

/-! ### Theorem 39.5 (17155) -/

/-- **Rockafellar, Theorem 39.5.** Let `A₁` and `A₂` be convex processes from `ℝᵐ` to `ℝⁿ` with the
**same orientation**. Then `(A₁ + A₂)* = A₁* + A₂*`.

The hypothesis that the orientations agree is load-bearing, and is the reason the orientation has
to be data: with a global convention the statement cannot be made at all.

**Divergence.** Rockafellar's hypothesis is `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`; the backbone's is the
exactness of the sum of the two support functions `u ↦ -⟨Aᵢ u, x*⟩`, one instance per `x*`, which is
Theorem 16.4's *conclusion*. The two are not interchangeable by `IsExactSum.of_relint`, which asks
for proper summands; see the module docstring.

Specialises `ConvexProcess.adjointProcess_add` and `ConvexProcess.coadjointProcess_add`. -/
theorem theorem_39_5 (A₁ A₂ : OrientedProcess m n) (hor : A₁.orientation = A₂.orientation)
    (hex : ∀ y : Rn n, IsExactSum (pairing m)
      (fun u => -(supportFn (pairing n) (A₁.process.eval u) y))
      (fun u => -(supportFn (pairing n) (A₂.process.eval u) y))) :
    (A₁ + A₂).adjoint = A₁.adjoint + A₂.adjoint := by
  obtain ⟨A₁, o₁⟩ := A₁
  obtain ⟨A₂, o₂⟩ := A₂
  have hor' : o₁ = o₂ := hor
  subst hor'
  cases o₁
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl

/-- **Rockafellar, Theorem 39.5**, second statement, first half: if `A₁` and `A₂` are closed and
`ri (dom A₁*)` and `ri (dom A₂*)` have a point in common, then `A₁ + A₂` is closed.

The backbone proves this without Corollary 38.2.1: `A₁ + A₂` *is* the infimum-oriented adjoint of
`A₁* + A₂*`, and an adjoint is closed with no hypothesis.

Specialises `ConvexProcess.isClosed_graph_add`. -/
theorem theorem_39_5_isClosed {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    IsClosed (((A₁ + A₂).graph : Set (Rn m × Rn n))) := by
  refine ConvexProcess.isClosed_graph_add (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-- **Rockafellar, Theorem 39.5**, second statement, second half: `(A₁ + A₂)*` is the **closure**
of `A₁* + A₂*`.

Specialises `ConvexProcess.graph_adjointProcess_add_eq_closure`. -/
theorem theorem_39_5_closure {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing n) (A₁ + A₂)).graph : Set (Rn n × Rn m))
      = closure (((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁
          + ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).graph
            : Set (Rn n × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_add_eq_closure (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-! ### Theorem 39.6 (17165) -/

/-- **Rockafellar, Theorem 39.6.** For any oriented convex process `A` and any `λ > 0`,
`(λA)* = λ(A*)`.

Specialises `ConvexProcess.adjointProcess_smul` and `ConvexProcess.coadjointProcess_smul`. -/
theorem theorem_39_6 (A : OrientedProcess m n) {a : ℝ} (ha : 0 < a) :
    (a • A).adjoint = a • A.adjoint := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact OrientedProcess.ext (ConvexProcess.adjointProcess_smul (pairing m) (pairing n) ha A) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_smul (pairing m) (pairing n) ha A) rfl

/-! ### Theorem 39.7 (17169) -/

/-- **Rockafellar, Theorem 39.7**, first assertion: for a supremum-oriented convex process `A` and
a proper convex `f` on `ℝᵐ`, `(Af)* = A*⁻¹ f*`.

**Divergence.** Rockafellar's hypothesis is `ri (dom f) ∩ ri (dom A) ≠ ∅`; the backbone asks for
the exactness of `f + (-⟨A ·, x*⟩)`, which is Theorem 16.4's conclusion. See the module docstring.

Specialises `ConvexProcess.conj_imageBifun_indicatorBifun`. -/
theorem theorem_39_7 (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal} (hf : Proper f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    conj (pairing n) (imageFn A f) y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f) y := by
  refine ConvexProcess.conj_imageBifun_indicatorBifun (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Rockafellar, Theorem 39.7**, second assertion: the infimum in the definition of
`(A*⁻¹ f*)(x*)` is attained for each `x*`.

Specialises `ConvexProcess.exists_imageBifun_indicatorBifun_adjointProcess_eq`. -/
theorem theorem_39_7_attained (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal} (hf : Proper f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    ∃ v : Rn m, conj (pairing m) f v
        + (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv.indicatorBifun v y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f) y := by
  refine ConvexProcess.exists_imageBifun_indicatorBifun_adjointProcess_eq
    (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Rockafellar, Theorem 39.7**, third assertion: if `A` and `f` are closed and
`ri (dom f*)` meets `ri (dom A*⁻¹)`, then `Af` is closed.

Specialises `ConvexProcess.closedFn_imageBifun_indicatorBifun`. -/
theorem theorem_39_7_closedFn {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    ClosedFn (imageFn A f) := by
  refine ConvexProcess.closedFn_imageBifun_indicatorBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Rockafellar, Theorem 39.7**, fourth assertion: the infimum in the definition of `(Af)(x)` is
attained, in the book's own form — wherever `Af` is finite there is a `u` with `x ∈ Au` and
`f u = (Af)(x)`.

Specialises `ConvexProcess.exists_mem_eval_and_eq_imageBifun`. -/
theorem theorem_39_7_attained_image {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f) {x : Rn n}
    (hex : IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x)))
    (hne : imageFn A f x ≠ ⊤) :
    ∃ u : Rn m, x ∈ A.eval u ∧ f u = imageFn A f x := by
  refine ConvexProcess.exists_mem_eval_and_eq_imageBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_ hne
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Rockafellar, Theorem 39.7**, last assertion: `(Af)*` is the **closure** of `A*⁻¹ f*`.

Specialises `ConvexProcess.conj_imageBifun_indicatorBifun_eq_clFn`. -/
theorem theorem_39_7_closure {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    conj (pairing n) (imageFn A f)
      = clFn (imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f)) := by
  refine ConvexProcess.conj_imageBifun_indicatorBifun_eq_clFn (Bu := pairing m) (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-! ### Corollary 39.7.1 (17181) -/

/-- **Rockafellar, Corollary 39.7.1.** Let `A` be a closed convex process from `ℝᵐ` to `ℝⁿ` and let
`C` be a non-empty closed convex set in `ℝᵐ`. If no non-zero vector in `A⁻¹0` belongs to the
recession cone of `C`, then `AC` is closed in `ℝⁿ`.

The backbone proves this as **Theorem 9.1** for the projection `(u, x) ↦ x`, not by specialising
Theorem 39.7: `AC` is the image of `graph A ∩ (C × ℝⁿ)`, whose recession cone is
`graph A ∩ (0⁺C × ℝⁿ)`, and the hypothesis of Theorem 9.1 is literally the one above. Rockafellar's
own route separates the barrier cone of `C` from the range of `A*`.

Specialises `ConvexProcess.isClosed_image`. -/
theorem corollary_39_7_1 {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty)
    (h : ∀ v ∈ A.inv.eval 0, v ≠ 0 → v ∉ recessionCone C) :
    IsClosed (A.image C) := by
  refine ConvexProcess.isClosed_image hA hC hCcl hCne fun v hv hrec => ?_
  by_contra hv0
  exact h v hv hv0 hrec

/-- **Rockafellar, Corollary 39.7.1**, the parenthesis "which is true in particular if `C` is
bounded": the image of a non-empty compact convex set under a closed convex process is closed.

Specialises `ConvexProcess.isClosed_image_of_isBounded`. -/
theorem corollary_39_7_1_isBounded {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) :=
  ConvexProcess.isClosed_image_of_isBounded hA hC hCcl hCne hb

/-! ### Theorem 39.8 (17191) -/

/-- **Rockafellar, Theorem 39.8.** Let `A` be a convex process from `ℝᵐ` to `ℝⁿ`, let `B` be a
convex process from `ℝⁿ` to `ℝᵖ`, and let `A` and `B` have the **same orientation**. Then
`(BA)* = A* B*`.

As in Theorem 39.5, the agreement of orientations is a hypothesis that only a formal orientation
*pair* can express.

**Divergence.** Rockafellar's hypothesis is `ri (range A) ∩ ri (dom B) ≠ ∅`; the backbone asks for
the exactness of the corresponding sum, one instance per `(z*, u*)`. The backbone also proves the
theorem without Theorem 38.5, as a linear sandwich produced by Fenchel's duality theorem.

Specialises `ConvexProcess.adjointProcess_comp` and `ConvexProcess.coadjointProcess_comp`. -/
theorem theorem_39_8 (A : OrientedProcess m n) (B : OrientedProcess n p)
    (hor : B.orientation = A.orientation)
    (hex : ∀ (w : Rn p) (v : Rn m), IsExactSum (pairing n)
      (fun x => ⨅ u ∈ A.process.inv.eval x, ((pairing m u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.process.eval x, ((pairing p z w : ℝ) : EReal)))) :
    (B.comp A).adjoint = A.adjoint.comp B.adjoint := by
  obtain ⟨A, oA⟩ := A
  obtain ⟨B, oB⟩ := B
  have hor' : oB = oA := hor
  subst hor'
  cases oB
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl

/-- **Rockafellar, Theorem 39.8**, second statement, first half: if `A` and `B` are closed and
`ri (range B*)` meets `ri (dom A*)`, then `BA` is closed.

Specialises `ConvexProcess.isClosed_graph_comp`. -/
theorem theorem_39_8_isClosed {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    IsClosed (((B.comp A).graph : Set (Rn m × Rn p))) := by
  refine ConvexProcess.isClosed_graph_comp (pairing m) (pairing n) (pairing p) hA hB ?_
  simpa only [flip_pairing] using hex

/-- **Rockafellar, Theorem 39.8**, second statement, second half: `(BA)*` is the **closure** of
`A* B*`.

Specialises `ConvexProcess.graph_adjointProcess_comp_eq_closure`. -/
theorem theorem_39_8_closure {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing p) (B.comp A)).graph
        : Set (Rn p × Rn m))
      = closure ((((ConvexProcess.adjointProcess (pairing m) (pairing n) A).comp
          (ConvexProcess.adjointProcess (pairing n) (pairing p) B)).graph
            : Set (Rn p × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_comp_eq_closure (pairing m) (pairing n) (pairing p)
    hA hB ?_
  simpa only [flip_pairing] using hex

end Rockafellar
