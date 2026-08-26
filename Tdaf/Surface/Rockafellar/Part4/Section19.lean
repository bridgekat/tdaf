/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.HellyRefined
import Tdaf.Analysis.Convex.Optimization.Perturbation
import Tdaf.Analysis.Convex.Polyhedral.Closedness
import Tdaf.Analysis.Convex.Polyhedral.Conjugate
import Tdaf.Analysis.Convex.Polyhedral.Faces
import Tdaf.Analysis.Convex.Polyhedral.NormalForm
import Tdaf.Analysis.Convex.Polyhedral.Recession
import Tdaf.Analysis.Convex.Polyhedral.Simplicial
import Tdaf.Analysis.Convex.Representation
import Tdaf.Surface.Rockafellar.Part2.Section09

/-!
# Rockafellar, §19: Polyhedral Convex Sets and Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §19, pp. 170–178: the Minkowski–Weyl
theorem and the polyhedral calculus.

## The section's five notions

* **polyhedral convex set** — the backbone's `Polyhedral`, a solution set of finitely many weak
  linear inequalities. The book writes the inequalities as `⟨x, bᵢ⟩ ≤ βᵢ` with *vectors* `bᵢ`;
  `theorem_19_1_pairing` is that translation.
* **polyhedral convex cone** — `PolyhedralCone`, the homogeneous case.
* **finitely generated convex set** — `FinitelyGenerated`, i.e. `conv S` for a finite set `S` of
  points *and directions*. The mixed point/direction hull is the backbone's `convexHullPD`, which
  is §17's idiom; `theorem_19_1_convexHullPD` records that the two spellings agree.
* **polytope** — `IsPolytope`, defined here, with `isPolytope_iff` as its bridge: a polytope is
  exactly a bounded polyhedral convex set.
* **polyhedral convex function** — `PolyhedralFn f := Polyhedral (epi f)`, and **finitely
  generated convex function** — `FinitelyGeneratedFn f := FinitelyGenerated (epi f)`, whose
  equality is Corollary 19.1.2.

## The `λ ≥ 0⁺` convention

Theorem 19.6, Theorem 19.7 and Corollary 19.5.1 are stated with Rockafellar's extended
coefficient, which §9 already models as `ExtCoeff` (`Part2/Section09.lean`): `ExtCoeff.smulSet`
sends `0⁺` to the recession cone and `ExtCoeff.smulFn` sends it to the recession function. This
module imports that treatment rather than case-splitting the convention away, and §9's
`iUnion_extCoeff_pair` is what turns the backbone's `conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)` into the
book's union over weights.

## Contents

| label | declaration |
|---|---|
| Theorem 19.1 | `theorem_19_1`, `theorem_19_1_pairing`, `theorem_19_1_convexHullPD`,
  `theorem_19_1_isClosed`, `theorem_19_1_finite_faces`, `theorem_19_1_of_finite_faces`,
  `theorem_19_1_finitelyGenerated_of_finite_faces`, `theorem_19_1_iff_finite_faces`,
  `theorem_19_1_face` |
| Corollary 19.1.1 | `corollary_19_1_1_extremePoints`, `corollary_19_1_1_extremeDirections` |
| Corollary 19.1.2 | `corollary_19_1_2`, `corollary_19_1_2_closed`, `corollary_19_1_2_attained` |
| Theorem 19.2 | `theorem_19_2` |
| Corollary 19.2.1 | `corollary_19_2_1` |
| Corollary 19.2.2 | `corollary_19_2_2` |
| Theorem 19.3 | `theorem_19_3_image`, `theorem_19_3_preimage` |
| Corollary 19.3.1 | `corollary_19_3_1_image`, `corollary_19_3_1_attained`,
  `corollary_19_3_1_preimage` |
| Corollary 19.3.2 | `corollary_19_3_2` |
| Corollary 19.3.3 | `corollary_19_3_3` |
| Corollary 19.3.4 | `corollary_19_3_4`, `corollary_19_3_4_attained` |
| Theorem 19.4 | `theorem_19_4` |
| §19, the normal form | `polyhedralFn_iff_normalForm` |
| Theorem 19.5 | `theorem_19_5_smul`, `theorem_19_5_recession`, `theorem_19_5_generators` |
| Corollary 19.5.1 | `corollary_19_5_1` |
| Theorem 19.6 | `theorem_19_6`, `theorem_19_6_iUnion`, `theorem_19_6_biUnion`,
  `theorem_19_6_biUnion_add` |
| Theorem 19.7 | `theorem_19_7`, `theorem_19_7_iUnion` |
| Corollary 19.7.1 | `corollary_19_7_1` |

## What is not here

**Omitted with a reason.**

* **Theorem 19.5's `λ < 0` and `λ = 0` case analysis.** `Polyhedral.smul` covers every real `λ`
  in one statement, so the book's three-way split is not reproduced. Rockafellar's `0C = {0}`
  convention differs from Lean's `(0 : ℝ) • C`, which is `∅` for `C = ∅`; both are polyhedral.
* **Theorem 19.6's `λ ≥ 0⁺` union formula for `m > 2`.** The polyhedrality clause and the
  convention-free identity are here for a `Finset` of sets (`theorem_19_6_biUnion`,
  `theorem_19_6_biUnion_add`); the union-over-weights spelling is here only for `m = 2`
  (`theorem_19_6_iUnion`), because it rests on §9's `iUnion_extCoeff_pair`, and `Part2/Section09`
  records the `m`-ary forms of §9 as deferred by scope. This is a §9 gap, not a §19 one.
* **The unnumbered examples and exercises** — `‖·‖₁` and `‖·‖∞` as polyhedral norms (6841–6867),
  the Tchebycheff-approximation illustration (6885–6915), the "umbra and penumbra" exercise
  (7000) — carry no numbered label.

**Deferred by scope.** None.

**Stated and refuted.** None. §19's statements are correct. Two of its printed *proofs* are not
complete as written, and neither defect touches a statement:

* **Theorem 19.1's proof of (b) ⇒ (a)** opens "It suffices to treat the case where `C` is
  `n`-dimensional in `Rⁿ`" and never says why. The reduction is repairable — a lower-dimensional
  `C` is polyhedral in `Rⁿ` exactly when it is polyhedral inside `aff C`, which is itself
  polyhedral — but it is not needed at all: `theorem_19_1_of_finite_faces` goes (b) ⇒ (c) ⇒ (a),
  using the book's own route through Theorem 18.5 for (b) ⇒ (c) and `theorem_19_1` for (c) ⇒ (a),
  and Theorem 18.8 never enters. See `polyhedral_of_finite_setOf_isFace`.
* **Theorem 19.6 is printed with no `Proof.` paragraph at all** — the book derives it in the
  running text at 6949–6971, and that is the argument the backbone formalises.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

open scoped Pointwise

variable {n m : ℕ}

/-! ### The book's spellings of the two definitions -/

/-- **Rockafellar, §19**: a **polytope** is a bounded finitely generated convex set — equivalently
(`isPolytope_iff`) a bounded polyhedral convex set. The definition is taken in the hull form
because that is the one the book uses when it says "including the simplices". -/
def IsPolytope (C : Set (Rn n)) : Prop := ∃ P : Finset (Rn n), C = convexHull ℝ (P : Set (Rn n))

/-- **Rockafellar, §19**: a convex function is **finitely generated** when its epigraph is a
finitely generated convex set in `ℝⁿ⁺¹`.

The book defines it by the infimum formula
`f x = inf {∑ λᵢαᵢ | ∑ λᵢaᵢ = x, λ₁ + ⋯ + λₖ = 1, λᵢ ≥ 0}` and then observes, in the paragraph
before Corollary 19.1.2, that this says exactly `f x = inf {μ | (x, μ) ∈ F}` for `F` the convex
hull of the points `(aᵢ, αᵢ)`, the directions of `(aᵢ, αᵢ)` and the direction `(0, 1)` — and that
`F` is then all of `epi f`. So `FinitelyGenerated (epi f)` is the book's condition, with the
generator `(0, 1)` absorbed into the requirement that the set be an epigraph. -/
def FinitelyGeneratedFn (f : Rn n → EReal) : Prop := FinitelyGenerated (epi f)

/-- A polytope is a bounded polyhedral convex set, and conversely.

Forward: `polyhedral_convexHull_finset`, and the convex hull of a finite set is compact
(Corollary 17.2.1). Backward: `Polyhedral.exists_finset_convexHull`, since boundedness kills every
generating direction. -/
theorem isPolytope_iff {C : Set (Rn n)} :
    IsPolytope C ↔ Polyhedral C ∧ Bornology.IsBounded C := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨polyhedral_convexHull_finset P,
      (P.finite_toSet.isCompact.isCompact_convexHull).isBounded⟩
  · rintro ⟨hC, hb⟩
    exact hC.exists_finset_convexHull hb

/-! ### Theorem 19.1 -/

/-- **Rockafellar, Theorem 19.1** (Minkowski–Weyl), the equivalence of clauses (a) and (c): a
convex set `C` is *polyhedral* — an intersection of finitely many closed half-spaces — if and only
if it is *finitely generated*, the convex hull of a finite set of points and directions.

Specialises `polyhedral_iff_finitelyGenerated`. -/
theorem theorem_19_1 {C : Set (Rn n)} : Polyhedral C ↔ FinitelyGenerated C :=
  polyhedral_iff_finitelyGenerated

/-- **Rockafellar, Theorem 19.1**, clause (a) in the book's own notation: `C` is polyhedral exactly
when it is the solution set of a finite system `⟨x, bᵢ⟩ ≤ βᵢ` of weak linear inequalities in
*vectors* `bᵢ`.

The backbone quantifies over linear functionals; on `ℝⁿ` the pairing represents every one of them,
which is `Polyhedral.exists_finset_pairing`. -/
theorem theorem_19_1_pairing {C : Set (Rn n)} :
    Polyhedral C ↔ ∃ s : Finset (Rn n × ℝ), C = {x : Rn n | ∀ q ∈ s, pairing n x q.1 ≤ q.2} := by
  classical
  refine ⟨fun hC => hC.exists_finset_pairing, ?_⟩
  rintro ⟨s, rfl⟩
  refine ⟨s.image fun q => ((pairing n).flip q.1, q.2), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_image]
  constructor
  · rintro h q ⟨p, hp, rfl⟩
    exact h p hp
  · intro h q hq
    exact h ((pairing n).flip q.1, q.2) ⟨q, hq, rfl⟩

/-- **Rockafellar, Theorem 19.1**, clause (c) in the book's own notation: `C` is finitely generated
exactly when `C = conv S` for a finite set `S` of points and directions.

`convexHullPD P D` is §17's mixed point/direction hull, `conv P + cone D`, so this is a change of
spelling and not of content. It is recorded because the book states clause (c) that way and every
later proof in §19 reads a presentation `C = conv S` off it. -/
theorem theorem_19_1_convexHullPD {C : Set (Rn n)} :
    FinitelyGenerated C ↔ ∃ P D : Finset (Rn n),
      C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := Iff.rfl

/-- **Rockafellar, Theorem 19.1**, the first half of clause (b): a polyhedral convex set is closed.

Specialises `Polyhedral.isClosed`. -/
theorem theorem_19_1_isClosed {C : Set (Rn n)} (hC : Polyhedral C) : IsClosed C :=
  hC.isClosed

/-- **Rockafellar, Theorem 19.1**, the second half of clause (b): a polyhedral convex set has only
finitely many faces.

The book proves this from Theorem 6.5 and Theorem 18.2, by intersecting the relatively open sets
`int Hᵢ` or `Mᵢ` that contain `ri C'`. The backbone reads it off the generators instead: by
Theorem 18.3 (`IsFace.eq_convexHullPD`) a face of `conv P + cone D` is the hull of the points of
`P` it contains and the directions of `D` in which it recedes, so the face map factors through
`P.powerset ×ˢ D.powerset`. Specialises `Polyhedral.finite_setOf_isFace`. -/
theorem theorem_19_1_finite_faces {C : Set (Rn n)} (hC : Polyhedral C) :
    {C' : Set (Rn n) | IsFace C C'}.Finite :=
  hC.finite_setOf_isFace

/-- **Rockafellar, Theorem 19.1**, clause (b) implies clause (c): a closed convex set with only
finitely many faces is finitely generated.

This is the book's argument, in the backbone as
`finitelyGenerated_of_finite_setOf_isFace_of_containsNoLine` and
`polyhedral_of_finite_setOf_isFace`. When `C` contains no lines, Theorem 18.5 writes it as the
hull of its extreme points and extreme directions, and a finite face set makes the extreme points
finite (they are the singleton faces) and the extreme rays finitely many (they are the half-line
faces). In general `C = L + (C ∩ M)` for `L` the lineality space and `M` any complement, the
faces of `C ∩ M` correspond to the faces of `C` (`isFaceEquivInter`, the book's remark on
p. 166), and `C ∩ M` contains no lines. -/
theorem theorem_19_1_finitelyGenerated_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) :
    FinitelyGenerated C :=
  finitelyGenerated_of_finite_setOf_isFace hC hCcl hfin

/-- **Rockafellar, Theorem 19.1**, clause (b) implies clause (a): a closed convex set with only
finitely many faces is polyhedral.

**The book's own proof of this implication has a hole**, and this is not it. He writes "It
suffices to treat the case where `C` is `n`-dimensional in `Rⁿ`" and gives no justification, then
runs the tangent half-spaces of Theorem 18.8 over that case. The reduction is repairable — a
lower-dimensional `C` is polyhedral exactly when it is polyhedral relative to `aff C`, which is
itself a polyhedral set — but it is also avoidable, and avoiding it is what
`polyhedral_of_finite_setOf_isFace` does: clause (b) gives clause (c)
(`theorem_19_1_finitelyGenerated_of_finite_faces`) and clause (c) gives clause (a)
(`theorem_19_1`). Theorem 18.8 is not used, and no dimension is counted. -/
theorem theorem_19_1_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) : Polyhedral C :=
  polyhedral_of_finite_setOf_isFace hC hCcl hfin

/-- **Rockafellar, Theorem 19.1**, the equivalence of clauses (a) and (b): a convex set is
polyhedral if and only if it is closed and has only finitely many faces.

Together with `theorem_19_1` — the equivalence of (a) and (c) — this completes the three-way
statement. Specialises `polyhedral_iff_isClosed_finite_setOf_isFace`. -/
theorem theorem_19_1_iff_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) :
    Polyhedral C ↔ IsClosed C ∧ {C' : Set (Rn n) | IsFace C C'}.Finite :=
  polyhedral_iff_isClosed_finite_setOf_isFace hC

/-- **Rockafellar, §19**, the remark after Theorem 19.1: "the proof of Theorem 19.1 shows,
incidentally, that every face of a polyhedral convex set is itself polyhedral."

Same route as `theorem_19_1_finite_faces`: Theorem 18.3 exhibits the face as the hull of a subset
of the generators. Specialises `Polyhedral.of_isFace`. -/
theorem theorem_19_1_face {C C' : Set (Rn n)} (hC : Polyhedral C) (hface : IsFace C C') :
    Polyhedral C' :=
  hC.of_isFace hface

/-! ### Corollary 19.1.1 -/

/-- **Rockafellar, Corollary 19.1.1**, the points half: a polyhedral convex set has at most
finitely many extreme points.

The book argues that extreme points are the faces which are points, and Theorem 19.1 bounds the
faces. The backbone gets there more directly, through `extremePoints_convexHullPD_subset`: every
extreme point of `conv P + cone D` is one of the generating points. Specialises
`FinitelyGenerated.finite_extremePoints`. -/
theorem corollary_19_1_1_extremePoints {C : Set (Rn n)} (hC : Polyhedral C) :
    (C.extremePoints ℝ).Finite :=
  hC.finitelyGenerated.finite_extremePoints

/-- **Rockafellar, Corollary 19.1.1**, the directions half: a polyhedral convex set has at most
finitely many extreme directions.

"Finitely many *directions*" cannot be `(extremeDirections C).Finite`: the backbone represents a
direction by a generating vector, so `extremeDirections C` is closed under positive rescaling and
is infinite as soon as it is non-empty. The finiteness is therefore stated up to positive scaling,
which is what the book means. Specialises
`exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded`. -/
theorem corollary_19_1_1_extremeDirections {C : Set (Rn n)} (hC : Polyhedral C) :
    ∃ D : Finset (Rn n), ∀ y ∈ extremeDirections C,
      ∃ z ∈ (D : Set (Rn n)), ∃ a : ℝ, 0 < a ∧ y = a • z := by
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  have hPD' : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := hPD
  refine ⟨D, fun y hy => ?_⟩
  rw [hPD'] at hy
  exact exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded _ _ P.finite_toSet.isBounded hy

/-! ### Corollary 19.1.2 -/

/-- **Rockafellar, Corollary 19.1.2**, first sentence: a convex function is polyhedral if and only
if it is finitely generated.

Both sides are Theorem 19.1 applied to the epigraph, which is what the two definitions say. -/
theorem corollary_19_1_2 {f : Rn n → EReal} : PolyhedralFn f ↔ FinitelyGeneratedFn f :=
  polyhedral_iff_finitelyGenerated

/-- **Rockafellar, Corollary 19.1.2**, second sentence: a polyhedral convex function, if proper, is
necessarily closed.

Specialises `PolyhedralFn.closedFn`, whose hypothesis `∀ x, f x ≠ ⊥` is exactly the `ne_bot` field
of properness. Properness cannot be dropped: `f ≡ ⊥` has epigraph `ℝⁿ⁺¹`, polyhedral by the empty
system, and is not closed in the `ClosedFn` sense. -/
theorem corollary_19_1_2_closed {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : Proper f) :
    ClosedFn f :=
  hf.closedFn hp.ne_bot

/-- **Rockafellar, Corollary 19.1.2**, third sentence: the infimum defining a finitely generated
convex function is attained wherever it is finite.

Given a presentation `epi f = conv P + cone D` of the epigraph, the point `(x, f x)` itself — and
not merely points above it — belongs to the generated set, so a representation of `f x` by
coefficients `λᵢ` exists. The content is Theorem 19.1: the generated set is *closed*, hence equal
to the whole epigraph rather than to a dense part of it. -/
theorem corollary_19_1_2_attained {f : Rn n → EReal} {P D : Finset (Rn n × ℝ)}
    (hPD : epi f = convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)))
    {x : Rn n} {μ : ℝ} (hx : f x = (μ : EReal)) :
    ((x, μ) : Rn n × ℝ) ∈ convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)) := by
  rw [← hPD]
  exact mk_mem_epi.2 (le_of_eq hx)

/-! ### Theorem 19.2 and its corollaries -/

/-- **Rockafellar, Theorem 19.2.** The conjugate of a polyhedral convex function is polyhedral.

Specialises `PolyhedralFn.conj`. No properness is assumed, and none is needed. -/
theorem theorem_19_2 {f : Rn n → EReal} (hf : PolyhedralFn f) :
    PolyhedralFn (conj (pairing n) f) :=
  hf.conj

/-- **Rockafellar, Corollary 19.2.1.** A closed convex set `C` is polyhedral if and only if its
support function `δ*(· | C)` is polyhedral.

The indicator and the support function are conjugate to each other, so Theorem 19.2 sends each
side to the other; `polyhedralFn_indicatorFn` and `PolyhedralFn.polyhedral_dom` are the two
translations between a polyhedral set and its indicator. -/
theorem corollary_19_2_1 {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C) :
    Polyhedral C ↔ PolyhedralFn (supportFn (pairing n) C) := by
  constructor
  · intro hC
    rw [supportFn_eq_conj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).conj
  · intro hs
    have h := hs.conj (B := (pairing n).flip)
    rw [conj_supportFn hconv hcl] at h
    have hd := h.polyhedral_dom
    rwa [dom_indicatorFn] at hd

/-- **Rockafellar, Corollary 19.2.2.** The polar of a polyhedral convex set is polyhedral.

The polar is the sublevel set `{y | δ*(y | C) ≤ 1}` of the support function, which Corollary 19.2.1
makes polyhedral; `PolyhedralFn.polyhedral_sublevel` finishes. -/
theorem corollary_19_2_2 {C : Set (Rn n)} (hC : Polyhedral C) :
    Polyhedral (polarSet (pairing n) C) := by
  have hs : PolyhedralFn (supportFn (pairing n) C) := by
    rw [supportFn_eq_conj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).conj
  have heq : polarSet (pairing n) C
      = {y : Rn n | supportFn (pairing n) C y ≤ ((1 : ℝ) : EReal)} := by
    ext y
    rw [Set.mem_ofPred_eq, supportFn_le_coe_iff, mem_polarSet]
  rw [heq]
  exact hs.polyhedral_sublevel 1

/-! ### Theorem 19.3 and its corollaries -/

/-- **Rockafellar, Theorem 19.3**, first half. For a linear transformation `A` from `ℝⁿ` to `ℝᵐ`,
`AC` is a polyhedral convex set in `ℝᵐ` for each polyhedral convex set `C` in `ℝⁿ`.

Specialises `Polyhedral.image`; the proof is on the generator side, as in the book. -/
theorem theorem_19_3_image {C : Set (Rn n)} (hC : Polyhedral C) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A '' C) :=
  hC.image A

/-- **Rockafellar, Theorem 19.3**, second half. `A⁻¹D` is a polyhedral convex set in `ℝⁿ` for each
polyhedral convex set `D` in `ℝᵐ`.

Specialises `Polyhedral.comap`; the proof is on the inequality side, as in the book. -/
theorem theorem_19_3_preimage {D : Set (Rn m)} (hD : Polyhedral D) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A ⁻¹' D) :=
  hD.comap A

/-- **Rockafellar, Corollary 19.3.1**, first half: for each polyhedral convex function `f` on
`ℝⁿ`, the image `Af` is polyhedral on `ℝᵐ`.

Specialises `polyhedralFn_mapLin`: the image of `epi f` under `(x, μ) ↦ (Ax, μ)` is polyhedral by
Theorem 19.3, hence closed, hence an epigraph — and it is `epi (Af)`. -/
theorem corollary_19_3_1_image {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m) :
    PolyhedralFn (mapLin A f) :=
  polyhedralFn_mapLin hf A

/-- **Rockafellar, Corollary 19.3.1**, the attainment clause: the infimum defining `(Af)(y)` is
attained wherever it is finite.

`epi (Af)` really is the image of `epi f`, because the image is polyhedral hence closed; a point of
it splits, and `mapLin_le` turns the resulting inequality into an equality. Specialises
`exists_mapLin_eq_of_polyhedralFn`, which has carried that argument since the §16 round; this file
reproduced all eighteen lines of it. -/
theorem corollary_19_3_1_attained {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m)
    {y : Rn m} {μ : ℝ} (hy : mapLin A f y = (μ : EReal)) :
    ∃ x : Rn n, A x = y ∧ f x = mapLin A f y :=
  exists_mapLin_eq_of_polyhedralFn hf A hy

/-- **Rockafellar, Corollary 19.3.1**, second half: for each polyhedral convex function `g` on
`ℝᵐ`, `gA` is polyhedral on `ℝⁿ`.

`epi (gA)` is the preimage of `epi g` under `(x, μ) ↦ (Ax, μ)`, so this is Theorem 19.3 again.
Specialises `polyhedralFn_compLin`, which used to be stranded in `Saddle/Correspondence.lean` (§37)
where §19 could not reach it, and is now in `Polyhedral/Duality.lean` (remediation §12.14b). -/
theorem corollary_19_3_1_preimage {g : Rn m → EReal} (hg : PolyhedralFn g)
    (A : Rn n →ₗ[ℝ] Rn m) : PolyhedralFn (compLin g A) :=
  polyhedralFn_compLin hg A

/-- **Rockafellar, Corollary 19.3.2.** If `C₁` and `C₂` are polyhedral convex sets in `ℝⁿ`, then
`C₁ + C₂` is polyhedral.

Specialises `Polyhedral.add`. -/
theorem corollary_19_3_2 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂) :
    Polyhedral (C₁ + C₂) :=
  h₁.add h₂

/-- **Rockafellar, Corollary 19.3.3.** If `C₁` and `C₂` are non-empty disjoint polyhedral convex
sets, there exists a hyperplane separating `C₁` and `C₂` strongly.

Specialises `separatesStrongly_of_polyhedral`, which needs neither set to be non-empty: `C₁ - C₂`
is polyhedral by Corollary 19.3.2, hence already closed, and Theorem 11.4 applies. The book's
non-emptiness hypotheses are kept here because the book has them. -/
theorem corollary_19_3_3 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂)
    (_hne₁ : C₁.Nonempty) (_hne₂ : C₂.Nonempty) (hdisj : Disjoint C₁ C₂) :
    ∃ (φ : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly φ c C₁ C₂ :=
  separatesStrongly_of_polyhedral h₁ h₂ hdisj

/-- **Rockafellar, Corollary 19.3.4.** If `f₁` and `f₂` are proper polyhedral convex functions on
`ℝⁿ`, then `f₁ □ f₂` is a polyhedral convex function too.

Specialises `PolyhedralFn.infConv`, whose proof is the book's: `epi f₁ + epi f₂` is polyhedral,
hence closed, hence an epigraph, and it is `epi (f₁ □ f₂)`. Properness is not needed. -/
theorem corollary_19_3_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂) :
    PolyhedralFn (infConv f₁ f₂) :=
  h₁.infConv h₂

/-- **Rockafellar, Corollary 19.3.4**, the attainment clause: the infimum in the definition of
`(f₁ □ f₂)(x)` is attained for each `x` at which it is finite.

Specialises `epi_infConv_of_polyhedralFn`: the epigraph of the infimal convolute *is* the sum of
the epigraphs, so a point of it splits. -/
theorem corollary_19_3_4_attained {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁)
    (h₂ : PolyhedralFn f₂) {x : Rn n} {μ : ℝ} (hx : infConv f₁ f₂ x = (μ : EReal)) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f₁ x₁ + f₂ x₂ ≤ (μ : EReal) := by
  have hmem : ((x, μ) : Rn n × ℝ) ∈ epi (infConv f₁ f₂) := mk_mem_epi.2 (le_of_eq hx)
  rw [epi_infConv_of_polyhedralFn h₁ h₂] at hmem
  obtain ⟨⟨x₁, μ₁⟩, hp₁, ⟨x₂, μ₂⟩, hp₂, hsum⟩ := hmem
  refine ⟨x₁, x₂, congrArg Prod.fst hsum, ?_⟩
  have hμ : μ₁ + μ₂ = μ := congrArg Prod.snd hsum
  calc f₁ x₁ + f₂ x₂ ≤ (μ₁ : EReal) + (μ₂ : EReal) :=
        add_le_add (mk_mem_epi.1 hp₁) (mk_mem_epi.1 hp₂)
    _ = (μ : EReal) := by rw [← EReal.coe_add, hμ]

/-! ### Theorem 19.4 -/

/-- **Rockafellar, Theorem 19.4.** If `f₁` and `f₂` are proper polyhedral convex functions, then
`f₁ + f₂` is polyhedral.

Specialises `PolyhedralFn.add`. Its hypothesis is `∀ x, fᵢ x ≠ ⊥`, which is the `ne_bot` half of
properness — and it is exactly what makes the `EReal` splitting
`f₁ x + f₂ x ≤ μ ↔ ∃ α β, f₁ x ≤ α ∧ f₂ x ≤ β ∧ α + β = μ` valid, the `⊤ + ⊥` case being the one
that would break it. -/
theorem theorem_19_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂)
    (hp₁ : Proper f₁) (hp₂ : Proper f₂) : PolyhedralFn (f₁ + f₂) :=
  h₁.add h₂ hp₁.ne_bot hp₂.ne_bot

/-! ### The normal form `f = h + δ(· | C)` -/

/-- **Rockafellar, §19**, the unnumbered characterisation of a polyhedral convex function: `f` is
polyhedral convex if and only if it can be written

`f x = h x + δ(x | C)`, with `h x = max {⟨x, b₁⟩ - β₁, …, ⟨x, bₖ⟩ - βₖ}` and
`C = {x | ⟨x, bₖ₊₁⟩ ≤ βₖ₊₁, …, ⟨x, bₘ⟩ ≤ βₘ}`.

The two families are the two kinds of closed half-space that can bound `epi f` in `ℝⁿ⁺¹`: those
that are epigraphs of affine functions and those that are "vertical". The book uses this to prove
Theorem 19.4; here `theorem_19_4` is proved from the epigraph instead, so the normal form is
recorded for its own sake.

`∀ x, f x ≠ ⊥` is the `ne_bot` half of properness, which the book's convention supplies, and it
cannot be dropped: `EReal` has `⊥ + ⊤ = ⊥`, so a right-hand side of this shape can take the value
`⊥` only *inside* `C`, whereas the function that is `⊥` on a proper non-empty polyhedral `C` and
`⊤` outside it is convex with polyhedral epigraph `C ×ˢ univ`. Specialises
`polyhedralFn_iff_maxAffineFn_add_indicatorFn`, whose `h` is written with linear functionals; the
translation to the book's vectors `bᵢ` is the one `theorem_19_1_pairing` performs for sets. -/
theorem polyhedralFn_iff_normalForm {f : Rn n → EReal} (hb : ∀ x, f x ≠ ⊥) :
    PolyhedralFn f ↔ ∃ (s : Finset (Rn n × ℝ)) (C : Set (Rn n)), Polyhedral C ∧
      ∀ x, f x = (⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal)) + indicatorFn C x := by
  classical
  have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ a : Rn n, ∀ x, φ x = pairing n x a := by
    intro φ
    obtain ⟨a, ha⟩ := exists_pairing_eq (pairing n) (LinearMap.toContinuousLinearMap φ)
    exact ⟨a, fun x => ha x⟩
  choose rep hrep using hrep
  constructor
  · intro hf
    obtain ⟨s, C, hC, hfC⟩ := (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).1 hf
    refine ⟨s.image fun q => (rep q.1, q.2), C, hC, fun x => ?_⟩
    have hval : f x = maxAffineFn s x + indicatorFn C x := congrFun hfC x
    have hunfold : maxAffineFn s x = ⨆ q ∈ s, ((q.1 x - q.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn s x
        = ⨆ q ∈ s.image fun q => (rep q.1, q.2), ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun ψ hψ => ?_)
      · refine le_iSup₂_of_le (rep ψ.1, ψ.2) (Finset.mem_image_of_mem _ hψ) (le_of_eq ?_)
        rw [hrep ψ.1 x]
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        refine le_iSup₂_of_le q hq (le_of_eq ?_)
        rw [hrep q.1 x]
    rw [hval, hmax]
  · rintro ⟨s, C, hC, hfC⟩
    refine (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).2
      ⟨s.image fun q => ((pairing n).flip q.1, q.2), C, hC, funext fun x => ?_⟩
    have hunfold : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ ψ ∈ s.image fun q => ((pairing n).flip q.1, q.2),
            ((ψ.1 x - ψ.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun q hq => ?_)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        exact le_iSup₂_of_le q hq (le_of_eq rfl)
      · exact le_iSup₂_of_le ((pairing n).flip q.1, q.2)
          (Finset.mem_image_of_mem _ hq) (le_of_eq rfl)
    change f x = maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x + indicatorFn C x
    rw [hmax]
    exact hfC x

/-! ### Theorem 19.5 and its corollary -/

/-- **Rockafellar, Theorem 19.5**, first assertion: `λC` is polyhedral for every scalar `λ`.

Specialises `Polyhedral.smul`, which covers `λ > 0`, `λ = 0` and `λ < 0` in one statement, so the
book's three-way case split is not reproduced. -/
theorem theorem_19_5_smul {C : Set (Rn n)} (hC : Polyhedral C) (l : ℝ) : Polyhedral (l • C) :=
  hC.smul l

/-- **Rockafellar, Theorem 19.5**, second assertion: the recession cone `0⁺C` of a non-empty
polyhedral convex set is a polyhedral convex cone.

Specialises `Polyhedral.polyhedralCone_recessionCone`: setting every right-hand side of a
representing system to zero gives a representing system for the recession cone. -/
theorem theorem_19_5_recession {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (recessionCone C) :=
  hC.polyhedralCone_recessionCone hne

/-- **Rockafellar, Theorem 19.5**, third assertion: if `C = conv S` for a finite set `S` of points
and directions, then `0⁺C = conv S₀`, where `S₀` consists of the origin and the directions in `S`.

`conv S₀` for `S₀` the origin together with the directions is the cone they generate, which is the
backbone's `PointedCone.hull ℝ ↑D`. Specialises `recessionCone_of_finitelyGenerated`; `⊇` is easy
and `⊆` is Corollary 9.1.2, vacuous here because `conv P` is compact. -/
theorem theorem_19_5_generators {C : Set (Rn n)} {P D : Finset (Rn n)}
    (hPD : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n))) (hne : C.Nonempty) :
    recessionCone C = (PointedCone.hull ℝ (D : Set (Rn n)) : Set (Rn n)) :=
  recessionCone_of_finitelyGenerated hPD hne

/-- **Rockafellar, Corollary 19.5.1.** If `f` is a proper polyhedral convex function, then `fλ` is
polyhedral for `λ ≥ 0` and `λ = 0⁺`.

The `λ ≥ 0⁺` convention is §9's `ExtCoeff.smulFn`. The proof is Rockafellar's — apply Theorem 19.5
to `C = epi f` — in three cases: `epi (fλ) = λ • epi f` for `λ > 0` (`epi_smulRight`),
`f0 = δ(· | 0)` (`smulRight_zero`, and properness is what makes `dom f` non-empty), and
`epi (f0⁺) = 0⁺(epi f)` (`epi_recessionFn`, which needs no hypothesis at all). -/
theorem corollary_19_5_1 {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : Proper f)
    {l : ExtCoeff} (hl : l.Nonneg) : PolyhedralFn (l.smulFn f) := by
  cases l with
  | ofReal t =>
    rw [ExtCoeff.smulFn_ofReal]
    rcases eq_or_lt_of_le (hl : (0 : ℝ) ≤ t) with ht | ht
    · rw [← ht, smulRight_zero hp.dom_nonempty]
      exact polyhedralFn_indicatorFn polyhedral_zero
    · change Polyhedral (epi (smulRight f t))
      rw [epi_smulRight ht]
      exact hf.smul t
  | zeroPlus =>
    change Polyhedral (epi (recessionFn f))
    rw [epi_recessionFn]
    exact (hf.polyhedralCone_recessionCone
      ((epi_nonempty_iff f).2 hp.dom_nonempty)).polyhedral

/-! ### Theorems 19.6 and 19.7 -/

/-- **Rockafellar, Theorem 19.6** for `m = 2`. If `C₁` and `C₂` are non-empty polyhedral convex
sets in `ℝⁿ`, then `C = cl (conv (C₁ ∪ C₂))` is a polyhedral convex set.

Specialises `polyhedral_closure_convexHull_union`. The book prints Theorem 19.6 with **no `Proof.`
paragraph**; its argument is the running text at 6949–6971, which sandwiches `conv (S₁ ∪ S₂)`
between `cl (conv (C₁ ∪ C₂))` and itself using Theorem 8.3, and that is the proof the backbone
formalises. -/
theorem theorem_19_6 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    Polyhedral (closure (convexHull ℝ (C₁ ∪ C₂))) :=
  polyhedral_closure_convexHull_union h₁ hne₁ h₂ hne₂

/-- **Rockafellar, Theorem 19.6** for `m = 2`, the formula

`cl (conv (C₁ ∪ C₂)) = ⋃ {λ₁C₁ + λ₂C₂ | λᵢ ≥ 0, λ₁ + λ₂ = 1}`,

with `0⁺Cᵢ` substituted for `0Cᵢ` when `λᵢ = 0`.

The union is indexed by `ExtCoeff` exactly as in Theorem 9.8, and §9's `iUnion_extCoeff_pair` is
what identifies it with the backbone's `conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)`. -/
theorem theorem_19_6_iUnion {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    closure (convexHull ℝ (C₁ ∪ C₂))
      = ⋃ p : ExtCoeff × ExtCoeff,
          ⋃ _ : p.1.Nonneg ∧ p.2.Nonneg ∧ p.1.toReal + p.2.toReal = 1,
            p.1.smulSet C₁ + p.2.smulSet C₂ := by
  rw [iUnion_extCoeff_pair h₁.convex hne₁ h₂.convex hne₂]
  exact (finitelyGenerated_closure_convexHull_union h₁ hne₁ h₂ hne₂).2

/-- **Rockafellar, Theorem 19.6** for general `m`. If `C₁, …, Cₘ` are non-empty polyhedral convex
sets in `ℝⁿ`, then `C = cl (conv (C₁ ∪ ⋯ ∪ Cₘ))` is a polyhedral convex set.

Indexed by a `Finset`, which subsumes the book's `i = 1, …, m` and also allows the empty family,
where both sides are `∅`. Specialises `polyhedral_closure_convexHull_biUnion`. -/
theorem theorem_19_6_biUnion {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    Polyhedral (closure (convexHull ℝ (⋃ i ∈ s, C i))) :=
  polyhedral_closure_convexHull_biUnion hC hne

/-- **Rockafellar, Theorem 19.6** for general `m`, the formula

`cl (conv (C₁ ∪ ⋯ ∪ Cₘ)) = conv (C₁ ∪ ⋯ ∪ Cₘ) + (0⁺C₁ + ⋯ + 0⁺Cₘ)`.

This is the convention-free form: the book writes the right-hand side as a union over weights
`λᵢ ≥ 0` with `∑ λᵢ = 1` and `0⁺Cᵢ` substituted for `0Cᵢ`, which for `m = 2` is
`theorem_19_6_iUnion`. Adding the recession cones says the same and needs no convention. -/
theorem theorem_19_6_biUnion_add {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    closure (convexHull ℝ (⋃ i ∈ s, C i))
      = convexHull ℝ (⋃ i ∈ s, C i) + ∑ i ∈ s, recessionCone (C i) :=
  (finitelyGenerated_closure_convexHull_biUnion hC hne).2

/-- **The `λ ≥ 0⁺` convention for a single set**, reduced to the backbone. For a convex `C`,
Rockafellar's `⋃ {λC | λ > 0 or λ = 0⁺}` is exactly `cone C + 0⁺C`. Theorem 19.7 asks that `C` be
non-empty; the identity does not need it, since both sides collapse to `0⁺∅` when `C = ∅`.

This is Theorem 19.7's analogue of §9's `iUnion_extCoeff_pair`, and like it the convention has to
be *earned*: `⊆` is that both `λC` and `0⁺C` sit inside the sum, and `⊇` uses
`mem_coe_hull_iff_of_convex` to write a point of `cone C` as `0` or `λx` with `λ > 0`, after which
the recession direction is absorbed as `λ • (x + λ⁻¹ v)`. -/
theorem iUnion_extCoeff_pos {C : Set (Rn n)} (hC : Convex ℝ C) :
    (⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C)
      = (PointedCone.hull ℝ C : Set (Rn n)) + recessionCone C := by
  have hzeroK : (0 : Rn n) ∈ (PointedCone.hull ℝ C : Set (Rn n)) :=
    (PointedCone.hull ℝ C).zero_mem
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨l, hl, hmem⟩ := Set.mem_iUnion₂.1 hx
    cases l with
    | ofReal t =>
      obtain ⟨y, hy, hyx⟩ := hmem
      have hyx' : t • y = x := hyx
      have hKt : x ∈ (PointedCone.hull ℝ C : Set (Rn n)) := by
        rw [← hyx']
        exact Submodule.smul_mem _ (⟨t, (hl : (0 : ℝ) < t).le⟩ : {c : ℝ // 0 ≤ c})
          (PointedCone.subset_hull hy)
      simpa using Set.add_mem_add hKt (zero_mem_recessionCone C)
    | zeroPlus => simpa using Set.add_mem_add hzeroK hmem
  · obtain ⟨u, hu, v, hv, huv⟩ := hx
    have huv' : u + v = x := huv
    rcases (mem_coe_hull_iff_of_convex hC).1 hu with rfl | ⟨t, ht, y, hy, hty⟩
    · refine Set.mem_iUnion₂.2 ⟨ExtCoeff.zeroPlus, trivial, ?_⟩
      rw [ExtCoeff.smulSet_zeroPlus, ← huv', zero_add]
      exact hv
    · have hty' : t • y = u := hty
      refine Set.mem_iUnion₂.2 ⟨ExtCoeff.ofReal t, ht, ?_⟩
      rw [ExtCoeff.smulSet_ofReal]
      have hyC : y + t⁻¹ • v ∈ C :=
        add_mem_of_mem_recessionCone (smul_mem_recessionCone (by positivity) hv) hy
      have hmem := Set.smul_mem_smul_set (a := t) hyC
      have hval : t • (y + t⁻¹ • v) = x := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul, hty', huv']
      rwa [hval] at hmem

/-- **Rockafellar, Theorem 19.7.** Let `C` be a non-empty polyhedral convex set and let `K` be the
closure of the convex cone generated by `C`. Then `K` is a polyhedral convex cone.

Specialises `polyhedralCone_closure_coe_hull`. The closure is genuinely needed: for `C` the
horizontal line at height `1` in `ℝ²` the cone generated by `C` is the open upper half-plane
together with the origin, and the missing horizontal directions are exactly `0⁺C`. -/
theorem theorem_19_7 {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (closure (PointedCone.hull ℝ C : Set (Rn n))) :=
  polyhedralCone_closure_coe_hull hC hne

/-- **Rockafellar, Theorem 19.7**, the formula `K = ⋃ {λC | λ > 0 or λ = 0⁺}`.

`iUnion_extCoeff_pos` converts the book's union into the backbone's `cone C + 0⁺C`, which
`finitelyGeneratedCone_closure_coe_hull` identifies with the closure. -/
theorem theorem_19_7_iUnion {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    closure (PointedCone.hull ℝ C : Set (Rn n)) = ⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C := by
  rw [iUnion_extCoeff_pos hC.convex]
  exact (finitelyGeneratedCone_closure_coe_hull hC hne).2

/-- **Rockafellar, Corollary 19.7.1.** If `C` is a polyhedral convex set containing the origin, the
convex cone generated by `C` is polyhedral — no closure needed.

Specialises `finitelyGeneratedCone_hull_of_zero_mem`: with `0 ∈ C` the recession cone is already
contained in `λC` for every `λ > 0`, so it may be dropped from the union of Theorem 19.7. -/
theorem corollary_19_7_1 {C : Set (Rn n)} (hC : Polyhedral C) (h0 : (0 : Rn n) ∈ C) :
    PolyhedralCone (PointedCone.hull ℝ C : Set (Rn n)) :=
  (finitelyGeneratedCone_hull_of_zero_mem hC h0).polyhedralCone

end Rockafellar
