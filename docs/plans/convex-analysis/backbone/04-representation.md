# Sub-plan 4 — Representation and inequalities

Covers Rockafellar §17–§22. Layer D throughout (`FiniteDimensional ℝ E`); §17–§19 are the parts
that matter downstream.

Rockafellar himself says Part IV can be skipped without jeopardising the rest of the book, with
three exceptions: §18 feeds §25/§26 and §32; §19–§20 supply the *polyhedral* constraint
qualifications used in §21, §23, §27, §28, §31; §21 feeds §27/§28.

---

## 4.1 `Caratheodory.lean` — §17

Mathlib has Carathéodory for points (`Analysis/Convex/Caratheodory.lean`, `convexHull_eq_union`).
Rockafellar's Theorem 17.1 is the **points-and-directions** version, handled by
[D7](../00-overview.md#d7-points-and-directions-are-handled-by-homogenisation-not-by-an-ad-hoc-definition): a "set of points and directions" is a set `S ⊆ ℝ × E` with first coordinate
in `{0,1}`, and `conv S` is the level-1 slice of `cone S`.

| Lean name | book | status |
|---|---|---|
| `mem_convexHull_iff_exists_fin_finrank_succ` (points) | **Thm 17.1**, point case | done |
| `exists_linearIndepOn_of_mem_coneHull`, `exists_card_le_finrank_of_mem_coneHull` | Carathéodory for cones — the algebraic core of Thm 17.1 | done |
| `exists_of_mem_convexHull_add_coneHull` (points and directions) | **Thm 17.1** | done |
| `exists_affineIndependent_of_mem_convexHull_iUnion`, `exists_linearIndepOn_of_mem_coneHull_iUnion` | Cor 17.1.1–17.1.2 | done |
| `exists_affineIndependent_of_convFn_lt`, `convFn_apply_affineIndependent` | **Cor 17.1.3** | done |
| `convHullFn_apply_fin` | **Cor 17.1.5** | done |
| — | Cors 17.1.4, 17.1.6 | **not stated — false as the book states them**; see below |
| `IsCompact.isCompact_convexHull`, `Bornology.IsBounded.closure_convexHull` | **Thm 17.2**, Cor 17.2.1 | done |
| `inequalitySet`, `inequalitySet_subset_halfSpace_of_mem_coneHull`, `mem_coneHull_insert_of_subset_halfSpace`, `exists_card_le_finrank_of_mem_coneHull_insert`, `inequalitySet_subset_halfSpace_iff` | **Thm 17.3** | done — with the hypothesis `0 ∉ S*`, which the book omits and without which the theorem is false |

`IsCompact.convexHull` does **not** exist in Mathlib — the nearest is
`Set.Finite.isCompact_convexHull` (`Analysis/Convex/Topology.lean:348`), for *finite* sets. So the
compact case of Theorem 17.2 is genuinely new work, not a specialisation.

### What actually happened

**Formalized: Theorem 17.1 in full, and Theorem 17.2.** `Caratheodory.lean` has
`mem_convexHull_iff_exists_fin_finrank_succ` (the point case),
`exists_linearIndepOn_of_mem_coneHull` (Carathéodory for *cones*),
`exists_of_mem_convexHull_add_coneHull` (points and directions),
`IsCompact.isCompact_convexHull` (**Cor 17.2.1**) and `Bornology.IsBounded.closure_convexHull`
(**Thm 17.2**). **Corollaries 17.1.1, 17.1.2, 17.1.3 and 17.1.5 are done too.**

**Corollaries 17.1.4 and 17.1.6 are false as Rockafellar states them.** On `ℝ¹` take `f₁ y = -y`
and `f₂ y = y`. Then `conv {f₁, f₂} ≡ -∞`, so the positively homogeneous function it generates is
`-∞` everywhere, while at `x = 1` every admissible representation uses a single index and gives
`-1` or `1`. The root cause is structural: an *affine* dependency has coefficients summing to zero,
so both signs occur and the elimination step may pick the one that lowers the cost, whereas a
*conical* dependency can have every coefficient of one sign — and then the book's "minimal `α'` on
the vertical line" does not exist. That is exactly why 17.1.3 is provable and 17.1.4 / 17.1.6 are
not. Presumably repairable by assuming the generated function proper; not stated here in any form.

**Corollary 17.1.3 is the points half, not the directions half.** 17.1.1 and 17.1.3 are the
affine/points corollaries; 17.1.2 and 17.1.4 are the conical/directions ones. It is still the one
§21.3 consumes, so the priority §4.5 assigns it was right for the wrong reason.

**Theorem 17.3 is done, and it is false as the book states it.** It needs `0 ∉ S*`: the proof
asserts that the open half-space `{(x*, μ*) | ⟨x̄, x*⟩ - μ* < 0}` contains `S*`, which fails outright
at `(0, 0) ∈ S*`, and the theorem fails with it. The counterexample — a spiral arc in `ℝ² × ℝ`
accumulating at the origin along a boundary ray, with the limiting unit direction omitted from the
cone's unit slice — is recorded verbatim in the doc comment of `inequalitySet_subset_halfSpace_iff`.
The book's other hypothesis, `x* ≠ 0`, **is** unnecessary: the empty combination covers the zero
functional. **Corollary 9.6.1, which this plan named as the blocker, was already in the project**
as `isClosed_coe_hull_of_isBounded` (`Recession/ConeHull.lean`).

**The directions case needed a conical Carathéodory, which Mathlib does not have.** Rockafellar's
proof of Theorem 17.1 says so explicitly: after homogenising, "it is only necessary to show that any
non-zero vector `y ∈ K` … can actually be expressed as a non-negative linear combination of
linearly independent vectors of `S'`". That statement —

```lean
theorem exists_linearIndepOn_of_mem_coneHull {S : Set E} {x : E} (hx : x ∈ PointedCone.hull ℝ S) :
    ∃ (t : Finset E) (w : E → ℝ), ↑t ⊆ S ∧ (∀ y ∈ t, 0 < w y) ∧
      LinearIndepOn ℝ id (t : Set E) ∧ ∑ y ∈ t, w y • y = x
```

— is layer A (no topology, no dimension) and is the reusable half of §17. The elimination step is
the book's: normalise a dependency so one coefficient is positive, subtract `min (w y / μ y)` times
it, and keep only the coefficients that are still strictly positive.
`exists_of_mem_convexHull_add_coneHull` then runs it in `ℝ × E` against `{1} × P ∪ {0} × D` and
splits the answer by first coordinate; the bound `n + 1` is `finrank ℝ (ℝ × E)`.

**Corollaries 17.1.1–17.1.6 are deliberately left.** Every one of them insists the generators come
from *different* members of a family, which Carathéodory does not give: two generators from the same
`Cᵢ` have to be coalesced into their convex combination, and independence of the merged family
re-proved. Their only consumers are Corollaries 17.1.3/17.1.4 → **Theorem 21.3**, which is blocked
on **Theorem 13.5** anyway, so the coalescing argument buys nothing until §13 moves. Do it together
with Theorem 13.5, not before.

The plan under-described the gap. Mathlib's `convexHull_eq_union` gives an affinely independent
finite subset, and `AffineIndependent.card_le_finrank_succ` bounds it by `n + 1` — but a *bound* is
not what compactness needs. What it needs is a **fixed index type**, so that `convexHull ℝ S` is
the image of one compact set under one continuous map:

```
convexHull ℝ S = (fun (w, z) ↦ ∑ i, w i • z i) '' (stdSimplex ℝ (Fin (n+1)) ×ˢ (univ.pi fun _ ↦ S))
```

Getting there means padding Carathéodory's subset out to exactly `n + 1` entries, repeating one of
its points with weight zero. That padding — `sum_ite_lt`, plus the truncation
`r i = ⟨min i (card - 1), _⟩`, which is total precisely because the subset is nonempty — is the
whole of the work; compactness and Theorem 17.2 are three lines after it. `sum_ite_lt` is stated
with a plain `if`, not a `dite`, because making the index map total first is what keeps the two
sums (of weights, and of weighted points) rewritable by the same lemma.

## 4.2 `Face.lean` — §18

Mathlib has `IsExtreme`, `Set.extremePoints`, `IsExposed`, and Krein–Milman
(`Analysis/Convex/{Extreme,Exposed,KreinMilman}.lean`).

**Status: all of §18 is done.** `Face.lean` carries Theorems 18.1 and 18.2 and the compact
case of 18.4 and 18.5; `Representation.lean` carries 18.3–18.6 in general; `Exposed.lean` and
`Tangent.lean` carry 18.7 and 18.8.

| Lean name | book | status |
|---|---|---|
| `IsFace` | the definition of a face | done |
| `IsFace.subset_of_relint_inter_nonempty` | **Thm 18.1** | done |
| `IsFace.eq_inter_closure`, `IsFace.isClosed` | Cor 18.1.1 | done |
| `IsFace.eq_of_relint_inter_nonempty` | Cor 18.1.2 | done |
| `IsFace.disjoint_relint`, `.subset_intrinsicFrontier`, `.finrank_vectorSpan_lt` | Cor 18.1.3 | done |
| `exists_isFace_subset_relint`, `exists_isFace_mem_relint`, `eq_iUnion_relint_isFace`, `IsFace.relint_pairwise_disjoint`, `IsFace.relint_maximal` | **Thm 18.2** | done |
| `IsFace.eq_convexHullPD` | **Thm 18.3** | done, in `Representation.lean` |
| `extremePoints_convexHullPD_subset`, `exists_mem_eq_smul_of_mem_extremeDirections`, `…_of_isBounded` | Cor 18.3.1 | done, in `Representation.lean` |
| `exists_notMem_relint_mem_segment` | Thm 18.4, compact case | done |
| `IsAffineHalf`, `isAffineHalf_of_convex_sdiff_relint`, `exists_notMem_relint_mem_segment_of_not_isAffineHalf` | **Thm 18.4** | done, in `Representation.lean` |
| `convexHull_extremePoints`, `extremePoints_nonempty` | Cor 18.5.1, and Cor 18.5.3 for compact `C` | done |
| `ContainsNoLine`, `IsExtremeDirection`, `extremeDirections`, `exists_eq_halfLine`, `convexHullPD_extremePoints_extremeDirections` | **Thm 18.5** | done, in `Representation.lean` |
| `extremePoints_nonempty_of_containsNoLine` | Cor 18.5.3 | done, in `Representation.lean` |
| `coneHull_extremeDirections_eq`, `coneHull_of_forall_extremeDirection` | Cor 18.5.2 (cones) | done, in `Representation.lean` |
| `mem_exposedPoints_of_forall_norm_sub_le`, `image_exposedPoints`, `extremePoints_subset_closure_exposedPoints`, `closure_exposedPoints_eq_closure_extremePoints`, `closure_convexHull_exposedPoints` | **Thm 18.6** (Straszewicz) | done, in `Representation.lean` |
| `IsExposedDirection`, `exposedDirections`, `exists_forall_sub_le_mul_sub`, `closure_convexHullPD_exposedPoints_exposedDirections`, `closure_coneHull_exposedDirections`, `closure_coneHull_of_forall_exposedDirection` | **Thm 18.7**, Cor 18.7.1 | done, in `Exposed.lean` |
| `IsSupportingAt`, `IsTangentAt`, `exists_isTangentAt_lt_of_zero_mem_interior`, `eq_iInter_tangent_halfSpaces` | **Thm 18.8** | done, in `Tangent.lean` |

### What actually happened

**The plan's opening guess was wrong.** It read: "Rockafellar's *face* is more general than Mathlib's
`IsExtreme` … but the two coincide for convex `C`. First task: prove
`IsExtreme ℝ C C' ↔ Rockafellar.IsFace C C'` for convex `C`." They do **not** coincide:
`C = [0, 1] ⊆ ℝ` has `C' = {0, 1}` extreme but not convex, and a face must be convex. So

```lean
structure IsFace (C C' : Set E) : Prop extends IsExtreme ℝ C C' where
  convex : Convex ℝ C'
```

and the whole `IsExtreme` API is reused through `toIsExtreme`. The zero-dimensional case is
unaffected — `isFace_singleton : IsFace C {x} ↔ x ∈ C.extremePoints ℝ` — so Mathlib's extreme
points *are* Rockafellar's, and `IsExposed.isFace` makes Mathlib's exposed faces faces.

**Theorem 18.1 needs less than Rockafellar assumes.** He asks for `D` convex; the proof only uses
the prolongation principle at a point of `ri D`, which `exists_one_lt_smul_mem_of_mem_relint`
supplies for any set. The convexity hypothesis is therefore absent from
`IsFace.subset_of_relint_inter_nonempty`. Likewise Corollary 18.1.3 does not need `C` convex.

**Corollary 18.1.3's dimension statement is proved directly, not through Corollary 6.3.3.** A
nonempty proper face has `vectorSpan ℝ C' ≤ vectorSpan ℝ C` and cannot have equal `finrank`,
because equal directions plus a shared point would make the affine hulls equal, and then `ri C'`
(nonempty) would land inside `ri C`, contradicting the relative-boundary half of the corollary.

**Theorem 18.2 uses Corollary 11.6.2 rather than Theorem 11.6.** For the smallest face `C'`
containing a relatively open convex `D ⊆ C`, `notMem_relint_iff_exists_isMaxOn` produces a linear
function maximised over `C'` at a point of `D` and not constant on `C'`;
`eq_of_isMaxOn_of_mem_relint` makes it constant on `D` (this is the only place `ri D = D` is used),
so `Convex.isFace_inter_setOf_eq` cuts a strictly smaller face out of `C'` that still contains `D`.
Corollary 6.5.2 then upgrades `D ∩ ri C' ≠ ∅` to `D = ri D ⊆ ri C'`.

`Convex.relint_relint` (`ri (ri C) = ri C`, Corollary 6.3.1) moved from `Simplicial.lean` to
`RelativeInterior.lean`, where it belongs, so that the maximality half of Theorem 18.2 can use it
without dragging in §10.

**Minkowski's theorem is a real addition.** Mathlib's Krein–Milman gives only
`closure (convexHull ℝ (extremePoints ℝ C)) = C`, and the closure cannot be dropped in general
because the extreme points of a compact convex set need not be closed (Rockafellar's own disk-plus-
segment example). `convexHull_extremePoints` proves `convexHull ℝ (C.extremePoints ℝ) = C` for
compact convex `C` in finite dimensions, by Rockafellar's induction on `dim C`: a relative boundary
point lies in the relative interior of a face of strictly smaller dimension (Theorem 18.2 plus
Corollaries 18.1.1 and 18.1.3), and a relative interior point lies on a segment joining two
relative boundary points (Theorem 18.4). The compact case of Theorem 18.4 is elementary — the line
through `x` in a direction of `vectorSpan ℝ C` meets `C` in a compact set of parameters, whose
largest and smallest elements are pushed out of `ri C` by prolongation.

### 4.2a `HullDirections.lean` and `Representation.lean` — the rest of §18

**Status: all of §18 is done.** Theorems 18.7 and 18.8 are in `Exposed.lean` and `Tangent.lean`;
see the end of this section. The `conv S` for a set mixing
points and directions is `convexHullPD P D = convexHull ℝ P + PointedCone.hull ℝ D`
(`HullDirections.lean`), and `isLeast_convexHullPD` proves it *is* Rockafellar's operator — the
least convex set containing `P` and receding in every direction of `D`. `Representation.lean` then
carries Theorem 18.3 (`IsFace.eq_convexHullPD`), Corollary 18.3.1, Theorem 18.4 in general,
Theorem 18.5 with Corollaries 18.5.2–18.5.3, and **Straszewicz's Theorem 18.6**, which Mathlib does
not have.

**Three of this sub-plan's four stated blockers were not blockers.**

* **Theorem 18.3 does not need Theorem 6.4** in its positive-coefficients form, or at all. The point
  half is `IsExtreme.mem_convexHull_inter` — split `P` into `P ∩ C'` and `P \ C'`, use
  `convexHull_union` and `IsExtreme.convex_sdiff` — and uses only the *definition* of an extreme
  set. The direction half is an induction over the cone hull carrying a scaling parameter, so that
  the `smul` step reduces to the generator step, and needs only Theorem 8.3 and Corollary 18.1.1.
* **Corollary 18.3.1's first half needs neither 18.3 nor 6.4**: a nonzero recession component at an
  extreme point exhibits that point as the midpoint of `[u, x+v]`.
* **Theorem 11.2, which this plan lists as blocking Theorem 18.7, is available** as
  `exists_separates_of_isOpen_of_disjoint_affine` in `Separation.lean`. The only thing that was
  really missing was a definition of an *exposed direction*. The "dimension bookkeeping" this bullet
  used to name as the second blocker — an `(n-2)`-dimensional affine set inside a supporting
  hyperplane meeting `C ∩ H` in exactly one point — **is not needed at all**, and neither is the
  book's reduction to an `n`-dimensional `C` with `n ≥ 2`: the extension is exactly the assertion
  that some `g - c·f` is maximised over `C` at `x`, and `exists_forall_sub_le_mul_sub` produces `c`
  by a one-dimensional argument on difference quotients. The formal Theorem 18.7 carries no
  dimension hypothesis. Its endgame is bounded/unbounded rather than the book's
  line/segment/half-line trichotomy, since Minkowski plus Straszewicz settle the bounded case in
  every dimension.
* **Theorem 18.8 does not sit behind 18.7.** The book routes it through Corollary 18.7.1 applied to
  the epigraph of the support function one dimension up; `Tangent.lean` goes through the polar
  instead — `C°` is compact when `0 ∈ int C`, and its exposed points *are* the normals of the
  tangent half-spaces — using neither 18.7 nor 18.7.1. The step the book cannot see is that an
  exposed point of `C° ⊆ E*` is exposed by a functional on `E*`, which must be identified with a
  point of `E`: that is `exists_forall_apply_eq` (`Duality/Pairing.lean`), and it is why the theorem
  needs reflexivity outside `ℝⁿ`. Corollary 18.7.1's "containing more than just the origin" is
  unnecessary — for `K = {0}` both sides are `{0}`.
* The planned names `closure_convexHull_exposed` and `eq_iInter_tangent_halfspaces` in
  `Representation.lean` became `closure_convexHullPD_exposedPoints_exposedDirections` in
  `Exposed.lean` and `eq_iInter_tangent_halfSpaces` (capital `S`) in `Tangent.lean`. `Tangent.lean`
  deliberately sits outside `Representation.lean`'s import closure — it is a statement about the
  polar.

Theorem 18.4's two exceptions turned out to be one predicate: allowing the functional in
`IsAffineHalf` to be `0` makes "affine set" the degenerate case of "closed half of an affine set".
Theorem 18.5's `dim C ≤ 1` case, which the book calls trivial, needs an explicit classification of
`C` as a closed half-line; conversely the induction is *simpler* than the book's, since Minkowski
(Corollary 18.5.1) discharges the bounded case in every dimension, so only unbounded `dim ≥ 2` uses
18.4 and 18.2. Straszewicz is cleaner with a nearest-point projection than with Rockafellar's `ε`.

**Both cone corollaries are stated twice, and the second statement is the book's.** Corollaries
18.5.2 and 18.7.1 are phrased by Rockafellar for an arbitrary set `T` of vectors meeting each
extreme (resp. exposed) ray, not for the set of all extreme (resp. exposed) directions.
`coneHull_extremeDirections_eq` and `closure_coneHull_exposedDirections` are the "all directions"
form, which is what the induction produces; `coneHull_of_forall_extremeDirection` and
`closure_coneHull_of_forall_exposedDirection` are the book's, and follow by monotonicity of the
cone hull. Neither needs Rockafellar's "containing more than just the origin": the zero cone has
no extreme directions, so the hypothesis on `T` is vacuous and both sides are `{0}`. The cone `K`
is described throughout by convexity plus closure under non-negative scaling rather than as a
bundled `PointedCone`, because that is how the sets coming out of Theorem 18.5 present
themselves; `coeHull_subset_of_forall_smul_mem` and `add_mem_of_convex_of_forall_smul_mem` are
the two layer-A lemmas that bridge to `PointedCone.hull`.

**Theorem 18.6 is stated in the hull form Rockafellar wants it for.**
`closure_convexHull_exposedPoints` — a compact convex set is `cl (conv (exp C))` — is Minkowski's
theorem composed with Straszewicz's, and does not go through Theorem 18.7, which supersedes it
for line-free sets but lives downstream in `Exposed.lean`.

## 4.3 `Polyhedral/Defs.lean` — §19

**Formalized: Theorem 19.1.** It lives in two files, `Polyhedral/Cone.lean` (the cone case) and
`Polyhedral/Defs.lean` (the set case), and the plan's route was changed — see "What actually
happened" below. The rest of §19 is not started.

**Theorem 19.1 (Minkowski–Weyl) is the gate for all of §19–§22 and is not in Mathlib.**

```lean
/-- A polyhedral convex set: a finite intersection of closed half-spaces.
Note the parenthesisation: `→ₗ[ℝ]` binds looser than `×`, so `Finset (E →ₗ[ℝ] ℝ × ℝ)` would be
`Finset (E →ₗ[ℝ] (ℝ × ℝ))` and `p.2` would elaborate to the `map_smul'` field. -/
def Polyhedral (C : Set E) : Prop :=
  ∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ), C = ⋂ p ∈ s, {x | p.1 x ≤ p.2}

/-- A finitely generated convex set: `conv S` for a finite set of points and directions.
Mathlib has no `cone : Set E → Set E`; `ConvexCone.hull` is the *wrong* object here because it need
not contain `0`, whereas Rockafellar's `cone D` must. Use `PointedCone.span`. -/
def FinitelyGenerated (C : Set E) : Prop :=
  ∃ P D : Finset E, C = convexHull ℝ ↑P + (PointedCone.span ℝ ↑D : Set E)

theorem polyhedral_iff_finitelyGenerated : Polyhedral C ↔ FinitelyGenerated C   -- **Thm 19.1**
```

Proof route — the two directions are different proofs and must not be conflated. Do it for **cones**
first. "Polyhedral ⇒ finitely generated" is Fourier–Motzkin elimination, a projection argument with
nothing to do with polarity. "Finitely generated ⇒ polyhedral" goes by double polarity, but
`K = K°°` holds only for **closed** cones, so it needs a prior theorem, which is the real content:

```lean
theorem isClosed_pointedCone_span (D : Finset E) : IsClosed (PointedCone.span ℝ ↑D : Set E)
```

(Carathéodory-for-cones plus a compactness argument.) Homogenising to the non-cone case needs
`C ≠ ∅` — for `C = ∅` the cone `{(λ,x) | λ ≥ 0, aᵢ x ≤ λ bᵢ}` is not the cone over `C` — and needs
`0⁺C = {x | aᵢ x ≤ 0}` to identify the `λ = 0` slice. Both directions need the polar-cone theory of
`Duality/Polar.lean` (Theorem 14.1).

### What actually happened

Four departures from the paragraph above, all of them simplifications.

(i) **Fourier–Motzkin is run for the *other* direction, and only once.** The plan assigned
elimination to "polyhedral ⇒ finitely generated". Assigning it to "finitely generated ⇒
polyhedral" is strictly better, because that direction has an induction with a trivial base: the
origin is polyhedral (`± bᵢ*` for a basis), and `PolyhedralCone.add_ray` adds one generator at a
time. The elimination step is then the elementary one — from `∃ t ≥ 0, ∀ i, φᵢ x ≤ t φᵢ v`, keep
the rows with `φᵢ v ≤ 0` and add one combination `(φᵢ v) φⱼ - (φⱼ v) φᵢ` per pair with
`φᵢ v > 0 > φⱼ v` — and the witness `t` is the largest of `0` and the lower bounds, which, being a
`Finset.max'`, is *one of them*; that observation removes every division from the feasibility
argument except one.

(ii) **Carathéodory is not needed, and neither is `isClosed_pointedCone_span` as a prior theorem.**
With Weyl proved first, a finitely generated cone *is* an intersection of finitely many closed
half-spaces, so `FinitelyGeneratedCone.isClosed` is three lines. The plan had this dependency
backwards.

(iii) **Minkowski's half needs no polar calculus.** `Duality/Polar.lean`'s Theorem 14.1 would do
the job, at the cost of choosing a pairing of `E` with a space representing its continuous dual.
Pairing `E` with `Module.Dual ℝ E` and calling `geometric_hahn_banach_closed_point` directly is
shorter and leaves the statement free of a pairing parameter: the constraint functionals generate
a cone `C` in the dual, Weyl makes `C` polyhedral, reflexivity turns the functionals cutting `C`
out into evaluations at points of `E`, and those points generate `K`.

(iv) **The empty set needs no side condition.** The homogenisation used is not "the cone over
`C`" but the explicit polyhedral cone `{(a, x) | a ≥ 0, φᵢ x ≤ bᵢ a}`, whose level-one slice is `C`
by construction, and the dictionary
`slice_hull_union : {x | (1,x) ∈ cone ({1} × P ∪ {0} × D)} = conv P + cone D` is proved for
arbitrary `P` and `D`. When `P = ∅` both sides are empty, because `(1, x)` never lies in the cone
generated by `{0} × D`. So Theorem 19.1 is stated with no nonemptiness hypothesis.

| Lean name | book | status |
|---|---|---|
| `PolyhedralCone`, `FinitelyGeneratedCone` (defs) | §19 | done |
| `PolyhedralCone.add_ray` — Fourier–Motzkin | §19 | done |
| `FinitelyGeneratedCone.polyhedralCone` | **Thm 19.1** (cones, Weyl) | done |
| `PolyhedralCone.finitelyGeneratedCone` | **Thm 19.1** (cones, Minkowski) | done |
| `FinitelyGeneratedCone.isClosed` | prerequisite Rockafellar proves from Carathéodory | done, as a corollary |
| `liftAt`, `coneOver`, `slice_hull_liftOne`, `slice_hull_union` | the homogenisation dictionary | done |
| `polyhedral_iff_finitelyGenerated` | **Thm 19.1** | done |
| `polyhedral_convexHull_finset` | Cor 19.1.1 | done |
| `Polyhedral.isClosed`, `FinitelyGenerated.isClosed` | Cor 19.1.2 (part) | done |

**One deviation of statement.** `Polyhedral C` is defined as `∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ),
C = {x | ∀ q ∈ s, q.1 x ≤ q.2}`, with `setOf` rather than the `⋂` of the plan; the two are the same
set and `Polyhedral.eq_biInter` records the intersection form. Every proof in the file works with
the `setOf` form, so it is the definition.

### The calculus (`Polyhedral/Ops.lean`) and functions (`Polyhedral/Function.lean`)

The organising observation is that **each operation is proved on whichever side of Theorem 19.1
makes it trivial**, and that the two easy sides are complementary. Intersections and affine
preimages are trivial for the inequality description — concatenate the two systems; compose each
functional with the map and absorb the translation into the right-hand side — and need no
finite-dimensionality, so they sit at layer A. Images and sums are trivial for the generator
description — push the generators forward; add the point sets and unite the direction sets — and
are layer D only because Theorem 19.1 is.

| Lean name | book | status |
|---|---|---|
| `polyhedral_univ`, `polyhedral_halfSpace` | §19 | done |
| `Polyhedral.inter`, `Polyhedral.comap`, `Polyhedral.comap_affine` | **Thm 19.3** (part) | done, layer A |
| `Polyhedral.prod`, `PolyhedralCone.polyhedral`, `polyhedral_zero` | §19 | done |
| `Polyhedral.image`, `Polyhedral.add`, `.neg`, `.sub`, `.smul` | **Thm 19.3**, Cor 19.3.2 | done |
| `separatesStrongly_of_polyhedral` | **Cor 19.3.3** | done |
| `toNNLinear`, `image_coe_hull`, `coe_hull_union` | plumbing for the generator side | done |
| `recessionCone_polyhedral_system`, `Polyhedral.polyhedralCone_recessionCone` | **Thm 19.5**, inequality side | done |
| `recessionCone_of_finitelyGenerated`, `Polyhedral.recessionCone_image` | **Thm 19.5**, generator side | done — `Polyhedral/Recession.lean` |
| `verticalRay`, `epi_posHomGen_of_epi_eq`, `polyhedralFn_posHomGen_of_epi_eq`, `epi_convFn_of_epi_eq`, `polyhedralFn_posHomGen_convFn` | **Cor 19.1.2 for functions** | done — `Polyhedral/Homogeneous.lean` |
| `coe_hull_of_convex_zero_mem`, `FinitelyGeneratedCone.add`, `polyhedral_singleton` | plumbing for §20 | done |
| `coe_hull_coe_submodule`, `polyhedral_coe_submodule`, `polyhedral_coe_affineSubspace` | subspaces and affine sets are polyhedral | done |
| `finitelyGeneratedCone_hull_of_zero_mem`, `finitelyGeneratedCone_coe_submodule` | **Cor 19.7.1** | done |
| `PolyhedralFn`, `.convexFn`, `.lowerSemicontinuous`, `.closedFn` | §19 | done |
| `PolyhedralFn.polyhedral_dom`, `.polyhedral_sublevel` | Thm 19.1 for functions | done |
| `polyhedralFn_indicatorFn` | §19 | done |
| `mem_epi_conj_iff`, `PolyhedralFn.conj` | **Thm 19.2** | done, in `Polyhedral/Conjugate.lean` |
| `PolyhedralFn.add` | **Thm 19.4** | done |
| `epi_infConv_of_polyhedralFn`, `PolyhedralFn.infConv` | Cor 19.3.4 | done |
| `coe_subset_of_finitelyGenerated`, `coe_hull_subset_recessionCone_of_finitelyGenerated`, `subset_coe_hull_of_finitelyGenerated` | the generator dictionary Thms 19.6/19.7 run on | done |
| `finitelyGenerated_closure_convexHull_union`, `polyhedral_closure_convexHull_union` | **Thm 19.6** | done |
| `finitelyGeneratedCone_closure_coe_hull`, `polyhedralCone_closure_coe_hull` | **Thm 19.7** | done |

Four notes. (i) `recessionCone_polyhedral_system` is `Recession/Cone.lean`'s
`recessionCone_setOf_forall_le` with the inequalities turned around, not a second proof; the two
`neg`s in its statement are the cost of that reuse, and it is cheaper than the index juggling
would be if §19 adopted the `≥` orientation. (ii) `PolyhedralFn.closedFn` carries `∀ x, f x ≠ ⊥`,
because `PolyhedralFn` alone does not exclude `f ≡ ⊥` (whose epigraph is all of `E × ℝ`, cut out
by the empty system) and `ClosedFn` has a separate `⊥` branch; lower semicontinuity needs no such
hypothesis. (iii) `polyhedralFn_indicatorFn` is the bridge that lets §20's constraint
qualifications be stated about sets as well as functions, and it is what turns a support function
into a polyhedral function in Theorem 20.3. (iv) Corollary 19.3.3 turned out to be
cheaper than its §11 analogue rather than harder: Theorem 11.4
(`separatesStrongly_iff_zero_notMem_closure_sub`) asks that the origin miss the *closure* of
`C - D`, and `C - D` is polyhedral, hence already closed — so neither set needs to be compact and
neither needs to be nonempty.

**Theorem 19.2 lives in its own file.** `Polyhedral/Conjugate.lean` holds it, because it is the
only part of §19 that needs `Duality/Conjugate.lean`; keeping it out of `Polyhedral/Function.lean`
keeps the whole polyhedral calculus independent of conjugacy. The proof is on the epigraph, not on
the `⨆` formula: `mem_epi_conj_iff` says that `(y, c) ∈ epi f*` exactly when the linear functional
`p ↦ ⟨p.1, y⟩ - p.2` is bounded by `c` on `epi f`, and on `conv P + cone D` that is *two finite
families* of linear inequalities in `(y, c)`. No properness hypothesis is needed: the `⊥`/`⊤` cases
are handled uniformly by `EReal.lt_iff_exists_real_btwn`, and `P = ∅` (i.e. `epi f = ∅`) is the one
case split, where `epi f*` is everything and the empty system describes it.

**Corollary 19.3.4 is two lines once the epigraph sum is known to be an epigraph.** `epi_infConv`
needs `IsEpiLike (epi f + epi g)`, whose two halves are upward closure — `mem_epi_add_epi_of_le`,
added to `Operations/InfConv.lean` — and closedness, which polyhedrality supplies for free.

**Theorems 19.6 and 19.7 are about *closures*; this plan's one-line summary of them was wrong.**
The identity one would guess — `conv (⋃ᵢ (conv Pᵢ + cone Dᵢ)) = conv (⋃ᵢ Pᵢ) + cone (⋃ᵢ Dᵢ)` — is
*false*. Take `C₁ = {0}` and `C₂ = {a + s d : s ≥ 0}` with `a ≠ 0`. Then
`conv (C₁ ∪ C₂) = {0} ∪ {μ a + u d : μ ∈ (0, 1], u ≥ 0}`, which does not contain `d`, while the
right-hand side `conv {0, a} + cone {d}` does. So `conv (C₁ ∪ C₂)` need not be closed, let alone
polyhedral. The book says so: 19.6 asserts that `cl (conv (C₁ ∪ ⋯ ∪ Cₘ))` is polyhedral and
describes it as `⋃ {λ₁C₁ + ⋯ + λₘCₘ}` over `λᵢ ≥ 0` with `Σλᵢ = 1`, *with `0⁺Cᵢ` substituted for
`0·Cᵢ`*; 19.7 does the same for `cl (cone C)`, described as `⋃ {λC : λ > 0 or λ = 0⁺}`.

**The `0⁺` convention is dropped in favour of adding the recession cones.** Rockafellar's unions
over weights are, in both cases, the plain construction plus the recession cones, so the Lean
statements are

```lean
theorem finitelyGenerated_closure_convexHull_union (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    FinitelyGenerated (closure (convexHull ℝ (C₁ ∪ C₂)))
      ∧ closure (convexHull ℝ (C₁ ∪ C₂))
          = convexHull ℝ (C₁ ∪ C₂) + (recessionCone C₁ + recessionCone C₂)      -- Thm 19.6

theorem finitelyGeneratedCone_closure_coe_hull (hC : Polyhedral C) (hne : C.Nonempty) :
    FinitelyGeneratedCone (closure (PointedCone.hull ℝ C : Set E))
      ∧ closure (PointedCone.hull ℝ C : Set E)
          = (PointedCone.hull ℝ C : Set E) + recessionCone C                    -- Thm 19.7
```

with `polyhedral_closure_convexHull_union` and `polyhedralCone_closure_coe_hull` as the
first-component wrappers. Two sets, not `m`: the `m`-set version is the evident induction and
nothing in the backbone asks for it. Nonemptiness is not decoration — `0⁺∅` is everything, and the
step that pushes a recession direction into the closure needs a point to push it from.

**Each proof is a sandwich between three sets.** With `Cᵢ = conv Pᵢ + cone Dᵢ`, let `A` be the
finitely generated set built from the pooled generators. Then (1) `cl (conv (C₁ ∪ C₂)) ⊆ A`, because
`A` is closed and convex and contains both `Cᵢ`; (2) `A ⊆ conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)`, because
the point generators lie in the sets and the direction generators recede; (3) the repaired set is
back inside the closure, by Theorem 8.3 (`mem_recessionCone_of_exists_ray`) applied to the closure.
The three inclusions close the circle, so all three sets coincide — which gives both halves of the
conjunction at once. Steps (1) and (2) run on three one-line dictionary lemmas about a finitely
generated presentation — `coe_subset_of_finitelyGenerated`,
`coe_hull_subset_recessionCone_of_finitelyGenerated` and `subset_coe_hull_of_finitelyGenerated` —
which live in `Ops.lean`'s layer A and also shorten Corollary 19.7.1.

| Lean name | book |
|---|---|
| `polyhedral_iff_finitelyGenerated` | **Thm 19.1**, Cor 19.1.1–2 |
| `PolyhedralFn` and `polyhedralFn_iff_finitelyGenerated` | Thm 19.1, Cor 19.1.2 |
| `PolyhedralFn.conj` | **Thm 19.2**, Cor 19.2.1–2 |
| `Polyhedral.image`, `.preimage`, `.add`, `PolyhedralFn.infConv` | **Thm 19.3**, Cor 19.3.1–4 |
| `PolyhedralFn.add` | Thm 19.4 |
| `Polyhedral.recessionCone`, `.smul` | Thm 19.5, Cor 19.5.1 |
| `finitelyGenerated_closure_convexHull_union`, `finitelyGeneratedCone_closure_coe_hull`, `finitelyGeneratedCone_hull_of_zero_mem` | Thm 19.6, 19.7, Cor 19.7.1 |

Corollary 19.3.3 (two disjoint polyhedral sets are strongly separated) is the polyhedral analogue of
Corollary 11.4.1 and is used in §22.

## 4.4 §20 — four files, not one

The plan put all of §20 in `Polyhedral/Duality.lean`. It ended up in four modules, because the
section's five theorems have almost nothing in common beyond the word "polyhedral": 20.1 is
conjugacy, 20.2 is separation, 20.3 is both at once, and 20.4/20.5 are elementary geometry that
needs neither. Splitting keeps `Polyhedral/Simplicial.lean` — the one §20 file that `Continuity.lean`
consumes, through Theorem 10.2 — free of the duality stack.

| Lean name | file | book | status |
|---|---|---|---|
| `IsExactSum.of_polyhedral_pair` | `Polyhedral/Duality.lean` | Thm 20.1, both sides polyhedral | done |
| `IsExactSum.of_polyhedral` | `Polyhedral/Duality.lean` | **Thm 20.1** | done |
| `relint_inter_relint_nonempty_of_subset_affineSpan` | `Polyhedral/Duality.lean` | the `ri` step Thm 20.1 turns on | done |
| `disjoint_relint_of_separates_of_not_subset` | `Polyhedral/Separation.lean` | Thm 20.2, necessity | done |
| `exists_separates_not_subset_iff_disjoint_relint` | `Polyhedral/Separation.lean` | **Thm 20.2** | done |
| `supportFn_le_neg_supportFn_neg_iff` | `Polyhedral/Separation.lean` | the support-function dictionary | done |
| `nonempty_inter_relint_iff_forall_supportFn` | `Polyhedral/Separation.lean` | **Cor 20.2.1** | done |
| `polyhedral_dom_supportFn`, `nonempty_dom_supportFn_inter_relint` | `Polyhedral/Closedness.lean` | the barrier-cone constraint qualification | done |
| `isClosed_add_of_polyhedral` | `Polyhedral/Closedness.lean` | **Thm 20.3** | done |
| `separatesStrongly_of_polyhedral_of_recession` | `Polyhedral/Closedness.lean` | **Cor 20.3.1** | done |
| `exists_polyhedral_mem_nhds_subset_ball`, `Polyhedral.exists_finset_convexHull` | `Polyhedral/Simplicial.lean` | Cor 19.1.2 and plumbing | done |
| `exists_polyhedral_between` | `Polyhedral/Simplicial.lean` | Thm 20.4 | done |
| `Polyhedral.locallySimplicial` | `Polyhedral/Simplicial.lean` | **Thm 20.5** (used by Thm 10.2) | done |
| `polarCone_dom_supportFn` | `Duality/Barrier.lean` | **Cor 14.2.1**, the §14 debt Thm 20.3 collects | done |

**Corollary 20.1.1 is not stated separately.** It is Theorem 20.1 applied to conjugates and iterated
over a finite family; the only consumer in the backbone is Theorem 20.3, and there the two-function
case is what is used.

**Theorem 20.1 needs one lemma Rockafellar states in a clause.** He asserts
`ri (M ∩ dom g₁) ∩ ri (dom g₂) ≠ ∅` in a line; formalised, that is
`relint_inter_relint_nonempty_of_subset_affineSpan`, proved by prolonging the segment from a point
of `ri D₁` *through* `x₀` (the prolongation principle) and then applying the line-segment principle
twice with a common parameter `s = min (t/2) 1`.

**Theorem 20.2 is proved with an explicit translation.** Rockafellar moves the common point of `C₁`
and the relative boundary of `C₂'` to the origin; the Lean proof carries the translation, so the cone
is `hull (C₁ - x₀)` and the subspace is `(aff C₂).direction ⊓ ker f`. The separating functional is
then found by a positivity argument rather than by Rockafellar's elimination: any `φ` in a conic
representation of `K + M₀` with `φ w > 0` at a `w` outside it already works, because
`z - (f z / f w) • w ∈ M₀` for every `z` of the translated `C₂'` and `φ` vanishes on `M₀`.

**Theorem 20.3 reads closedness off effective domains.** Once `IsExactSum.of_polyhedral` gives
`(δ*(·|C₁) + δ*(·|C₂))* = δ(·|C₁) □ δ(·|C₂)`, the left side is `δ(· | cl (C₁ + C₂))` by
`conj_supportFn_of_convex` and the right side has effective domain `C₁ + C₂` by `dom_infConv`, so
comparing domains gives `cl (C₁ + C₂) = C₁ + C₂` — the infimal convolution itself is never computed.
The constraint qualification comes from Theorem 20.2 applied to the two barrier cones, with
Corollary 14.2.1 turning the separating functional into a recession direction.

**Theorem 20.4 uses cubes, not simplices, and needs less than the book asks.** Rockafellar covers `C`
by simplices; coordinate cubes `{y | ∀ i, |bᵢ*(y - x)| ≤ c}` do the same job, are polyhedral by
inspection and bounded by a one-line norm estimate. Convexity and nonemptiness of `C` are not used —
only compactness — and the deviation is recorded in the file's docstring.

## 4.5 `Helly.lean` and `HellyRefined.lean` — §21

Mathlib has `Convex.helly_theorem'` for **finite** families of convex sets in finite dimension.
Rockafellar's Corollary 21.3.2 is the infinite-family version under a recession hypothesis, and
Theorem 21.3 is a statement about systems of convex *inequalities*, of which Helly is the
indicator-function case.

| Lean name | book | status |
|---|---|---|
| `alternative_of_convex_system`, `not_exists_forall_neg_of_forall_zero_le_weighted` | **Thm 21.1** | done |
| `alternative_of_convex_system_affine` | **Thm 21.2** | done |
| `combo_affine_sum`, `convexFn_coe_affine_sum`, `eq_zero_of_nonneg_of_mem_relint_affine_sum`, `polyhedral_nonpos_orthant` | the small lemmas Thm 21.2 runs on | done |
| `alternative_infinite_system_univ`, `alternative_infinite_system` | **Thm 21.3** | done |
| `exists_forall_le_zero_of_forall_subsystem` | **Cor 21.3.1** | done |
| `helly_of_no_common_recession` | **Cor 21.3.2** | done |
| `alternative_infinite_system_univ_of_affine_tail` (`HellyRefined.lean`) | **Thm 21.4** | done |
| `exists_forall_le_zero_of_forall_subsystem_of_affine_tail` (`HellyRefined.lean`) | **Cor 21.3.1** under Thm 21.4's hypothesis | done |
| `helly_of_polyhedral_tail` (`HellyRefined.lean`) | **Thm 21.5** | done |
| `helly_finite` | **Thm 21.6** ← Mathlib `Convex.helly_theorem'` | done |
| `exists_mem_of_forall_subsystem`, `exists_mem_of_forall_subsystem_lt` | **Cor 21.6.1** | done |
| `sparse_alternative_of_convex_system` | **Cor 21.6.2** | done |

Theorem 21.1 is a Gordan/Fan-style alternative proved from the separation theorem applied to the
image of `C` under `x ↦ (f₁ x, …, f_m x)`; it is the workhorse for §27 and §28 existence results.

**The weighted sum is `∑ i, (l i : EReal) * f i x`.** `EReal` sends `0 * ⊤` to `0`, which is exactly
Rockafellar's convention that a vanishing multiplier drops its constraint; no `0⁺` substitution
convention is needed anywhere in §21. The separation is done in `ι → ℝ`, the multipliers are read off
as `l i = g (Pi.single i 1)`, and **Corollary 7.3.3** (`ConvexFn.le_of_mem_closure`, added to
`RelativeInterior.lean` for this purpose) is what moves the conclusion from `ri C` to `C`.

**Theorem 21.2 keeps the affine constraints in a second index type `κ`, not in a tail of `ι`.** They
are modelled as `E →ᵃ[ℝ] ℝ`, enter `C₁` as *equations*, and the separation is the polyhedral
Theorem 20.2 in `(ι ⊕ κ) → ℝ`. Theorem 21.1 is the case `κ = Empty` but is **proved
independently**, because Rockafellar's own remark — §21 is readable without §20 as long as 21.2,
21.4 and 21.5 are skipped — is only true if 21.1 has a proof that uses no more than Theorem 11.3,
and Corollary 28.2.1 is meant to take that route.

**Theorem 21.3 and Corollaries 21.3.1–21.3.2 are done**, once Theorem 13.5 and Corollary 17.1.3
arrived. Two corrections came out of it.

*The last step needs neither Theorem 16.4 nor Theorem 16.1.* Rockafellar routes it through
`f* = cl (f₁*λ₁ □ ⋯ □ fₘ*λₘ)`; the inequality `∑ λᵢ fᵢ x ≥ -∑ λᵢ fᵢ* yᵢ` is Fenchel's inequality
summed termwise, using only `∑ λᵢ yᵢ = 0`. No infimal convolution appears anywhere.

*Corollary 21.3.1's tolerance has to be halved.* The book normalises `∑ λᵢ = 1` and uses tolerance
`ε/λ`, which makes the summed inequality strict; `EReal` is not a cancellative ordered monoid, so
`Finset.sum_lt_sum` is unavailable. Tolerance `ε/(2λ)` keeps every step non-strict.

**The closedness obstruction was closed before 21.4 landed.** This plan recorded
that the real obstruction was `IsExactSum.of_relint`/`of_polyhedral` asking for
`ClosedProperConvexFn` where Rockafellar asks only for proper convex, and that closing it meant
proving `cl (f + g) = cl (cl f + cl g)` and threading it through Theorem 16.4 — "a §16 project, not
a §21 one". **That analysis was right about the defect and wrong about the fix.** Closedness was
never load-bearing in `conj_add_eq_clFn_infConv`; it was load-bearing only in the comparison of
`(f + g)*` with `(cl f + cl g)*`, and those two conjugates are *equal* under the constraint
qualification. `conj_add_eq_conj_clFn_add_clFn` (Theorem 9.3 in conjugate form) proves it by one
passage to the limit along a segment, and `IsExactSum.of_relint` and `IsExactSum.of_polyhedral` now
carry the book's hypotheses; the closed cases survive as `IsExactSum.of_relint_closed` and
`IsExactSum.of_polyhedral_closed`, which is where the argument still lives. Theorem 9.3 as the book
states it, `clFn_add`, was already in `Recession/Closedness.lean` — but it is *not* what §20
consumes, because proving it needs Theorem 7.5 for `f + g` and hence a relative interior point of
both domains, whereas Theorem 20.1 has only a point of `dom f`. The conjugate form is what makes
the polyhedral side work.

**Theorems 21.4 and 21.5 are done**, in `HellyRefined.lean`. The two §19/§20 prerequisites this plan
named are both discharged:

* **Corollary 19.1.2 for *functions*** is `polyhedralFn_posHomGen_of_epi_eq`
  (`Polyhedral/Homogeneous.lean`): if `epi f` is `conv P` plus the vertical ray `cone {(0,1)}` for a
  finite `P`, then `epi (posHomGen f)` is the cone generated by `P` together with `(0, 1)`, which is
  finitely generated and so polyhedral. The extra generator is exactly Rockafellar's, and it is not
  optional: the cone hull of `epi f` meets the vertical axis only at the origin. The hypothesis is
  `epi f = conv P + cone {(0,1)}` and **not** "`f` is polyhedral" — with a general direction set the
  identity is false (`f x = |x| + 1` on `ℝ`, where `(1,1) ∈ epi (posHomGen f)` is in no
  non-negative combination of `epi f ∪ {(0,1)}`), and the vertical-ray case is the one §21 needs,
  since the conjugate of an affine function is a point indicator.
* `epi_convFn_of_epi_eq` and `polyhedralFn_posHomGen_convFn` carry that through the convex hull:
  for a *finite* family whose members have single translated vertical rays for epigraphs,
  `epi (convFn g) = conv {pᵢ} + cone {(0,1)}` and `posHomGen (convFn g)` is polyhedral. `IsEpiLike`
  for a convex hull of a union is not automatic — `Operations/Hull.lean` carries it as a hypothesis
  — and here it is paid for by finite generation.
* The bridge to `k₀` is `conj_affineFn` / `epi_conj_affineFn`: `fᵢ* = δ(· ∣ aᵢ) + αᵢ`, so
  `epi fᵢ*` is one translated vertical ray. The separating hypothesis it needs is
  **`B.SeparatingRight`** — not `IsCompatiblePairing`, which gives surjectivity of `evalCLM` rather
  than injectivity. In finite dimensions `separatingRight_flip_of_separatingDual` supplies it, but
  it is carried explicitly, as `Saddle/Conjugate.lean` and `LinearInequalities.lean` already do.
* `kⱼ* = δ(· ∣ Cⱼ)` is `conj_posHomGen_convFn_conj` — `conj_posHomGen` (Theorem 13.5, no
  hypotheses) followed by `conj_convFn` (Theorem 16.5) and Fenchel–Moreau — and the separation step
  is `nonempty_neg_dom_inter_relint_dom`, Theorem 20.2 applied to `-dom k₀` and `dom k₁`.

**Rockafellar's reduction to `I₀ ≠ ∅ ≠ I₁` is unnecessary.** He adjoins identically-zero functions
to both halves so that `k₀` and `k₁` are defined. In Lean neither half has to be nonempty:
`posHomGen h 0 ≤ 0` whatever `h` is, so `0 ∈ dom kⱼ` always, and `convFn` over an empty family
generates `δ(· ∣ 0)`, which is polyhedral and whose domain `{0}` is exactly what the separation
step needs. The two halves are indexed by `{i // i ∈ I₀}` and `{i // i ∉ I₀}`.

**The subadditivity step is Theorem 4.7 with the *other* hypothesis.**
`PosHomogeneous.convexFn_iff_subadditive` asks `∀ x, f x ≠ -∞`, which an improper `k₁` violates.
`PosHomogeneous.add_le_add_of_ne_top` asks `f x ≠ +∞` and `f y ≠ +∞` instead, and reads the
inequality straight off `PosHomogeneous.epiCone`. Neither hypothesis can be dropped: on `ℝ²` the
function with epigraph `{(s,t,μ) ∣ s > 0} ∪ {(0,0,μ) ∣ μ ≥ 0}` is positively homogeneous, convex
and `0` at the origin, yet `g(0,0) = 0 > ⊥ = g(-1,0) + g(1,0)`.

**Theorem 27.3's polyhedral refinement no longer waits for Theorem 21.5.** It was the one downstream
consumer named for 21.5 in `06-optimization.md`; it is now proved by projecting along the constancy
space of the objective, and `Polyhedral.recessionCone_image` is what pays for polyhedrality of the
constraint set. Theorems 21.4 and 21.5 keep their own interest, but nothing in §27 is blocked on
them.

The epigraph-sum description of `conv {k₀, k₁}` was **not** needed at all: 21.4 uses it only as
`k 0 ≤ k₀ (-z) + k₁ z`, which follows from `posHomGen_mono` (a subfamily has the larger `convFn`,
hence `k ≤ kⱼ`) and the fact that `epi k` is a convex cone containing `epi k₀ ∪ epi k₁`. So
`apply_zero_eq_bot_of_le_of_le` takes an *arbitrary* positively homogeneous convex `k` below both
`kⱼ`, and `conv {k₀, k₁}` is never formed.

**Theorem 21.5 is pure re-indexing on top of 21.4.** Each polyhedral `Cᵢ`, `i ∈ I₀`, is cut out by
finitely many inequalities *of the pairing* (`Polyhedral.exists_finset_pairing`, which represents
Rockafellar's linear functionals through `LinearMap.toContinuousLinearMap` and `exists_pairing_eq`),
the family is re-indexed by `{i ∉ I₀} ⊕ Σ (i ∈ I₀), (constraints of Cᵢ)`, and the
`(n+1)`-intersection property survives because several constraints of the same `Cᵢ` project to one
index of the original family (`Finset.card_image_le`). "Linear in a direction" becomes "constant in
a direction" through `constancySpace_indicatorFn`.

**Theorem 21.6 does not wait for any of that.** Rockafellar derives it from Corollary 21.3.2, but
Mathlib proves it directly from Radon's theorem, so `helly_finite` is an alias and Corollaries
21.6.1 and 21.6.2 are available now. Corollary 21.6.2 is stated as
`∃ S l, S.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧ …`, which avoids deciding `l i ≠ 0` and makes
"extend the subsystem's multipliers by zero" a one-liner.

## 4.6 `LinearInequalities.lean` — §22

Rockafellar flags §22 as special and used nowhere else in the book. Backbone value is low; the two
results worth having are:

| Lean name | book | status |
|---|---|---|
| `farkas_of_pairing`, `farkas`, `mem_pointedCone_hull_range_iff`, `isClosed_coe_pointedCone_hull_range` | **Cor 22.3.1**, Farkas' Lemma | done |
| `exists_multipliers_of_infeasible`, `alternative_linear_system` | **Thm 22.1** (Gale) | done |
| `affineMapOfPairing`, `pairing_sum_smul`, `combined_value`, `eq_zero_of_forall_pairing_eq_zero`, `eq_zero_and_nonpos_of_forall_nonneg`, `alternative_linear_system_strict` | **Thm 22.2** (Motzkin) | done |
| `le_consequence_iff` | **Thm 22.3** | done |
| `ElementaryVector` and its API | Lemma 22.4, 22.5, Cor 22.4.1 | not done — out of scope |
| `alternative_interval_system` | **Thm 22.6** | not done — out of scope |

**Theorem 22.1 does not have to wait for Theorem 21.4.** This section inherited Rockafellar's
derivation of 22.1 from 21.4. It is available directly from Farkas' Lemma, which is `K°° = K`
(`polarCone_polarCone`, Theorem 14.1) for a cone that is closed because finitely generated
(Minkowski–Weyl, `Polyhedral/Cone.lean`). Only Theorem 22.2 uses §21, and it uses Theorem 21.2,
which was already formalized.

**Theorem 22.2's multiplier condition needs a *separating* pairing.** Over `ℝⁿ` the step "the affine
function is non-negative everywhere, hence its linear part is zero" is invisible; in the pairing
formulation `IsCompatiblePairing B` is not enough, since it gives surjectivity rather than
injectivity of `evalCLM`. `IsCompatiblePairing B.flip` supplies it through Hahn–Banach on `F`.
| `tucker_complementarity` | **Thm 22.7** |

Everything except Tucker's complementarity theorem is derivable from §21; Rockafellar gives an
independent elementary proof, which the surface can record as an alternative.

Assign §22 to the **surface** unless a downstream demand appears; the backbone keeps only
`alternative_linear_system` (Farkas-type lemmas are broadly reusable).
