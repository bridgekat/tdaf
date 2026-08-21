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
[D7](00-overview.md#d7): a "set of points and directions" is a set `S ⊆ ℝ × E` with first coordinate
in `{0,1}`, and `conv S` is the level-1 slice of `cone S`.

| Lean name | book |
|---|---|
| `mem_convexHull_iff_exists_card_le` (points and directions) | **Thm 17.1** |
| `convexHull_iUnion_eq_affineIndependent_combination` | Cor 17.1.1–17.1.2 |
| `convFn_eq_finite_combination` | Cor 17.1.4–17.1.6 |
| `IsCompact.isClosed_convexHull` : `cl (conv S) = conv (cl S)` for bounded `S` | **Thm 17.2**, Cor 17.2.1 |
| `convFn_of_compact_epi` | Thm 17.3 |

Theorem 17.2 for *compact* `S` is `IsCompact.convexHull` in Mathlib
(`Analysis/Convex/Topology.lean`); only the bounded-not-closed case is new.

## 4.2 `Face.lean` — §18

Mathlib has `IsExtreme`, `Set.extremePoints`, `IsExposed`, and Krein–Milman
(`Analysis/Convex/{Extreme,Exposed,KreinMilman}.lean`). Rockafellar's *face* is more general than
Mathlib's `IsExtreme` in one respect — his faces are convex subsets `C'` such that every segment in
`C` with a relative interior point in `C'` lies in `C'` — but the two coincide for convex `C`.
First task: prove `IsExtreme ℝ C C' ↔ Rockafellar.IsFace C C'` for convex `C`, then reuse Mathlib.

| Lean name | book |
|---|---|
| `IsFace.subset_of_relint_meets` | **Thm 18.1**, Cor 18.1.1–3 |
| `relint_faces_partition` | **Thm 18.2** |
| `IsFace.convexHull_inter` | Thm 18.3, Cor 18.3.1 |
| `mem_relint_iff_mem_segment_of_relbd` | Thm 18.4 |
| `eq_convexHull_extremePoints_directions` | **Thm 18.5**, Cor 18.5.1–3 (Cor 18.5.1 = Krein–Milman, in Mathlib) |
| `dense_exposedPoints` (Straszewicz) | **Thm 18.6** |
| `closure_convexHull_exposed` | Thm 18.7, Cor 18.7.1 |
| `eq_iInter_tangent_halfspaces` | Thm 18.8 |

New relative to Mathlib: extreme/exposed **directions** (which are extreme rays of the recession
cone, so again the `ℝ × E` cone picture), Straszewicz's theorem, Theorem 18.8.

## 4.3 `Polyhedral/Defs.lean` — §19

**Theorem 19.1 (Minkowski–Weyl) is the gate for all of §19–§22 and is not in Mathlib.**

```lean
/-- A polyhedral convex set: a finite intersection of closed half-spaces. -/
def Polyhedral (C : Set E) : Prop := ∃ (s : Finset (E →ₗ[ℝ] ℝ × ℝ)), C = ⋂ p ∈ s, {x | p.1 x ≤ p.2}

/-- A finitely generated convex set: `conv S` for a finite set of points and directions. -/
def FinitelyGenerated (C : Set E) : Prop := ∃ (P D : Finset E), C = convexHull ℝ P + cone D

theorem polyhedral_iff_finitelyGenerated : Polyhedral C ↔ FinitelyGenerated C   -- **Thm 19.1**
```

Proof route: prove it first for **cones** (`K = {x | ⟨x,aᵢ⟩ ≤ 0}` ⟺ `K = cone {b₁,…,b_k}`) by double
polarity — `K°` finitely generated ⟺ `K` polyhedral — with induction on the number of generators
(Fourier–Motzkin), then homogenise to get the general case via [D6](00-overview.md#d6). Both
directions need the polar-cone theory of `Duality/Polar.lean` (Theorem 14.1).

| Lean name | book |
|---|---|
| `polyhedral_iff_finitelyGenerated` | **Thm 19.1**, Cor 19.1.1–2 |
| `PolyhedralFn` and `polyhedralFn_iff_finitelyGenerated` | Thm 19.1, Cor 19.1.2 |
| `PolyhedralFn.conj` | **Thm 19.2**, Cor 19.2.1–2 |
| `Polyhedral.image`, `.preimage`, `.add`, `.infConv` | **Thm 19.3**, Cor 19.3.1–4 |
| `PolyhedralFn.add` | Thm 19.4 |
| `Polyhedral.recessionCone`, `.smul` | Thm 19.5, Cor 19.5.1 |
| `Polyhedral.convexHull_iUnion`, `.cone` | Thm 19.6, 19.7, Cor 19.7.1 |

Corollary 19.3.3 (two disjoint polyhedral sets are strongly separated) is the polyhedral analogue of
Corollary 11.4.1 and is used in §22.

## 4.4 `Polyhedral/Duality.lean` — §20

The polyhedral refinements of the constraint qualifications; these feed
[`Exact.lean`](03-relint-recession.md#36-tdafanalysisconvexdualityexactlean--d5) as
`IsExactSum.of_polyhedral`.

| Lean name | book |
|---|---|
| `IsExactSum.of_polyhedral` | **Thm 20.1**, Cor 20.1.1 |
| `separatesProperly_of_polyhedral` | **Thm 20.2**, Cor 20.2.1 |
| `isClosed_add_of_polyhedral` | **Thm 20.3**, Cor 20.3.1 |
| `exists_polyhedral_between` | Thm 20.4 |
| `Polyhedral.locallySimplicial` | **Thm 20.5** (used by Thm 10.2) |

## 4.5 `Helly.lean` — §21

Mathlib has `helly_theorem'` for **finite** families of convex sets in finite dimension. Rockafellar's
Corollary 21.3.2 is the infinite-family version under a recession hypothesis, and Theorem 21.3 is a
statement about systems of convex *inequalities*, of which Helly is the indicator-function case.

| Lean name | book |
|---|---|
| `alternative_of_convex_system` (a theorem of the alternative) | **Thm 21.1** |
| `alternative_with_affine` | Thm 21.2 *(needs §20)* |
| `alternative_infinite_system` | **Thm 21.3**, Cor 21.3.1 |
| `helly_of_no_common_recession` | **Cor 21.3.2** |
| `helly_of_polyhedral_tail` | Thm 21.4, 21.5 |
| `helly_finite` | **Thm 21.6** ← Mathlib `helly_theorem'` |
| `exists_sparse_multipliers` | Cor 21.6.1–2 |

Theorem 21.1 is a Gordan/Fan-style alternative proved from the separation theorem applied to the
image of `C` under `x ↦ (f₁ x, …, f_m x)`; it is the workhorse for §27 and §28 existence results.

## 4.6 `LinearInequalities.lean` — §22

Rockafellar flags §22 as special and used nowhere else in the book. Backbone value is low; the two
results worth having are:

| Lean name | book |
|---|---|
| `alternative_linear_system` (Gale / Motzkin transposition) | **Thm 22.1**, 22.2, 22.3 |
| `ElementaryVector` and its API | Lemma 22.4, 22.5, Cor 22.4.1 |
| `alternative_interval_system` | **Thm 22.6** |
| `tucker_complementarity` | **Thm 22.7** |

Everything except Tucker's complementarity theorem is derivable from §21; Rockafellar gives an
independent elementary proof, which the surface can record as an alternative.

Assign §22 to the **surface** unless a downstream demand appears; the backbone keeps only
`alternative_linear_system` (Farkas-type lemmas are broadly reusable).
