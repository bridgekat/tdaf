# Sub-plan 3 — Relative interiors, recession, closedness criteria, dual operations

Covers Rockafellar §6, §8, §9, §10, §16.
Layer D of [D9](00-overview.md#d9-generality-boundaries) except where noted:
`[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`.

This is the largest block of genuinely finite-dimensional work (~60 results) and the main schedule
risk. It is also what unlocks every "the closure operation can be omitted" clause in the book.

---

## 3.1 `Tdaf/Analysis/Convex/RelativeInterior.lean` — §6

Mathlib supplies `intrinsicInterior ℝ s` (= Rockafellar's `ri`), `intrinsicClosure`,
`intrinsicFrontier`, and — crucially — `Set.Nonempty.intrinsicInterior` (Theorem 6.2's hard half).
It does **not** supply the calculus, which is §6's real content.

```lean
open scoped Tdaf in
notation "ri" => intrinsicInterior ℝ
```

| Lean name | statement | book |
|---|---|---|
| `Convex.segment_mem_relint` | `x ∈ ri C → y ∈ cl C → 0 ≤ a < 1 → (1-a)x + ay ∈ ri C` | **Thm 6.1** |
| `Convex.affineSpan_relint`, `.relint_nonempty` | Mathlib + affine hull preserved | **Thm 6.2** |
| `Convex.closure_relint`, `.relint_closure` | `cl (ri C) = cl C`, `ri (cl C) = ri C` | **Thm 6.3** |
| `Convex.relint_eq_iff_closure_eq` | Cor 6.3.1 |
| `Convex.mem_relint_iff_prolong` | `z ∈ ri C ↔ ∀ x ∈ C, ∃ μ>1, (1-μ)x+μz ∈ C` | **Thm 6.4** |
| `Convex.relint_iInter`, `.closure_iInter` | intersections, finite for `ri` | **Thm 6.5** |
| `Convex.relint_inter_affine` | Cor 6.5.1 — used constantly |
| `Convex.relint_subset_relint_of_subset_closure` | Cor 6.5.2 — used in §8, §11 |
| `Convex.relint_image`, `.closure_image_subset` | `ri (A C) = A (ri C)` | **Thm 6.6** |
| `Convex.relint_add` | `ri (C₁+C₂) = ri C₁ + ri C₂` | **Cor 6.6.2** |
| `Convex.relint_preimage`, `.closure_preimage` — **done** | `ri (A⁻¹ C) = A⁻¹ (ri C)` | **Thm 6.7** |
| `Convex.mem_relint_prod_iff` | slices | **Thm 6.8**, Cor 6.8.1 |
| `Convex.relint_convexHull_iUnion` | Thm 6.9 |

Theorem 6.1 is the engine; everything else is an application of it plus Theorem 6.4. Rockafellar's
own proof of 6.1 reduces to the full-dimensional case by an affine transformation carrying `aff C`
onto a coordinate subspace; in Lean the cleaner route is to work inside the affine span directly,
using `intrinsicInterior`'s definition as the image of the interior in `affineSpan ℝ s` — Mathlib's
`Analysis/Convex/Intrinsic.lean` already sets this up and proves the transport lemmas
(`intrinsicInterior_image` for affine isometry equivalences).

Also here (they are §7 results whose proofs need `ri`, deferred from sub-plan 2):

- `ConvexFn.eq_bot_of_mem_relint_dom` (**Thm 7.2**) and its corollaries 7.2.1–7.2.3;
- `Lemma 7.3` : `ri (epi f) = {(x,μ) | x ∈ ri (dom f), f x < μ < ∞}` — used everywhere;
- `clFn_eq_of_mem_relint_dom` (**Thm 7.4**) and Cor 7.4.1–7.4.2;
- `ConvexFn.tendsto_lscHull_along_segment_relint` (**Thm 7.5**, the `ri` form — the layer-B
  `interior` form is in `Closure.lean`) and its `clFn` companion;
- Theorem 7.6 on level sets.

**Theorem 6.7 was the last missing prerequisite of §9.** It is proved exactly as in the book: with
`M` the graph of `A` and `P` the projection to the first factor, `A⁻¹ C = P (M ∩ (univ ×ˢ C))`, so
Corollary 6.5.1 and Theorem 6.6 do all the work and the only new ingredient is the set identity
`image_fst_inter_prod_univ`. Theorem 9.5's closure formula is an immediate consequence, applied to
`epi g` rather than to `C`.

## 3.2 `Tdaf/Analysis/Convex/Recession/Cone.lean` — §8 (sets)

```lean
/-- The recession cone `0⁺C`: directions in which `C` recedes. -/
def recessionCone (C : Set E) : Set E := {y | ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C}

/-- The lineality space of `C`. -/
def linealitySpace (C : Set E) : Set E := recessionCone C ∩ (-recessionCone C)
```

| Lean name | book | layer |
|---|---|---|
| `convexCone_recessionCone`, `recessionCone_eq_add_subset` | **Thm 8.1** | A |
| `IsClosed.isClosed_recessionCone`, `recessionCone_eq_limits` | **Thm 8.2** | D |
| `mem_recessionCone_of_exists_ray` | **Thm 8.3**, Cor 8.3.1–8.3.4 | D |
| `isBounded_iff_recessionCone_eq_zero` | **Thm 8.4**, Cor 8.4.1 | D |
| `linealitySpace_isSubspace`, `rank`, `directSum_decomposition` | §8 | D |

Theorem 8.2's proof is where the `ℝ × E` cone picture (`hom`) pays: `cl K = K ∪ {(0,x) | x ∈ 0⁺C}`
is the statement, and it is proved from Corollary 6.5.1 and Corollary 6.5.2.

## 3.3 `Tdaf/Analysis/Convex/Recession/Function.lean` — §8 (functions)

```lean
/-- The recession function `f0⁺`, defined by `epi (f0⁺) = 0⁺(epi f)`. -/
noncomputable def recessionFn (f : E → EReal) : E → EReal := ofEpi (recessionCone (epi f))
```

`epi (ofEpi S) = S` is **not** automatic: it needs every vertical section of `S` to be closed below.
`0⁺(epi f)` has that property only when `epi f` is closed. So `epi_recessionFn` and the §8 function
statements carry `ClosedFn f`, exactly as Rockafellar assumes. Make the section-closedness condition
a named lemma in `Operations/Epi.lean` — `lscHull`, `infConv`, `mapLin`, `convFn` and `smulRight` all
consume it.

| Lean name | statement | book |
|---|---|---|
| `epi_recessionFn` (needs `ClosedFn f`) | `epi (recessionFn f) = recessionCone (epi f)` | §8 |
| `recessionFn_eq_iSup_diff` | `f0⁺ y = ⨆ x ∈ dom f, f (x+y) - f x` | **Thm 8.5** |
| `recessionFn_eq_limit` | `f0⁺ y = lim_{a→∞} (f (x+a•y) - f x)/a` for closed `f`, any `x ∈ dom f` | **Thm 8.5** |
| `recessionFn_isLeast` | least `h` with `f z ≤ f x + h (z-x)` | Cor 8.5.1 |
| `recessionFn_eq_hom_at_zero` | `f0⁺ = clFn (hom f) (0, ·)` | **Cor 8.5.2** ⇐ [D6](00-overview.md#d6) |
| `monotone_along_iff_recessionFn_nonpos` | **Thm 8.6**, Cor 8.6.1–2 |
| `recessionCone_level_eq` | all level sets share `0⁺` and lineality | **Thm 8.7**, Cor 8.7.1 |
| `affine_along_iff` | **Thm 8.8**; lineality space, rank of `f` | §8 |

`recessionFn_eq_hom_at_zero` is the D6 payoff: Corollary 8.5.2 stops being a separate limit argument
and becomes Corollary 7.5.1 (`cl f` along segments) applied to `hom f`.

## 3.4 `Tdaf/Analysis/Convex/Recession/Closedness.lean` — §9

**Theorems 9.1–9.5 and Corollaries 9.1.1–9.1.3 are formalized.** Theorems 9.6–9.8 (and
Corollaries 9.2.1–9.2.2, 9.6.1, 9.7.1, 9.8.1–9.8.3) are not yet; they need the *convex cone
generated by a set*, which no file defines, and with it the `cl K` formula of Theorem 8.2 that
`Recession/Cone.lean` deliberately skipped. They are the gateway to §15 (gauges) rather than to
anything §16 or §23 needs, so they are scheduled with §15.

Seven things the plan did not anticipate.

(i) **The two halves of 9.1 share one argument.** Both closedness and the recession identity come
from *the same* Cantor-intersection step: a decreasing sequence of nonempty closed convex sets with
recession cone `{0}`, hence compact. For closedness the sets are
`C ∩ A⁻¹(closedBall y (n+1)⁻¹)`; for the recession cone they are
`{z | x₀ + (n+1) • z ∈ C} ∩ A⁻¹{v}`. The second family needed one new layer-A lemma,
`recessionCone_preimage_affine` (the recession cone does not see `z ↦ x + c • z` for `c > 0`) —
which is what makes that family *decreasing* rather than merely nonempty. The plan's suggested
route through the recession-function machinery is not needed.

(ii) **The reduction is packaged, not repeated.** `exists_reduction_of_recessionCone_inter_ker`
produces the set `cl C ∩ M` with the same image, the same image of the recession cone, and the
reduced hypothesis `0⁺ ∩ ker A ⊆ {0}`; both halves of 9.1 then consume it in three lines. This is
what forced `eq_add_inter_of_isCompl_of_le` — the direct-sum decomposition had to be stated for an
arbitrary subspace *of* the lineality space, since the relevant one is `lin (cl C) ∩ ker A`.

(iii) **Corollary 8.3.3 already covered the prerequisites.** `recessionCone_inter`,
`recessionCone_preimage_closedBall` and `isCompact_iff_recessionCone_eq_zero` were all in
`Recession/Cone.lean` already; only `recessionCone_coe_submodule` and
`convex_preimage_affine_smul` had to be added, both one-liners.

(iv) **Theorem 9.2 gives properness for free.** Rockafellar assumes `A f` is not identically `+∞`;
here `Proper (mapLin A f)` is *derived*, using the recession half of 9.1: a vertical line in the
image would be a direction of recession `(0, -1)`, hence `(z, -1) ∈ 0⁺(epi f)` with `A z = 0`,
contradicting the constancy hypothesis. So `closedProperConvexFn_mapLin` returns the epigraph
identity (which *is* the attainment statement) together with `ClosedProperConvexFn (mapLin A f)`,
and `exists_mapLin_eq` is the attainment reading.

(v) **Corollary 9.1.1 is one line of set algebra on top of 9.1.** `C + D` is the image of
`C ×ˢ D` under `LinearMap.id.coprod LinearMap.id`, so the corollary is Theorem 9.1 for that map
once `recessionCone_prod` and `linealitySpace_prod` are available (both new, both three lines, both
needing *nonempty* factors — `0⁺(C ×ˢ ∅) = univ`). No induction over `m` summands is needed for
the binary case, which is the only one §16 uses.

(vi) **Theorems 9.3, 9.4 and 9.5 are three different proofs, not three instances of one.** 9.4 and
9.5 are *epigraph* statements — `epi (sup fᵢ) = ⋂ epi fᵢ` and `epi (g A) = prodMapId A ⁻¹' epi g` —
so each is one line of `epi_injective` on top of a set-level theorem: Theorem 6.5 and Corollary
8.3.3 for the supremum, Theorem 6.7 and Corollary 8.3.4 for the composition. A *sum* of functions
is not any set operation on epigraphs, so 9.3 has to go through Theorem 7.5: all three of
`cl f`, `cl g` and `cl (f + g)` at `y` are limits along one and the same segment out of a common
relative interior point, and uniqueness of limits does the rest.

(vii) **The recession half of 9.3 costs one `EReal` lemma and nothing else.** Base the difference
quotients of Theorem 8.5 at one common point of `dom f ∩ dom g`; then
`Tdaf.EReal.coe_mul_sub_add_coe_mul_sub` — `c(u-p) + c(v-q) = c((u+v)-(p+q))` for `c > 0` and
`u, v ≠ ⊥` — says the quotients add up, and uniqueness of limits gives the identity in one step,
without proving the two inequalities separately. Closedness enters only as "one base point
suffices", which is exactly what Theorem 8.5 needs it for.

```lean
theorem Convex.closure_image_eq (hC : Convex ℝ C) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C                                             -- **Thm 9.1**
theorem Convex.recessionCone_image_closure (hC : Convex ℝ C) (hne : C.Nonempty) (A) (h) :
    recessionCone (A '' closure C) = A '' recessionCone (closure C)               -- **Thm 9.1**
theorem closedProperConvexFn_mapLin (hf : ConvexFn f) (hp : Proper f) (hc : IsClosed (epi f))
    (A : E →ₗ[ℝ] G) (h : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f) :
    epi (mapLin A f) = A.prodMap LinearMap.id '' epi f ∧
      ClosedProperConvexFn (mapLin A f)                                           -- **Thm 9.2**
theorem Convex.isClosed_add (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) : IsClosed (C + D)             -- **Cor 9.1.1**
theorem Convex.closure_add_eq … : closure (C + D) = closure C + closure D         -- **Cor 9.1.1**
theorem Convex.recessionCone_add … :
    recessionCone (closure C + closure D)
      = recessionCone (closure C) + recessionCone (closure D)                     -- **Cor 9.1.1**
```

Rockafellar's Theorem 9.2 hypothesis transports to the epigraph through
`mk_zero_mem_linealitySpace_epi_iff`: `(z, 0) ∈ lin (epi f) ↔ z ∈ constancySpace f` for proper `f`,
and `Ẃ (z, ν) = 0` forces `ν = 0`, so the pairs Theorem 9.1 quantifies over are exactly the
`(z, 0)`.

**The original plan for §9 follows.** Theorem 9.1 is the hardest single result in Parts I–III and
everything else in §9, §16 and §27 depends on it.

```lean
theorem Convex.closure_image_eq (hC : Convex ℝ C) (hC' : C.Nonempty) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C ∧
    recessionCone (A '' closure C) = A '' recessionCone (closure C)
```

Prerequisites, easily missed: `recessionCone (S ∩ T) = recessionCone S ∩ recessionCone T`
for nonempty closed convex `S`, `T` (Corollary 8.3.3); `recessionCone (A ⁻¹' closedBall y ε) = ker A`;
and the translation lemma turning `L ⊆ linealitySpace (cl C)` into "`L^⊥ ∩ cl C` has the same image".
Note also that Mathlib's nested-compacts lemma is
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, indexed by a **type** with
`[Nonempty ι]` and `Directed (· ⊇ ·)`, so the proof must be reorganised around `t n = C_{1/(n+1)}`
and then `⋂ n, A '' t n ⊆ ⋂ n, closedBall y (1/(n+1)) = {y}`. Continuity of `A` comes free from
`FiniteDimensional ℝ E`.

Proof (Rockafellar's, and there is no shorter one): let
`L = 0⁺(cl C) ∩ ker A` (a subspace by hypothesis); replace `C` by `L^⊥ ∩ cl C`, which has the same
image; for each `ε > 0` set `Cε = L^⊥ ∩ cl C ∩ A⁻¹(closedBall y ε)`; show `0⁺Cε = {0}` via
Corollary 8.3.3, hence `Cε` is compact (Theorem 8.4 **and finite-dimensionality**); the `Cε` are a
nested family of nonempty compacts, so their intersection is nonempty, and any point in it maps to
`y`.

Consequences, all mechanical once 9.1 is in place:

| Lean name | book |
|---|---|
| `Convex.isClosed_add`, `Convex.closure_add_eq`, `Convex.recessionCone_add` — **done** | Cor 9.1.1 (binary) |
| `Convex.isClosed_add_of_neg_notMem_recessionCone`, `.recessionCone_add_of_neg_notMem_recessionCone`, `.isClosed_add_of_isBounded` — **done** | **Cor 9.1.2** |
| `closure_add_coe_pointedCone` — **done** | Cor 9.1.3 (binary) |
| `closedProperConvexFn_mapLin` (`Ah` closed, infimum attained) — **done** | **Thm 9.2** |
| `infConv_closed_of_recession` | Cor 9.2.1, 9.2.2 |
| `ClosedProperConvexFn.add`, `recessionFn_add`, `lscHull_add`, `clFn_add` — **done** | **Thm 9.3** |
| `isClosed_epi_iSup`, `recessionFn_iSup`, `lscHull_iSup` — **done** | **Thm 9.4** |
| `isClosed_epi_compLin`, `recessionFn_compLin`, `lscHull_compLin`, `clFn_compLin` — **done** | **Thm 9.5** |
| `closure_cone_generated` | Thm 9.6, Cor 9.6.1 |
| `clFn_hom_eq` , `gaugeFn_closed` | **Thm 9.7**, Cor 9.7.1 |
| `closure_convexHull_iUnion` | Thm 9.8, Cor 9.8.1–9.8.3 |

**On the `m`-ary forms.** Corollaries 9.1.1 and 9.1.3 and Theorem 9.3 are stated in the book for
`m` sets or functions; the binary case is what §16, §23 and §27 consume, and the induction from
binary to `m`-ary is a bookkeeping exercise (the `m`-ary hypothesis implies the `(m-1)`-ary one by
taking `z_m = 0`, and `Σ lin Cᵢ ⊆ lin (Σ Cᵢ)` closes the step). They are deferred, not blocked, and
this is flagged here so a later agent does not read the missing rows as a gap in the theory.

## 3.5 `Tdaf/Analysis/Convex/Continuity.lean` — §10

**Theorems 10.1–10.5 are formalized**, across two files: `Continuity.lean` (10.1, Cor 10.1.1,
10.4, 10.5 with Cors 10.5.1–10.5.2) and `Simplicial.lean` (`IsSimplex`, `LocallySimplicial`, 10.2,
10.3). Theorems 10.6–10.9 are not; see the note at the end. Six things the plan did not anticipate.

(i) **Mathlib supplies the hard half and stops one step short.** `ConvexOn.continuousOn_interior`
(finite dimensions, via `ConvexOn.locallyLipschitzOn`) is the whole analytic content of Theorem
10.1; the `intrinsicInterior` version is an explicit `proof_wanted` in
`Mathlib/Analysis/Convex/Continuous.lean`, left open only because that file does not import
`Mathlib/Analysis/Convex/Intrinsic.lean`. So §10.1 is a *reduction*, not an analysis proof.

(ii) **The reduction must go through a linear subspace, not the affine hull.** `intrinsicInterior`
is defined as an interior taken inside `↥(affineSpan ℝ C)` — which is an `AddTorsor`, and `Convex`,
`ConvexOn` and every Mathlib continuity theorem need a *module*. Fixing `x₀ ∈ C` and charting `C`
in a subspace `V` spanned by `C - x₀` costs one translation (`intrinsicInterior_vadd`, also new)
and buys the whole module API. The chart identity is `relint_eq_vadd_image_interior`:
`ri C = x₀ + ι (int (chart C x₀ V))`.

(iii) **Carrying continuity back needs a retraction.** `ContinuousOn` on an image is not formally
`ContinuousOn` upstairs. In finite dimensions `V` has a complement, so
`LinearMap.linearProjOfIsCompl` supplies a continuous left inverse and `ContinuousOn.congr`
finishes. This is also what makes the real-valued form
(`ConvexFn.continuousOn_toReal_relint_dom`) the primary statement and the `EReal` form a
three-line corollary.

(iv) **The retraction is the whole of Theorem 10.4 as well.** `exists_chart_retraction` packages
(ii) and (iii) as "there is a subspace `V` and a *continuous linear* `r : E →L[ℝ] V` carrying
`ri C` into `interior (chart C x₀ V)`, with `x₀ + r (x - x₀) = x` there". A bounded linear map
transports Lipschitz constants exactly as it transports continuity, so the `ri` form of Theorem
10.4 is the `interior` form (`ConvexOn.exists_lipschitzOnWith_of_isCompact` — Rockafellar's own
collar argument, which Mathlib has only for balls, not for a general compact set) read through the
chart.

(v) **Theorem 10.2 needs no triangulation.** Rockafellar reduces to the case where `x` is a
*vertex*, by triangulating the simplex around `x` — a step he calls "intuitively obvious" and does
not prove, and which in Lean would cost affine independence of the derived families plus a
`Finset`-level argmin argument. It is avoidable. With `x = ∑ μᵢ vᵢ` and `z = ∑ wᵢ vᵢ`, the identity

```
w = (1 - ε) • μ + ε • ((w - (1 - ε) • μ) / ε)
```

writes *any* `z` whose weights satisfy `wᵢ ≥ (1 - ε) μᵢ` as `(1 - ε) x + ε y` with `y` again in the
simplex, for a *fixed* `ε` chosen in advance from the target bound. Convexity then gives
`f z ≤ (1 - ε) β + ε ν` with `β` above `f x` and `ν` above `f` on the whole simplex, and `ε` was
chosen to make that `< b`. The vertex case is `μ = eᵢ₀`.

(vi) **Affine independence is used exactly once, and topologically.** The weights failing
`wᵢ ≥ (1 - ε) μᵢ` at some `i` in the support of `μ` form a *closed* subset of the standard simplex
(a finite union of half-spaces met with `stdSimplex`), hence a compact one, hence one with closed
image under the weight map; and `x` is not in that image, because affine independence makes the
weights of a point unique (`affineIndependent_iff_eq_of_fintype_affineCombination_eq`). So the
failure set misses a neighbourhood of `x`, which is the neighbourhood the theorem asks for. No
metric, no finite dimension, no local convexity: §10.2 lives in a Hausdorff real TVS.

| Lean name | book | note |
|---|---|---|
| `ConvexFn.continuousOn_relint_dom`, `ConvexFn.continuousOn_toReal_relint_dom` — **done** | **Thm 10.1** | the only §10 result used elsewhere so far |
| `ConvexFn.continuous_of_dom_eq_univ`, `ConvexFn.continuous_toReal_of_dom_eq_univ` — **done** | Cor 10.1.1 | |
| `IsSimplex`, `LocallySimplicial` (defs), `ConvexFn.upperSemicontinuousOn_of_locallySimplicial`, `ConvexFn.continuousOn_of_locallySimplicial` — **done** | **Thm 10.2** | `Simplicial.lean`, layer B + T2 |
| `exists_closedFn_continuousOn_of_locallySimplicial`, `eqOn_of_continuousOn_of_eqOn_relint` — **done** | Thm 10.3 | existence and uniqueness stated separately |
| `ConvexOn.exists_lipschitzOnWith_of_isCompact`, `ConvexFn.exists_lipschitzOnWith_of_isCompact` — **done** | **Thm 10.4** | `interior` and `ri` forms |
| `ConvexFn.uniformContinuous_toReal_iff`, `.exists_lipschitzWith_of_recessionFn_ne_top`, `.exists_lipschitzWith_of_frequently_le`, `.exists_lipschitzWith_of_le_lipschitz` — **done** | **Thm 10.5**, Cor 10.5.1–2 | dualised in Cor 13.3.3 |
| `equiLipschitz_of_pointwise_bounded` | **Thm 10.6** | deferred |
| `continuous_of_convex_in_x_continuous_in_t` | Thm 10.7 | deferred |
| `tendsto_uniformlyOn_of_pointwise` | **Thm 10.8**, Cor 10.8.1 | deferred |
| `exists_subseq_tendsto_uniformlyOn` | Thm 10.9 | Arzelà–Ascoli-flavoured; deferred |

**On the deferrals.** Theorems 10.6–10.9 are the equi-Lipschitz and convergence results; §24, §25
and §35 are their only consumers, and none of those has started. Theorem 10.6's proof is explicitly
"the proof of Theorem 10.4 again, noting that the Lipschitz constant depends only on the given
bounds", so when it is written it should reuse `ConvexOn.exists_lipschitzOnWith_of_isCompact` with
the constant `2|M|/ε` exposed rather than existentially quantified — a small change to the existing
statement now, a second proof later.

`LocallySimplicial` has, for now, no supply of instances beyond simplices themselves: **Theorem
20.5** (every polyhedral convex set is locally simplicial) is what makes Theorems 10.2 and 10.3
usable, and it is in §20. Rockafellar also notes that every relatively open convex set is locally
simplicial; that is not proved here either.

## 3.6 `Tdaf/Analysis/Convex/Duality/Exact.lean` — [D5](00-overview.md#d5)

**Formalized.** Two adjustments were needed: the file also imports `Operations/Image.lean` (that is
where `mapLin`/`compLin` live), and the interface gained two lemmas that turn D5's remark about
unsatisfiability into working API — `IsExactSum.proper_add` and `IsExactImage.proper_compLin`,
which say that the interface itself rules out disjoint effective domains.

```lean
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  proper_left  : Proper f
  proper_right : Proper g
  exact_le : ∀ y, ∃ y₁ y₂, y₁ + y₂ = y ∧ conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y

structure IsExactImage (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) (hA : IsAdjointPair B B' A A') (g : G → EReal) : Prop where
  proper : Proper g
  exact_le : ∀ y, ∃ z, A' z = y ∧ conj B' g z ≤ conj B (g ∘ A) y
```

Three corrections from review. (i) `conj B (f + g) ≤ infConv (conj B f) (conj B g)` is
*unconditional*, so `conj_add` is a **theorem** derived from `exact_le`, not a second field; stating
both was redundant, and the equality form was moreover *unsatisfiable* when `dom f ∩ dom g = ∅`
(then `f + g ≡ ⊤`, so `conj B (f+g) ≡ ⊥`, while conjugates of proper functions are never `⊥`).
(ii) Properness is a genuine hypothesis of Theorems 16.3/16.4, and it is also what keeps the `Pi` sum `f + g` from hiding an `∞ − ∞`. (iii) `A.adjoint` does not exist for
a linear map between arbitrary paired spaces; the transpose is extra *data*, supplied as `A'`
together with `IsAdjointPair` (see `Duality/Pairing.lean`).

Sufficient conditions, each proved once:

```lean
-- in Duality/Relint.lean (done — see §3.7; `ClosedProperConvexFn`, not just `Proper`)
theorem IsExactSum.of_relint (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g   -- Thm 16.4
theorem IsExactImage.of_relint (hA) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (dom g)) : …                                        -- Thm 16.3
-- in Polyhedral/Duality.lean (done — see sub-plan 4 §4.4)
theorem IsExactSum.of_polyhedral (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ClosedProperConvexFn g) {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ ri (dom g)) :
    IsExactSum B f g                                                                -- Thm 20.1
theorem IsExactSum.of_polyhedral_pair (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : PolyhedralFn g) (hpg : Proper g) {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ dom g) :
    IsExactSum B f g                                              -- Thm 20.1, both sides polyhedral
-- in Duality/Continuity.lean (done — see §3.8)
theorem IsExactSum.of_continuousAt (hf : ConvexFn f) (hpf : Proper f) (hg : ConvexFn g)
    (hpg : Proper g) {x₀ : E} (hfx₀ : x₀ ∈ dom f) (hgx₀ : x₀ ∈ dom g)
    (hcont : ContinuousAt f x₀) : IsExactSum B f g                            -- not in the book
```

**Placement matters.** These do *not* live in `Exact.lean`. §20's theorems *are* `IsExactSum`
statements, so `Polyhedral/Duality.lean` imports `Exact.lean`; putting `of_polyhedral` in
`Exact.lean` makes the two mutually importing. `Exact.lean` holds only the interface and its
interface-only consequences, importing `Duality/Conjugate` and `Operations/InfConv`. Note also
`PolyhedralFn` (functions), not `Polyhedral` (sets); applying the set-level predicate to a function
is a type error.

`of_relint` is proved from §9 (Theorem 9.2 for images, Corollary 9.1.1 for sums) plus §13's
Theorem 13.3 plus §6 — not via Lemma 16.2 and Corollary 16.2.1, which are never stated. It also
needs the *closed* proper convex hypothesis, not just `Proper`, because Theorem 12.2 is what makes
`f*` proper and Theorem 9.2 needs a closed epigraph. It lives in its own file, `Duality/Relint.lean`,
since no one of §6/§9/§13 owns it. `of_continuousAt` is a genuine generalisation valid in any
TVS, cheap to prove, and is the version practitioners actually use — worth having even though
Rockafellar does not state it. It is done, in `Duality/Continuity.lean`; see §3.8.

Downstream consumers, each reduced to `IsExactSum`/`IsExactImage` once and for all:

- Theorem 16.3, 16.4, 16.5 and their corollaries (§3.7 below);
- Theorem 23.8 (`∂(f+g) = ∂f + ∂g`) and Theorem 23.9 (`∂(h ∘ A) = Aᵀ ∂h`);
- Theorem 31.1 (Fenchel's duality theorem);
- Theorems 38.2, 38.4, 38.5 and 39.5, 39.7 (bifunctions and convex processes).

## 3.7 `Tdaf/Analysis/Convex/Duality/Ops.lean` — §16

**Formalized in full**, including the constraint qualification. Five adjustments.

(i) The conditional halves are *stated here after all*, in Rockafellar's own form — with a `clFn`
on the dual side rather than with a constraint qualification: `conj_add_eq_clFn_infConv`,
`conj_iSup_eq_clFn_convFn`, `conj_compLin_eq_clFn_mapLin`. Each is three lines (apply the
unconditional identity for the *dual* operation, then `biconj_eq_self` and `biconj_eq_clFn`), and
each is genuinely more general than the `Exact.lean` form, which drops the closure but demands the
qualification. So each row of the table now appears in three forms, not two.

(ii) Two epigraph lemmas had to come first: `conj_ofEpi` (the conjugate of `ofEpi S` is
`⨆ p ∈ S, ⟨p.1, y⟩ - p.2`) and its specialisation `conj_eq_biSup_epi`. `conj_infConv` is proved
through them, because its right-hand side is a *sum* and so has no affine-minorant
characterisation to compare against; every other unconditional row is proved by
`Tdaf.EReal.eq_of_forall_le_coe_iff` + `conj_le_coe_iff`, i.e. by comparing affine minorants
directly. This is also what made two new `Order/EReal.lean` lemmas necessary
(`biSup_add_biSup`, `coe_le_coe_mul_iff`).

(iii) `smulLeft` does not exist as a definition — ordinary scalar multiplication of an `EReal`-valued
function is just `fun x => (a : EReal) * f x`, so **Thm 16.1** is stated that way
(`conj_smul`, `conj_smulRight`).

(iv) `sSupFn` likewise does not exist: the pointwise supremum is `⨆ i, f i` from the `Lattice.lean`
`CompleteLattice` instance, so **Thm 16.5** is `conj_convFn` / `conj_iSup_eq_clFn_convFn`, with
`conj_convHullFn` (a function and its convex hull have the same conjugate) and the binary
`conj_convFn₂` alongside.

The dual-operations table. Each row is one theorem, and each has an unconditional half (an identity)
plus a conditional half (closure omitted, infimum attained) supplied by `Exact.lean`.

| primal operation | dual operation | book |
|---|---|---|
| `smulLeft a f` ↔ `smulRight (conj f) a` | | **Thm 16.1**, Cor 16.1.1–2 |
| `mapLin A f` ↔ `compLin (conj f) Aᵀ` | *unconditional* | **Thm 16.3** |
| `compLin g A` ↔ `mapLin Aᵀ (conj g)` | *conditional*, discharged by `IsExactImage.of_relint` | **Thm 16.3** |
| `infConv` ↔ `+` | *unconditional* | **Thm 16.4** |
| `+` ↔ `infConv` | *conditional*, discharged by `IsExactSum.of_relint` | **Thm 16.4**, Cor 16.4.1 |
| `convFn` ↔ `sSupFn` | *unconditional* | **Thm 16.5** |
| `sSupFn` ↔ `convFn` | *conditional* | **Thm 16.5**, Cor 16.5.1–2 |

Set-level corollaries (support functions of sums/intersections, polars of hulls/intersections) come
free by applying the function-level result to indicators — and in the event `supportFn_add`,
`supportFn_convexHull` and `supportFn_iUnion` were already proved directly in `Duality/Support.lean`
when §13 was done, so nothing was re-derived here.

(v) **Lemma 16.2 and Corollary 16.2.1 are never stated.** They were planned as the technical bridge
from the `ri` hypothesis to the recession hypothesis of §9. That bridge turned out to be **Theorem
13.3** (`constancySpace_conj`: the constancy space of `f*` is the annihilator of `dom f`) composed
with §6's `eq_of_isMaxOn_of_mem_relint` / `eq_zero_of_nonpos_of_mem_relint`, and it is four lines
inside each constructor rather than a lemma of its own. The constructors themselves live in a new
file, `Duality/Relint.lean`, not in `Exact.lean` — `Exact.lean` is layer A and must stay that way,
while `of_relint` needs finite dimensions, §9 and §13 all at once:

```lean
theorem IsExactImage.of_relint (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (dom g)) : IsExactImage B B' A A' hA g          -- **Thm 16.3**
theorem IsExactSum.of_relint (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g   -- **Thm 16.4**
```

The image rule runs on Theorem 9.2 and puts finite-dimensionality on `G` and `H`; the sum rule runs
on Corollary 9.1.1 inside `F × ℝ` and puts it on `F` instead. Neither touches `E` beyond a norm.

## 3.8 `Tdaf/Analysis/Convex/Duality/Continuity.lean` — `of_continuousAt`

**Formalized.** The plan guessed this would be cheap and it was: one separation, at layer B, in
about ninety lines. Four things worth recording.

(i) **It is layer B, not even C.** The instinct is that separating convex sets needs local
convexity, and for two *closed* sets it does. Here one of the two sets is open, and
`geometric_hahn_banach_open` asks for nothing but a real topological vector space. Continuity of
`f` at `x₀` is precisely what makes it open: `f` is bounded above by some `r` on a neighbourhood
`V` of `x₀`, so `V ×ˢ Ioi r` sits inside the strict epigraph.

(ii) **The right pair of sets is epigraph-against-*hypograph*.** With `a = (f + g)* y` finite —
the case `= ⊤` is free — what has to be refuted is `f x + g x < ⟨x, y⟩ - a` for some `x`. Written
as a statement about `E × ℝ`, that says the strict epigraph `{(x, μ) | f x < μ}` meets the
hypograph `{(x, μ) | g x ≤ ⟨x, y⟩ - a - μ}` of the concave function `x ↦ ⟨x, y⟩ - a - g x`. So the
two convex sets to separate are not two epigraphs; the second is the reflection of one.

(iii) **`geometric_hahn_banach_open` separates strictly only on the open set**, and the estimate is
needed on the whole strict epigraph, not just its interior. The bridge is
`Convex.closure_interior_eq_closure_of_nonempty_interior` — for a convex set with nonempty
interior, `closure (interior C) = closure C` — together with the fact that `{φ ≤ u}` is closed.
Worth remembering as the standard way to upgrade an open-set separation.

(iv) **The vertical coefficient is negative, and both signs need an argument.** After splitting `φ`
with `exists_unique_dual_prod` into `ψ x + c μ`, `c ≠ 0` because a vertical functional would be
`< u` at `(x₀, μ)` for every `μ > r` and `≥ u` at a point of the hypograph over the same `x₀`; and
`c > 0` is impossible because the strict epigraph is unbounded upwards, so `ψ x₀ + c μ` would
exceed `u` for large `μ`. With `c = -t`, `t > 0`, `exists_pairing_eq` turns `t⁻¹ • ψ` into the
`y₁ : F` the interface asks for, and `y₂ = y - y₁`.

Also here: `ConvexFn.convex_strictEpi`, which is Theorem 4.2 (`convexFn_iff_forall_lt`) read as a
statement about a set. It belongs to §4 mathematically but had no consumer until now.

## 3.9 Left to the surface

- §6's counterexamples (the `[0,1+α]` family, the positive orthant vs the axis).
- §8's worked recession functions (`(1+⟨x,Qx⟩)^{1/2}`, quadratics, log-sum-exp).
- §9's counterexample `exp(-√(ξ₁ξ₂))`.
- §10's parabolic counterexample and the nondecreasing-function extension example.
- §16's `ℝⁿ` statements with the inner-product pairing and adjoint matrices.
