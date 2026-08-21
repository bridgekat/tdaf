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
| `Convex.relint_preimage` | Thm 6.7 |
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
- Theorem 7.6 on level sets.

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

| Lean name | statement | book |
|---|---|---|
| `epi_recessionFn` | `epi (recessionFn f) = recessionCone (epi f)` | definition |
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

**Theorem 9.1 is the hardest single result in Parts I–III** and everything else in §9, §16 and §27
depends on it.

```lean
theorem Convex.closure_image_eq (hC : Convex ℝ C) (hC' : C.Nonempty) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C ∧
    recessionCone (A '' closure C) = A '' recessionCone (closure C)
```

Proof (Rockafellar's, and there is no shorter one): let
`L = 0⁺(cl C) ∩ ker A` (a subspace by hypothesis); replace `C` by `L^⊥ ∩ cl C`, which has the same
image; for each `ε > 0` set `Cε = L^⊥ ∩ cl C ∩ A⁻¹(closedBall y ε)`; show `0⁺Cε = {0}` via
Corollary 8.3.3, hence `Cε` is compact (Theorem 8.4 **and finite-dimensionality**); the `Cε` are a
nested family of nonempty compacts, so their intersection is nonempty, and any point in it maps to
`y`.

Consequences, all mechanical once 9.1 is in place:

| Lean name | book |
|---|---|
| `closure_sum_eq` , `recessionCone_sum` | Cor 9.1.1–9.1.3 |
| `mapLin_closed_of_recession` (`Ah` closed, infimum attained) | **Thm 9.2** |
| `infConv_closed_of_recession` | Cor 9.2.1, 9.2.2 |
| `clFn_add_eq_add_clFn` (needs `ri (dom fᵢ)` to meet) | **Thm 9.3** |
| `clFn_sSup_eq` | **Thm 9.4** |
| `clFn_compLin_eq` | **Thm 9.5** |
| `closure_cone_generated` | Thm 9.6, Cor 9.6.1 |
| `clFn_hom_eq` , `egauge_closed` | **Thm 9.7**, Cor 9.7.1 |
| `closure_convexHull_iUnion` | Thm 9.8, Cor 9.8.1–9.8.3 |

## 3.5 `Tdaf/Analysis/Convex/Continuity.lean` — §10

| Lean name | book | note |
|---|---|---|
| `ConvexFn.continuousOn_relint_dom` | **Thm 10.1**, Cor 10.1.1 | the only §10 result used elsewhere |
| `LocallySimplicial` (def) + `ConvexFn.upperSemicontinuousOn` | **Thm 10.2** | needs simplices |
| `ConvexFn.exists_unique_continuous_extension` | Thm 10.3 | |
| `ConvexFn.lipschitzOn_of_isCompact_subset_relint` | **Thm 10.4** | |
| `ConvexFn.uniformContinuous_iff_recessionFn_finite` | **Thm 10.5**, Cor 10.5.1–2 | dualised in Cor 13.3.3 |
| `equiLipschitz_of_pointwise_bounded` | **Thm 10.6** | |
| `continuous_of_convex_in_x_continuous_in_t` | Thm 10.7 | |
| `tendsto_uniformlyOn_of_pointwise` | **Thm 10.8**, Cor 10.8.1 | |
| `exists_subseq_tendsto_uniformlyOn` | Thm 10.9 | Arzelà–Ascoli-flavoured |

Mathlib's `Analysis/Convex/Continuous.lean` already has "a convex function bounded above on a
neighbourhood is continuous"; Theorem 10.1 and Corollary 10.1.1 should be derived from it rather
than reproved. Theorems 10.6–10.9 are only used in §24, §25 and §35 and can be deferred.

`LocallySimplicial` (§10, before Theorem 10.2) is needed again in §20 (Theorem 20.5: every
polyhedral convex set is locally simplicial), so define it here.

## 3.6 `Tdaf/Analysis/Convex/Duality/Exact.lean` — [D5](00-overview.md#d5)

```lean
structure IsExactSum (B) (f g : E → EReal) : Prop where
  conj_add : conj B (f + g) = infConv (conj B f) (conj B g)
  attained : ∀ y, ∃ y₁ y₂, y₁ + y₂ = y ∧ conj B (f + g) y = conj B f y₁ + conj B g y₂

structure IsExactImage (B) (A : E →ₗ[ℝ] G) (g : G → EReal) : Prop where
  conj_comp : conj B (g ∘ A) = mapLin A.adjoint (conj B' g)
  attained : ∀ y, ∃ z, A.adjoint z = y ∧ …
```

Sufficient conditions, each proved once:

```lean
theorem IsExactSum.of_relint (h : (ri (dom f) ∩ ri (dom g)).Nonempty) : IsExactSum B f g -- Thm 16.4
theorem IsExactSum.of_polyhedral (hf : Polyhedral f) (h : (dom f ∩ ri (dom g)).Nonempty) : …  -- Thm 20.1
theorem IsExactSum.of_continuousAt (h : ∃ x ∈ dom g, ContinuousAt f x ∧ f x ≠ ⊤) : …          -- not in book
theorem IsExactImage.of_relint (h : ∃ x, A x ∈ ri (dom g)) : IsExactImage B A g               -- Thm 16.3
```

`of_relint` is proved from §9 (Theorem 9.2 / Corollary 9.2.1 give closedness and attainment, via
Lemma 16.2 and Corollary 16.2.1) plus §6. `of_continuousAt` is a genuine generalisation valid in any
TVS, cheap to prove, and is the version practitioners actually use — worth having even though
Rockafellar does not state it.

Downstream consumers, each reduced to `IsExactSum`/`IsExactImage` once and for all:

- Theorem 16.3, 16.4, 16.5 and their corollaries (§3.7 below);
- Theorem 23.8 (`∂(f+g) = ∂f + ∂g`) and Theorem 23.9 (`∂(h ∘ A) = Aᵀ ∂h`);
- Theorem 31.1 (Fenchel's duality theorem);
- Theorems 38.2, 38.4, 38.5 and 39.5, 39.7 (bifunctions and convex processes).

## 3.7 `Tdaf/Analysis/Convex/Duality/Ops.lean` — §16

The dual-operations table. Each row is one theorem, and each has an unconditional half (an identity)
plus a conditional half (closure omitted, infimum attained) supplied by `Exact.lean`.

| primal operation | dual operation | book |
|---|---|---|
| `smulLeft a f` ↔ `smulRight (conj f) a` | | **Thm 16.1**, Cor 16.1.1–2 |
| `mapLin A f` ↔ `compLin (conj f) Aᵀ` | *unconditional* | **Thm 16.3** |
| `compLin g A` ↔ `mapLin Aᵀ (conj g)` | *conditional* | **Thm 16.3** |
| `infConv` ↔ `+` | *unconditional* | **Thm 16.4** |
| `+` ↔ `infConv` | *conditional* | **Thm 16.4**, Cor 16.4.1 |
| `convFn` ↔ `sSupFn` | *unconditional* | **Thm 16.5** |
| `sSupFn` ↔ `convFn` | *conditional* | **Thm 16.5**, Cor 16.5.1–2 |

Set-level corollaries (support functions of sums/intersections, polars of hulls/intersections) come
free by applying the function-level result to indicators. Lemma 16.2 and Corollary 16.2.1 are the
technical bridge from the `ri` hypothesis to the recession hypothesis of §9; they live in
`Exact.lean`, not here.

## 3.8 Left to the surface

- §6's counterexamples (the `[0,1+α]` family, the positive orthant vs the axis).
- §8's worked recession functions (`(1+⟨x,Qx⟩)^{1/2}`, quadratics, log-sum-exp).
- §9's counterexample `exp(-√(ξ₁ξ₂))`.
- §10's parabolic counterexample and the nondecreasing-function extension example.
- §16's `ℝⁿ` statements with the inner-product pairing and adjoint matrices.
