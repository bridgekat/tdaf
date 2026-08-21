# Sub-plan 2 — Closure, separation, conjugacy, support functions, polars

Covers Rockafellar §7, §11, §12, §13, §14, §15.
Layers B and C of [D9](00-overview.md#d9-generality-boundaries). **No finite-dimensionality anywhere
in this sub-plan** — this is the reordering argued in [D4](00-overview.md#d4).

This is the keystone of the library: Fenchel–Moreau (`f** = cl f`) is what every later duality
statement reduces to.

---

## 2.1 `Tdaf/Analysis/Convex/Closure.lean` — §7

Layer B: `E` a real topological vector space.

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The lower semicontinuous hull: the function whose epigraph is `closure (epi f)`. -/
noncomputable def lscHull (f : E → EReal) : E → EReal := ofEpi (closure (epi f))

/-- The closure of a convex function: the lsc hull, except that if the lsc hull takes `-∞` anywhere
then the closure is the constant `-∞`.

Rockafellar branches on whether `f` itself takes `-∞`. That is equivalent for convex `f` in `ℝⁿ`
(by Theorems 7.2/7.4) but **not** in general: a discontinuous linear functional is proper with
`lscHull` identically `-∞`, and branching on `f` would falsify Fenchel–Moreau. Branching on the hull
is the standard Γ-regularization and makes `f** = clFn f` unconditional. -/
open Classical in
noncomputable def clFn (f : E → EReal) : E → EReal :=
  if ∃ x, lscHull f x = ⊥ then (fun _ => ⊥) else lscHull f

def ClosedFn (f : E → EReal) : Prop := clFn f = f
```

The `-∞` exception looks arbitrary but is exactly what makes `f** = cl f` hold for improper `f`, and
Part VII depends on that. Rockafellar says so where he defines it; the docstring should too.

`open Classical in` is required: there is no `Decidable (∃ x, lscHull f x = ⊥)` instance, and the
`⨅ _ : p, f` trick used for `restrict` does not apply here because the default branch is a function.

The surface then owes a proof that for convex `f` on `ℝⁿ` this agrees with the book's definition.

| Lean name | book |
|---|---|
| `lowerSemicontinuous_iff_isClosed_epi` (**not** a wrap: Mathlib's version puts the epigraph in `E × EReal`, ours in `E × ℝ`; ~10 lines) | **Thm 7.1** |
| `ConvexFn.eq_bot_of_mem_relint_dom` | Thm 7.2 *(finite-dim; see note)* |
| `lscHull_eq_liminf` : `lscHull f x = liminf f (𝓝[≠] x)` | §7 |
| `clFn_le`, `clFn_mono`, `clFn_idem`, `sInf_clFn_eq_sInf` | §7 |
| `exists_affine_le_of_closed_proper`, `eq_bot_of_lsc_of_eq_bot` | — (replace Thm 7.2/7.4 at layer C) |
| `ClosedFn.proper_of_proper` : `Proper f → Proper (clFn f)` | **Thm 7.4** *(finite-dim)* |
| `clFn_eq_of_mem_relint_dom` | Thm 7.4 *(finite-dim)* |
| `clFn_eq_limit_along_segment` | **Thm 7.5**, Cor 7.5.1 |
| `relint_lt_level`, `closure_level_eq` | Thm 7.6 |

**Theorem 7.4 does not generalise to layer C**, and in particular a proper convex function need not
have a continuous affine minorant there: a
discontinuous linear functional `g` has dense kernel, so `closure (epi g) = univ` and
`lscHull g ≡ ⊥`, while `g` is convex, finite everywhere and proper. The sketch assumed
`(x₀, f x₀ − 1) ∉ closure (epi f)`, which is exactly what fails.

What is true, and what this file should prove:

```lean
/-- A closed proper convex function has a continuous affine minorant. -/
theorem exists_affine_le_of_closed_proper (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ∃ (y : F) (c : ℝ), ∀ x, ((B x y : ℝ) : EReal) - c ≤ f x

/-- Dichotomy (**Corollary 7.2.1**): a lower semicontinuous improper convex function has no finite
values. Replaces Theorem 7.2 outside finite dimensions; true in any TVS. -/
theorem ConvexFn.eq_bot_or_eq_top (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) (x : E) : f x = ⊥ ∨ f x = ⊤
```

For the first, the usual argument is correct once `f` is closed: `epi f` is a
nonempty closed convex set, `(x₀, f x₀ − 1) ∉ epi f`, and the separating functional cannot be
vertical because a functional `(y,0)` takes the same value at `(x₀, f x₀ − 1)` and `(x₀, f x₀)`,
while `x₀ ∈ dom f`.

The second must be stated as "**no finite values**", *not* as "identically `⊥`". The stronger form
is false: on `ℝ`, the function that is `⊥` at the origin and `⊤` elsewhere is convex (its epigraph
is a vertical line) and lower semicontinuous (that line is closed), takes `⊥`, and is not constant.
Rockafellar's Corollary 7.2.1 says exactly "can have no finite values", and that is what
generalises.

`ClosedFn.proper_of_proper` in its unconditional form is therefore **layer D**, alongside §7's other
`ri`-flavoured refinements (Theorem 7.2, "`cl f` agrees with `f` on `ri (dom f)`"), all deferred to
`RelativeInterior.lean`. D4's *ordering* conclusion is unaffected: conjugacy still needs only
separation.

## 2.2 `Tdaf/Analysis/Convex/Separation.lean` — §11

Layer C. Almost all content is already in `Mathlib/Analysis/LocallyConvex/Separation.lean`; this
file supplies Rockafellar's *vocabulary* and the two statements Mathlib lacks.

```lean
/-- `f` separates `s` and `t`: `s ⊆ {x | f x ≤ c}` and `t ⊆ {x | c ≤ f x}`. -/
def Separates (f : E →L[ℝ] ℝ) (c : ℝ) (s t : Set E) : Prop := …
def SeparatesProperly (f : E →L[ℝ] ℝ) (c : ℝ) (s t : Set E) : Prop := Separates f c s t ∧ ¬(…)
def SeparatesStrongly …
```

| Lean name | book | source |
|---|---|---|
| `separates_iff_iInf_le_iSup` | **Thm 11.1** | new, elementary |
| `exists_hyperplane_of_relopen_disjoint_affine` | Thm 11.2 | new *(finite-dim, or LCS + `int ≠ ∅`)* |
| `separatesProperly_iff_relint_disjoint` | **Thm 11.3** | new *(finite-dim)* |
| `separatesStrongly_iff_zero_notMem_closure_sub` | **Thm 11.4** | Mathlib `geometric_hahn_banach_*` + `Convex.add` |
| `separatesStrongly_of_no_common_recession` | Cor 11.4.1 | needs §9 |
| `isClosed_convex_eq_iInter_halfspaces` | **Thm 11.5** | Mathlib `iInter_halfSpaces_eq` |
| `exists_supporting_hyperplane_iff` | Thm 11.6 | *(finite-dim)* |
| `separates_cone_through_origin` | Thm 11.7, Cor 11.7.1–3 | new, easy |

Theorem 11.3 (proper separation ⟺ disjoint relative interiors) is finite-dimensional and belongs to
layer D; it is *not* on the path to conjugacy. Only Theorem 11.5 (equivalently, Mathlib's
`geometric_hahn_banach_closed_point`) is.

## 2.3 `Tdaf/Analysis/Convex/Duality/Pairing.lean` — [D3](00-overview.md#d3)

```lean
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
```

Contents:

- `Pairing.IsSeparating B` — abbreviation for `B.SeparatingLeft ∧ B.SeparatingRight`
  (Mathlib has `LinearMap.SeparatingLeft`/`SeparatingRight`).
- The affine functions of the pairing: `affineFn B y c : E → EReal := fun x => (B x y : EReal) - c`.
- **Adjoint pairs.** `Aᵀ` does not exist for a bare `A : E →ₗ[ℝ] G` between paired spaces; it is
  extra data. Following Mathlib's `LinearMap.IsAdjointPair`:
  ```lean
  def IsAdjointPair (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
      (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) : Prop := ∀ x z, B' (A x) z = B x (A' z)
  ```
  with constructors for the inner-product and finite-dimensional cases.
- **Product pairings** for D8: `prodPairing Bu Bx`, `negFst`, and `conj_prodPairing`.
- **Compatible topologies — use Mathlib's, do not rebuild.**
  `Mathlib/Analysis/LocallyConvex/WeakSpace.lean` already has the theorem, so there is no
  `Compatible τ B` predicate to define and nothing to prove from `iInter_halfSpaces_eq`.

  ```lean
  theorem Convex.toWeakSpace_closure (hs : Convex ℝ s) :
      toWeakSpace 𝕜 E '' closure s = closure (toWeakSpace 𝕜 E '' s)

  theorem LinearEquiv.image_closure_of_convex (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
      (he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))
      (he₂ : ∀ f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) :
      e '' closure s = closure (e '' s)
  ```

  Mathlib phrases compatibility as two hypotheses on a linear equivalence rather than as a predicate
  on topologies, deliberately — "rather than creating two separate topologies on the same space".
  `he₁`/`he₂` are `IsCompatiblePairing`'s two fields in another notation.

  What remains for us is the specialisation to epigraphs, `cl f` independent of the compatible
  topology, which is a handful of corollaries at layer C. This is *not* how `f** = cl f` is proved
  — see D3.

- The canonical instances:
  - `E` a real normed space, `F := StrongDual ℝ E`, `B := topDualPairing ℝ E`;
  - `E` a real inner-product space, `F := E`, `B := innerₗ` (this is Rockafellar's `ℝⁿ`);
  - a general `B`, with compatibility carried as hypotheses rather than by a change of topology.

## 2.4 `Tdaf/Analysis/Convex/Duality/Conjugate.lean` — §12

```lean
/-- The convex conjugate of `f` with respect to the pairing `B`. -/
noncomputable def conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x

/-- The biconjugate, back on `E`. -/
noncomputable abbrev biconj (B) (f : E → EReal) : E → EReal := conj B.flip (conj B f)
```

| Lean name | statement | book |
|---|---|---|
| `le_add_conj` | `(B x y : EReal) ≤ f x + conj B f y` — **Fenchel's inequality** | §12 |
| `convexFn_conj` | `ConvexFn (conj B f)` always | §12 |
| `closedFn_conj` | `conj B f` is `σ(F,E)`-closed always | §12 |
| `conj_antitone` | `f ≤ g → conj B g ≤ conj B f` | §12 |
| `closedFn_iff_eq_sSup_affine` | a closed convex function is the sup of the affine functions below it | **Thm 12.1** |
| `conj_clFn` | `conj B (clFn f) = conj B f` | **Thm 12.2** |
| `biconj_eq_clFn` | `biconj B f = clFn f` for convex `f` — **Fenchel–Moreau** | **Thm 12.2** |
| `conjEquiv` | the induced involution on closed proper convex functions | Cor 12.2.1 |
| `conj_eq_iSup_relint` | the sup may be restricted to `ri (dom f)` | Cor 12.2.2 *(finite-dim)* |
| `conj_comp_affine` | conjugate of `f ∘ T` for an affine `T` | Thm 12.3 |
| `monotoneConj` | the monotone conjugate `g⁺` on the nonnegative orthant | Thm 12.4 *(surface)* |

**Proof plan for `biconj_eq_clFn`.**

1. Improper case first, and it is easy: if `f x = ⊥` for some `x` then `conj B f = ⊤` identically,
   so `biconj B f = ⊥` identically, which is `clFn f` by definition. If `f = ⊤` identically then
   `conj B f = ⊥` and `biconj B f = ⊤`.
2. Proper case. `biconj B f ≤ clFn f` is immediate from Fenchel's inequality.
   For `≥`: work in `E` with its own topology. Suppose `biconj B f x₀ < c < clFn f x₀`.
   Then `(x₀, c) ∉ closure (epi f)`, a closed convex set; separate by
   `geometric_hahn_banach_closed_point` in `E × ℝ`, then split the functional with
   `exists_unique_dual_prod` and recognise the horizontal part via `IsCompatiblePairing.surjective_eval`. Two cases: the separating functional is non-vertical (gives directly an affine minorant
   of `f` above `c` at `x₀`, contradicting `biconj B f x₀ < c`), or vertical (then add a large
   multiple of it to a known affine minorant — which exists by §2.1's affine-minorant lemma — to get
   a non-vertical one; this is exactly the last paragraph of Rockafellar's proof of Theorem 12.1).
3. No transport step: the compatibility hypotheses already cover every admissible topology, and
   there are **three** cases in step 2, not two — the vertical coefficient may be negative, zero or
   positive, and ruling out positive needs upward closedness of the epigraph.

Step 2 is where the affine-minorant lemma from §2.1 is consumed, which is why the two files must be
developed together.

## 2.5 `Tdaf/Analysis/Convex/Duality/Support.lean` — §13

```lean
/-- The support function `δ*(· | s)`. -/
noncomputable def supportFn (B) (s : Set E) : F → EReal := fun y => ⨆ x ∈ s, ((B x y : ℝ) : EReal)

theorem supportFn_eq_conj_indicator : supportFn B s = conj B (indicatorFn s)
```

| Lean name | book |
|---|---|
| `mem_closure_iff_le_supportFn` | **Thm 13.1** |
| `conj_indicator`, `conj_supportFn` — indicator and support function are conjugate | **Thm 13.2** |
| `posHomogeneous_closed_iff_isSupportFn` — the closed proper positively homogeneous convex functions *are* the support functions | **Thm 13.2** |
| `clFn_eq_supportFn_of_posHomogeneous` | Cor 13.2.1 |
| `isSupportFn_bounded_iff_finite` | Cor 13.2.2 |
| `supportFn_dom_eq_recession_conj` : `δ*(·|dom f) = (conj B f) 0⁺` | **Thm 13.3** |
| `conj_finite_iff_cofinite` | Cor 13.3.1 |
| `lineality_conj_eq_orthogonal_aff_dom` | Thm 13.4 *(finite-dim)* |
| `supportFn_level_eq_clFn_hom_conj` | **Thm 13.5** |

Theorem 13.2 is the reason support functions are not a separate theory: they are conjugates of
indicators, so every property is inherited. The *characterisation* half (positively homogeneous +
closed + proper ⟹ is a support function) is `biconj_eq_clFn` plus
`PosHomogeneous.convexFn_iff_subadditive` from sub-plan 1.

Theorems 13.3–13.5 need recession functions (§8) and so are finished in sub-plan 3; the statements
belong here.

## 2.6 `Tdaf/Analysis/Convex/Duality/Polar.lean` — §14, §15

**Rockafellar's polars are one-sided**; Mathlib's `LinearMap.polar` is the absolute polar.

```lean
/-- Polar of a convex cone: `K° = {y | ∀ x ∈ K, ⟨x,y⟩ ≤ 0}`. -/
def polarCone (B) (K : Set E) : Set F := {y | ∀ x ∈ K, B x y ≤ 0}

/-- Polar of a convex set containing the origin: `C° = {y | ∀ x ∈ C, ⟨x,y⟩ ≤ 1}`. -/
def polarSet (B) (C : Set E) : Set F := {y | ∀ x ∈ C, B x y ≤ 1}

/-- Gauge, `EReal`-valued. Named `gaugeFn` because **Mathlib already has an `egauge`**
(`Mathlib/Analysis/Convex/EGauge.lean`, `ℝ≥0∞`-valued); consider reusing that instead, since
Rockafellar's gauge is nonnegative and `ℝ≥0∞` loses nothing. Mathlib's `gauge` is the `ℝ`-valued
restriction to absorbing sets and returns `0`, not `⊤`, off them. -/
noncomputable def gaugeFn (C : Set E) : E → EReal :=
  fun x => ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal)
```

| Lean name | book |
|---|---|
| `indicator_polarCone_eq_conj_indicator` , `polarCone_polarCone` | **Thm 14.1** |
| `polarCone_cone_dom_eq_recession_conj` | Thm 14.2, Cor 14.2.1–2 |
| `polarCone_of_level_sets` | Thm 14.3 |
| `polar_of_epi_cone` (the `ℝ × E × ℝ` construction) | **Thm 14.4** |
| `polarSet_polarSet`, `gaugeFn_eq_supportFn_polar` | **Thm 14.5**, Cor 14.5.1 |
| `recession_polar_duality` | Thm 14.6, Cor 14.6.1 |
| `conj_nonneg_vanishing` | Thm 14.7 |
| `polarGauge`, `polarGauge_polarGauge` | **Thm 15.1**, Cor 15.1.1–2 |
| `isGauge_iff` | Thm 15.2, 15.3 |
| `polarFn`, `polarFn_polarFn` | **Thm 15.4**, Cor 15.4.1 |
| `obverse`, `obverse_conj_polar` | **Thm 15.5**, Cor 15.5.1 |

Bridge lemmas to Mathlib:

```lean
theorem polarSet_eq_polar_of_balanced (h : Balanced ℝ C) : polarSet B C = B.polar C
theorem gaugeFn_eq_gauge (h : Absorbent ℝ C) (x) : gaugeFn C x = (gauge C x : EReal)
```

Rockafellar's own remark in §14 — that the general polarity of sets "is not mentioned subsequently"
outside §15 — means §14 beyond Theorem 14.1, and all of §15, are **low priority**. Theorem 14.1
(polar cones) is high priority: it is used in §23 (normal cones), §27 (optimality), §31.4 and §39.

## 2.7 Ordering within this sub-plan

```
Closure.lean  ─┬─→ Separation.lean ─┐
               │                     ├─→ Duality/Conjugate.lean ─┬─→ Duality/Support.lean
Pairing.lean ──┴─────────────────────┘                           └─→ Duality/Polar.lean
```

`Closure.lean` and `Conjugate.lean` are mutually informed (the affine-minorant lemma), so develop
them in one pass: prove `exists_affine_le_of_proper` in `Closure.lean` using Mathlib's separation,
then `Conjugate.lean` depends on it and never needs to reopen §7.
