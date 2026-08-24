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
| `tendsto_lscHull_along_segment`, `clFn_eq_limit_along_segment`, `tendsto_along_segment_of_closed_proper` | **Thm 7.5**, Cor 7.5.1 |
| `ConvexFn.relint_setOf_le`, `.closure_setOf_le`, `.relint_setOf_lt`, `.closure_setOf_lt`, `.closure_setOf_le_clFn`, `.relint_setOf_le_of_relint_dom_eq`, `.closure_setOf_lt_of_closedFn` | Thm 7.6, Cor 7.6.1 — done in `RelativeInterior.lean` |

**Theorem 7.5 has two forms, and only one of them lives here.** The layer-B form proved in this
file starts the segment at an *interior* point of `epi f`, because relative interiors are
finite-dimensional. Rockafellar's own hypothesis is `x ∈ ri (dom f)`, and that form —
`ConvexFn.tendsto_lscHull_along_segment_relint` — is in `RelativeInterior.lean`, with Lemma 7.3
supplying the relative interior point of the epigraph and Theorem 6.1 replacing Mathlib's
`Convex.combo_interior_closure_mem_interior`. The `ri` form is what Theorem 9.3 consumes; neither
form subsumes the other, since `interior (epi f)` can be empty when `ri (epi f)` is not.

**Theorem 7.4 does not generalise to layer C**, and in particular a proper convex function need not
have a continuous affine minorant there: a
discontinuous linear functional `g` has dense kernel, so `closure (epi g) = univ` and
`lscHull g ≡ ⊥`, while `g` is convex, finite everywhere and proper. The sketch assumed
`(x₀, f x₀ − 1) ∉ closure (epi f)`, which is exactly what fails.

What is true, and what this file should prove:

```lean
/-- A closed proper convex function has a continuous affine minorant.

The hypotheses are bundled as `ClosedProperConvexFn` (`Closure.lean`), and the conclusion is stated
with `y : E →L[ℝ] ℝ` rather than a pairing-valued `y : F`, so that `Closure.lean` need not import
`Duality/Pairing.lean`; `Conjugate.lean` converts with `exists_pairing_eq` at the two places that
need the pairing form. -/
theorem exists_affine_le_of_closed_proper (hf : ClosedProperConvexFn f) :
    ∃ (y : E →L[ℝ] ℝ) (c : ℝ), ∀ x, ((y x : ℝ) : EReal) - c ≤ f x

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
| `conjEquiv` | the induced involution on `ClosedProperConvexFn` | Cor 12.2.1 |
| `conj_eq_iSup_relint` | the sup may be restricted to `ri (dom f)` | Cor 12.2.2 *(finite-dim)* |
| `conj_comp_affine` | conjugate of `f ∘ T` for an affine `T` | Thm 12.3 |
| `monotoneConj`, `monotoneConj_monotoneConj` — **done**, in `Duality/GaugeLike.lean` | the monotone conjugate `g⁺`, in one dimension | **Thm 12.4**. Stated as a genuine involution by *truncating* `g⁺` to `+∞` off the half-line; the proof is Fenchel–Moreau for `mulPairing`. There is no general-cone version: the `ℝⁿ` orthant proof uses `y ↦ max(y,0)`, which no general cone supplies |

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
| `mem_closure_convexHull_iff_le_supportFn` — **done**, in `Duality/Support.lean` | **Thm 13.1**, closure clause — the only one of the four that survives outside finite dimensions |
| `mem_relint_iff_lt_supportFn`, `mem_interior_iff_lt_supportFn`, `mem_affineSpan_iff_eq_supportFn`, `neg_supportFn_neg_eq_iff`, `exists_forall_eq_of_notMem_affineSpan` — **done**, in `Duality/SupportRelint.lean` | **Thm 13.1**, the `ri`, `int` and `aff` clauses, the last being **Cor 1.4.1**. All three are genuinely layer D: for `C = ker φ` with `φ` discontinuous, `ri C = aff C = C` and `int C = ∅` while all three stated conditions hold at *every* point. The `int` clause additionally needs `C.Nonempty` (false over the zero space otherwise) and `B.SeparatingRight`, since over a pairing `y ≠ 0` and `⟨·, y⟩ ≠ 0` differ; the `aff` clause needs **no convexity** |
| `conj_indicator`, `conj_supportFn` — indicator and support function are conjugate | **Thm 13.2** |
| `posHomogeneous_closed_iff_isSupportFn` — the closed proper positively homogeneous convex functions *are* the support functions | **Thm 13.2** |
| `clFn_eq_supportFn_of_posHomogeneous` | Cor 13.2.1 |
| `isSupportFn_bounded_iff_finite` | Cor 13.2.2, with "bounded" in the pairing sense |
| `isBounded_iff_forall_bddAbove` — **done**, in `Duality/SupportRelint.lean` | **Cor 13.2.2** with "bounded" read as `Bornology.IsBounded`. Genuinely layer D: a coordinate estimate against `Module.finBasis`, each coordinate being `⟨·, yᵢ⟩` by `exists_pairing_eq`. Cor 23.7.1, the last clause of Thm 23.4 and Cor 29.1.5 all consume this form and not the one above |
| `recessionFn_conj` : `(conj B f) 0⁺ = δ*(·|dom f)` — **formalized**, in `Recession/Conjugate.lean`; with `constancySpace_conj` | **Thm 13.3** |
| `conj_finite_iff_cofinite` | Cor 13.3.1 |
| `mem_closure_dom_conj_iff`, `mem_relint_dom_conj_iff`, `mem_interior_dom_conj_iff`, `mem_affineSpan_dom_conj_iff` — **done**, in `Duality/Level.lean` | **Cor 13.3.4**, all four clauses. They need **neither Thm 12.3 nor the translation by `-y₀`**: stating them through `recessionFn f` and `⟨y, y₀⟩` rather than through `g 0⁺` makes the translation vanish. The book's exception set in (b) is `y₀`-independent, and its "`= 0`" is forced by the inequality at `-y` |
| `lineality_conj_eq_orthogonal_aff_dom` | Thm 13.4 *(finite-dim)* |
| `interior_dom_conj_nonempty_iff` — **done**, in `Duality/Level.lean` | **Cor 13.4.2**. It needs **no `finrank` count**: "dim `f*` = n ⇺ lineality `f` = 0" is `vectorSpan (dom f*) = ⊤ ⇺ annihilator = {0}`, i.e. Hahn–Banach. Only Cor 13.4.1 (rank) needs the count |
| `supportFn_level_eq_clFn_hom_conj` | **Thm 13.5** |

Theorem 13.2 is the reason support functions are not a separate theory: they are conjugates of
indicators, so every property is inherited. The *characterisation* half (positively homogeneous +
closed + proper ⟹ is a support function) is `biconj_eq_clFn` plus
`PosHomogeneous.convexFn_iff_subadditive` from sub-plan 1.

Theorems 13.3–13.5 need recession functions (§8) and so are finished in sub-plan 3; the statements
belong here.

**Theorem 13.3 is formalized**, in `Recession/Conjugate.lean` — a new file that is exactly the join
of `Duality/Support.lean` and `Recession/Function.lean`, since neither can name both `f*` and
`f 0⁺`. Four adjustments to the plan:

* **The name is `recessionFn_conj`, and the equation runs the other way** (`(f*)0⁺ = δ*(·|dom f)`),
  matching Rockafellar's own direction and the direction consumers rewrite in.
* **The file is layer A.** Only *one* of the two inequalities needs anything: `(f*)0⁺ ≤ δ*(·|dom f)`
  is a termwise bound on the supremum defining `f*` and holds for arbitrary `f`
  (`recessionFn_conj_le_supportFn_dom`). The reverse needs a point where `f*` is finite — that is
  `Proper (conj B f)`, i.e. **Theorem 12.2** — and it is taken as a *hypothesis* rather than derived,
  so layer-C callers supply it from `proper_conj` and everybody else can still use the statement.
* **`constancySpace_conj` is the form that gets used**, not Theorem 13.3 itself: the constancy space
  of `f*` is the annihilator `{y | ∀ x ∈ dom f, ⟨x, y⟩ = 0}` of the effective domain. That is the
  shape Theorem 9.2 and Theorem 16.3 consume — it converts "`f*` is constant along `y`" into a
  statement about `dom f` that a relative-interior hypothesis can discharge.
* **Corollary 13.3.1 and Theorems 13.4–13.5 remain unstated.** Nothing needs them yet; Theorem 13.4
  is `constancySpace_conj` read as an orthogonal complement and should be cheap when wanted.

## 2.6 `Tdaf/Analysis/Convex/Duality/Polar.lean` — §14, and `Duality/Gauge.lean` — §14.6–14.7, §15

**Status: §14 is done, and §15 is done except Theorem 15.3.** Theorems 14.6 and 14.7 and all of
§15 live in `Duality/Gauge.lean`, not in `Polar.lean` — their content is §15's, and the middle set
of Theorem 14.7 is literally `setOf_polarFn_le` from §15.

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
| `recessionConeFn_conj`, `recessionConeFn_conj_hull`, `recessionConeFn_eq_polarCone_dom_conj`, `polarCone_recessionConeFn`, `polarCone_coe_hull` — **done**, in `Recession/Conjugate.lean` | **Thm 14.2**. Half of it costs nothing: the recession cone of `f*` is the polar of `dom f` by Theorem 13.3 at the zero level set, with no closedness anywhere. The other half is that one fed `f** = f` |
| `zero_mem_interior_iff_polarCone_eq_zero`, `isBounded_setOf_le_iff_zero_mem_interior_dom_conj` — **done**, in `Recession/Conjugate.lean` | **Cor 14.2.2**, via Theorems 8.7 and 8.4. The dictionary lemma's nonemptiness hypothesis is real: for `D = ∅` between trivial spaces the polar is `{0}` and the interior is empty. Both its directions run on **Cor 6.4.1**, `Convex.mem_interior_iff_absorbs`, which was a gap in Mathlib as well |
| `polarCone_of_level_sets` | Thm 14.3 |
| `polar_of_epi_cone` (the `ℝ × E × ℝ` construction) | **Thm 14.4** |
| `polarSet_polarSet`, `gaugeFn_eq_supportFn_polar` | **Thm 14.5**, Cor 14.5.1 |
| `recessionCone_eq_polarCone_polarSet`, `polarCone_recessionCone`, `linealitySpace_eq_setOf_pairing_eq_zero`, `polarCone_linealitySpace` — **done** | **Thm 14.6** (needs only the bipolar theorem, not Cor 8.3.2) |
| `polarSubmodule`, `finrank_add_finrank_polarSubmodule`, `vectorSpan_eq_span_of_zero_mem`, `finrank_vectorSpan_polarSet_add_lineality`, `finrank_vectorSpan_add_lineality_polarSet` — **done**, in `Duality/Gauge.lean` | **Cor 14.6.1**. It cannot live in `Duality/Polar.lean`: it consumes `polarCone_linealitySpace`, which is in `Gauge.lean`, and `Gauge` imports `Polar`. The `finrank` API turned out to be six lines of rank–nullity. The third relation, `rank C° = rank C`, is the difference of the other two and is a docstring remark rather than a theorem |
| `polarSet_setOf_le_subset_and_subset` — **done** | **Thm 14.7**, with no closedness and neither Thm 13.5 nor 9.7 |
| `polarGauge`, `polarGauge_polarGauge`, `polarGaugeEquiv` — **done** | **Thm 15.1**, Cor 15.1.1–2 |
| `isGauge_iff`, `gaugeEquiv` — **done** | the §15 gauge characterisation (the paragraph before Thm 15.1) |
| `IsNorm`, `isNorm_iff`, `isNorm_polarGauge_gaugeFn` — **done** | **Thm 15.2** |
| `monotoneComp`, `conj_monotoneComp`, `closedProperConvexFn_monotoneComp`, `PosHomogeneousDeg`, `degGauge`, `posHomogeneousDeg_iff_exists_isGauge`, `conj_monotoneComp_powHalfLine`, `polarGauge_degGauge`, `pairing_le_rpow_mul_rpow`, `polarSet_setOf_le_inv` — **done**, in `Duality/GaugeLike.lean` | **Thm 15.3**'s first assertion and conjugacy formula `(g ∘ k)* = g⁺ ∘ k°`, and **Cors 15.3.1–15.3.2** in full, Hölder included. Beyond Thm 12.4 it needed the Thm 8.6 growth estimate for a non-constant convex function of the half-line and right-continuity at the origin — and, for the first assertion only, Fenchel–Moreau, hence a compatible pairing, a continuous flip and local convexity of `E`; the conjugacy formula needs none of those. **Not done**: the converse half of Thm 15.3 (gauge-like ⇒ `g ∘ k`), blocked on convexity of the reconstructed `g` |
| `polarFn`, `polarFn_polarFn`, `polarFnEquiv` — **done** | **Thm 15.4**, Cor 15.4.1 |
| `obverse`, `obverse_obverse`, `conj_eq_obverse_polarFn`, `polarFn_eq_obverse_conj`, `polarFn_obverse`, `conj_obverse`, `polarFn_conj_eq_conj_polarFn` — **done** | **Thm 15.5**, Cor 15.5.1 |

Bridge lemmas to Mathlib:

```lean
theorem polarSet_eq_polar_of_balanced (h : Balanced ℝ C) : polarSet B C = B.polar C
theorem gaugeFn_eq_gauge (h : Absorbent ℝ C) (x) : gaugeFn C x = (gauge C x : EReal)
```

Rockafellar's own remark in §14 — that the general polarity of sets "is not mentioned subsequently"
outside §15 — made §14 beyond Theorem 14.1, and all of §15, low priority. They are nonetheless done;
see `NOTES.md` §1 under `Duality/Gauge.lean` for the design decisions and the corrections
established while proving them.

**`gaugeFn` is a third gauge, and the plan's suggestion to reuse `egauge` was rejected.** `egauge ℝ≥0`
*is* Rockafellar's gauge, but it is `ℝ≥0∞`-valued while every function in this library is
`EReal`-valued, and Mathlib has no lemma commuting `ENNReal.toEReal` with `iInf`. `gaugeFn` is
literally the same infimum taken in `EReal`; `gaugeFn_eq_gauge` records the agreement with Mathlib's
`gauge` under absorbency.

## 2.7 Ordering within this sub-plan

```
Closure.lean  ─┬─→ Separation.lean ─┐
               │                     ├─→ Duality/Conjugate.lean ─┬─→ Duality/Support.lean
Pairing.lean ──┴─────────────────────┘                           └─→ Duality/Polar.lean
```

`Closure.lean` and `Conjugate.lean` are mutually informed (the affine-minorant lemma), so develop
them in one pass: prove `exists_affine_le_of_proper` in `Closure.lean` using Mathlib's separation,
then `Conjugate.lean` depends on it and never needs to reopen §7.
