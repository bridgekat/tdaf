# Working notes: current backbone API and Lean gotchas

Central record for anyone (human or agent) writing backbone modules for the convex-analysis
project. Keep it up to date: it exists so that the same obstacles are not rediscovered twice.

---

## 1. The API that already exists

Everything under `Tdaf/Analysis/Convex/` lives in `namespace Tdaf.ConvexAnalysis`; the names below
are written as they are inside it. `Tdaf/Order/EReal.lean` is `Tdaf.EReal`, deliberately outside the
topic namespace: its lemmas are general-purpose `EReal` facts with no convexity in them.

### `Tdaf/Order/EReal.lean`

```lean
theorem le_coe_of_forall_lt {z : EReal} {r : ℝ} (h : ∀ q : ℝ, r < q → z < (q : EReal)) :
    z ≤ (r : EReal)
theorem exists_real_btwn_of_lt_coe {z : EReal} {r : ℝ} (h : z < (r : EReal)) :
    ∃ q : ℝ, z < (q : EReal) ∧ q < r
theorem coe_mul_coe (a r : ℝ) : (a : EReal) * (r : EReal) = ((a * r : ℝ) : EReal)
theorem eq_bot_of_forall_le_coe {z : EReal} (h : ∀ r : ℝ, z ≤ (r : EReal)) : z = ⊥
theorem exists_coe_of_ne_bot_of_lt_top {z : EReal} (h₁ : z ≠ ⊥) (h₂ : z < ⊤) :
    ∃ r : ℝ, z = (r : EReal)
theorem coe_sub_le_comm {a : ℝ} {z w : EReal} : (a : EReal) - z ≤ w ↔ (a : EReal) - w ≤ z
theorem le_coe_sub_comm {a : ℝ} {z w : EReal} : z ≤ (a : EReal) - w ↔ w ≤ (a : EReal) - z
theorem neg_iSup {ι : Sort*} (u : ι → EReal) : -(⨆ i, u i) = ⨅ i, -(u i)
theorem neg_iInf {ι : Sort*} (u : ι → EReal) : -(⨅ i, u i) = ⨆ i, -(u i)
```

`coe_sub_le_comm` carries §12; `le_coe_sub_comm` is its mirror and carries the concave §12. Both are
unconditional because `a` is finite. `neg_iSup`/`neg_iInf` are what make the sign dictionary of
`Duality/ConcaveConj.lean` a one-line rewrite.

The multiplication-and-supremum group, which §13 and §16 run on:

```lean
theorem coe_mul_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z w : EReal} :
    (a : EReal) * z ≤ (a : EReal) * w ↔ z ≤ w
theorem coe_mul_le_coe_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (a : EReal) * z ≤ (r : EReal) ↔ z ≤ ((r / a : ℝ) : EReal)
theorem coe_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (r : EReal) ≤ (a : EReal) * z ↔ ((r / a : ℝ) : EReal) ≤ z
theorem coe_mul_iSup {a : ℝ} (ha : 0 < a) {ι : Sort*} (u : ι → EReal) :
    (a : EReal) * (⨆ i, u i) = ⨆ i, (a : EReal) * u i
theorem coe_mul_iInf {ι : Sort*} {a : ℝ} (ha : 0 < a) (g : ι → EReal) :
    (a : EReal) * (⨅ i, g i) = ⨅ i, (a : EReal) * g i
theorem biSup_add_of_ne_bot {α : Type*} {s : Set α} {u : α → EReal} (hu : ∀ a ∈ s, u a ≠ ⊥)
    (w : EReal) : (⨆ a ∈ s, u a) + w = ⨆ a ∈ s, (u a + w)
theorem biSup_add_biSup {α β : Type*} {s : Set α} {t : Set β} {u : α → EReal} {v : β → EReal}
    (hu : ∀ a ∈ s, u a ≠ ⊥) (hv : ∀ b ∈ t, v b ≠ ⊥) :
    (⨆ a ∈ s, u a) + (⨆ b ∈ t, v b) = ⨆ a ∈ s, ⨆ b ∈ t, (u a + v b)
theorem eq_of_forall_le_coe_iff {z w : EReal}
    (h : ∀ r : ℝ, z ≤ (r : EReal) ↔ w ≤ (r : EReal)) : z = w
theorem le_coe_of_add_le_coe_add {p q : ℝ} {u v : EReal} (hp : (p : EReal) ≤ u)
    (hq : (q : EReal) ≤ v) (h : u + v ≤ ((p + q : ℝ) : EReal)) : u ≤ (p : EReal)
```

`coe_mul_le_coe_iff`/`coe_le_coe_mul_iff` are the two sides of "divide by `a > 0`", and are how
**Thm 16.1** is proved without ever case-splitting on `⊤`/`⊥`. `biSup_add_biSup` is the sum of two
suprema over sets — the shape `conj_infConv` lands in — and needs `≠ ⊥` on both families, since
`⊥ + ⊤` would otherwise break the interchange. `eq_of_forall_le_coe_iff` is the workhorse of §16:
it turns "these two `EReal`s are equal" into "these two functions have the same affine minorants",
which is exactly what `conj_le_coe_iff` supplies. `le_coe_of_add_le_coe_add` says two slack
inequalities cannot compensate: if `p ≤ u`, `q ≤ v` and `u + v ≤ p + q` with `p q : ℝ`, then each
is tight. It is one-sided — apply it again with `add_comm` for the other summand — and it is what
splits one joint equality in Fenchel's inequality into two (Theorem 23.8).

Note the namespace clash: plain `EReal.foo` resolves to `Tdaf.EReal.foo` first, from anywhere under
`namespace Tdaf`. Write `_root_.EReal.foo` for Mathlib's lemmas when the name exists in both, and
`Tdaf.EReal.foo` for ours when the surrounding context makes plain `EReal.foo` ambiguous.

### `Tdaf/Analysis/Convex/Epigraph.lean`

No structure on `E` at all:

```lean
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
@[simp] theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal)
theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal)
theorem epi_anti {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f
theorem le_iff_epi_subset {f g : E → EReal} : f ≤ g ↔ epi g ⊆ epi f

def dom (f : E → EReal) : Set E := {x | f x < ⊤}
@[simp] theorem mem_dom {f : E → EReal} {x : E} : x ∈ dom f ↔ f x < ⊤

structure Proper (f : E → EReal) : Prop where
  dom_nonempty : (dom f).Nonempty
  ne_bot : ∀ x, f x ≠ ⊥

/-- `dom` is Rockafellar's projection of the epigraph — with no hypothesis on `f`. -/
theorem dom_eq_fst_image_epi (f : E → EReal) : dom f = Prod.fst '' epi f

noncomputable def restrict (s : Set E) (f : E → EReal) : E → EReal := fun x => ⨅ _ : x ∈ s, f x
@[simp] theorem restrict_of_mem    {…} (hx : x ∈ s) : restrict s f x = f x
@[simp] theorem restrict_of_notMem {…} (hx : x ∉ s) : restrict s f x = ⊤
```

With `[AddCommGroup E] [Module ℝ E]`:

```lean
structure ConvexFn (f : E → EReal) : Prop where
  convex_epi : Convex ℝ (epi f)
@[simp] theorem convexFn_iff_convex_epi {f : E → EReal} : ConvexFn f ↔ Convex ℝ (epi f)

theorem combo_of_pos {P : E → Prop} {x y : E} {a b : ℝ} (hx : P x) (hy : P y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h : 0 < a → 0 < b → P (a • x + b • y)) :
    P (a • x + b • y)

theorem ConvexFn.epi_combo {f : E → EReal} (hf : ConvexFn f) {x y : E} {μ ν : ℝ}
    (hx : f x ≤ (μ : EReal)) (hy : f y ≤ (ν : EReal)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)

theorem convexFn_of_epi_combo {f : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), f x ≤ (μ : EReal) → f y ≤ (ν : EReal) →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)) :
    ConvexFn f

theorem convexFn_iff_forall_lt (f : E → EReal) :        -- Rockafellar Theorem 4.2
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal)

theorem convexFn_iff_le {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :  -- Rockafellar Theorem 4.1
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

theorem ConvexFn.convex_lt  {f} (hf : ConvexFn f) (α : EReal) : Convex ℝ {x | f x < α}  -- Thm 4.6
theorem ConvexFn.convex_le  {f} (hf : ConvexFn f) (α : EReal) : Convex ℝ {x | f x ≤ α}  -- Thm 4.6
theorem ConvexFn.convex_dom {f} (hf : ConvexFn f) : Convex ℝ (dom f)

theorem epi_restrict_coe (s : Set E) (g : E → ℝ) :
    epi (restrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2}
theorem convexOn_iff_convexFn (s : Set E) (g : E → ℝ) :
    ConvexOn ℝ s g ↔ ConvexFn (restrict s fun x => (g x : EReal))
```

### `Tdaf/Analysis/Convex/Indicator.lean`

```lean
noncomputable def indicatorFn (s : Set E) : E → EReal := restrict s (fun _ => 0)
@[simp] theorem indicatorFn_of_mem    (hx : x ∈ s) : indicatorFn s x = 0
@[simp] theorem indicatorFn_of_notMem (hx : x ∉ s) : indicatorFn s x = ⊤
theorem indicatorFn_ne_bot (s : Set E) (x : E) : indicatorFn s x ≠ ⊥
@[simp] theorem dom_indicatorFn (s : Set E) : dom (indicatorFn s) = s
@[simp] theorem indicatorFn_add (s t : Set E) :
    indicatorFn s + indicatorFn t = indicatorFn (s ∩ t)
theorem epi_indicatorFn (s : Set E) : epi (indicatorFn s) = s ×ˢ Set.Ici (0 : ℝ)
@[simp] theorem convexFn_indicatorFn {s : Set E} : ConvexFn (indicatorFn s) ↔ Convex ℝ s
theorem restrict_eq_add_indicatorFn {s : Set E} {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    restrict s f = f + indicatorFn s
```

### `Tdaf/Analysis/Convex/Concave.lean`

`hypo`, `ConcaveFn` (structure over `Convex ℝ (hypo g)`), `domConcave`, `ProperConcave`,
`restrictConcave s g = ⨆ _ : x ∈ s, g x` (extension by `⊥` — `restrict` extends by `⊤` and is the
wrong object for a concave function), `concaveFn_iff_convexFn_neg` (**no** side condition),
`concaveFn_iff_forall_gt`, `concaveFn_iff_le` (needs `∀ x, g x ≠ ⊤`), `ConcaveFn.convex_gt/_ge`,
`concaveOn_iff_concaveFn`.

### `Tdaf/Analysis/Convex/Homogeneous.lean`

`PosHomogeneous`, `posHomogeneous_iff_isCone_epi`, `convex_iff_add_mem_of_isCone` (Thm 2.6),
`PosHomogeneous.convexFn_iff_subadditive` (Thm 4.7), `.sum_le` (Cor 4.7.1, **needs `s.Nonempty`**),
`.neg_le` (Cor 4.7.2), `.isLinearOn_iff` / `.exists_linearMap_iff` / `.exists_linearMap_span`
(Thm 4.8), `.map_zero_trichotomy` (`f 0 ∈ {0, ⊤, ⊥}`; the conditional equality is
`.map_zero_eq_zero`).

### `Tdaf/Analysis/Convex/Operations/Epi.lean`

`ofEpi F = fun x => ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)`, `ofEpi_lt_iff` (**the** witness
extractor — the infimum is not attained, so this is the only way in), `subset_epi_iff_le_ofEpi`,
`ofEpi_epi` (`simp`, unconditional), `IsEpiLike F := ∃ f, F = epi f`, `isEpiLike_iff_forall`
(sections upward-closed and closed below), `epi_ofEpi` (needs `IsEpiLike`), `IsEpiLike.iInter/.inter/
.union/.closure/.of_isClosed`, `convexFn_ofEpi` (Thm 5.3).

### `Tdaf/Analysis/Convex/Operations/Basic.lean`

`epi_iSup`, `epi_biSup`, `epi_sup`, `dom_add`, `epi_restrict`, `convexFn_iSup` (Thm 5.5),
`ConvexFn.add` (Thm 5.2, needs `∀ x, f x ≠ ⊥` on both), `.sum`, `.smul`, `.restrict`,
`.add_indicatorFn`, `extendTop`, `ConvexFn.comp` / `.comp_extendTop` (Thm 5.1).

### `Tdaf/Analysis/Convex/Operations/InfConv.lean`

`infConv f g := ofEpi (epi f + epi g)` (**not** the infimum formula — that is `infConv_apply`, under
`∀ x, f x ≠ ⊥` on *both*), `dom_infConv : dom (f □ g) = dom f + dom g` (**no** hypothesis),
`infConv_comm`, `infConv_assoc` (needs `epi_ofEpi_add_subset`, *not* set `add_assoc`),
`infConv_indicatorFn_zero` (identity), `convexFn_infConv` (Thm 5.4), and the type synonym
`InfConvFn E` carrying `AddCommMonoid`, whose `nsmul` is n-fold infimal convolution.

### `Tdaf/Analysis/Convex/Operations/Hull.lean`

`convFn` (family), `convHullFn` (single function), `convFn₂`; `isGreatest_convFn` (the universal
property), `convFn_apply` (**Theorem 5.6**, proved), `convFn₂_apply`, and
`gci_val_convHullFn` — `conv` as a **`GaloisCoinsertion`**, right adjoint to the inclusion of convex
functions. `Lattice.lean` gets its `CompleteLattice` from `GaloisCoinsertion.liftCompleteLattice`.

### `Tdaf/Analysis/Convex/Operations/Image.lean`

`mapLin A f`, `compLin g A`; `convexFn_mapLin`/`convexFn_compLin` (**Theorem 5.7**),
`gc_compLin_mapLin` (an honest *monotone* `GaloisConnection`, no `OrderDual`), `mapLin_eq_ofEpi`,
`dom_mapLin`, `convexFn_iInf_right` (partial minimisation, the form §29 uses), and
`exists_epi_mapLin_ne_image` — a witness that `epi (A f) ≠ (A × id) '' epi f`.

### `Tdaf/Analysis/Convex/Homogenize.lean`

`smulRight f a := ofEpi (a • epi f)` with `epi_smulRight` for `a > 0` **only**, `smulRight_zero`
(`= δ(·|0)`, needs `f ≢ ⊤`), `not_isEpiLike_zero_smul_epi`; `smulRightHom : ℝ≥0 →* Function.End _`;
`levelOneLift`; `hom`, `posHomogeneous_hom`, `convexFn_hom`, `hom_isGreatest`; `homCone` and
`epi_hom : epi (hom f) = homCone f ∪ {0} ×ˢ Ici 0` (**the cone is not the epigraph**); `homEpiCone`.

### `Tdaf/Analysis/Convex/Closure.lean`

`lscHull f := ofEpi (closure (epi f))` with `epi_lscHull` **unconditional**;
`clFn` (branching on `lscHull f`, `open Classical in`), `ClosedFn`;
`lowerSemicontinuous_iff_isClosed_epi` (**Thm 7.1**), `isGreatest_lscHull`, `closedFn_iff`,
`iInf_clFn_eq_iInf`, `ConvexFn.eq_bot_or_eq_top` (**Cor 7.2.1**);
`ClosedProperConvexFn` (the bundled `convex`/`closed`/`proper` triple, with `.isClosed_epi`,
`.lowerSemicontinuous` and the `of_isClosed_epi` constructor §8 uses);
`exists_affine_le_of_closed_proper` (**the Fenchel–Moreau keystone**),
`tendsto_lscHull_along_segment` (**Thm 7.5**), `lscHullClosure`/`clFnClosure` as `ClosureOperator`s.

### `Tdaf/Analysis/Convex/Continuity.lean`

**Thm 10.1** as `ConvexFn.continuousOn_toReal_relint_dom` (real-valued, the working form) and
`ConvexFn.continuousOn_relint_dom` (`EReal`-valued). The chart machinery is reusable:
`intrinsicInterior_vadd` (translation invariance of `ri`, absent from Mathlib), `chart C x₀ V`,
`image_chart`, `zero_mem_chart`, `convex_chart`, `affineSpan_chart`, and
`relint_eq_vadd_image_interior` (`ri C = x₀ + ι (int (chart C x₀ V))`). Also
`ConvexFn.convexOn_toReal_dom`, the bridge from `ConvexFn f` + `Proper f` to Mathlib's
`ConvexOn ℝ (dom f) (·.toReal)`.

The subspace `V` is always a *parameter* carrying `hV : V = span ℝ (C - x₀)`, never a definition —
see gotcha 52.

### `Tdaf/Analysis/Convex/Lattice.lean`

`ConvexFns E` (`abbrev` on the subtype) with `CompleteLattice` from
`gci_val_convHullFn.liftCompleteLattice`; `coe_sSup`/`coe_iSup` (join is pointwise),
`coe_sInf`/`coe_iInf` (meet is `convFn`, **not** pointwise), `coe_top`/`coe_bot`,
`coeOrderEmbedding`, `coeSSupHom`, and `not_coe_inf_eq_inf` (the strictness witness).

### `Tdaf/Analysis/Convex/Separation.lean`

`Separates`, `SeparatesProperly`, `SeparatesStrongly` (**the strict-gap definition in `EReal`** —
needs no topology on `E`); Theorem 11.1 in all three forms; `separatesStrongly_iff_exists_nhds` and
`..._closedBall` (the `εB` form); Thm 11.2, 11.4 (+ compact/closed corollaries), 11.5, 11.6
(full `iff` at layer C, with `(interior C).Nonempty`), 11.7; `halfSpaceCone : _ → PointedCone ℝ E`;
and `exists_affine_lt_of_notMem` / `exists_affine_le_of_isClosed_epi` — the reusable non-vertical
separation lemma that `Closure.lean` now consumes.

### `Tdaf/Analysis/Convex/Recession/Cone.lean`

`recessionCone`, `recessionPointedCone : PointedCone ℝ E` (**no hypothesis on `C`**),
`linealitySpace`, `linealitySubmodule` (`= PointedCone.lineal`, so Thm 2.7 is two lines);
Thm 8.1 (layer A), Thm 8.2/8.3 and Cors 8.3.2–8.3.4 (**layer B**), `isClosed_recessionCone`
(**layer B**), Thm 8.4/Cor 8.4.1 (layer D); bridges to Mathlib's `asymptoticCone`. Also
`eq_add_inter_of_isCompl_of_le`, `recessionCone_preimage_affine`, `recessionCone_coe_submodule`,
and the product lemmas `prod_recessionCone_subset` / `recessionCone_prod` / `linealitySpace_prod`
(the last two need both factors nonempty).

### `Tdaf/Analysis/Convex/Duality/Pairing.lean`

`affineFn`, `IsAdjointPair` (four-space — Mathlib's pairs a module with *itself*),
`prodPairing`/`negFst` (for D8), and `dual_prod_apply`/`exists_unique_dual_prod` (the dual of
`E × ℝ`, which Mathlib lacks). The dual precomposition datum is Mathlib's
`ContinuousLinearMap.precomp ℝ A` — see gotcha 28.

### `Tdaf/Analysis/Convex/Duality/Conjugate.lean`

`conj B f`, `biconj`; `sub_le_conj` (**unconditional**), `le_add_conj` (Fenchel's inequality —
needs properness, see gotcha 23), `conj_le_iff` (the adjunction, unconditional), `conj_clFn`,
`eq_biSup_affineFn` (**Thm 12.1**), `biconj_eq_clFn` (**Thm 12.2, Fenchel–Moreau**), `conjEquiv`,
`gc_conj_conj`/`conjClosure`, and two instantiations, both in the space's *own* topology:
`_topDual` (a locally convex space against its continuous dual — so, a Banach space in its norm
topology) and `_inner` (Hilbert/`ℝⁿ`, via Fréchet–Riesz).

### `Tdaf/Analysis/Convex/Duality/ConcaveConj.lean`

`concaveConj B g y = ⨅ x, ⟨x,y⟩ - g x` and `biconcaveConj`; the sign dictionary
`neg_concaveConj : -(concaveConj B g y) = conj B (-g) (-y)` with its two solved forms
`concaveConj_eq_neg_conj_neg` and `conj_eq_neg_concaveConj_neg` (**note the reflection on the dual
side** — `g* ≠ -(-g)*`); `concaveConj_le_sub` and `add_concaveConj_le` (**both unconditional**, see
gotcha 40); `coe_le_concaveConj_iff`, `concaveConj_antitone`, `le_concaveConj_iff` (the adjunction),
`le_biconcaveConj`; the improper cases `concaveConj_eq_top_iff`/`_of_eq_top`/`_bot`/`_top`/`_ne_top`;
`concaveFn_concaveConj`; `biconcaveConj_eq_neg_biconj_neg` (**pure algebra — the two reflections
cancel, so there is no sign on the argument**) and, at layer C,
`biconcaveConj_eq_neg_clFn_neg`/`biconcaveConj_eq_self`.

### `Tdaf/Analysis/Convex/Duality/Exact.lean`

`IsExactSum B f g` (`proper_left`, `proper_right`, `exact_le`) and
`IsExactImage B B' A A' hA g` (`proper`, `exact_le`) — the D5 interfaces. Unconditional halves:
`conj_add_le_coe_add`, `epi_conj_add_epi_conj_subset`, `conj_add_le_infConv`,
`conj_add_le_add_conj` (this last one needs nonempty domains), `conj_compLin_le_mapLin`.
Consequences: `IsExactSum.{conj_left_ne_bot, conj_right_ne_bot, symm, proper_add,
infConv_le_conj_add, conj_add, conj_add_apply, exists_conj_add_eq}` and
`IsExactImage.{proper_compLin, mapLin_le_conj_compLin, conj_compLin, exists_conj_compLin_eq}`.
The `of_relint`/`of_polyhedral`/`of_continuousAt` sufficient conditions are **not** here — see D5;
`of_relint` is in `Duality/Relint.lean`.

The two `exact_le` fields are **not** symmetric in shape:

```lean
IsExactSum.exact_le   : ∀ y : F, ∃ y₁ y₂ : F, y₁ + y₂ = y ∧
                          conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y
IsExactImage.exact_le : ∀ y : F, conj B (compLin g A) y < ⊤ →
                          ∃ z : H, A' z = y ∧ conj B' g z ≤ conj B (compLin g A) y
```

The `< ⊤` guard on the image side is load-bearing: without it the field demands a point of the
fibre `A' ⁻¹ {y}` at every `y`, i.e. it forces `A'` surjective, and the interface becomes
unsatisfiable for e.g. `A = 0`. The sum side needs no guard because `y = y + 0` always splits.

### `Tdaf/Analysis/Convex/Duality/Relint.lean`

The only file that *produces* a D5 interface. `IsExactImage.of_relint` (**Thm 16.3**) and
`IsExactSum.of_relint` (**Thm 16.4**), plus the three steps they are assembled from:
`mem_constancySpace_conj_of_relint`, `le_of_mk_mem_recessionCone_epi_conj`,
`mk_mem_linealitySpace_epi_conj_of_relint`. Layers differ between the two: the image rule needs
`FiniteDimensional ℝ G` and `ℝ H` (Thm 9.2 runs in `H`), the sum rule needs `FiniteDimensional ℝ F`
(Cor 9.1.1 runs in `F × ℝ`); `E` is only ever a normed space.

### `Tdaf/Analysis/Convex/Recession/Closedness.lean`

**Thm 9.1** as `isClosed_image_of_recessionCone_inter_ker` /
`recessionCone_image_of_recessionCone_inter_ker` (reduced hypothesis `0⁺C ∩ ker A ⊆ {0}`) and
`Convex.{isClosed_image_closure, closure_image_eq, recessionCone_image_closure,
closure_image_eq_and_recessionCone}` (Rockafellar's hypothesis), with the reduction packaged as
`exists_reduction_of_recessionCone_inter_ker`. **Cor 9.1.1** as `Convex.{isClosed_add,
closure_add_eq, recessionCone_add}`, via `image_coprod_id_prod` and
`forall_mem_linealitySpace_prod`. **Thm 9.2** as `closedProperConvexFn_mapLin` (epigraph identity
*and* `ClosedProperConvexFn`) with `exists_mapLin_eq` as the attainment reading, and
`mk_zero_mem_linealitySpace_epi_iff` transporting the hypothesis to the epigraph.

### `Tdaf/Analysis/Convex/Recession/Conjugate.lean`

**Thm 13.3**: `recessionFn_conj_le_supportFn_dom` (unconditional half),
`supportFn_dom_le_recessionFn_conj` (needs `Proper f` and `Proper (conj B f)`), `recessionFn_conj`,
and `constancySpace_conj` — the form §9.2 and §16.3 actually consume. Layer A throughout:
properness of `f*` is a hypothesis, not derived.

### `Tdaf/Analysis/Convex/Duality/Ops.lean`

The §16 table. Reading the epigraph:

```lean
theorem conj_ofEpi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set (E × ℝ)) (y : F) :
    conj B (ofEpi S) y = ⨆ p ∈ S, ((B p.1 y - p.2 : ℝ) : EReal)
theorem conj_eq_biSup_epi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    conj B f y = ⨆ p ∈ epi f, ((B p.1 y - p.2 : ℝ) : EReal)
```

The unconditional rows — no hypothesis on the functions, layer A on both spaces:

```lean
theorem conj_smul (ha : 0 < a) (B) (f) :                                          -- Thm 16.1
    conj B (fun x => (a : EReal) * f x) = smulRight (conj B f) a
theorem conj_smulRight (ha : 0 < a) (B) (f) :                                     -- Thm 16.1
    conj B (smulRight f a) = fun y => (a : EReal) * conj B f y
theorem conj_mapLin (hA : IsAdjointPair B B' A A') (f : E → EReal) :              -- Thm 16.3
    conj B' (mapLin A f) = compLin (conj B f) A'
theorem conj_infConv (B) (f g : E → EReal) :                                      -- Thm 16.4
    conj B (infConv f g) = conj B f + conj B g
theorem conj_convFn (B) (f : ι → E → EReal) :                                     -- Thm 16.5
    conj B (convFn f) = ⨆ i, conj B (f i)
theorem conj_convHullFn (B) (g) : conj B (convHullFn g) = conj B g
theorem conj_convFn₂ (B) (f g) : conj B (convFn₂ f g) = conj B f ⊔ conj B g
```

The closure rows — layer C on **both** spaces, `[IsCompatiblePairing B] [IsCompatiblePairing B.flip]`,
inputs closed convex:

```lean
theorem conj_add_eq_clFn_infConv (hf : ConvexFn f) (hfc : ClosedFn f) (hg : ConvexFn g)
    (hgc : ClosedFn g) : conj B (f + g) = clFn (infConv (conj B f) (conj B g))    -- Thm 16.4
theorem conj_iSup_eq_clFn_convFn {f : ι → E → EReal} (hf : ∀ i, ConvexFn (f i))
    (hfc : ∀ i, ClosedFn (f i)) : conj B (⨆ i, f i) = clFn (convFn fun i => conj B (f i))
theorem conj_compLin_eq_clFn_mapLin [IsCompatiblePairing B'] [IsCompatiblePairing B.flip]
    (hA : IsAdjointPair B B' A A') (hg : ConvexFn g) (hgc : ClosedFn g) :         -- Thm 16.3
    conj B (compLin g A) = clFn (mapLin A' (conj B' g))
```

So each row has three forms: unconditional (here), with a closure (here), and exact under a
constraint qualification (`Exact.lean`). `Duality/Support.lean`'s `supportFn_add`,
`supportFn_convexHull`, `supportFn_iUnion` are the indicator instances and were proved directly
in §13.

### `Tdaf/Analysis/Convex/Subgradient/Defs.lean`

`subgradient`, `subgradientRel`, `normalCone`, `normalPointedCone`, `dirDeriv`, and §23.1–§23.7.
The full name table is in [`05-differential.md` §5.1](05-differential.md); the four names the rest
of the project reaches for are `mem_subgradient` (`Iff.rfl`), `mem_subgradient_iff_conj_eq`,
`mem_subgradient_iff_add_conj_le` (Theorem 23.5, unconditional — `y ∈ ∂f x ↔ f x + f* y ≤ ⟨x, y⟩`)
and `subgradient_indicatorFn` (carries `x ∈ C`).

### `Tdaf/Analysis/Convex/Subgradient/Calculus.lean`

Layer A throughout — no topology, because Theorem 23.5 does all the work:

```lean
theorem subgradient_add_subset (B) (f g) (x : E) :                                -- unconditional
    subgradient B f x + subgradient B g x ⊆ subgradient B (f + g) x
theorem IsExactSum.subgradient_add (h : IsExactSum B f g) (x : E) :               -- Thm 23.8
    subgradient B (f + g) x = subgradient B f x + subgradient B g x
theorem image_subgradient_subset (hA : IsAdjointPair B B' A A') (g) (x : E) :     -- unconditional
    A' '' subgradient B' g (A x) ⊆ subgradient B (compLin g A) x
theorem IsExactImage.subgradient_compLin {hA : IsAdjointPair B B' A A'}
    (h : IsExactImage B B' A A' hA g) (x : E) :                                   -- Thm 23.9
    subgradient B (compLin g A) x = A' '' subgradient B' g (A x)
theorem normalCone_add_subset (B) (C D : Set E) (x : E) :                         -- unconditional
    normalCone B C x + normalCone B D x ⊆ normalCone B (C ∩ D) x
theorem IsExactSum.normalCone_inter (h : IsExactSum B (indicatorFn C) (indicatorFn D))
    (hC : x ∈ C) (hD : x ∈ D) :                                                  -- Cor 23.8.1
    normalCone B (C ∩ D) x = normalCone B C x + normalCone B D x
```

The sum rule spends `IsExactSum`'s properness on `Tdaf.EReal.le_coe_of_add_le_coe_add`; the image
rule uses no properness at all. Theorem 23.10 is absent — it needs `PolyhedralFn` (§19), and it is
a nonemptiness statement rather than a calculus rule.

---

## 1a. House style

From the repository `README.md` ("Reviewing a formalization"):

* **Minimize duplication.** Before writing a lemma, check whether Mathlib or this project already
  has it.
* **Bundle *concepts*, not individual assumptions.** `Proper`, `ConvexFn`, `ClosedProperConvexFn`,
  `IsExactSum` are named mathematical concepts and are structures. A single side condition such as
  `∀ x, f x ≠ ⊥` is not a concept — repeat it inline rather than inventing a name for it. A
  *conjunction* of concepts qualifies when the book names it: "closed proper convex function" is
  Rockafellar's most repeated phrase and is `ClosedProperConvexFn`. Two of the three is not — leave
  `(hf : ConvexFn f) (hc : IsClosed (epi f))` inline.
* **A name must not resolve to the wrong statement.** The worst outcome is a name a reader will
  guess that exists and means something else. `epi_anti` is antitone, so it may not be `epi_mono`;
  `PosHomogeneous.map_zero_trichotomy` is `f 0 ∈ {0, ⊤, ⊥}` rather than Mathlib's universal
  `f 0 = 0`, so it may not be `map_zero` (the conditional equality is `map_zero_eq_zero`). Leaving
  the guessable name *unbound* is better than binding it to a near-miss.
* **Instantiate the Mathlib interfaces that emerge implicitly.** If a definition turns out to be a
  Galois connection, a closure operator, a cone, a module, a lattice — say so, eagerly, and get the
  machinery and the lemma names for free instead of hand-rolling them. `gc_ofEpi_epi` /
  `gi_ofEpi_epi` / `epiClosure` (`Operations/Epi.lean`) turn `subset_epi_iff_le_ofEpi` into a
  `GaloisInsertion` and identify `IsEpiLike` with closure-operator closedness;
  `PosHomogeneous.epiCone` (`Homogeneous.lean`) bundles the epigraph of a positively homogeneous
  convex function as a `ConvexCone ℝ (E × ℝ)`, which §13 and §14 want.
* Code should be idiomatic and pleasant to read, not merely correct.

---

## 2. Lean/Mathlib gotchas

Only what cost real time to find. Trivia that an error message explains on its own does not belong
here.

1. **Convex combinations do not project through `simp`.** `(a • (x,μ) + b • (y,ν)).2` is defeq to
   `a * μ + b * ν` but not syntactically equal, and `linarith` cannot see through it. Prefer
   `convexFn_of_epi_combo` / `ConvexFn.epi_combo`, which present the statement already projected,
   over unfolding `Convex` by hand. A *single* scaled or added pair is fine (`Prod.smul_fst`,
   `Prod.fst_add` are `@[simp]`); it is combinations that stall. For sets,
   `simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hF hμ hν ha.le hb.le hab` works. And
   `rintro ⟨y, ρ⟩ hp` beats `intro p hp; obtain ⟨y, ρ⟩ := p`, which leaves `hp` phrased with
   `(y, ρ).2` and defeats `exact_mod_cast`.

2. **Degenerate coefficients.** Almost every convexity proof needs the `a = 0` and `b = 0` cases
   separately (the interesting argument needs `0 < a` and `0 < b`). Use `combo_of_pos`; it
   discharges both degenerate branches by `simpa`.

3. **`EReal` has no `SMul ℝ EReal` instance.** Write `(a : EReal) * z`. `Tdaf.EReal.coe_mul_coe`
   converts `(a : EReal) * (r : EReal) = ((a * r : ℝ) : EReal)`.

4. **`open Pointwise` is needed by every file using `epi f + epi g`, `a • epi f` or set negation**,
   and its absence shows up as an instance-synthesis failure rather than a clear error.

5. **`nlinarith` often fails on `a * p + b * q < r` given `p < r`, `q < r`, `a + b = 1`.**
   Feed it the products explicitly:
   ```lean
   have h1 : a * p < a * r := mul_lt_mul_of_pos_left hp ha
   have h2 : b * q < b * r := mul_lt_mul_of_pos_left hq hb
   have h3 : a * r + b * r = r := by linear_combination r * hab
   linarith
   ```
   `linear_combination c * hab` is the reliable way to use `a + b = 1` in a nonlinear identity.

6. **Style linters that fail the build if ignored**: the file header must be
   ```
   /-
   Copyright (c) 2026 TDAF contributors. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: TDAF contributors
   -/
   ```
   `show` may not change the goal — use `change`. `push_neg` is deprecated in favour of `push Not`.
   `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq` — or just rely on definitional
   equality (`have hx' : f x < α := hx`). `if_pos`/`if_neg` are deprecated, and so are the
   replacements they suggest, `ite_cond_eq_true`/`ite_cond_eq_false`; the live names are
   `ite_eq_left_of_eq_true _ _ (eq_true h)` and `ite_eq_right_of_eq_false _ _ (eq_false h)`.

7. **Unused section variables are an error-level warning — and a useful signal.** Write
   ```lean
   omit [AddCommGroup E] [Module ℝ E] in
   ```
   immediately *before* the declaration, and before its docstring, not after. When the linter fires
   unexpectedly it is usually reporting that the result belongs in a weaker layer of D9: that is how
   the upper half of Corollary 8.5.2 was found to be layer A, and how the three
   transversal-thickening lemmas of `RelativeInterior.lean` were found not to need finite dimension.

8. **`⨅ _ : p, f` for a `Prop` `p`** is the decidability-free way to write `if p then f else ⊤`
   in a complete lattice; `iInf_pos` and `iInf_neg` are the defining equations. Same trick with
   `⨆ _ : p, f` for `… else ⊥`.

9. **Two `simp` loops, both real, and both about negation.** `simp [Tdaf.EReal.coe_mul_coe]` loops —
   it is the exact inverse of Mathlib's `EReal.coe_mul`, which is in the default simp set; use `rw`.
   And a simp set containing `← EReal.neg_lt_neg_iff` loops against `neg_neg`/`neg_bot`/`neg_top`.
   **This kills D2's "generate the concave API by `simp`-normalising through negation"** — each
   transfer is one or two hand-written lines. Underneath both: `EReal` negation does not distribute
   over addition (`-(⊥ + ⊤) = ⊤` but `(-⊥) + (-⊤) = ⊥`), and Mathlib's `EReal.neg_add` carries two
   hypotheses.

10. **`Mathlib.Analysis.Convex.Function` imports no topology at all.** `IsClosed`, `closure`,
    `ContinuousAdd` are unknown identifiers in a file whose Mathlib reach is only `Epigraph.lean`.
    Minimal pair: `Mathlib.Topology.Instances.Real.Lemmas` and
    `Mathlib.Topology.Order.DenselyOrdered`.

11. **`relaxedAutoImplicit = false` turns one missing import into a landslide** — a missing
    `TopologicalSpace` produced ~12 cascading errors with `sorry`-typed hypotheses. Only the first
    error is real.

12. **`PosMulMono EReal` lives in `Mathlib/Data/EReal/Inv.lean`**, not `Operations.lean`; and there
    is **no** `PosMulStrictMono EReal`, so `le_of_mul_le_mul_left` cannot reflect an order. Multiply
    through by `(a⁻¹ : EReal)` — that is what `Tdaf.EReal.coe_mul_le_coe_iff` packages.

13. **`Finset` induction.** `Finset.cons_induction` (cases `empty`/`cons`) needs no `DecidableEq`.
    `Finset.Nonempty.cons_induction` has **one** major premise: write
    `induction hs using Finset.Nonempty.cons_induction`, not `induction s, hs using …`. Both
    auto-revert hypotheses mentioning `s`, so `ih` is the full implication.

14. **`EReal` is a `def` over `WithBot (WithTop ℝ)`, not an `abbrev`, and is not a semiring.**
    `WithBot` big-operator lemmas do not transfer, and `Finset.mul_sum` and relatives do not apply.
    `EReal.coe_sum`, `coe_mul_ne_bot` and `forall_ne_top_of_sum_ne_top` fill that gap in
    `Tdaf/Order/EReal.lean`.

15. **`ConvexCone` is half-reusable.** `ConvexCone.convex` accepts an anonymous-constructor cone
    `⟨s, _, _⟩` whose coercion is `rfl`-equal to `s`, giving "closed under `+` and positive `•` ⇒
    convex" directly. The converse is **not** in Mathlib. There is no `IsCone` predicate on bare
    sets, only the bundled structure.

16. **`open Set` makes bare `restrict` ambiguous** with `Set.restrict`; write
    `Tdaf.ConvexAnalysis.restrict`.

17. **`EReal.rec` is usable as a definitional combinator**, not just an eliminator:
    `EReal.rec (⊥ : EReal) φ ⊤` defines a function by cases, with `rec_bot`/`rec_coe`/`rec_top`
    `@[simp]` and `rfl`. Write `_root_.EReal.rec` inside `namespace Tdaf.ConvexAnalysis`.

18. **Antitone Galois connections need the `OrderDual` dance**, and it is only half free.
    `GaloisConnection (fun F => toDual (ofEpi F)) (fun g => epi (ofDual g))` is `rfl`-easy from the
    adjunction lemma, and `ClosureOperator` / `GaloisInsertion` / injectivity all follow. But
    transporting `gc.u_iInf` / `gc.l_iSup` back through `toDual` does **not** `simp` away: the goal
    keeps `sSup (⇑toDual ⁻¹' range …)` against `fun x => sSup (range …)`. Prove `epi_iSup`-style
    lemmas directly (three lines) rather than fighting the dual.

19. **A `def` producing a structure whose fields mention section variables must live inside the
    section that binds them.** Appending a `ConvexCone ℝ (E × ℝ)` definition after `end Module`
    fails with `failed to synthesize AddCommMonoid (E × ℝ)`, not with a scoping error.

20. **`AddCommMonoid` on a type synonym: the `nsmul` default cannot fire.** `nsmulRecAuto` needs an
    `AddSemigroup` *instance*, which does not exist while the instance is being elaborated. Declare
    standalone `Add`/`Zero` instances first, then `nsmul := nsmulRec`, `nsmul_zero := fun _ => rfl`,
    `nsmul_succ := fun _ _ => rfl`. A failed instance then produces gotcha-11-style landslides
    through `rfl` (`Not a definitional equality` everywhere downstream); only the first error is
    real.

21. **`⋃ a > 0, a • s` silently elaborates `a : ℕ`** via `AddMonoid.toNatSMul`, giving a definition
    that is not the one you wrote. Symptom: an "unused section variable `[Module ℝ E]`" warning on a
    statement that visibly scales by a real. Always write `⋃ a > (0 : ℝ), …`.

22. **Infinite dimensions cost hypotheses, not generality — see design decision D0.** In the
    category of topological vector spaces the arrows are the *continuous* linear maps, so a
    discontinuous linear functional is not a morphism, and a subspace expected to behave like a
    finite-dimensional one must be assumed *closed*. Both are automatic in finite dimensions, which
    is why Rockafellar never writes them. When one of his statements fails here, restore one of
    those two hypotheses rather than abandon the generalisation: Theorem 7.4 needs `f` closed, the
    branch in `cl f` must be taken on `lscHull f`, Corollaries 11.5.2/11.7.3 need
    `closure C ≠ univ`, and §16/§30's adjoints need `A` continuous with the transpose as data.
    **Before transcribing an `ℝⁿ` statement quantifying over "proper", "`≠ ℝⁿ`" or "closed", test it
    against a discontinuous functional** — it is the standard witness for exactly this.

23. **`⊤ + ⊥ = ⊥`, so `a ≤ u + v` statements need checking at the improper values.** Fenchel's
    inequality `⟨x,y⟩ ≤ f x + f* y` is *false* for `f ≡ ⊤` (RHS `= ⊤ + ⊥ = ⊥`) and for `f` taking
    `⊥`. The unconditional content is `sub_le_conj : ⟨x,y⟩ - f x ≤ f* y`.

24. **`Tdaf.EReal.coe_sub_le_comm : (a:ℝ) - z ≤ w ↔ (a:ℝ) - w ≤ z` is unconditional** (all eight
    `⊥`/`⊤` combinations work, because `a` is finite). This one symmetry makes `conj_le_iff`, the
    conjugacy Galois connection and `biconj B f ≤ f` hypothesis-free. It is the `EReal` fact §12
    turns on. `add_iSup`/`iSup_add`/`iSup_sub` for `EReal`, long expected to carry every conjugacy
    proof, are **not needed for §12 at all**; §13 does need them, as `Tdaf.EReal.coe_mul_iSup` and
    friends.

25. **Do not reach for the weak topology.** The duality theorems hold in whatever topology `E`
    carries, provided its continuous dual is the `F` side of the pairing — that is
    `IsCompatiblePairing`, and it is trivial when `E` is paired with its own dual. `σ(E, F)` is one
    instance of it, the coarsest, never the mechanism. The general pairing exists so that `E` and
    `F` may differ (§30, §33). `WeakBilin B` is besides a type synonym, so `simp`/`rw` do not fire
    through it and pair literals in `WeakBilin B × ℝ` need manual ascription.

26. **`PointedCone`, not `ConvexCone`, is the bundling to reach for.** `PointedCone R E` is
    `Submodule {c // 0 ≤ c} E`, so it has a span (`PointedCone.hull`, renamed from `span`), and
    `PointedCone.lineal` already *is* `C ⊓ -C` with the "largest subspace inside" Galois connection.
    `ConvexCone` has no span at all. `lineal` needs `[LinearOrder R]`, so wrappers over `ℝ` must be
    `noncomputable` — and the error blames `Real.linearOrder`, which looks unrelated.

27. **`GaloisCoinsertion.liftCompleteLattice` computes by `rfl`** and keeps the ambient
    `PartialOrder` syntactically, so on a subtype the lifted order *is* `Subtype.partialOrder`. Use
    `abbrev`, not `def`, for the bundled subtype.

28. **Mathlib survey corrections.** `LinearMap.Nondegenerate` already is
    `SeparatingLeft ∧ SeparatingRight`; `LinearMap.IsAdjointPair` pairs a module with *itself*, so a
    four-space version must be written; there is no `ContinuousLinearMap.dualMap`, **but the thing
    it names does exist under another name** — `ContinuousLinearMap.precomp` in
    `Mathlib/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`, which is precomposition as a
    *continuous* linear map of duals and is definitionally what a hand-rolled `dualPrecomp` would
    be; `asymptoticCone` exists (`Mathlib/Topology/Algebra/AsymptoticCone.lean`) and is `0⁺(cl C)`,
    with `isBounded_iff_asymptoticCone_subset_singleton` giving Theorem 8.4 in three lines; the
    usable `{x | l x ≤ c}` form of `iInter_halfSpaces_eq` exists only in the `RCLike` namespace.
    Every one of these was first missed by grepping for a name instead of for the concept — which is
    the next entry.

29. **Search Mathlib *semantically* before concluding it lacks something.** Grepping for names
    misses whole files. `Mathlib/Analysis/LocallyConvex/WeakSpace.lean` holds the
    compatible-topology theorem (`Convex.toWeakSpace_closure`, `LinearMap.image_closure_of_convex`,
    `LinearEquiv.image_closure_of_convex`) and no declaration in it contains the word "compatible";
    `LinearMap.dualEmbedding_surjective` is the Weak Representation Theorem and says neither word.
    **Use <https://leansearch.net> (`POST /search`, body
    `{"query": ["…"], "num_results": 8}`), which matches informal descriptions, and only then
    grep.**

30. **Do not use `LinearMap.IsContPerfPair` for the pairing hypotheses.** The name is inviting and
    the trap is quiet. It demands *joint* continuity of `(x, y) ↦ B x y` (so `F` needs a topology),
    and *bijectivity* on both sides where we need surjectivity on one; and its only
    `topDualPairing` instance is
    `variable [FiniteDimensional 𝕜 E] [T2Space E]` — adopting it silently reimposes exactly the
    hypothesis D0 exists to avoid.

31. **Mathlib's own precedent for the pairing hypotheses is to leave them unbundled.**
    `LinearEquiv.image_closure_of_convex` carries
    `(he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))` and the `e.symm` twin —
    `IsCompatiblePairing`'s two fields in another notation — as plain hypotheses, with a docstring
    explaining the choice to phrase compatibility "in terms of linear maps between locally convex
    spaces, rather than creating two separate topologies on the same space". Our case differs only
    in scale (67 signatures, not 3), which is the argument for a class here and not there.

32. **`Rel` is now `SetRel α β := Set (α × β)`** (an `abbrev`, `Mathlib/Data/Rel.lean`), with
    `SetRel.inv`, `.dom`, `.cod`, `.image`, `.comp`. This is *the* bundling for a multivalued map,
    and it is what makes Corollary 23.5.1 read as `∂(f*) = (∂f)⁻¹` rather than as a `∀ x y`
    biconditional.

33. **Generalised field notation resolves against the *root* namespace only.** A declaration named
    `Convex.foo` in this project is `Tdaf.ConvexAnalysis.Convex.foo`, and `hC.foo` for
    `hC : Convex ℝ C` will not find it — it fails with "The environment does not contain
    `Function.foo`". Write `Convex.foo hC …`. The same reasoning is why `IsCompatiblePairing` is a
    prefix predicate rather than a `LinearMap` field: a downstream project should not squat in
    Mathlib's namespace just to buy dot notation, and `[IsCompatiblePairing B.flip]` reads better
    than the projection form anyway.

34. **Name clashes across the library are silent until they are not.** A duplicate reports as "has
    already been declared" at a line far from the real cause, with no hint where the other
    declaration lives. `grep -rn <name> Tdaf/` before naming. Worse, a *near*-duplicate does not
    report at all: `le_of_forall_le_coe` and `le_of_forall_coe_le` were the same statement written
    twice by two agents, and only a hand comparison caught it. The same hazard points outward:
    inside `namespace Tdaf.EReal` a local `EReal.foo` shadows a future Mathlib `EReal.foo`, and
    `EReal.sub_le_iff_le_add`, `le_sub_iff_add_le` and `sub_le_of_le_add` already exist upstream
    with *weaker* disjunctive hypotheses than the obvious hand-written versions.

35. **`intrinsicInterior` is defined through the subspace topology**, so `x ∈ ri s` unfolds inside
    `affineSpan ℝ s` with its own `AddTorsor` structure. Prove the ambient metric characterisation
    first and nothing else needs torsor transport. The stuck-instance error to expect is
    "typeclass instance problem is stuck: `AddTorsor ?V E`", triggered inside a `fun` or anonymous
    constructor where the expected type is not yet known.

36. **`class Foo (B) : Prop extends B.Bar where` parses, and dot notation works in `extends`.** The
    field of the extension may mention a definition that itself requires the parent instance —
    `surjective_eval (B) : Function.Surjective (evalCLM B)` elaborates off the parent. Ordering the
    file *base class → map → extension* is what makes this possible, and it is worth the trouble:
    stating the field through the map rather than through an inlined anonymous constructor is what
    let `exists_pairing_eq` be a `rw` instead of `rfl`-poking, and it means the map is available to
    downstream files instead of being re-defined there.

37. **`LinearMap.flip` is a plain `def`, so instance search will not unfold it.** With
    `[IsContinuousPairing B]` in context, `inferInstance` for `IsContinuousPairing B.flip.flip`
    **fails**, although `‹IsContinuousPairing B.flip.flip›` typechecks at that type — defeq holds at
    default transparency, not at instance transparency. One bridge instance fixes it for the whole
    library; check whether it is load-bearing by demoting it to a `theorem` and rebuilding.

38. **An instance binder does not pin implicit arguments the way a hypothesis did.** A hypothesis
    mentioning `B` determined `B` for free; `[IsCompatiblePairing B]` never does. Any lemma whose
    *conclusion* does not mention `B` now needs `(B := B)` at the call site, and the error is the
    less helpful "typeclass instance problem is stuck".

39. **Two hand-rolled `AffineSubspace` arguments have Mathlib names.** "A map constant on `s` is
    constant on `affineSpan ℝ s`" is `AffineMap.eqOn_affineSpan` (with `AffineMap.const` as the
    second map), and "… so its linear part vanishes on the direction" is
    `AffineMap.linear_eqOn_vectorSpan` composed with `direction_affineSpan`. Building the level-set
    `AffineSubspace` by hand costs ~25 lines and is what `exists_lt_of_notMem_relint` used to do.

40. **`EReal` is not a `SubNegMonoid`, so `sub_eq_add_neg` does not always fire — but `a - b` *is*
    `a + -b` by `rfl`.** `EReal`'s `Sub` instance is literally `⟨fun x y => x + -y⟩`, so a goal that
    `simp only [sub_eq_add_neg]` leaves as `a - b = a + -b` is closed by a bare `rfl`. The practical
    recipe for a sign-transfer proof is: rewrite the coercions, `simp only [sub_eq_add_neg]` to
    expose the sums, apply `EReal.neg_add` (whose two disjunctive side conditions are discharged by
    `.inl (EReal.coe_ne_bot _)` and `.inl (EReal.coe_ne_top _)` whenever the first summand is a real
    coercion), then `rfl`.

41. **`EReal.le_sub_iff_add_le {a b c} (hb : b ≠ ⊥ ∨ c ≠ ⊥) (ht : b ≠ ⊤ ∨ c ≠ ⊤) : a ≤ c - b ↔
    a + b ≤ c`** — note that `b` is the *subtrahend* and `c` the minuend, which is the opposite of
    the reading the argument names suggest. Feeding it `.inl` where `.inr` is wanted produces an
    "application type mismatch" naming a metavariable, not a helpful error.

42. **Sign transfer reverses the order but not the arithmetic.** `⊤ + ⊥ = ⊥` is not self-dual, so a
    convex statement of the form `a ≤ u + v` and its concave mirror `u + v ≤ a` need *different*
    hypotheses: the first collapses to `⊥` on its large side and needs properness, the second
    collapses on its small side and does not. Check each mirror rather than assuming D2's symmetry;
    `add_concaveConj_le` is the case where it bit.

43. **`forall_congr'` does not see through `≤` on a Pi type.** `f ≤ g` for `f g : E → EReal` is
    *definitionally* `∀ x, f x ≤ g x`, but it is not *syntactically* a `∀`, so
    `refine forall_congr' fun x => ?_` fails to unify against it. Rewrite with `Pi.le_def` first —
    once per side. Both halves of Thm 16.1 need this, since their proofs reduce
    `conj B f ≤ …` to a termwise comparison of affine minorants.

44. **`ring` handles `a⁻¹` as an atom, `field_simp` is only needed when `a * a⁻¹` must cancel.**
    `(t - c) / a = a⁻¹ * t - c / a` is a ring identity (both sides normalise to
    `t * a⁻¹ - c * a⁻¹`) and `ring` closes it with no side condition; `(a * t - c) / a = t - c / a`
    is *not*, and needs `field_simp` with `a ≠ 0` in context. The two appear side by side in
    `conj_smul` and `conj_smulRight` — reaching for `field_simp` in the first case leaves a goal
    `ring` would have closed outright.

45. **A sum of two conjugates cannot be proved by comparing affine minorants.** `conj_le_coe_iff`
    characterises `conj B f y ≤ (c : EReal)`, and with `Tdaf.EReal.eq_of_forall_le_coe_iff` that
    settles every identity whose right-hand side is a `conj`, a `⨆`, or a `⊔`. It says nothing
    about `conj B f y + conj B g y`, because `u + v ≤ c` is not a condition on `u` and `v`
    separately. `conj_infConv` therefore goes the other way — through `conj_ofEpi` and
    `Tdaf.EReal.biSup_add_biSup`, interchanging two suprema over the epigraphs. It is the only row
    of §16 that does.

46. **`add_le_add_left` adds on the *right*.** In current Mathlib
    `add_le_add_left : b ≤ c → ∀ (a), b + a ≤ c + a` (with `AddRightMono`) — the "left" names the
    side the *hypothesis's* operands sit on, not the side the constant is added to. Reaching for it
    to get `a + b ≤ a + c` produces a type mismatch that reads like an instance failure. Use
    `add_le_add le_rfl h`, which is unambiguous and works for `EReal` in both directions.

47. **It is `push Not`, not `push_not`.** The tactic that pushes negations inwards is spelled with
    a space and a capital `N` in this toolchain; `push_not` is an unknown identifier and the error
    does not suggest the right form. `Closure.lean` already used `push Not`; grep for it before
    reaching for `push_neg` (which exists but is about `¬ ∀`/`¬ ∃` in `Prop` only).

48. **`omit [Inst] in` goes *before* the docstring, not between it and the theorem.** A doc comment
    must be immediately followed by the declaration, so
    `/-- … -/ omit [FiniteDimensional ℝ E] in theorem …` is a parse error ("unexpected token
    'omit'"). The order is `omit … in`, then `/-- … -/`, then `theorem`. Also note the linter
    reports only the *first* offending declaration per build, so fixing one can reveal the next.

49. **Pointwise set addition beta-reduces in goals and breaks `rw [Prod.mk_add_mk]`.** Destructing
    a membership in `s + t` (`Set.image2`) leaves goals of the shape
    `(fun x1 x2 ↦ x1 + x2) (y₁, a) (y₂, b) = (y, μ)`, which no `+` lemma matches syntactically.
    `change ((y₁, a) : F × ℝ) + (y₂, b) = (y, μ)` first — the two are defeq — and then rewrite.
    `open Pointwise` is needed at all for `epi f + epi g` to elaborate.

50. **`Convex.foo` from this project is not reachable by dot notation.** Given `hC : Convex ℝ C`,
    `hC.isClosed_add …` fails: elaboration whnf's `Convex ℝ C` to a Pi type and looks for
    `Function.isClosed_add`. Write `Convex.isClosed_add hC …` — inside `namespace
    Tdaf.ConvexAnalysis` that resolves to the project lemma. Only declare a `_root_.Convex.*` name
    when the lemma is a pure Mathlib gap.

51. **Give a rewrite rule an explicit expected type when its implicit type argument is a subtype.**
    `rw [foo h] at k` elaborates `foo h` with the target type unknown, so a lemma
    `foo {E} [NormedAddCommGroup E] … {s : Set E} (h : … s …) : …` has to solve `?E` and `?s` by
    unification. When the answer is `↥V` for a `Submodule`, that unification *diverges* — a
    `maxHeartbeats 1000000` bump does not save it. Binding the instance first,
    `have h2 : ri (chart C x₀ V) = interior (chart C x₀ V) := foo h`, and then `rw [h2] at k`,
    elaborates instantly, because the expected type pins `?E` and `?s` before instance search
    starts. This cost an hour on `intrinsicInterior_eq_interior` in `Continuity.lean`.

52. **A subspace you will take `Set ↥V` over must be a variable, not a definition.** Defining
    `chartSpace C x₀ := Submodule.span ℝ ((· - x₀) '' C)` and then working in
    `Set ↥(chartSpace C x₀)` makes every instance query for `↥(chartSpace C x₀)` re-unfold the
    `span`, and rewriting in that type times out. Take `V : Submodule ℝ E` as a variable with
    `hV : V = Submodule.span ℝ …` as a hypothesis, and let the caller produce an opaque one with
    `obtain ⟨V, hV⟩ : ∃ V, V = … := ⟨_, rfl⟩`. Same proofs, no timeouts.

---

## 3. Build and verification

From the repository (or worktree) root:

```
lake build Tdaf.Analysis.Convex.<Module>     # builds one module and its dependencies
lake build                                   # builds everything reachable from Tdaf.lean
```

A module does **not** need to be listed in `Tdaf.lean` to be built by name.

Before declaring a module done:

- `lake build Tdaf.…<Module>` completes with no `error:` and no warnings other than deprecations;
- `grep -rn "sorry" <file>` finds nothing;
- `#print axioms <each main theorem>` reports only `propext`, `Classical.choice`, `Quot.sound`.
