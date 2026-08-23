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
`InfConvFn E` carrying `AddCommMonoid`, whose `nsmul` is n-fold infimal convolution. Also
`mem_epi_add_epi_of_le` — `epi f + epi g` is upward closed in the vertical coordinate, which is one
of the two halves of `IsEpiLike` and the reason Corollary 19.3.4 is short.

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

### `Tdaf/Analysis/Convex/RelativeInterior.lean`

All of §6 and the §7 results whose proofs need `ri`. Four additions worth knowing about:

* **Thm 6.7** — `Convex.relint_preimage` and `Convex.closure_preimage`, with the set identity
  `image_fst_inter_prod_univ` (`fst '' (graph A ∩ univ ×ˢ T) = A ⁻¹' T`). Rockafellar's proof
  transported verbatim: `A ⁻¹' C` is a projection of an intersection with the graph of `A`, so
  Corollary 6.5.1 and Theorem 6.6 do all the work. Theorem 9.5 is its main consumer, applied to
  `epi g`.
* **Cor 6.8.1 and Thm 6.9** — `Convex.relint_cone_prodMk_one`,
  `Convex.mem_relint_iff_mk_one_mem_relint_cone` (a point is in `ri C` iff `(1, x)` is in the
  relative interior of the cone generated by `{1} ×ˢ C`), `cone_prodMk_one_convexHull_union`
  (**Thm 3.8** for these cones) and `Convex.relint_convexHull_union` (**Thm 6.9**). All of them are
  stated about the explicit set `insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C}` rather than
  `PointedCone.hull ℝ ({1} ×ˢ C)`, so that this central file need not import
  `Recession/ConeHull.lean`; `coe_hull_prodMk_one` identifies the two. Theorem 6.9 is done for two
  sets, following the precedent Theorem 9.8 set — the step to `m` sets is a bare induction.
* **Thm 7.6 and Cor 7.6.1** — `ConvexFn.relint_setOf_le`, `.closure_setOf_le`,
  `.closure_setOf_lt_eq`, `.relint_setOf_lt_eq`, `.relint_setOf_lt`, `.closure_setOf_lt`,
  `.closure_setOf_le_clFn`, `.relint_setOf_le_of_relint_dom_eq`, `.closure_setOf_lt_of_closedFn`,
  on `ConvexFn.exists_mem_relint_dom_lt` (**Cor 7.3.1**) and `intrinsicInterior_Iic`.
  **No `AffineSubspace` machinery is needed.** Rockafellar intersects `epi f` with the horizontal
  hyperplane `{(x, α)}`; intersecting with the *slab* `univ ×ˢ Iic α` — a plain convex set — and
  then applying `Convex.relint_inter`, `Convex.relint_image` along `LinearMap.fst` and
  `intrinsicInterior_prod_eq` avoids Corollary 6.5.1 and the hyperplane construction entirely.
* **Thm 7.5, `ri` form** — `ConvexFn.tendsto_lscHull_along_segment_relint` and its `clFn`
  companion. `Closure.lean` has the layer-B form with `interior (epi f)`; this one uses Lemma 7.3
  and Theorem 6.1 instead of `Convex.combo_interior_closure_mem_interior`, and is Rockafellar's
  own statement. Theorem 9.3 is its main consumer.
* **Cor 7.3.3** — `ConvexFn.le_of_mem_closure`: a convex function bounded below by a real constant
  on a convex set on which it is finite keeps that bound on the closure. The proof runs the bound
  along the segment from a relative interior point (`Convex.segment_mem_relint`) and lets the
  parameter tend to `1`; the finiteness hypothesis is only used at the two endpoints, so it asks
  `∀ z ∈ D, f z ≠ ⊤` rather than properness. Theorem 21.1 is the reason it exists, and it is what
  moves that theorem's conclusion from `ri C` to `C`.
* **Cor 6.3.1, idempotence form** — `Convex.relint_relint` (`ri (ri C) = ri C`). It used to live in
  `Simplicial.lean`; §18's Theorem 18.2 needs it too, and it is a §6 fact, so it moved here.
* **Cor 6.4.1** — `Convex.mem_interior_iff_absorbs`: for a convex set in a finite-dimensional
  space, `z ∈ int C` iff `C` absorbs every direction from `z` (`∀ y, ∃ ε > 0, z + ε • y ∈ C`).
  Neither Mathlib nor this repository had it. Forwards is a ball argument; backwards derives
  `z ∈ C` and `affineSpan ℝ C = ⊤` (so `intrinsicInterior_eq_interior` applies) and then quotes
  Theorem 6.4. Theorem 14.2's bounded-level-set corollary is the consumer.

### `Tdaf/Analysis/Convex/Closure.lean`

`lscHull f := ofEpi (closure (epi f))` with `epi_lscHull` **unconditional**;
`clFn` (branching on `lscHull f`, `open Classical in`), `ClosedFn`;
`lowerSemicontinuous_iff_isClosed_epi` (**Thm 7.1**), `isGreatest_lscHull`, `closedFn_iff`,
`iInf_clFn_eq_iInf`, `ConvexFn.eq_bot_or_eq_top` (**Cor 7.2.1**);
`ClosedProperConvexFn` (the bundled `convex`/`closed`/`proper` triple, with `.isClosed_epi`,
`.lowerSemicontinuous` and the `of_isClosed_epi` constructor §8 uses);
`exists_affine_le_of_closed_proper` (**the Fenchel–Moreau keystone**),
`tendsto_lscHull_along_segment` (**Thm 7.5**), `lscHullClosure`/`clFnClosure` as `ClosureOperator`s.

**The liminf description** — `lscHull_eq_liminf` (`lscHull f x = liminf f (𝓝 x)`, *unconditional*),
`clFn_eq_liminf` (under `∀ z, lscHull f z ≠ ⊥`) and `clFn_eq_liminf_or`, the Corollary 7.2.1
dichotomy `clFn f x = liminf f (𝓝 x)` **or** (`clFn f x = ⊥` and `liminf f (𝓝 x) = ⊤`). Corollary
30.2.3 consumes the last of these, and Rockafellar's "except in cases where the left side is `-∞`
and the right `+∞`" is exactly its second branch — the exception is real, not an artefact of the
formalization. The section is split into `Liminf` (topology only) and `LiminfHull`/`LiminfConvex`
(which need `IsTopologicalAddGroup`, then `Module ℝ` and `ContinuousSMul`) because
`lowerSemicontinuous_lscHull` already lives behind those instances — gotcha 92.

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

`exists_chart_retraction` is the reusable packaging: it hands back `V` together with a *continuous
linear* `r : E →L[ℝ] V` such that `x ↦ r (x - x₀)` maps `ri C` into `interior (chart C x₀ V)` and
`x₀ + r (x - x₀) = x` there. Both Theorem 10.1 and Theorem 10.4 are three lines on top of it; a
bounded linear map transports Lipschitz constants exactly as it transports continuity.

**Cor 10.1.1** as `ConvexFn.continuous_of_dom_eq_univ` / `.continuous_toReal_of_dom_eq_univ`.

**Thm 10.4** as `ConvexOn.exists_lipschitzOnWith_of_isCompact` (the `interior` form, and the whole
analytic content: Rockafellar's `ε`-collar argument, which Mathlib has only for balls) and
`ConvexFn.exists_lipschitzOnWith_of_isCompact` (the `ri` form).

**Thm 10.5** as `ConvexFn.uniformContinuous_toReal_iff`, split into
`.exists_lipschitzWith_of_recessionFn_ne_top` (sufficiency, quantitative) and
`.recessionFn_ne_top_of_uniformContinuous` (necessity), with
`exists_recessionFn_le_of_forall_ne_top` — `f0⁺ y ≤ M ‖y‖` — as the piece that carries Rockafellar's
`α = sup {f0⁺ z | ‖z‖ = 1}`. **Cor 10.5.1** is `.exists_lipschitzWith_of_frequently_le`, whose
hypothesis `∃ᶠ a in atTop, f (a • y) ≤ c a` is Rockafellar's `liminf f(λy)/λ < ∞`; **Cor 10.5.2** is
`.exists_lipschitzWith_of_le_lipschitz`, stated for an arbitrary Lipschitz `g : E → ℝ` because the
proof never uses convexity of the dominating function. Service lemmas:
`coe_toReal_of_dom_eq_univ` and `ConvexFn.isClosed_epi_of_dom_eq_univ`.

### `Tdaf/Analysis/Convex/Simplicial.lean`

`IsSimplex` (convex hull of a finite affinely independent family) and `LocallySimplicial`
(Rockafellar's §10 definition), with `IsSimplex.isCompact`.

Weights: `weightPt v w = ∑ i, w i • v i`, `weightPt_eq_affineCombination`, `weightPt_combo` (the
weight map is affine), and `convexHull_range_eq_image_stdSimplex`.

**Thm 10.2** as `ConvexFn.upperSemicontinuousWithinAt_convexHull_range` (the analytic core, at
*every* point of a simplex — no triangulation, see gotcha 57),
`ConvexFn.upperSemicontinuousOn_of_locallySimplicial`, and
`ConvexFn.continuousOn_of_locallySimplicial` for the closed case. **Thm 10.3** as
`exists_closedFn_continuousOn_of_locallySimplicial` (existence, `g = clFn f`) and
`eqOn_of_continuousOn_of_eqOn_relint` (uniqueness, which is just `C ⊆ cl (ri C)`).

The whole of §10.2 is layer B plus `T2Space`: no metric, no finite dimension, no local convexity.
Only §10.3 is finite-dimensional, and only because Theorems 7.4 and 7.5 are.

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
(the last two need both factors nonempty). `zero_mem_linealitySpace`, and
`recessionCone_coe_pointedCone` / `recessionCone_closure_coe_pointedCone` — a pointed convex cone,
and the closure of one, is its own recession cone, which is what makes Corollary 9.1.3 an instance
of Corollary 9.1.1. `recessionCone_neg : 0⁺(-C) = -0⁺C` is what lets Corollary 20.3.1 read
Theorem 20.3's one-sided hypothesis off a difference of sets.

### `Tdaf/Analysis/Convex/Duality/Pairing.lean`

**A global instance lives here**: `instIsCompatiblePairingTopDualFinite`, i.e.
`IsCompatiblePairing (topDualPairing ℝ E)` for finite-dimensional `E` — the *flip* side of the
pre-existing `instIsCompatiblePairingTopDual`. It rests on `exists_forall_apply_eq`, reflexivity of
a finite-dimensional normed space in the form "every continuous functional on the dual is an
evaluation". Both started in `Tangent.lean` and were moved down so that `Subgradient/Gradient.lean`
could reach them without importing §18.

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

Since §33, this file also carries the **concave closure**:

```lean
noncomputable def clConcave (g : E → EReal) : E → EReal := fun x => -(clFn (fun z => -(g z)) x)
def ClosedConcaveFn (g : E → EReal) : Prop := clConcave g = g
@[simp] theorem neg_clConcave (g) (x) : -(clConcave g x) = clFn (fun z => -(g z)) x
theorem closedConcaveFn_iff : ClosedConcaveFn g ↔ ClosedFn (fun z => -(g z))
theorem le_clConcave (g) : g ≤ clConcave g          -- note the direction: closure *raises*
theorem closedConcaveFn_clConcave (g) : ClosedConcaveFn (clConcave g)
theorem concaveFn_clConcave (hg : ConcaveFn g) : ConcaveFn (clConcave g)
theorem biconcaveConj_eq_clConcave (hg : ConcaveFn g) : biconcaveConj B g = clConcave g
```

It lives here rather than in `Closure.lean` or a file of its own because this is the first module
with both `ConcaveFn` (from `Concave.lean`) and `clFn` (from `Closure.lean`) in scope. The three
sections it needs have different instance requirements — `clFn` wants only `[TopologicalSpace E]`,
`closedFn_clFn` adds `[AddCommGroup E] [IsTopologicalAddGroup E]`, and `convexFn_clFn` adds
`[Module ℝ E] [ContinuousSMul ℝ E]` — so they are three sections, not one.

### `Tdaf/Analysis/Convex/Duality/Exact.lean`

`IsExactSum B f g` (`proper_left`, `proper_right`, `exact_le`) and
`IsExactImage B B' A A' hA g` (`proper`, `exact_le`) — the D5 interfaces. Unconditional halves:
`conj_add_le_coe_add`, `epi_conj_add_epi_conj_subset`, `conj_add_le_infConv`,
`conj_add_le_add_conj` (this last one needs nonempty domains), `conj_compLin_le_mapLin`.
Consequences: `IsExactSum.{conj_left_ne_bot, conj_right_ne_bot, symm, proper_add,
infConv_le_conj_add, conj_add, conj_add_apply, exists_conj_add_eq}` and
`IsExactImage.{proper_compLin, mapLin_le_conj_compLin, conj_compLin, exists_conj_compLin_eq}`.
The `of_relint`/`of_polyhedral`/`of_continuousAt` sufficient conditions are **not** here — see D5;
`of_relint` is in `Duality/Relint.lean`, `of_continuousAt` in `Duality/Continuity.lean`.

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

### `Tdaf/Analysis/Convex/Duality/Continuity.lean`

The second producer of a D5 interface, and the one that survives into infinite dimensions.
`IsExactSum.of_continuousAt` — `f`, `g` proper convex, both finite at `x₀`, and `f` continuous at
`x₀` — is layer B: the only topological input is `geometric_hahn_banach_open`, which wants a
nonempty *open* convex set and no local convexity at all. Also `ConvexFn.convex_strictEpi`
(Theorem 4.2 as a statement about `{p : E × ℝ | f p.1 < p.2}`), which belongs to §4 but had no
consumer before.

The proof separates the strict epigraph of `f` from the *hypograph*
`{(x, μ) | g x ≤ ⟨x, y⟩ - a - μ}`, with `a = (f + g)* y`; those two sets are disjoint exactly when
the inequality to be proved holds. Three moves worth reusing: continuity gives `V ×ˢ Ioi r` inside
the strict epigraph and hence a nonempty interior;
`Convex.closure_interior_eq_closure_of_nonempty_interior` carries the strict estimate off the
interior onto the whole set; and `exists_unique_dual_prod` + `exists_pairing_eq` turn the separating
functional into the `y₁ : F` that `exact_le` asks for.

### `Tdaf/Analysis/Convex/Polyhedral/Cone.lean`

`PolyhedralCone K` (`∃ s : Finset (E →ₗ[ℝ] ℝ), K = {x | ∀ φ ∈ s, φ x ≤ 0}`) and
`FinitelyGeneratedCone K` (`∃ s : Finset E, K = ↑(PointedCone.hull ℝ ↑s)`), with `convex`,
`zero_mem`, `smul_mem` for both.

`halfSpaceConeₗ θ` is `Separation.lean`'s `halfSpaceCone` for a *linear* functional (Weyl's half
uses no topology), and `forall_nonpos_of_mem_hull` — a functional nonpositive on a set is
nonpositive on the cone it generates — is the workhorse, used once in `E` and once in its dual.

**Minkowski–Weyl** as `polyhedralCone_iff_finitelyGeneratedCone`, split into
`FinitelyGeneratedCone.polyhedralCone` (Weyl, algebraic, by induction over the generators from
`polyhedralCone_zero` through `PolyhedralCone.add_ray`) and
`PolyhedralCone.finitelyGeneratedCone` (Minkowski, by separation in the dual). `add_ray` is the
Fourier–Motzkin step. `PolyhedralCone.isClosed` and `FinitelyGeneratedCone.isClosed` follow.

### `Tdaf/Analysis/Convex/Polyhedral/Defs.lean`

`Polyhedral C` (`∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ), C = {x | ∀ q ∈ s, q.1 x ≤ q.2}`; the `⋂` form is
`Polyhedral.eq_biInter`) and `FinitelyGenerated C` (`∃ P D : Finset E,
C = convexHull ℝ ↑P + ↑(PointedCone.hull ℝ ↑D)` — needs `open scoped Pointwise`).

Homogenisation lives here: `liftAt a S` is the copy of `S` at height `a` in `ℝ × E`, `inrₙ` is the
height-zero lift as an `ℝ≥0`-linear map (built by hand — see gotcha 62), `coneOver C hC` is the
cone over a convex set, and the dictionary is
`slice_hull_union : {x | (1,x) ∈ cone (liftAt 1 P ∪ liftAt 0 D)} = convexHull ℝ P + cone D`,
proved from `coe_hull_liftZero` and `slice_hull_liftOne`.

**Thm 19.1** as `polyhedral_iff_finitelyGenerated`, from `Polyhedral.exists_polyhedralCone` (the
explicit homogenising cone) and `exists_liftOne_liftZero` (splitting a generating set into points
and directions) in one direction, and `Polyhedral.of_slice` in the other. **Cor 19.1.1** is
`polyhedral_convexHull_finset`; `Polyhedral.isClosed` and `FinitelyGenerated.isClosed` are part of
Cor 19.1.2.

### `Tdaf/Analysis/Convex/Caratheodory.lean`

§17: Theorems 17.1 and 17.2 with **Corollaries 17.1.1, 17.1.2, 17.1.3, 17.1.5 and 17.2.1**.

```lean
theorem exists_affineIndependent_of_mem_convexHull_iUnion …     -- Cor 17.1.1
theorem exists_linearIndepOn_of_mem_coneHull_iUnion …           -- Cor 17.1.2
theorem exists_affineIndependent_of_convFn_lt …
theorem convFn_apply_affineIndependent …                        -- Cor 17.1.3
theorem convHullFn_apply_fin …                                  -- Cor 17.1.5
```

**Corollaries 17.1.4 and 17.1.6 are false as Rockafellar states them, and are deliberately not
stated.** On `ℝ¹` take `f₁ y = -y` and `f₂ y = y`. Then `conv {f₁, f₂} ≡ -∞`, so the positively
homogeneous function it generates is `-∞` everywhere, while at `x = 1` every admissible
representation uses a single index and gives `-1` or `1`. The root cause is gotcha 114: an *affine*
dependency has coefficients summing to zero, so both signs occur and the elimination may pick the
one that lowers the cost; a *conical* dependency can have every coefficient of one sign, and then
Rockafellar's "minimal `α'` on the vertical line" simply does not exist. Presumably repairable by
assuming the generated function proper.

**Corollary 17.1.3 is the points half, not the directions half.** 17.1.1 and 17.1.3 are the
affine/points corollaries; 17.1.2 and 17.1.4 are the conical/directions ones. It is still the one
§21.3 consumes.

`sum_ite_lt` (a sum over `Fin N` cut off after `m` indices is a sum over `Fin m`) is the padding
lemma. **Thm 17.1** for points is `mem_convexHull_iff_exists_fin_finrank_succ`, which fixes the
index type at `Fin (finrank ℝ E + 1)`; that is what makes `IsCompact.isCompact_convexHull`
(**Cor 17.2.1**, a genuine Mathlib gap) and `Bornology.IsBounded.closure_convexHull` (**Thm 17.2**)
short.

**Carathéodory for cones** — `exists_linearIndepOn_of_mem_coneHull` — is the other Mathlib gap, and
the algebraic core of Theorem 17.1:

```lean
theorem exists_linearIndepOn_of_mem_coneHull {S : Set E} {x : E} (hx : x ∈ PointedCone.hull ℝ S) :
    ∃ (t : Finset E) (w : E → ℝ), ↑t ⊆ S ∧ (∀ y ∈ t, 0 < w y) ∧
      LinearIndepOn ℝ id (t : Set E) ∧ ∑ y ∈ t, w y • y = x
```

Layer A — no topology, no finite-dimensionality. The recursion (`exists_linearIndepOn_coneRepr_aux`,
private) is an induction on a cardinality *bound* rather than Mathlib's minimum-cardinality trick,
and the elimination step is Rockafellar's: normalise a dependency `∑ μ y • y = 0` so some
`μ y > 0`, subtract `min (w y / μ y)` times it, and keep `t.filter (0 < w' ·)` — which drops every
coefficient that vanished, not only the engineered one. `linearDepOn_iff` is what turns "not
linearly independent" into a `Finsupp` relation without any coe-sort gymnastics; stating the
conclusion as `LinearIndepOn ℝ id ↑t` is also what makes
`LinearIndependent.finset_card_le_finrank` apply verbatim.

**Thm 17.1 for points and directions** is `exists_of_mem_convexHull_add_coneHull`, proved in `ℝ × E`
against `liftPD P D = {1} × P ∪ {0} × D`. Splitting the Carathéodory subset by its first coordinate
gives the points and the directions simultaneously; the first coordinate of `∑ w q • q = (1, x)` is
the statement `∑ λ = 1`, and the bound `n + 1` is `finrank ℝ (ℝ × E)`. The homogenisation is
duplicated from `Polyhedral/Defs.lean`'s `liftAt`/`slice_hull_union` on purpose — §17 precedes §19
and must not import it.

**Corollaries 17.1.4 and 17.1.6 are not done, and are false as the book states them** — see
`04-representation.md`. 17.1.1, 17.1.2, 17.1.3 and 17.1.5 are done.

**Theorem 17.3 is here too**, and it is false as the book states it.

```lean
def inequalitySet (…) : Set (F × ℝ)                         -- the set `C` of Thm 17.3
theorem inequalitySet_subset_halfSpace_of_mem_coneHull …     -- sufficiency
theorem mem_coneHull_insert_of_subset_halfSpace …            -- necessity
theorem exists_card_le_finrank_of_mem_coneHull_insert …      -- the count, via Thm 17.1
theorem inequalitySet_subset_halfSpace_iff …                 -- Thm 17.3 in full
```

**Theorem 17.3 needs `0 ∉ S*`.** The book's proof asserts that the open half-space
`{(x*, μ*) | ⟨x̄, x*⟩ - μ* < 0}` contains `S*`, which fails outright at `(0, 0) ∈ S*`; and the theorem
itself fails then. The counterexample is written out in the doc comment of
`inequalitySet_subset_halfSpace_iff`: a spiral arc in `ℝ² × ℝ` accumulating at the origin along a
boundary ray, with the limiting unit direction omitted from the cone's unit slice, so the generated
cone is not closed and a half-space containing `C` admits no finite representation. Conversely the
book's hypothesis `x* ≠ 0` **is** unnecessary: the empty combination covers the zero functional, so
the `iff` holds for every pair.

`isClosed_coneHull_insert` (private) is Theorem 17.2 plus **Corollary 9.6.1**, which the project
already had as `isClosed_coe_hull_of_isBounded` in `Recession/ConeHull.lean` — an earlier note in
this file claimed otherwise.

**Relocation candidate**: `inequalitySet` and its API are the compact-infinite-system analogue of
`le_consequence_iff` (Theorem 22.3) and belong in `LinearInequalities.lean`. They cannot move as
things stand — `LinearInequalities.lean` imports `Helly.lean` and sits far above this file — so
this is a note for whoever restructures §17/§22. In the same direction:
`eq_zero_of_forall_pairing_eq_zero` (`LinearInequalities.lean`) is a two-line fact about a
compatible pairing with no §22 content and belongs in `Duality/Pairing.lean`; because it is
stranded high in the import graph its contrapositive had to be reproved here as the private
`exists_pairing_ne_zero`.

### `Tdaf/Analysis/Convex/Polyhedral/Ops.lean`

The polyhedral calculus. Layer A: `polyhedral_univ`, `polyhedral_halfSpace`, `Polyhedral.inter`,
`Polyhedral.comap`, `Polyhedral.comap_affine` — all proved on the inequality side, so no
finite-dimensionality. Layer D, through the generator side: `FinitelyGenerated.image`,
`FinitelyGenerated.add`, and then **Thm 19.3** as `Polyhedral.image` / `Polyhedral.add`, with
`.neg`, `.sub`, `.smul`. Plumbing: `toNNLinear` (an `ℝ`-linear map read over `ℝ≥0`),
`image_coe_hull`, `coe_hull_union`.

Also layer A: `PolyhedralCone.polyhedral` (a cone system is a system with zero right-hand sides)
and `Polyhedral.prod`; `polyhedral_zero` needs finite dimensions, through `polyhedralCone_zero`.

**Thm 19.5** as `recessionCone_polyhedral_system` — derived from `Recession/Cone.lean`'s
`recessionCone_setOf_forall_le` by turning the inequalities around, which is where the `neg`s in
its statement come from — and `Polyhedral.polyhedralCone_recessionCone`. **Cor 19.3.3** as
`separatesStrongly_of_polyhedral`, straight off Theorem 11.4, because `C - D` is polyhedral hence
already closed.

For §20: `polyhedral_singleton`, `polyhedral_coe_submodule` and `polyhedral_coe_affineSubspace`
(a subspace is the preimage of `{0}` under its own quotient map; an affine set is a translate of
its direction), `coe_hull_coe_submodule`, `FinitelyGeneratedCone.add` (`hull S + hull T =
hull (S ∪ T)`), and **Cor 19.7.1** as `finitelyGeneratedCone_hull_of_zero_mem` — the cone generated
by a polyhedral set containing the origin is generated by the *same* points and directions, with
`finitelyGeneratedCone_coe_submodule` as its subspace case. `coe_hull_of_convex_zero_mem` is the
lemma that makes any of that usable pointwise: for convex `S ∋ 0`, `hull S = ⋃_{t ≥ 0} t • S`, so a
property invariant under positive scaling transfers from `S` to the whole cone. Without it there is
no induction principle for `hull`, since `Submodule.span_induction`'s `add` case knows nothing about
the summands individually.

Three one-line lemmas read a finitely generated presentation `C = conv P + cone D` back off itself:
`coe_subset_of_finitelyGenerated` (`P ⊆ C`, since `0 ∈ cone D`),
`coe_hull_subset_recessionCone_of_finitelyGenerated` (`cone D ⊆ 0⁺C`, the easy half of Thm 19.5)
and `subset_coe_hull_of_finitelyGenerated` (`C ⊆ hull (P ∪ D)`). They were extracted from the middle
of Cor 19.7.1's proof and are what makes **Thms 19.6 and 19.7** short.

The last section of the file, `Generated`, holds those two. Both are conjunctions —
`FinitelyGenerated (closure …) ∧ closure … = …` — because the proof is a *three-set sandwich*
(`cl ⊆ A ⊆ repaired ⊆ cl`, with `A` the finitely generated set built from the pooled generators),
which establishes both halves in one circle; splitting them would mean proving the circle twice.
`recessionCone` enters through Theorem 8.3, `mem_recessionCone_of_exists_ray`: a single ray inside
the closure is enough, and that ray issues from a point of `Cᵢ`, which is why both statements insist
the sets are nonempty. Rockafellar's `⋃ {λ₁C₁ + λ₂C₂}`-with-`0⁺`-substituted description is not
formalised — `conv (C₁ ∪ C₂) + (0⁺C₁ + 0⁺C₂)` says the same thing without a convention.

### `Tdaf/Analysis/Convex/Polyhedral/Function.lean`

`PolyhedralFn f := Polyhedral (epi f)`, with `convexFn`, `isClosed_epi`, `lowerSemicontinuous`,
and `closedFn` (which needs `∀ x, f x ≠ ⊥`: `f ≡ ⊥` has epigraph `E × ℝ`, polyhedral by the empty
system, and `ClosedFn` has a `⊥` branch). `polyhedral_dom` and `polyhedral_sublevel` are the
calculus applied to the epigraph — a linear image and an affine preimage. `polyhedralFn_indicatorFn`
turns a polyhedral *set* into a polyhedral *function*, which is the bridge §20 will need.

**Thm 19.4** as `PolyhedralFn.add`, via the auxiliary linear maps `addEpiMap`
(`((x, α), (y, β)) ↦ (x, α + β)`) and `diagMap` (`((x, α), (y, β)) ↦ x - y`): the epigraph of the
sum is the image under the first of `(epi f ×ˢ epi g) ∩ diagMap ⁻¹' {0}`. It carries
`∀ x, f x ≠ ⊥` and the same for `g`, which is exactly what makes the `EReal` splitting
`f x + g x ≤ μ ↔ ∃ α β, f x ≤ α ∧ g x ≤ β ∧ α + β = μ` valid — the `⊤ + ⊥` case is the one that
would break it.

**Cor 19.3.4** as `PolyhedralFn.infConv`, with `epi_infConv_of_polyhedralFn` as the content:
`epi (f □ g) = epi f + epi g` needs `IsEpiLike (epi f + epi g)`, and polyhedrality gives the
closedness half for free while `mem_epi_add_epi_of_le` gives the other.

### `Tdaf/Analysis/Convex/Polyhedral/Conjugate.lean`

**Thm 19.2.** The functionals `epiFunctional B x = ⟨·, x⟩ - (vertical)`, `dirFunctional`,
`recFunctional` name the three linear forms on `F × ℝ` / `E × ℝ` that the system uses.
`mem_epi_conj_iff` is the whole idea: `q ∈ epi (conj B f)` iff `⟨p.1, q.1⟩ - q.2 ≤ p.2` for every
`p ∈ epi f`, i.e. iff a single linear functional is bounded on `epi f`. Feeding `epi f = conv P +
cone D` in gives one inequality per element of `P ∪ D`, so `epi (conj B f)` is cut out by a finite
system. `P = ∅` is the one case split: then `epi f = ∅`, `conj B f ≡ ⊥`, and the *empty* system
describes its epigraph. No properness hypothesis is needed — `EReal.lt_iff_exists_real_btwn` covers
the `⊥`/`⊤` values uniformly.

### `Tdaf/Analysis/Convex/Polyhedral/Duality.lean`

**Thm 20.1** as `IsExactSum.of_polyhedral`, with `of_polyhedral_pair` (both functions polyhedral,
so only `dom f ∩ dom g ≠ ∅` is asked) as the base case. `of_polyhedral_pair` is `of_relint`'s proof
with Corollary 9.1.1 replaced by polyhedrality: both proofs need only that `epi f* + epi g*` is
closed. `of_polyhedral` follows Rockafellar — put `δ = δ(· | aff (dom g))`, apply `of_relint` to
`δ + f` and `g`, the pair case to `δ` and `f`, and re-absorb `δ*` using `δ + g = g`
(`indicatorFn_add_eq_self`). The step he states in a clause is
`relint_inter_relint_nonempty_of_subset_affineSpan`: if `D₁ ⊆ aff D₂`, `x₀ ∈ D₁ ∩ ri D₂`, then
`ri D₁ ∩ ri D₂ ≠ ∅` — prolong the segment from a point of `ri D₁` *through* `x₀` to land in `D₂`
beyond `x₀`, then apply the line-segment principle on both sides with `s = min (t/2) 1`.

### `Tdaf/Analysis/Convex/Polyhedral/Separation.lean`

**Thm 20.2** as `exists_separates_not_subset_iff_disjoint_relint`, with
`disjoint_relint_of_separates_of_not_subset` (no polyhedrality) as the easy half. `levelSet f c` is
`{x | f x = c}` bundled as an `AffineSubspace`, used only through `affineSpan_le` to turn "constant
on `C₂`" into "constant on `aff C₂`". The proof is Rockafellar's, translated by hand rather than by
moving the origin: `K = hull (C₁ - x₀)`, `M₀ = (aff C₂).direction ⊓ ker f`, and `C₁' = K + ↑M₀` is
finitely generated, hence a polyhedral *cone*, so its representation has zero right-hand sides —
which is exactly why the cone hull cannot be replaced by `(C₁ - x₀) + ↑M₀`. The separating
functional is any `φ` in that representation with `φ w > 0` at a `w` of the translated `ri C₂'`
outside `C₁'`; `φ ≥ 0` on the rest of `C₂'` follows because `z - (f z / f w) • w ∈ M₀` and `φ`
vanishes on `M₀`. `ri C₂'` itself is never computed — the translated description
`{y | y + x₀ ∈ aff C₂ ∧ f (y + x₀) > c}` is all the argument uses.

**Cor 20.2.1** as `nonempty_inter_relint_iff_forall_supportFn`, on top of
`supportFn_le_neg_supportFn_neg_iff : δ*(y | s) ≤ -δ*(-y | t) ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ t, ⟨x₁,y⟩ ≤ ⟨x₂,y⟩`
(unconditional — an empty `s` sends the left side to `⊥`, an empty `t` the right side to `⊤`). Both
directions of the corollary go through Theorem 20.2 rewritten with
`Set.not_disjoint_iff_nonempty_inter`; the forward one builds the hyperplane at level
`(δ*(y | C₁)).toReal`, which is a *real* number precisely because the pointwise separation bounds
`δ*(y | C₁)` above by `⟨x₂, y⟩` for any `x₂ ∈ C₂`.

### `Tdaf/Analysis/Convex/Polyhedral/Closedness.lean`

**Thm 20.3** as `isClosed_add_of_polyhedral` and **Cor 20.3.1** as
`separatesStrongly_of_polyhedral_of_recession`. The constraint qualification
`nonempty_dom_supportFn_inter_relint` is Theorem 20.2 applied to the two *barrier* cones
`dom δ*(· | Cᵢ)`, with `polyhedral_dom_supportFn` (Thm 19.2 then Thm 19.1) making the first one
polyhedral and Corollary 14.2.1 turning a separating functional into a `v` with `v ∈ 0⁺C₁`,
`-v ∈ 0⁺C₂`, `v ∉ 0⁺C₂` — a counterexample to the hypothesis. Closedness is then read off effective
domains: `IsExactSum.of_polyhedral` gives `(δ*(·|C₁) + δ*(·|C₂))* = δ(·|C₁) □ δ(·|C₂)`, whose left
side is `δ(· | cl (C₁ + C₂))` (`conj_supportFn_of_convex`) and whose right side has domain
`C₁ + C₂` (`dom_infConv`). The infimal convolution is never evaluated.

### `Tdaf/Analysis/Convex/Polyhedral/Simplicial.lean`

**Thm 20.5** as `Polyhedral.locallySimplicial`, which is what discharges Theorem 10.2's hypothesis
for polyhedral sets, and **Thm 20.4** as `exists_polyhedral_between`. Both rest on
`exists_polyhedral_mem_nhds_subset_ball`: the coordinate cube `{y | ∀ i, |bᵢ*(y - x)| ≤ c}` of a
basis is polyhedral by inspection, bounded by `‖z‖ ≤ c ∑ ‖bᵢ‖`, and a neighbourhood because the
strict cube is a finite intersection of open sets. Rockafellar uses simplices; nothing in either
proof needs simplex-ness. `Polyhedral.exists_finset_convexHull` is Cor 19.1.2 — a bounded polyhedral
set is a polytope, since boundedness forces every generating direction to be `0` — and
`isSimplex_convexHull_coe` turns an affinely independent `Finset` into an `IsSimplex`. **Thm 20.4
is proved without convexity or nonemptiness of `C`**; only compactness is used, and the departure
from the book's statement is recorded in the file.

### `Tdaf/Analysis/Convex/Duality/Barrier.lean`

**Cor 14.2.1** as `polarCone_dom_supportFn : (dom δ*(· | C))° = 0⁺C` for nonempty closed convex `C`.
Rockafellar derives it from Theorem 14.2, which quantifies over recession *functions*; this proof
goes straight through Theorem 13.1 instead, so `Polar.lean`'s deferral of Theorems 14.2/14.3 stands.
`⊇` is "a linear function bounded above on a half-line has nonpositive slope"; `⊆` is
`mem_closure_convexHull_iff_le_supportFn`, since a recession direction leaves every inequality
`⟨·, y⟩ ≤ δ*(y | C)` intact.

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

**Cor 9.1.2** as `Convex.{isClosed_add_of_neg_notMem_recessionCone,
recessionCone_add_of_neg_notMem_recessionCone, isClosed_add_of_isBounded}`, through the bridge
`forall_mem_linealitySpace_of_neg_notMem`; **Cor 9.1.3** as `closure_add_coe_pointedCone`, through
`recessionCone_closure_coe_pointedCone` (`Recession/Cone.lean`).

The function half of §9 is three separate arguments:

* **Thm 9.3** — `ClosedProperConvexFn.add` (closed case), `recessionFn_add`, `lscHull_add` and
  `clFn_add` (the `ri` case), plus the two service lemmas `add_ne_bot` and `Proper.add`. The sum
  is the one case that is *not* an epigraph operation, so `lscHull_add` goes through Theorem 7.5:
  all three hulls at `y` are limits along one segment. `recessionFn_add` goes through Theorem
  8.5's difference quotients based at a common point, glued by
  `Tdaf.EReal.coe_mul_sub_add_coe_mul_sub`.
* **Thm 9.4** — `isClosed_epi_iSup`, `recessionFn_iSup`, `lscHull_iSup`. `epi (sup fᵢ) = ⋂ epi fᵢ`,
  so these are `epi_injective` on top of Corollary 8.3.3 and Theorem 6.5 respectively. The common
  relative interior point of the epigraphs comes from Lemma 7.3.
* **Thm 9.5** — `isClosed_epi_compLin`, `recessionFn_compLin`, `lscHull_compLin`, `clFn_compLin`,
  with `preimage_relint_epi_nonempty` transporting the hypothesis. `epi (g A)` is the preimage of
  `epi g` under `prodMapId A` (`Operations/Image.lean`), so these are `epi_injective` on top of
  Corollary 8.3.4 and Theorem 6.7.

Layers are *not* uniform across the section: the recession halves of 9.3, 9.4 and 9.5 and the
closed cases carry `omit [FiniteDimensional …]`, because only the `ri` halves call Theorem 6.5,
6.7 or 7.5.

### `Tdaf/Analysis/Convex/Recession/Conjugate.lean`

**Thm 13.3**: `recessionFn_conj_le_supportFn_dom` (unconditional half),
`supportFn_dom_le_recessionFn_conj` (needs `Proper f` and `Proper (conj B f)`), `recessionFn_conj`,
and `constancySpace_conj` — the form §9.2 and §16.3 actually consume. Layer A throughout:
properness of `f*` is a hypothesis, not derived.

**Thm 14.2 and Cor 14.2.2** are here too, in four layers.

```lean
theorem polarCone_coe_hull …                                 -- polars do not see the cone hull
theorem recessionConeFn_conj …            -- 0⁺(f*) = (dom f)°, no closedness anywhere
theorem recessionConeFn_conj_hull …
theorem recessionConeFn_eq_polarCone_dom_conj …               -- Thm 14.2, closed proper form
theorem polarCone_recessionConeFn …                          -- Thm 14.2, the bipolar half
theorem zero_mem_interior_iff_polarCone_eq_zero …
theorem isBounded_setOf_le_iff_zero_mem_interior_dom_conj …   -- Cor 14.2.2
```

**Half of Theorem 14.2 costs nothing.** `recessionConeFn_conj` is Theorem 13.3 read at the zero
level set — the recession cone of `f*` is the polar of `dom f` — and needs only properness of `f`
and of `f*`. It is the *other* direction that needs Fenchel–Moreau, and it is got by feeding
`f** = f` back into the first.

**`zero_mem_interior_iff_polarCone_eq_zero` is the dictionary Cor 14.2.2 runs on**, and its
nonemptiness hypothesis is not decorative: for `D = ∅` between two trivial spaces the polar is `{0}`
while the interior is empty. Both directions run on Corollary 6.4.1
(`Convex.mem_interior_iff_absorbs`, in `RelativeInterior.lean`) — forwards, absorbency makes every
value of the pairing vanish and the pairing separates points; backwards, the bipolar theorem turns a
trivial polar into "the cone generated by `D` is dense", Theorem 6.3 upgrades dense to everything,
and that is absorbency again.

**Corollary 13.3.4(a) is not here** — `zero_mem_closure_dom_conj_iff` is in `Duality/Level.lean`,
because it consumes `recessionFn_eq_supportFn_dom_conj`, which lives there for Corollary 13.3.1 and
cannot move down (`Level.lean` imports this file, not the other way round).

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

### `Tdaf/Analysis/Convex/Subgradient/Existence.lean`

**Theorems 23.4 and 23.10**, which are one theorem asked twice. `clFn_dirDeriv` (Thm 23.2) gives
`cl (f'(x; ·)) = δ*(· | ∂f x)` for free, so both reduce to *is `f'(x; ·)` closed?*, and the two
shared endings — `dirDeriv_eq_supportFn_of_closedFn` and
`subgradient_nonempty_of_closedFn_dirDeriv` — take that closedness as a hypothesis. Nonemptiness is
then one line: `δ*(· | ∅)` is the constant `⊥` and `f'(x; 0) = 0`.

Theorem 23.4 supplies the closedness through the effective domain:
`dom_dirDeriv_of_mem_relint_dom` identifies `dom (f'(x; ·))` with `(affineSpan ℝ (dom f)).direction`
— `⊆` because a finite difference quotient exhibits a point of `dom f`, `⊇` because
`mem_intrinsicInterior_iff` moves `x` a little in any direction of the affine hull — and then
Corollary 7.4.2 (`ConvexFn.closedFn_of_dom_eq_coe`) applies. Properness has to be argued, not
assumed: `f'(x; ·)` genuinely can be `−∞` somewhere (take `f y = -√y` on `[0, ∞)` at `x = 0`), and
what rules it out here is that a subspace is its own relative interior, so Theorem 7.2 would place
the `−∞` at the origin.

Theorem 23.10 supplies it through the epigraph: `epi (f'(x; ·))` is the convex cone generated by
`epi f − (x, f x)`, *provided that cone is closed*. Both inclusions are proved separately, because
only one of them needs the hypothesis — for `f y = y²` at `x = 0` the cone is the open upper half
plane plus the origin while the epigraph is the closed one. **Corollary 19.7.1** closes the cone in
the polyhedral case. `polyhedral_subgradient_of_polyhedralFn` then reads `∂f x` off as
`dom ((f'(x; ·))*)` using `conj_dirDeriv` and **Theorem 19.2**.

**Theorem 23.7 and Corollary 23.7.1 are here** — `subgradient_subset_normalCone_setOf_le` (the
easy half), `polarCone_subgradient` (Theorem 23.2 read as a polar),
`normalCone_setOf_le_eq_closure_coe_hull_subgradient` and
`normalCone_setOf_le_eq_coe_hull_subgradient`. `isClosed_normalCone` comes with them and belongs in
`Subgradient/Defs.lean`.

**Neither needs `f` closed, and neither needs properness as a separate hypothesis.** The book says
"proper convex"; properness follows from `∂f x ≠ ∅` through `proper_of_subgradient_nonempty`, so
what is actually assumed is `ConvexFn f`, `f x` finite, `⨅ f < f x` and `∂f x ≠ ∅`. That last one
*is* in the book ("`f` is subdifferentiable at `x`") and cannot be dropped — the `-√y` example in
the module docstring shows why.

**Corollary 23.7.1 deviates from the book's statement.** The book asks for `x ∈ int (dom f)`; the
version here asks for `Bornology.IsBounded (∂f x)`, which is what `isClosed_coe_hull_of_isBounded`
consumes. `bddAbove_subgradient_iff_mem_interior_dom` gives only the *pairing* form of boundedness
("every `⟨v, ·⟩` is bounded above"); upgrading that to `Bornology.IsBounded` in `F` is a separate
finite-dimensional lemma that does not exist yet.

### `Tdaf/Analysis/Convex/Subgradient/Approx.lean`

§23's ε-subgradients and **Theorem 23.6**.

```lean
def epsSubgradient (B) (ε : ℝ) (f : E → EReal) (x : E) : Set F
def shiftFn (f : E → EReal) (x : E) : E → EReal          -- `h(y) = f (x + y) - f x`
theorem epsSubgradient_eq_supportSet … ; theorem epsSubgradient_eq_setOf_conj_le …
theorem convex_epsSubgradient … ; theorem isClosed_epsSubgradient …
theorem iInter_epsSubgradient …                        -- `⋂ ε > 0, ∂_ε f x = ∂f x`
theorem closedFn_posHomGen_shiftFn …                    -- Thm 9.7 applied to `h + ε`
theorem supportFn_epsSubgradient …                      -- Thm 13.5 applied to `h + ε`
theorem dirDeriv_eq_iInf_supportFn_epsSubgradient …     -- **Thm 23.6**
```

The conjugate-side reading of the ε-subdifferential that §23's discussion gives before Theorem 23.6
falls out as `epsSubgradient_eq_setOf_conj_le`, so no separate development is needed.

**Relocation candidates.** Six `EReal` service lemmas belong in `Tdaf/Order/EReal.lean`:
`iInf_add_pos_coe`, `le_of_forall_pos_le_add`, `coe_le_add_coe_iff`, `coe_add_le_add_coe_iff`,
`coe_mul_eq_div_coe_inv`, `iInf_add_sub_pos_coe`. `posHomGen_mono`, `posHomGen_le_iInf_coe_mul`,
`iInf_coe_mul_eq_iInf_div` and `posHomGen_apply_eq_iInf_div` belong in `Recession/ConeHull.lean`
or `Duality/Level.lean`.

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

### `Tdaf/Analysis/Convex/Subgradient/Monotone.lean`

§24's characterisation of subdifferentials: **Theorems 24.4 and 24.8**, and the half of
**Theorem 24.9** that follows from 24.8.

```lean
def chainVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : E × F → List (E × F) → E → ℝ
  | s, [], x => B (x - s.1) s.2
  | s, q :: l, x => B (q.1 - s.1) s.2 + chainVal B q l x

def IsCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ s ∈ ρ, ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → chainVal B s l s.1 ≤ 0
```

**Cycles are lists.** Rockafellar's cycle `(x₀,y₀), …, (x_m,y_m)` is a starting pair plus a
`List (E × F)`, and the free endpoint comes *last* in `chainVal`. Three consequences, and they are
the whole file:

* `exists_chainVal_eq : ∃ y c, ∀ x, chainVal B s l x = B x y - c` — a chain is affine in its free
  endpoint, so `cyclicPotential` is a supremum of `affineFn`s and is closed convex by Theorem 5.5
  and `closedFn_affineFn`.
* `chainVal_append_singleton : chainVal B s (l ++ [q]) z = chainVal B s l q.1 + B (z - q.1) q.2` —
  adding the last edge, which is the whole content of `ρ ⊆ ∂(cyclicPotential …)`.
* `chainVal B s l s.1 ≤ 0` is "come back to where you started", so the cycle condition needs no
  index arithmetic.

**Necessity is stated additively.** `le_of_chain_mem_subgradientRel : f s.1 + chainVal B s l x ≤ f x`
rather than `chainVal ≤ f x - f s.1`, which keeps `EReal` subtraction out of the induction
entirely. Properness is used exactly once, at the end, to know `f` is finite at the base point.

**`cyclicPotential B ρ s`** is Rockafellar's `f`. `cyclicPotential_eq_zero` is the only place cyclic
monotonicity is used, and it is what makes the function proper; `cyclicPotential_ne_bot` is the
empty chain.

**Theorem 24.4 asks for a jointly continuous pairing.** `IsContinuousPairing B` gives `⟨·, y⟩`
continuous for fixed `y`, which is not enough when both arguments move, so `isClosed_subgradientRel`
takes `Continuous fun p : E × F => B p.1 p.2` explicitly (automatic in `ℝⁿ`). The proof writes the
graph as `⋂ z, {p | f p.1 + ⟨z - p.1, p.2⟩ ≤ f z}` and each slice, where `f z` is finite, as a
preimage of `epi f`.

**Not done**: Thms 24.1–24.3 (one-dimensional: `f'₊`, `f'₋`, complete nondecreasing curves — §23
gives `dirDeriv` but no one-sided derivatives on `ℝ`), Thms 24.5–24.7 (they rest on Thms 10.6–10.9,
deferred), and the maximality half of Thm 24.9 (needs `∂f ⊆ ∂g → g = f + const`, which runs through
Thm 23.4, Thm 23.2 and the one-dimensional material of 24.1–24.3). Corollary 31.5.2 — `∂f` is
maximal *monotone* — is a different, easier statement and does not wait on any of this.

### `Tdaf/Analysis/Convex/Subgradient/Gradient.lean`

§25's differentiability theory: **Theorem 25.1** in full, **Corollary 25.1.1**, and the necessity
half of **Theorem 25.2**.

**Differentiability of an `EReal`-valued function is a local real representative.** `HasFDerivAt`
needs a normed target, so every Fréchet statement in the file carries

```lean
(hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x)
```

with `f : E → EReal`, `g : E → ℝ` and `f' : E →L[ℝ] ℝ` — Rockafellar's own hypothesis, since his
`∇f x` presupposes `f x` finite. Do **not** restate the file for `f : E → ℝ`: §26's functions are
`+∞` off an open set. Two immediate consequences are **Corollary 25.1.1**:
`mem_interior_dom_of_eventuallyEq_coe` (`mem_interior_iff_mem_nhds` applied to `hfg`; needs neither
convexity nor differentiability) and `proper_of_eventuallyEq_coe` (`ConvexFn.eq_bot_of_lt_one` along
`[u, x)` against local finiteness at the limit — the piece of Thm 7.2 that §25 needs, valid in any
topological vector space).

**One calculus lemma serves the whole file.** `tendsto_slope_ray_of_hasFDerivAt` gives
`(g (x + t • v) - g x) / t → f' v` along `𝓝[>] 0`; `tendsto_ray_nhdsGT` transports `hfg` onto that
filter. Everything else is filter bookkeeping:

* `le_of_hasFDerivAt` (the gradient inequality) bounds the quotient above by `f z - f x` using
  `ConvexFn.epi_combo` on `Ioc 0 1`;
* `eq_of_mem_subgradient_of_hasFDerivAt` bounds it below by `⟨v, y⟩` and applies that to `v` and
  `-v`. **It uses neither convexity nor properness.**

**`dirDeriv_eq_of_hasFDerivAt` is Theorem 25.2's necessity half**, done directly on the defining
infimum: `EReal.coe_le_sub_div_iff` for the lower bound, and `EReal.lt_iff_exists_real_btwn` plus
`EReal.sub_div_le_coe_iff` for the upper one, so no `EReal` division is ever computed. Sufficiency
proper (linear `f'(x; ·)` ⇒ Fréchet differentiable) is **not** done and is not a transcription: it
is Gâteaux ⇒ Fréchet, which needs `[FiniteDimensional ℝ E]` and compactness of the unit sphere.
What sufficiency gets used for is available algebraically as
`subgradient_eq_singleton_of_dirDeriv_eq`, over an arbitrary pairing with `Function.Injective B.flip`.

**`HasGradientAt f f' x` packages the hypothesis pair.** It is `∃ g : E → ℝ, f =ᶠ[𝓝 x] (g · : EReal)
∧ HasFDerivAt g f' x`, with `DifferentiableAtFn f x := ∃ f', HasGradientAt f f' x`. Use the dot
lemmas — `.le`, `.subgradient_eq`, `.mem_subgradient`, `.dirDeriv_eq`, `.mem_interior_dom`,
`.proper`, `.unique`, `.exists_coe` — rather than the `_of_hasFDerivAt` workhorses; §26 is written
entirely against them. `.unique` is `HasFDerivAt.unique` on the representatives and needs no
convexity.

**Cors 25.1.2 and 25.1.3 are done in their subgradient form** — `mem_exposedPoints_epi_conj_iff`
and `mem_exposedPoints_supportSet_iff`, with `mem_exposedPoints_prod_Ici_iff` and
`Proper.eq_sub_of_mem_subgradient` (Thm 23.5 (d) solved for `f x`) as the two supporting facts.
**They need no §18 at all**: the proof is a direct supporting-hyperplane argument on `epi f*` —
split the functional, show the vertical coefficient is negative, normalise — plus Theorem 23.5.
They do need `f` (resp. `g`) **closed**, which the book does not assume: Rockafellar writes "we can
assume `f` is closed" because `(cl f)* = f*` and the gradients agree, and the subgradient form has
only *half* of that reduction for free (`clFn_eq_of_mem_subgradient` gives
`∂f x ≠ ∅ ⇒ ∂f x = ∂(cl f) x`; the other half needs "a singleton subdifferential forces
relative-interiority", which the project does not have). Cor 25.1.3's "non-empty closed convex set
`C`" is unnecessary — `C` is `supportSet B.flip g`, automatically closed and convex, and emptiness
is harmless.

**Not done**: Thms 25.3–25.7 (25.3 rests on Thm 24.1; 25.4 on Thm 24.5; 25.5 is Rademacher plus
Thm 24.4; 25.6 and 25.7 rest on 25.5 and Thms 10.6–10.9), and the *differentiability* reading of
Cors 25.1.2–25.1.3 — "the exposed points of `epi f*` are the `(x*, f*(x*))` with `f` differentiable
at some `x` and `∇f x = x*`". The geometry gives `∂f x = {x*}`; upgrading that to differentiability
is exactly **the converse half of Theorem 25.1**. The route, worked out but not started: (a) `∂f x`
a singleton ⇒ the normal cone of `dom f` at `x` is trivial ⇒ `x ∈ int (dom f)`, a
separation/normal-cone argument; (b) hence `f'(x; ·)` is finite everywhere, so convex, continuous
and closed, which removes the closure subtlety in Rockafellar's proof and lets
`clFn_dirDeriv_eq_of_subgradient_eq_singleton` (Thm 23.2) give `f'(x; ·)` linear *everywhere*;
(c) a compactness step on the unit sphere — cheaper than the book's polytope-covering-the-ball
argument: for each `u` on the sphere pick a parameter making the difference quotient small, use
continuity near `u`, take a finite subcover, and use monotonicity of the quotient.

**Relocation candidates**: `mem_exposedPoints_prod_Ici_iff` is a general fact about exposed points
of a half-cylinder and belongs beside `epi_indicatorFn` in `Indicator.lean` or in a general
exposed-points module; `Proper.eq_sub_of_mem_subgradient` belongs in `Subgradient/Defs.lean` with
the rest of Theorem 23.5.

### `Tdaf/Analysis/Convex/Subgradient/Legendre.lean`

§26's Legendre transformation, reduced to what is reachable: **Theorem 26.4**.

**§26 is not self-contained**, contrary to sub-plan 5's guess. Theorem 26.1 needs Theorem 25.6 in
one direction and the sufficiency half of Theorem 25.2 in the other; Theorems 26.3, 26.5, 26.6 and
Corollaries 26.3.1–26.3.3 and 26.4.1 all route through 26.1. Theorem 26.4 needs only Theorem 25.1
and Theorem 23.5 (d), so it is here in full:

```lean
theorem HasGradientAt.add_conj_eq (hf : ConvexFn f) (h : HasGradientAt f y x) :
    f x + conj (topDualPairing ℝ E).flip f y = ((y x : ℝ) : EReal)
```

`conj_eq_of_hasGradientAt` turns this into `f* (∇f x) = ⟨x, ∇f x⟩ - f x`, which *is* Rockafellar's
"`g` is the restriction of `f*` to `D`"; `sub_eq_sub_of_hasGradientAt` is his remark that `∇f` need
not be one-to-one for `g` to be single-valued; `legendreDom_subset_dom_conj` is `D ⊆ dom f*`.

**Two things are deliberately *not* defined.** `EssentiallySmooth`, `EssentiallyStrictlyConvex` and
`LegendreType` have no provable theorem until 26.1 is reachable, and an untestable definition is
exactly what cost §18 a rewrite (`IsExtreme` is not Rockafellar's face). And `legendreConj` itself
would need a choice function for `(∇f)⁻¹` and would then have to be proved equal to `conj B f` on
`D` — `conj_eq_of_hasGradientAt` states that equality without the detour.

The file's one private helper, `eq_coe_of_coe_add_eq_coe`, solves `(r : EReal) + c = (s : EReal)`
for `c`; the two infinities are excluded by the equation itself. Promote it to `Tdaf/Order/EReal.lean`
if a second consumer appears.

### `Tdaf/Analysis/Convex/Optimization/Fenchel.lean`

§31: **Theorem 31.1** (both of Rockafellar's conditions), **Theorem 31.2**, and **Theorem 31.3**
with **Corollary 31.3.1**, for a general linear map `A`.

**Theorem 31.2 does not need the `EReal` splitting lemma the plan said it did.**
`06-optimization.md` recorded the blocker as "an `EReal` lemma splitting `⨅ (a,b) (u a + v b)` into
`⨅ u + ⨅ v`". Going through the *concave* face of Theorem 16.3 instead — `concaveConj_compLin` —
turns the dual value at `y` into a supremum over the fibre `A'⁻¹{y}`, and the only arithmetic left
is `(⨆ i, u i) - c = ⨆ i, (u i - c)` for `c ≠ ⊥`, which `IsExactSum.conj_left_ne_bot` supplies.

**Theorem 31.3 consumes nothing from Theorem 31.2.** The general-`A` form
`sub_comp_eq_concaveConj_sub_conj_iff` needs only the `IsAdjointPair` datum, to identify
`⟨A x, z⟩'` with `⟨x, A' z⟩`; it is Corollary 31.3.1's attainment clause alone
(`iInf_sub_comp_eq_iff_exists_kuhnTucker`) that calls `exists_concaveConj_sub_conj_comp_eq`, and
hence Theorem 31.2. That corollary also needs `Proper (-g)` on all of `G`, which
`IsExactSum.proper_right` does **not** give — it gives properness of `-(g ∘ A)` — so the
`IsExactImage` hypothesis is load-bearing for more than attainment.

**The hypothesis is `IsExactSum B f (-g)`, never a constraint qualification.** Rockafellar's (a),
his (b), and their two polyhedral weakenings are four sufficient conditions for the same thing;
supply the instance from `Duality/Relint.lean` (Thm 16.4) or `Polyhedral/Duality.lean` (Thm 20.1).

**No separation.** Theorem 31.1 is `conj_zero_eq_neg_iInf` (Thm 27.1(a)) at `h = f + (-g)`, then
`IsExactSum.conj_add_apply` at `0`, then `neg_concaveConj` to turn `(-g)*(-y)` into `-g*(y)`. The
reindexing `y' ↦ -y'` under the infimum is the private `iInf_neg_comp`.

**Weak duality is unconditional.** `concaveConj_sub_conj_le_sub` takes no hypotheses: when
`f x = ⊥` the conjugate `f* y` is `⊤` and the dual value collapses to `⊥`, and when `g x = ⊤` the
concave conjugate `g* y` is `⊥` and it collapses again. Do not add properness hypotheses back.

**Two `∞ - ∞` helpers, not one.** `-(a - b) = b - a` needs *either* (`a ≠ ⊥` and `b ≠ ⊤`) *or*
(`a ≠ ⊤` and `b ≠ ⊥`), because `EReal.neg_sub` asks for two disjunctions and each pair discharges
them through different disjuncts. Both are private in the file (`neg_sub_comm`, `neg_sub_comm'`);
promote them to `Tdaf/Order/EReal.lean` if a third caller appears.

**A closed proper concave `g` is spelled `ClosedProperConvexFn fun x => -(g x)`.** That is the sign
dictionary applied to the bundled interface, and it saves §31 from defining a concave twin of
`ClosedProperConvexFn`. `concaveFn_iff_convexFn_neg` and `domConcave_eq_dom_neg` are the two
projections needed.

**The concave subgradient is `-∂(-g)`, and that is why §31 does not define one.** Rockafellar's
Kuhn–Tucker condition `x ∈ ∂g*(y)` is `-y ∈ subgradient B (fun z => -(g z)) x` here, and
`neg_mem_subgradient_neg_iff_add_concaveConj_eq` turns it into `g x + g*(y) = ⟨x, y⟩`. If a
superdifferential ever gets defined, define it as `-∂(-g)` and keep this lemma as the bridge.

**The `EReal` finiteness bookkeeping is a case bash, deliberately.** `finite_of_sub_eq`,
`finite_of_add_eq` and `finite_of_add_eq'` are proved by
`induction a <;> induction b <;> … <;> simp_all`. Keep `simp_all` *terminal* in those lemmas: the
`flexible` linter fires if anything modifies a goal after it, which is why the arithmetic core
`sub_eq_sub_iff_of_le` reduces to reals via `EReal.exists_coe_of_ne_bot_of_lt_top` and finishes
with `linarith` instead of continuing the bash.

**Theorem 31.4 lives here too, and it does not use Theorem 31.1.** `g = -δ(· | K)` is a concave
function, but `-g = δ(· | K)` is an ordinary convex one, so the section goes straight to Theorem
27.1(a) on `f + δ(· | K)` plus `IsExactSum.conj_add_apply` at the origin plus
`conj_indicatorFn_eq_indicatorFn_polarCone`.

**Rockafellar's `K*` is `-(polarCone B K)`, with `Set` negation.** `Set.neg` is a *preimage*, so
`y ∈ -K°` unfolds to `-y ∈ K°`; `mem_neg_polarCone` states the useful form `∀ z ∈ K, 0 ≤ B z y`,
and `indicatorFn_neg_set` moves the negation onto the indicator's argument. Write `-(polarCone B K)`
with the parentheses: bare `-polarCone B K` makes the elaborator try to auto-bind `polarCone`.

**`IsExactSum.conj_add_apply y` splits as `conj B f (y - w) + conj B g w`, not the other way
round.** The variable that survives is attached to the *second* summand. That is why both the
Theorem 31.1 proof and the Theorem 31.4 proof reindex by `y ↦ -y` (`iInf_neg_comp`) — and the
reindexing is not bookkeeping, it is exactly the step that converts `K°` into `K*`.

**`a • K` for `K : Set E` needs `open Pointwise`.** The cone hypothesis
`∀ a : ℝ, 0 < a → a • K = K` fails to elaborate without it, with a
`failed to synthesize HSMul ℝ (Set E)` error that does not mention the missing `open`.

**Not done**: Thm 31.2 and Cors 31.2.1, 31.4.1. Thm 31.2 is stated for bifunctions and waits on
§§29–30; Cor 31.2.1 (a linear map interposed) needs `conj (f ∘ A)` as an image, the sup-analogue of
`mapLin`; Cor 31.4.1 is Thm 31.4 for the non-negative orthant of a coordinate space and belongs to
the surface layer.

### `Tdaf/Analysis/Convex/Optimization/Moreau.lean`

§31's Theorem 31.5, minus its existence-and-uniqueness half.

**The real inner product notation is `⟪x, y⟫`, not `⟪x, y⟫_ℝ`.** The `_ℝ`-suffixed form is a
*local* notation inside Mathlib's `InnerProductSpace/Basic.lean`; the scoped notation exported by
`open RealInnerProductSpace` has no suffix. Writing `⟪x, y⟫_ℝ` gives the unhelpful
`unexpected identifier; expected ':=' or '|'`.

**`innerₗ E x y` is the pairing; `innerₗ_apply_apply` is the bridge.** Everything bilinear —
`⟪u - z, y⟫ = ⟪u, y⟫ - ⟪z, y⟫`, `⟪z, -y⟫ = -⟪z, y⟫` — is cheapest as
`rw [← innerₗ_apply_apply, …, map_sub, LinearMap.sub_apply]` rather than by hunting for the
`real_inner_*` lemma with the right shape.

**`w` is `fun z => ((‖z‖ ^ 2 / 2 : ℝ) : EReal)`, and `E` is explicit in `quadFn E`.** Most of the
elementary lemmas about it use only `[NormedAddCommGroup E]`, so they need
`omit [InnerProductSpace ℝ E] in` — and the `omit` line must come *before* the doc-comment, not
between it and the `theorem`.

**Both self-conjugacy proofs are `le_antisymm` with a `linarith`/`nlinarith` defect.** For
`conj_quadFn` the defect is `½‖x - y‖²`; for `conj_quadFn_sub` it is `½‖(x - z) - y‖²`. Feed
`norm_sub_sq_real` and `sq_nonneg` of the right vector; and note that `‖z - x‖ = ‖x - z‖` is not
enough — `nlinarith` needs the *squared* form `‖z - x‖ ^ 2 = ‖x - z‖ ^ 2`, after which plain
`linarith` closes it.

**One `rw [quadFn_apply]` covers both sides when the arguments coincide.** `rw` rewrites every
occurrence of the instance it matched first, so listing `quadFn_apply` twice fails with
"did not find an occurrence" as soon as the two `quadFn` terms are the same.

**The constraint qualification is `IsExactSum.of_continuousAt`, and its arguments are ordered with
the continuous function first.** Apply it with the quadratic as the left summand and take `.symm`.

**Cancelling at the end forces a finiteness argument.** `moreau_add` ends with
`-(D + ↑c) + D = ↑(-c)`, which needs `D` to be a real number: bounded above by evaluating at a
point of `dom f*` (`proper_conj`, Theorem 12.2) and bounded below because `conj B (f + w(z - ·)) 0`
dominates `-(f x₀ + w(z - x₀))` at any `x₀ ∈ dom f`. `infConv_quadFn_ne_top` and its three
companions then follow from `moreau_add` itself.

**`Tdaf.EReal.iInf_add_coe` was added for this file** (`Tdaf/Order/EReal.lean`, next to
`iSup_add_coe`): a real constant moves in and out of an infimum with no hypothesis, including over
an empty index type.

**Not done**: the existence and uniqueness of the splitting `z = x + x*`, `prox`, the gradient
formulas `x = ∇(f* □ w) z`, and Cor 31.5.2. Existence is Theorem 27.2 in a Hilbert space —
`Optimization/Minimum.lean` proves it only in finite dimensions — uniqueness is strict convexity of
`w`, and the gradient formulas need Theorem 26.3.

### `Tdaf/Analysis/Convex/Optimization/Minimum.lean`

§27: **Theorems 27.1(a), 27.1(b), 27.2 with Corollaries 27.2.1–27.2.2, the non-polyhedral case of
Theorem 27.3 with Corollary 27.3.3, and Theorem 27.4**.

```lean
def argmin (f : E → EReal) : Set E := {x | ∀ z, f x ≤ f z}
```

**Use `argmin`, not `IsMinOn f Set.univ`.** It unfolds to exactly the subgradient inequality at
`y = 0`, so `mem_argmin_iff_zero_mem_subgradient` is a `simp` and `§27 = §23 at the origin` is
literally true. `mem_argmin_iff_isMinOn` and `mem_argmin_iff_le_iInf` are the bridges.

**Two theorems have fewer hypotheses than the book.** `conj_zero_eq_neg_iInf` (Thm 27.1(a)) has
*none* — `f*(0) = ⨆ x (0 - f x) = -(⨅ x, f x)` for any `f` — and `argmin_eq_subgradient_conj_zero`
(Thm 27.1(b)) needs only `ConvexFn` and `ClosedFn`, no properness: the `EReal` step is
`EReal.le_sub_iff_add_le` with `c = 0`, and `0` is neither `⊥` nor `⊤`, so both side conditions are
discharged by `.inr`.

**Theorem 27.4 is two theorems.** `le_of_mem_subgradient_of_neg_mem_normalCone` (sufficiency) needs
nothing at all — the subgradient inequality and the normality inequality add — and
`exists_mem_subgradient_neg_mem_normalCone` (necessity) is `IsExactSum.subgradient_add` applied to
`h + δ(· | C)` together with `subgradient_indicatorFn`. Supply the `IsExactSum` from
`Duality/Relint.lean` for Rockafellar's `ri` hypothesis, or from the polyhedral constructors.

**Theorem 27.2 uses Mathlib's lsc extreme value theorem.** `LowerSemicontinuousOn.exists_isMinOn`
(`Mathlib/Topology/Semicontinuity/Basic.lean`) works for any `LinearOrder` codomain, `EReal`
included; the compactness of the level set is `recessionCone_setOf_le` (Thm 8.7) followed by
`isCompact_iff_recessionCone_eq_zero` (Thm 8.4). The ε–δ clause
(`exists_pos_forall_exists_mem_argmin_dist_lt`) uses the *same* theorem once more instead of
Rockafellar's nest of closed bounded sets: minimise `f` over the compact
`lev_{inf f + 1} f \ (M + ε·int B)`, and the minimum value is `> inf f` because the minimiser is
not in `M`.

**Corollaries 27.2.1 and 27.2.2 go through `Metric.infDist`, and take an arbitrary filter.**
`tendsto_infDist_argmin` is the single content-bearing lemma; `mem_argmin_of_mapClusterPt` and
`tendsto_of_argmin_eq_singleton` are corollaries of it, and only
`isBounded_range_of_tendsto_iInf` — whose conclusion is about `Set.range u` — needs `ℕ` and
`atTop`. Corollary 27.2.2 carries no recession hypothesis: `argmin_eq_setOf_le` exhibits a
singleton minimum set as a level set, and Theorem 8.7 then forces `0⁺f = {0}`.

**Theorem 27.3's recession lemma is stated for indicators, not for sums.**
`recessionConeFn_add_indicatorFn` is `recessionFn_add` (Thm 9.3) plus the fact that
`δ(· | 0⁺C)` only takes the values `0` and `⊤`. There is no general
`recessionConeFn (f + g) = recessionConeFn f ∩ recessionConeFn g`: on `ℝ`, `f x = -x` and
`g x = x` have `0⁺f ∩ 0⁺g = {0}` while `f + g = 0` recedes in every direction.

**Thm 27.1(f) is done**: `recessionCone_setOf_le_eq_polarCone_dom_conj` and
`recessionCone_argmin_eq_polarCone_dom_conj` are Theorem 8.7 composed with Theorem 14.2. The first
sentence of Thm 27.1(i) is `zero_mem_closure_dom_conj_iff` in `Duality/Level.lean`.

**Cor 27.3.2 is done, and it does not need Helly.** `argmin_nonempty_of_polyhedralFn` runs the
finitely generated description of the epigraph (Theorem 19.1): a lower bound forces every
generating *direction* upward, so the vertical coordinate is minimised over `epi f` at one of the
finitely many generating *points*. No closedness, no properness.
`exists_forall_le_of_polyhedralFn_of_polyhedral` then restricts `f` to `C` by Rockafellar's own
vertical prism. The book derives 27.3.2 from 27.3.1 and hence from Theorem 21.5; that detour is
avoidable.

**Not done**: Thm 27.1(c), (d), (e), (g), (h) and the rest of (i) — (c), (d) and (i) need Thm 23.3
in full and the remaining clauses of Cor 13.3.4, (e) needs a reflexive pairing (`∂f*(0)` lives in
`E**`), (g) and (h) need Thm 13.5 — and the polyhedral refinement of Thm 27.3, Cor 27.3.1 and the
polyhedral half of Cor 27.3.3, which genuinely do need Helly in the form of Thm 21.5.

### `Tdaf/Analysis/Convex/Optimization/Maximum.lean`

§32: **Theorems 32.1, 32.2 and 32.4** with Corollaries 32.1.1, 32.4.1 and the compact case of
Corollary 32.3.2.

**Maximisation is `∀ z ∈ C, f z ≤ f x`, not `IsMaxOn`.** Every proof here applies the hypothesis at
one specific point, and the unfolded form is what `ConvexFn.epi_combo` and the subgradient
inequality want. `isMaxOn_iff` is the bridge if a caller arrives with `IsMaxOn`.

**Theorem 32.1 is `exists_one_lt_smul_mem_of_mem_relint` + `combo_prolong` + `epi_combo`.** The
prolongation factor `t > 1` gives `y := (1 - t) • x + t • z ∈ C`, and `combo_prolong x z ht0.ne'`
rewrites `(1 - t⁻¹) • x + t⁻¹ • y` back to `z`. Note the argument order: `combo_prolong` takes the
*endpoints* `x z` explicitly and the factor implicitly, so it is `combo_prolong x z ht0.ne'`, not
`combo_prolong x y _`.

**`ht0.ne'` not `ht0.ne`.** `combo_prolong` and `mul_inv_cancel₀` both want `t ≠ 0`, and from
`ht0 : 0 < t` that is `ht0.ne'` (`.ne` gives `0 ≠ t`).

**`mul_lt_mul_right` does not fire on `ℝ` here.** `(mul_lt_mul_right htinv0).2 ht` fails with
"failed to synthesize `MulLeftStrictMono ℝ`" — the name resolves to the ordered-monoid version.
For `t⁻¹ < 1` from `1 < t`, the robust route is `have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ …`
followed by `nlinarith`.

**Theorem 32.2 is `convexHull_min` twice, over `Module ℝ E`.** `ConvexFn.convex_le` gives the
sublevel set for the supremum clause and `ConvexFn.convex_lt` the strict one for the attainment
clause; neither needs a topology or a dimension bound. Keeping the section algebraic is what lets
`ConvexFn.iSup_extremePoints` reuse it verbatim in finite dimensions.

**`le_iSup₂` needs the motive spelled out.** For `⨆ x ∈ S, f x` the family is
`fun w (_ : w ∈ S) => f w`, and it has to be supplied as `le_iSup₂ (f := …) z hz`; elaboration does
not find it from the goal.

**`IsFace`'s subset field is `hface.toIsExtreme.1`.** `IsFace` extends Mathlib's `IsExtreme ℝ C C'`,
whose first component is `C' ⊆ C`. There is no `IsFace.subset`.

**Theorem 32.4 does not go through Theorem 23.7.** The subgradient inequality at `z` and maximality
at `z` sandwich `⟨z - x, y⟩` between `f x` and `f x`; extracting `f x` as a real with
`EReal.exists_coe_of_ne_bot_of_lt_top` and cancelling is the whole proof. Corollary 32.4.1
(`le_of_mem_normalCone`) is `map_sub` plus `LinearMap.sub_apply` plus `linarith`, with no convexity
hypothesis at all.

**Not done**: Thm 32.3 and Cors 32.2.1, 32.3.1, 32.3.3, 32.3.4, all blocked on Theorems 18.4–18.5
for *unbounded* closed convex sets (extreme directions), which `Face.lean` has only in the compact
case; and the "supremum is attained" clause of Cor 32.3.2, which needs Thm 10.1.

### `Tdaf/Analysis/Convex/Face.lean`

§18's facial structure: **Theorems 18.1 and 18.2** in full, and **Theorems 18.4 and 18.5** for
compact sets.

```lean
structure IsFace (C C' : Set E) : Prop extends IsExtreme ℝ C C' where
  convex : Convex ℝ C'
```

**Rockafellar's face is not Mathlib's `IsExtreme`, even for convex `C`.** `{0, 1}` is an extreme
subset of `[0, 1]` and is not convex, so it is not a face. The convexity field is therefore real,
and everything else is inherited: `IsFace.trans`, `.inter`, `.mono`, `isFace_sInter`,
`isFace_singleton : IsFace C {x} ↔ x ∈ C.extremePoints ℝ`, `IsExposed.isFace`.

The rest of the file:

* `IsFace.subset_of_relint_inter_nonempty` — **Thm 18.1**. Stated *without* `Convex ℝ D`: the proof
  only uses `exists_one_lt_smul_mem_of_mem_relint`, which needs nothing about `D`. The `x = z` case
  needs no separate treatment because that lemma already covers it.
* `IsFace.eq_inter_closure` (**Cor 18.1.1**) and `IsFace.isClosed`.
* `IsFace.eq_of_relint_inter_nonempty` — **Cor 18.1.2**.
* `IsFace.disjoint_relint`, `IsFace.subset_intrinsicFrontier`, `IsFace.affineSpan_ne`,
  `IsFace.finrank_vectorSpan_lt` — **Cor 18.1.3**. The dimension half is proved directly rather
  than through Corollary 6.3.3: equal `finrank` of the direction spaces plus a shared point makes
  the affine hulls equal, and then `ri C'` would sit inside `ri C`.
* `exists_isFace_subset_relint` — the engine of **Thm 18.2**; `exists_isFace_mem_relint`,
  `eq_iUnion_relint_isFace`, `IsFace.relint_pairwise_disjoint`, `IsFace.relint_maximal` are the
  four halves of the statement. `Convex.isFace_inter_setOf_eq` (an exposed face is a face) and
  `notMem_relint_iff_exists_isMaxOn` (**Cor 11.6.2**) are what make the smallest face containing a
  relatively open convex `D` meet `ri C'`; Corollary 6.5.2 finishes.
* `exists_notMem_relint_mem_segment` — **Thm 18.4** for compact `C`, with no convexity hypothesis.
  `T = {t | x + t • d ∈ C}` is compact, and prolongation pushes `max T` and `min T` out of `ri C`.
* `convexHull_extremePoints` — **Cor 18.5.1**, Minkowski's theorem, `conv (ext C) = C` for compact
  convex `C`. **Mathlib does not have this**: `closure_convexHull_extremePoints` only gives the
  closed convex hull, and the closure cannot be dropped in general because `ext C` need not be
  closed. Rockafellar's induction on `dim C`, via Theorems 18.2 and 18.4.
* `extremePoints_nonempty` — **Cor 18.5.3** for compact `C`, from Minkowski plus
  `convexHull_empty`.

**Not done here**: Thms 18.3, 18.6 (Straszewicz), Cor 18.5.2, and the unbounded halves of 18.4 and
18.5 — all of them now done in `Representation.lean`, which has the `conv S` for `S` a set of
points *and directions* that this file lacks. Theorems 18.7 and 18.8 are done in `Exposed.lean` and
`Tangent.lean`. See the "What is not here" block in the module docstring for the individual extra
obstructions.

### `Tdaf/Analysis/Convex/LinearInequalities.lean`

§22 through Theorem 22.3: the theorems of the alternative for *linear* systems.

```lean
theorem farkas_of_pairing … ; theorem farkas …                     -- Cor 22.3.1, Farkas
theorem exists_multipliers_of_infeasible … ; theorem alternative_linear_system …   -- Thm 22.1
theorem alternative_linear_system_strict …                        -- Thm 22.2, Motzkin
theorem le_consequence_iff …                                      -- Thm 22.3
```

**Theorem 22.1 does not have to wait for Theorem 21.4.** The plan inherits Rockafellar's derivation
of 22.1 from 21.4; it is available now from Farkas' Lemma, which is `K°° = K`
(`polarCone_polarCone`, Theorem 14.1) for a cone that is closed because finitely generated
(Minkowski–Weyl, `Polyhedral/Cone.lean`). Only Theorem 22.2 uses §21, and it uses Theorem 21.2,
which was already formalized.

**Theorem 22.2's multiplier condition needs a *separating* pairing.** Over `ℝⁿ` the step "the affine
function is non-negative everywhere, hence its linear part is zero, hence `∑ λᵢaᵢ + ∑ μⱼbⱼ = 0`" is
invisible. In the pairing formulation `IsCompatiblePairing B` is *not* enough — it gives
surjectivity, not injectivity, of `evalCLM`. `IsCompatiblePairing B.flip` supplies it through
Hahn–Banach on `F` (`eq_zero_of_forall_pairing_eq_zero`).

**Not here**: Lemma 22.4, Theorem 22.6 and Tucker's Theorem 22.7, which the plan leaves out; and
elementary vectors.

### `Tdaf/Analysis/Convex/Helly.lean`

§21: **Theorems 21.1, 21.2, 21.3, 21.6 and Corollaries 21.3.1, 21.3.2, 21.6.1, 21.6.2** —
everything except Theorems 21.4 and 21.5.

```lean
theorem alternative_infinite_system_univ … ; theorem alternative_infinite_system …   -- Thm 21.3
theorem exists_forall_le_zero_of_forall_subsystem …                                 -- Cor 21.3.1
theorem helly_of_no_common_recession …                                              -- Cor 21.3.2
```

**Theorem 21.3's last step does not need Theorems 16.4 or 16.1.** Rockafellar routes it through
`f* = cl (f₁*λ₁ □ ⋯ □ fₘ*λₘ)`; the inequality `∑ λᵢ fᵢ x ≥ -∑ λᵢ fᵢ* yᵢ` is Fenchel's inequality
summed termwise, using only `∑ λᵢ yᵢ = 0`. No infimal convolution appears.

**Corollary 21.3.1's tolerance has to be halved.** The book normalises `∑ λᵢ = 1` and works with
tolerance `ε/λ`, which makes the summed inequality *strict*; `EReal` is not a cancellative ordered
monoid, so `Finset.sum_lt_sum` is unavailable there (gotcha 117). Tolerance `ε/(2λ)` keeps every
step non-strict and the proof goes through unchanged.

**Not here**: Theorems 21.4 and 21.5. The real obstruction is not either of the two pieces this
entry used to name. `IsExactSum.of_relint` and `IsExactSum.of_polyhedral` — the project's Theorems
16.4 and 20.1 — are **strictly weaker than the book's**: they require `ClosedProperConvexFn` where
the book requires only *proper convex*. Rockafellar's 21.4 applies Theorem 20.1 to a *generated*
positively homogeneous function, which is in general neither closed nor proper, so the gap is
`cl (f + g) = cl (cl f + cl g)` under `ri (dom f) ∩ ri (dom g) ≠ ∅`, threaded through Theorem 16.4.
That is a §16 project, not a §21 one; closedness is load-bearing inside
`conj_add_eq_clFn_infConv`, and replacing `f, g` by their closures moves the inequality the wrong
way.

Three smaller pieces are missing as well: the epigraph-sum description of `conv {k₀, k₁}` (Theorem
3.8 for positively homogeneous functions); polyhedrality of the positively homogeneous function
generated by finitely many affine functions (Corollary 19.1.2 for *functions*); and the
subadditivity step `posHomGen h (x+y) ≤ posHomGen f x + posHomGen g y`, which
`PosHomogeneous.convexFn_iff_subadditive` cannot supply because it needs `∀ x, f x ≠ ⊥` — exactly
what an improper generated function violates. Theorem 20.1 and the identification
`kⱼ* = δ(· ∣ Cⱼ)` are available.

**Corollary 27.3.2 does not depend on Theorem 21.5**, contrary to what §6 of the plan said; see
`Optimization/Minimum.lean`.

```lean
theorem alternative_of_convex_system [Nonempty ι] (hC : Convex ℝ C)                 -- Thm 21.1
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hdom : ∀ i, ri C ⊆ dom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x
theorem alternative_of_convex_system_affine (hC : Convex ℝ C) …                     -- Thm 21.2
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)
```

The weighted sum is read in `EReal`, where `0 · (+∞) = 0` already implements Rockafellar's
convention that a vanishing multiplier drops its constraint — no `0⁺` bookkeeping is needed
anywhere in §21.

**Both proofs are the book's, with `R^m` read as `ι → ℝ` (resp. `(ι ⊕ κ) → ℝ`).** The set
`C₁ = {z | ∃ x ∈ C, ∀ i, fᵢ x < zᵢ}` misses the non-positive orthant exactly when the strict system
is unsolvable, and the separating functional's coordinates `l i = g (Pi.single i 1)` are the
multipliers. The orthant forces `l ≥ 0` (feed it `Pi.single i (-(c+1)/(-l i))`), and the *properness*
of the separation forces `l ≠ 0`. Separation only gives the inequality where every `fᵢ` is finite —
that is, on `ri C` — so **Corollary 7.3.3** (`ConvexFn.le_of_mem_closure`) carries it to
`cl (ri C) = cl C ⊇ C`; the ε in `fᵢ x < (fᵢ x).toReal + ε` is removed by a one-line
`ε := δ/(L+1)` contradiction rather than by a limit.

**Theorem 21.2 splits the index type instead of the index range.** Rockafellar cuts `1, …, m` at
`k`; here `ι` indexes the convex constraints and `κ` the affine ones. The affine constraints enter
`C₁` as *equations*, and they are `E →ᵃ[ℝ] ℝ` rather than `EReal`-valued: `combo_affine_sum`,
`convexFn_coe_affine_sum` and `eq_zero_of_nonneg_of_mem_relint_affine_sum` are the three lemmas the
proof needs, and none of them requires the `AffineMap` module structure (a finite combination of
affine maps is handled pointwise). `polyhedral_nonpos_orthant` supplies the polyhedrality that
**Theorem 20.2** wants; its `¬(C₁ ⊆ hyperplane)` clause is what rules out `l = 0`, via the
observation that a combination of affine functions attaining its minimum over `C` at a point of
`ri C` is constant on `C`.

**Theorem 21.1 is not derived from Theorem 21.2** even though it is the case `κ = Empty`. Rockafellar
notes that §21 can be read without §20 provided 21.2, 21.4 and 21.5 are skipped, and Corollary
28.2.1 takes exactly that cheaper route — 21.1 uses only Theorem 11.3.

**Theorem 21.6 comes from Mathlib.** `helly_finite` is an alias for `Convex.helly_theorem'`, which
Mathlib proves from Radon's theorem. Rockafellar derives 21.6 from Corollary 21.3.2; taking
Mathlib's route means Corollaries 21.6.1 and 21.6.2 do *not* wait on Theorem 21.3. Corollary 21.6.1
applies Helly to `C` together with the sublevel sets; the only fiddly step is the counting lemma
`S.card + T.card ≤ I.card`, done by injecting `S` and `T` into `I` along `some ∘ inl` and
`some ∘ inr`. Corollary 21.6.2 states the sparsity as `∃ S l, S.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0)`,
which sidesteps deciding `l i ≠ 0`.

**What §21 still owes.** Theorems 21.3, 21.4, 21.5 and Corollaries 21.3.1, 21.3.2 are blocked
*upstream*: Theorem 21.3 goes through the positively homogeneous function generated by
`conv {fᵢ* | i ∈ I}`, whose conjugate is **Theorem 13.5** (deferred), and extracts the multipliers by
**Corollary 17.1.3**, the directions half of Carathéodory (§17, not yet done). 21.4/21.5 weaken
21.3's recession hypothesis using §20, and 21.3.1/21.3.2 are its corollaries.

### `Tdaf/Analysis/Convex/Optimization/Perturbation.lean`

§29: **Theorem 29.1** in full, **Corollaries 29.1.1–29.1.6** and **Theorem 29.2**.

```lean
theorem supportFn_kuhnTucker …    -- Cor 29.1.1: `δ*(u ∣ KT) = cl (inf F)'(0; -u)`
theorem kuhnTucker_eq_empty_iff …                                     -- Cor 29.1.2
theorem kuhnTucker_eq_singleton_of_dirDeriv_eq …                      -- Cor 29.1.3
theorem dirDeriv_infBifun_eq …                                        -- Cor 29.1.4
theorem proper_infBifun_of_stronglyConsistent …                       -- Cor 29.1.5
theorem infBifun_eq_bot_of_mem_relint …                               -- Cor 29.1.6
def PolyhedralBifun … ; theorem kuhnTucker_nonempty_of_polyhedralBifun …    -- Thm 29.2
```

**Corollary 29.1.1's derivative clause is the support function of `-(KT)`, not of `KT`.** The sign
flip in `kuhnTucker_eq_neg_subgradient` propagates, which is what `supportFn_neg_set` is for.

**Theorem 29.2's optimal-solution clause is done** — `argmin_nonempty_of_polyhedralBifun` and
`polyhedral_argmin_of_polyhedralBifun`, on Corollary 27.3.2, which turned out not to need Helly.
**It needs less than the book asks**: Rockafellar says "if the optimal value in (P) is finite, (P)
has at least one optimal solution", but `inf F 0 ≠ -∞` suffices — an optimal value of `+∞` makes
every point optimal. Finiteness is needed only for *polyhedrality* of the minimum set, which is a
sublevel set at a real level.

**Not here**: Corollary 29.1.4's compactness clause. Theorem 29.3 is in `Saddle/Minimax.lean`,
with §36.

```lean
abbrev Bifun (U X : Type*) := U → X → EReal
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x
def domBifun (F : Bifun U X) : Set U := {u | ∃ x, F u x ≠ ⊤}
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)
def Consistent (F) : Prop := (0 : U) ∈ domBifun F
def StronglyConsistent (F) : Prop := (0 : U) ∈ ri (domBifun F)
def StrictlyConsistent (F) : Prop := (0 : U) ∈ interior (domBifun F)
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) = infBifun F 0}
theorem convexFn_infBifun (hF : ConvexBifun F) : ConvexFn (infBifun F)
theorem dom_infBifun (F : Bifun U X) : dom (infBifun F) = domBifun F
theorem iInf_add_infBifun_le (B) (F) (v) :
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) ≤ infBifun F 0
theorem mem_kuhnTucker_iff_neg_mem_subgradient (ht) (hb) :
    v ∈ KuhnTucker B F ↔ -v ∈ subgradient B (infBifun F) 0
theorem kuhnTucker_eq_neg_subgradient (ht) (hb) :
    KuhnTucker B F = -(subgradient B (infBifun F) 0)
theorem kuhnTucker_nonempty_of_stronglyConsistent [IsCompatiblePairing B] [FiniteDimensional ℝ U]
    (hF : ConvexBifun F) (hp : Proper (infBifun F)) (hs : StronglyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) : (KuhnTucker B F).Nonempty
```

**`KuhnTucker` is Rockafellar's definition, and that is the point.** The plan's draft used the
inequality `inf F 0 ≤ ⟨u, v⟩ + inf F u`, which would have made Theorem 29.1 an `Iff.rfl` — the cheat
`08-surface.md` §8.4 item 4 forbids. The book (≈ line 11740) says "finite and equal to `inf F 0`",
so the file says that, and `mem_kuhnTucker_iff_forall_le` derives the inequality form from
`iInf_add_infBifun_le` (evaluate the infimum at `u = 0`, where `B 0 v = 0`).

**`domBifun` is `{u | ∃ x, F u x ≠ ⊤}`, not `{u | F u ≠ fun _ => ⊤}`.** The two agree, but the
existential form is what `dom_iInf_right` states and what `Set.mem_setOf` unfolds to in one step.

**Theorem 29.1's convexity is `convexFn_iInf_right`, unmodified.** `infBifun F` is definitionally
`fun u => ⨅ x, graphFn F (u, x)`, which is that lemma's exact shape; there is nothing to massage.

**The `EReal` rearrangement in the subgradient equivalence is one private lemma.**
`(c : EReal) + ((-p : ℝ) : EReal) ≤ w ↔ (c : EReal) ≤ (p : EReal) + w` (`coe_add_neg_le_iff`) is all
that separates `-v ∈ ∂(inf F)(0)` from the Kuhn–Tucker inequality. Both sides of the coercion are
real, so no `∞ - ∞` case arises and the proof is `induction w`.

**Set negation is a preimage, so every property transfers.** With
`KuhnTucker B F = -(∂(inf F)(0))`, convexity is `(convex_subgradient …).neg` and closedness is
`(isClosed_subgradient …).neg`; nonemptiness is cheaper still — take the `y` that Theorem 23.4
supplies and exhibit `-y` through `mem_kuhnTucker_iff_neg_mem_subgradient` plus `neg_neg`.
Remember that `open Pointwise` is needed at file scope for `-(S : Set V)` to elaborate.

**`StronglyConsistent` matches Theorem 23.4 exactly.** `0 ∈ ri (domBifun F)` plus
`dom (infBifun F) = domBifun F` is literally the hypothesis of
`subgradient_nonempty_of_mem_relint_dom`; no `ri`-commutation lemma is involved.

### `Tdaf/Analysis/Convex/Optimization/Lagrangian.lean`

§§28–29, the Lagrangian half: the definition, its identification with a concave conjugate, the
infimum identity and the Lagrangian description of Kuhn–Tucker vectors.

```lean
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x
theorem lagrangian_eq_concaveConj (B) (F) (v) (x) :
    lagrangian B F v x = concaveConj B (fun u => -(F u x)) v
theorem iInf_lagrangian (B) (F) (v) :
    (⨅ x, lagrangian B F v x) = ⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      (⨅ x, lagrangian B F v x) = infBifun F 0
theorem concaveFn_lagrangian (B) (F) (x) : ConcaveFn (fun v => lagrangian B F v x)
```

**`L` is `concaveConj` on the nose, with no reflected argument.** `concaveConj B g v` is
`⨅ u (⟨u, v⟩ - g u)`, so `L(v, x) = concaveConj B (fun u => -(F u x)) v` needs only
`sub_eq_add_neg` and `neg_neg`. The plan's `-(conj B (fun u => -(F u x)) (-v))` is the same
function, but going through `concaveConj` keeps `Duality/ConcaveConj.lean`'s lemmas applicable
verbatim — in particular `concaveFn_concaveConj`, which proves concavity of `L(·, x)` **with no
hypothesis on `F`**.

**`Tdaf.EReal.iInf_add_coe` is the lemma `iInf_lagrangian` needs, and it had to be written.**
`(⨅ i, u i) + (r : EReal) = ⨅ i, (u i + r)` for a *real* `r` is not in Mathlib and is not a
`Monotone`/`Galois` consequence, because `iInf` does not commute with `EReal` addition in general.
The proof is the standard "add `-r` back": `≤` is `le_iInf ∘ add_le_add`, and the reverse direction
applies that same bound to `fun i => u i + r` at `-r` and cancels with
`EReal.add_sub_cancel_right` / `EReal.sub_add_cancel`. It lives in `Order/EReal.lean` next to
`biSup_add_coe`, and `Optimization/Adjoint.lean` reuses it.

**The two infima swap with `iInf_comm`, but only after `add_comm`.** `⨅ x ⨅ u (c + F u x)` has the
constant on the *left*, and `iInf_add_coe` wants it on the right; the file does
`rw [infBifun_apply, add_comm, Tdaf.EReal.iInf_add_coe]` and that single `add_comm` rewrites both
occurrences at once, so a trailing `iInf_congr fun x => add_comm _ _` is "No goals to be solved".

**`mem_kuhnTucker_iff_iInf_lagrangian` is `rw [KuhnTucker, Set.mem_ofPred_eq, iInf_lagrangian]`.**
`Set.mem_ofPred_eq` is the unfolding lemma for a set given by `{v | P v}` in this Mathlib version;
`Set.mem_setOf_eq` also works but leaves the conjunction in a shape `rw` cannot enter.

### `Tdaf/Analysis/Convex/Optimization/Adjoint.lean`

§30: **Theorem 30.1** in full, **Theorem 30.2**, **Corollary 30.2.2**, and the normality-free
half of Theorem 30.5.

```lean
noncomputable def adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))
theorem adjointBifun_eq_neg_conj_graphFn (Bu) (Bx) (F) (y) (v) :
    adjointBifun Bu Bx F y v = -(conj (prodPairing Bu Bx) (graphFn F) (-v, y))
def adjointSwap (V Y) : (Y × V) →ₗ[ℝ] (V × Y) :=
  LinearMap.prod (-LinearMap.snd ℝ Y V) (LinearMap.fst ℝ Y V)
theorem concaveFn_graphFn_adjointBifun (Bu) (Bx) (F) :
    ConcaveFn (graphFn (adjointBifun Bu Bx F))
theorem adjointBifun_zero_eq_concaveConj (Bu) (Bx) (F) :
    adjointBifun Bu Bx F 0 = concaveConj Bu (fun u => -(infBifun F u))
theorem adjointBifun_zero_le (Bu) (Bx) (F) (v) : adjointBifun Bu Bx F 0 v ≤ infBifun F 0
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx) : …
theorem iSup_adjointBifun_zero_le (Bu) (Bx) (F) : (⨆ v, adjointBifun Bu Bx F 0 v) ≤ infBifun F 0
noncomputable def concaveAdjointBifun (Bu) (Bx) (G : Bifun Y V) : Bifun U X :=
  fun u x => ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal))
noncomputable def clBifun (F : Bifun U X) : Bifun U X := fun u x => clFn (graphFn F) (u, x)
def ClosedBifun (F : Bifun U X) : Prop := ClosedFn (graphFn F)
def ConcaveBifun (G : Bifun U X) : Prop := ConcaveFn (graphFn G)
theorem surjective_adjointSwap : Function.Surjective (adjointSwap V Y)
theorem concaveAdjointBifun_adjointBifun_eq_biconj (Bu) (Bx) (F) (u) (x) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) u x
      = biconj (prodPairing Bu Bx) (graphFn F) (u, x)
theorem concaveAdjointBifun_adjointBifun_eq_clBifun (hF : ConvexBifun F) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) = clBifun F
theorem adjointBifun_clBifun : adjointBifun Bu Bx (clBifun F) = adjointBifun Bu Bx F
```

**`F** = cl F` is one reindexing.** Both adjoints are conjugates read at the reflected point
`adjointSwap q = (-v, y)`, so `F**` is a supremum over `Y × V` of exactly the summands the
biconjugate takes over `V × Y`, evaluated at `adjointSwap q`. `adjointSwap` is onto — given
`(v, y)` take `q = (y, -v)` — and `Function.Surjective.iSup_comp` closes the gap. No sign lemma is
involved; the whole proof of `concaveAdjointBifun_adjointBifun_eq_biconj` is the reindexing plus
`add_comm`, and Fenchel–Moreau does the rest.

**The blocker was a missing instance, not a missing theorem.** `biconj_eq_clFn` on `U × X` asks for
`IsCompatiblePairing (prodPairing Bu Bx)`, and `Duality/Pairing.lean` had no product instance, so
it would have had to be carried as a hypothesis at every use site. It is derivable:
continuity is componentwise, and surjectivity is the splitting `g (u, x) = g (u, 0) + g (0, x)`
through `ContinuousLinearMap.inl`/`inr`. `instIsContinuousPairingProd` and
`instIsCompatiblePairingProd` now live next to the other pairing instances, and Theorem 30.1 needs
no hypothesis mentioning `U × X` at all.

**`cl F` is the *joint* closure, not the slice-wise one.** `clBifun F u x = cl (graph F) (u, x)`,
which is *not* `cl (F u) x`; the bracket `⟨Fu, y⟩` sees only the slice-wise closure, which is
exactly why `⟨(cl F) u, y⟩` and `⟨Fu, y⟩` differ and why Theorem 33.2 has two equations rather
than one. Mixing the two up makes Theorem 33.2's second equation look trivial and false.

**`(cl F)* = F*` is what makes §34 terminate.** `adjointBifun_clBifun` is `conj_clFn` applied to
the graph function, two lines; without it the closure operations of §34 would keep producing new
functions.

**The sign flip goes on the argument, not on the pairing.** `negFst (prodPairing Bu Bx)` exists in
`Duality/Pairing.lean` and the plan expected §30 to use it. Reading `⟨u, -v⟩ + ⟨x, y⟩` as the
pairing of `(u, x)` with `(-v, y)` keeps `conj` for the *plain* `prodPairing`, so `convexFn_conj`,
`closedFn_conj` and the rest apply unchanged; the reflection becomes a linear map
(`adjointSwap`) and concavity of `F*` is `convexFn_compLin _ (convexFn_conj _ _)` after
`concaveFn_iff_convexFn_neg`. No hypothesis on `F` is needed anywhere in Theorem 30.1's concavity
clause.

**Group the finite terms inside one coercion.** Writing
`F u x + ((⟨u, v⟩ - ⟨x, y⟩ : ℝ) : EReal)` — one `EReal` addition, one real subtraction — is
strictly better than `F u x - ⟨x, y⟩ + ⟨u, v⟩`, which is two `EReal` operations and can hit `∞ - ∞`
where the first form cannot. The private lemma `neg_coe_sub`,
`-(((-c : ℝ) : EReal) - w) = w + (c : EReal)`, is the only sign bookkeeping the file needs; it goes
through `Tdaf.EReal.neg_add` with `.inl (EReal.coe_ne_bot _)`.

**`[IsContinuousPairing (prodPairing Bu Bx)]` does not elaborate.** `IsContinuousPairing B` demands
a `TopologicalSpace` on `B`'s *domain*, i.e. on `U × X`, which nothing in §30 supplies; the usable
form is `[IsContinuousPairing (prodPairing Bu Bx).flip]`, matching `closedFn_conj`'s own context
(`Duality/Conjugate.lean`, `section ConjClosed`). With that and `closedFn_compLin`
(`Operations/Closed.lean`) the closedness half of Theorem 30.1 is
`closedFn_compLin closedFn_conj continuous_adjointSwap`.

**An explicit argument silently shadows the section variable an instance binder refers to.**
`theorem closedConcaveFn_graphFn_adjointBifun [IsContinuousPairing (prodPairing Bu Bx).flip]
(Bu : …) (Bx : …)` type-checks its *statement* but then fails instance search, because the binder
saw the section's `Bu`/`Bx` and the conclusion sees the explicit ones. Any statement whose
hypotheses mention the pairing must leave the pairing implicit.

**Theorem 30.2 is `iInf_lagrangian`'s swap again.** `adjointBifun_zero_apply` uses
`Tdaf.EReal.iInf_add_coe` exactly as `Lagrangian.lean` does (and hits the same "No goals" trap from
`add_comm` rewriting both occurrences). The result must be phrased with `concaveConj`, not `conj`:
`inf F` is convex, its *convex* conjugate is not `F* 0`, and `g* ≠ -(-g)*`.

**Weak duality is free.** `adjointBifun_zero_le` is `iInf_add_infBifun_le` from
`Perturbation.lean`, and `iSup_adjointBifun_zero_le` is `iSup_le` over it.

**`ImageClosedBifun` is the predicate §33 runs on, and it is strictly weaker than `ClosedBifun`.**
`ClosedBifun F` is closedness of the graph function on `U × X`; `ImageClosedBifun F` is closedness
of every slice `F u`. `ClosedBifun.imageClosedBifun` is the implication — take the two cases of
`closedFn_iff` and push each through `x ↦ (u, x)`, using `lowerSemicontinuous_comp` for the
semicontinuity one — and there is no converse. The definition needs only `[TopologicalSpace X]`
while the slice lemma needs `AddCommGroup` and `IsTopologicalAddGroup` on both factors (it unfolds
`closedFn_iff`, whose properness clause is stated over a topological group), so the two live in
separate sections; putting them together makes instance search fail on `AddCommGroup (U × X)`.

### `Tdaf/Analysis/Convex/Optimization/Program.lean`

§28: ordinary convex programs, and **Theorem 28.2** (existence of a Kuhn–Tucker vector under
Slater's condition) with Corollaries 28.2.1 and 28.2.2.

```lean
def feasibleSet (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0}
noncomputable def programLagrangian (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : E → EReal :=
  fun x => f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal)
noncomputable def optimalValue (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : EReal :=
  ⨅ x ∈ feasibleSet f b, f₀ x
structure IsKuhnTuckerVector (f₀) (f) (b) (l : ι → ℝ) (μ : κ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ l i
  nonneg_affine : ∀ j, 0 ≤ μ j
  ne_bot : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊥
  ne_top : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊤
  iInf_eq : (⨅ x, programLagrangian f₀ f b l μ x) = optimalValue f₀ f b
theorem exists_isKuhnTuckerVector_of_slater (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ ri (dom f₀), (∀ i, f i x < 0) ∧ ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ
theorem exists_isKuhnTuckerVector_of_mem_dom …          -- Cor 28.2.1
theorem exists_isKuhnTuckerVector_of_affine …           -- Cor 28.2.2, `[IsEmpty ι]`
theorem exists_multipliers_of_slater_eq …               -- equality constraints, signed multipliers
```

**§28 was never blocked.** `00-overview.md` and `06-optimization.md` both recorded that Slater's
theorem waited on "§21's theorems of the alternative for *mixed* inequality/equality systems, which
`Helly.lean` does not have". That is wrong: `alternative_of_convex_system_affine` (Theorem 21.2)
already keeps the affine constraints in a **second index type** `κ`, which is exactly the mixed
form, and Rockafellar's own reduction splits an equality into two affine inequalities — which is
what `exists_multipliers_of_slater_eq` does with `Sum.elim a fun k => -(a k)`.

**The Slater proof is Theorem 21.2 applied to `Option ι`.** Add the objective as an extra
inequality `f₀ x - α < 0` (`α` the optimal value, finite by hypothesis) and run the alternative:
branch (a) would produce a feasible point strictly below the optimal value, so branch (b) holds and
gives multipliers `c : Option ι → ℝ`, `μ : κ → ℝ`. The whole content of the rest of the proof is
`0 < c none`: at the Slater point every `c (some i) * f i x` is `≤ 0` and every `μ j * a j x` is
`≤ 0`, so `c none = 0` would force all the `c (some i)` to vanish too, contradicting `c ≠ 0`.
Normalising by `c none` gives the Kuhn–Tucker vector.

**`ri (dom f₀)` needs no separate `hdom` hypothesis.** The plan's draft carried
`∀ i, ri (dom f₀) ⊆ dom (f i)` next to Rockafellar's assumption (b) `dom f₀ ⊆ dom (f i)`; the
first is implied by the second and was dropped.

**Corollary 28.2.1 is a prolongation along a segment.** From a Slater point `z ∈ ri (dom f₀)` and
any `y ∈ dom f₀`, `Convex.segment_mem_relint` puts the open segment in `ri (dom f₀)` and
`ConvexFn.tendsto_lscHull_along_segment_relint` (the `ri` form of Theorem 7.5) makes `f₀` converge
along it, so `Tendsto.eventually_lt_const` over `𝓝[<] (1 : ℝ)` finds a Slater point where `f₀` is
below any prescribed bound.

### `Tdaf/Analysis/Convex/Optimization/Normal.lean`

§30 from Corollary 30.2.1 on: **Corollaries 30.2.1, 30.2.2** (both formulas) **and 30.2.3**,
**Theorem 30.3** in full, **Theorem 30.4** clauses (a)–(f), and **Theorem 30.5**.
`ConcaveKuhnTucker` and `ConcavePolyhedralBifun` are the two definitions clauses (d)–(f) need;
`forall_conj_eq_top_iff` is the single lemma both halves of Corollary 30.2.1 run on. Corollary
30.5.1 is in `Saddle/Minimax.lean`, with §36.

**Not here**: Theorem 30.4 (g)–(j), which route through Theorem 27.1(d)/(f). **Theorem 14.2 is now
formalized** (`Recession/Conjugate.lean`) and with it Theorem 27.1(f), so what remains is
Corollary 13.3.4's clauses (b)–(d), which need Theorem 13.1's `ri`/`int`/`aff` clauses, and
`int (dom (F 0)*) = int (domConcave F*)`, a Corollary 7.4.1-type result.

```lean
theorem clFn_zero_eq_iSup_iInf (hf : ConvexFn f) :
    clFn f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x)
def Normal (F : Bifun U X) : Prop := clFn (infBifun F) 0 = infBifun F 0
noncomputable def supBifun (G : Bifun Y V) : Y → EReal := fun y => ⨆ v, G y v
def domConcaveBifun (G : Bifun Y V) : Set Y := {y | ∃ v, G y v ≠ ⊥}
def ConcaveConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ domConcaveBifun G
def ConcaveStronglyConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ ri (domConcaveBifun G)
def ConcaveNormal (G : Bifun Y V) : Prop := clConcave (supBifun G) 0 = supBifun G 0
theorem clFn_infBifun_zero_eq_iSup_adjointBifun (Bx) (hF : ConvexBifun F) :
    clFn (infBifun F) 0 = ⨆ v : V, adjointBifun Bu Bx F 0 v
theorem clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun (hG : ConcaveBifun G) :
    clConcave (supBifun G) 0 = infBifun (concaveAdjointBifun Bu Bx G) 0
theorem normal_iff_iSup_adjointBifun_eq (Bx) (hF : ConvexBifun F) :
    Normal F ↔ (⨆ v : V, adjointBifun Bu Bx F 0 v) = infBifun F 0
theorem normal_iff_concaveNormal_adjointBifun (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Normal F ↔ ConcaveNormal (adjointBifun Bu Bx F)
theorem StronglyConsistent.normal (hs) (hF : ConvexBifun F) : Normal F
theorem normal_of_kuhnTucker_nonempty (Bx) (hF) (h : (KuhnTucker Bu F).Nonempty) : Normal F
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bx) (hF) (hn : Normal F) (ht) (hb) :
    v ∈ KuhnTucker Bu F ↔ adjointBifun Bu Bx F 0 v = ⨆ w : V, adjointBifun Bu Bx F 0 w
theorem ConcaveFn.clConcave_eq_of_mem_relint_domConcave (hg : ConcaveFn g)
    (hx : x ∈ ri (domConcave g)) : clConcave g x = g x
```

**All of §30 after Theorem 30.2 is one lemma.** `clFn_zero_eq_iSup_iInf` is Fenchel–Moreau read at
the origin: `biconj B f 0 = ⨆ y (⟨0, y⟩ - f*(y)) = ⨆ y (-f*(y))`, and `-f*(y)` is
`⨅ x (f x - ⟨x, y⟩)`, which is the dual objective `(F* 0)(-y)`. The reindexing `y ↦ -y` is
`Function.Surjective.iSup_comp` on negation. Everything else in the file is bookkeeping on top of
it.

**Corollary 30.2.2's first formula needs no closedness.** Rockafellar states the whole corollary for
closed convex `F`; `clFn (inf F) 0 = sup F* 0` only uses Fenchel–Moreau for `inf F`. So
Theorem 30.3's (a) ⟺ (c) holds for *every* convex bifunction, and `ClosedBifun F` is needed only
where `F** = cl F` has to be turned back into `F` — the second formula and clause (b).

**The dual formula is the first one, negated.** `-(sup G) = inf (fun y v => -(G y v))`, so
`clConcave (sup G) 0 = -(clFn (inf (-G)) 0)` and the first formula applies with the pairings
`Bx.flip` and `Bu.flip`. The sign bookkeeping is that
`-(adjointBifun Bx.flip Bu.flip (-G) 0 x) = concaveAdjointBifun Bu Bx G 0 (-x)`, so a second
negation reindexing closes it. Composing with `F** = cl F` gives the book's
`(cl (sup F*))(0) = inf F 0`.

**Theorem 30.4(c) does not go through subgradients.** Rockafellar proves it from Theorem 23.5. Here
`mem_kuhnTucker_iff_adjointBifun_zero_eq` already says a Kuhn–Tucker vector is a point where the
dual objective attains `inf F 0`, and weak duality pins the dual optimal value down, so normality
is Theorem 30.3 — and no finite-dimensionality is needed.

**`ConcaveFn.clConcave_eq_of_mem_relint_domConcave` is misplaced but has nowhere to go.** It is the
concave mirror of Theorem 7.4 and belongs with `clConcave` in `Duality/ConcaveConj.lean`; that file
is layer C and does not import `RelativeInterior`. It lives in `Normal.lean` until something else
needs it.

### `Tdaf/Analysis/Convex/Saddle/Closure.lean`

§34: **Theorem 34.1**, both halves, with the closedness vocabulary of §33–§34.

```lean
noncomputable def lowerCl (K : U × X → EReal) : U × X → EReal := partialCl₂ (partialCl₁ K)
noncomputable def upperCl (K : U × X → EReal) : U × X → EReal := partialCl₁ (partialCl₂ K)
def LowerClosedFn (K) : Prop := lowerCl K = K
def UpperClosedFn (K) : Prop := upperCl K = K
def FullyClosedFn (K) : Prop := ConvexClosedFn K ∧ ConcaveClosedFn K
noncomputable def saddleSwap (K : U × X → EReal) : X × U → EReal := fun q => -(K (q.2, q.1))
theorem fullyClosedFn_iff : FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K
theorem partialCl₁_saddleSwap (K) : partialCl₁ (saddleSwap K) = saddleSwap (partialCl₂ K)
theorem upperClosedFn_upperCl (Bu) [IsCompatiblePairing Bu] (Bx) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hK : ConcaveConvexFn K) : UpperClosedFn (upperCl K)
theorem lowerClosedFn_lowerCl … : LowerClosedFn (lowerCl K)
```

**Theorem 34.1 is Theorem 33.2 twice and Theorem 30.1 once.** For `F = bifunOfSaddle Bx K`,
Theorem 33.1 gives `⟨Fu, y⟩ = cl₂ K`; Theorem 33.2's first equation turns `cl₁ cl₂ K` into
`⟨u, F* y⟩`; its second equation turns `cl₂ cl₁ cl₂ K` into `⟨(cl F) u, y⟩`; the first equation
again turns `cl₁ cl₂ cl₁ cl₂ K` into `⟨u, (cl F)* y⟩`, and `(cl F)* = F*` closes the loop. Nothing
in the argument is specific to the upper closure except the order of the two closures.

**The lower half is the upper half at the swap.** `saddleSwap K = -K` with the arguments
exchanged satisfies `cl₁ ∘ swap = swap ∘ cl₂` and `cl₂ ∘ swap = swap ∘ cl₁` — both are one
application of `clConcave_neg` / `neg_clConcave` — so `upperCl (saddleSwap K) = saddleSwap
(lowerCl K)` and lower closedness of `K` *is* upper closedness of `saddleSwap K`. The swapped
pairings are `Bx.flip` and `Bu.flip`, so the lower half needs `IsCompatiblePairing Bu.flip` and a
topology on `V` on top of what the upper half needs, and `Bu.flip.flip` needs
`instIsCompatiblePairingFlipFlip` (added to `Duality/Pairing.lean` for exactly this).

**The auxiliary spaces have to be explicit arguments.** `upperCl K` mentions only `U`, `Y` and
`K`; the pairings `Bu` and `Bx` appear only in the hypotheses, so nothing can infer them and they
are taken as explicit arguments with their instance binders attached *to the theorem* rather than
to the section. Putting the instances on a `variable` line and the pairings in the theorem's own
binder list is the shadowing trap recorded under `Adjoint.lean`.

**Fully closed = lower closed and upper closed, in three lines each way.** Forward is rewriting
with `cl₁ K = K` and `cl₂ K = K`; backward is the idempotence of the two partial closures
(Corollary 33.1.1), which the file already has as `convexClosedFn_partialCl₂` and
`concaveClosedFn_partialCl₁`.

### `Tdaf/Analysis/Convex/Saddle/Correspondence.lean`

§33: **Theorem 33.3** with **Corollaries 33.1.2, 33.3.1 and 33.3.2** — the one-to-one
correspondence between closed convex bifunctions and lower closed concave-convex functions, and the
two `Equiv`s that package it.

```lean
theorem eq_of_bracket_eq (hF : ConvexBifun F) (hG : ConvexBifun G) (hFi : ImageClosedBifun F)
    (hGi : ImageClosedBifun G) (h : bracket Bx F = bracket Bx G) : F = G
theorem partialCl₁_bracket (Bu) [IsCompatiblePairing Bu] (Bx) (hF : ConvexBifun F) :
    partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2)
      = fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2
theorem partialCl₂_concaveBracket_adjoint … (hF) (hcl : ClosedBifun F) :
    partialCl₂ (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)
      = fun p : U × Y => bracket Bx F p.1 p.2
theorem lowerClosedFn_bracket … : LowerClosedFn (fun p : U × Y => bracket Bx F p.1 p.2)
theorem exists_unique_convexBifun_bracket_eq … (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = K
theorem exists_unique_bifun_of_closure_pair … (h1 : partialCl₁ Klow = Kup)
    (h2 : partialCl₂ Kup = Klow) : ∃! F : Bifun U X, …
noncomputable def saddleOfBifun (Bx) (F : Bifun U X) : U × Y → EReal := fun p => bracket Bx F p.1 p.2
theorem saddleOfBifun_bifunOfSaddle … ; theorem bifunOfSaddle_saddleOfBifun …
noncomputable def bifunSaddleEquiv :                                          -- Cor 33.1.2
  {F : Bifun U X // ConvexBifun F ∧ ImageClosedBifun F} ≃
    {K : U × Y → EReal // ConcaveConvexFn K ∧ ConvexClosedFn K}
theorem upperClosedFn_partialCl₁ … ; theorem lowerClosedFn_partialCl₂ …
noncomputable def lowerUpperClosedEquiv (Bu) [IsCompatiblePairing Bu]         -- Cor 33.3.2
    (Bx) [IsCompatiblePairing Bx.flip] :
  {K : U × Y → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
    {K : U × Y → EReal // ConcaveConvexFn K ∧ UpperClosedFn K}
```

**Corollary 33.3.2's two round trips are definitional.** `LowerClosedFn K` *is* `cl₂ cl₁ K = K` and
`UpperClosedFn K` *is* `cl₁ cl₂ K = K`, so `left_inv` and `right_inv` of the `Equiv` are the
hypotheses themselves. All the corollary contains is that `cl₁` lands in the upper closed class and
`cl₂` in the lower closed one — the same unfolding once more, since
`lowerCl = cl₂ ∘ cl₁` and `upperCl = cl₁ ∘ cl₂`.

**Corollary 33.1.2 needs both closedness hypotheses named, one per side.** Its round trips are the
two halves of Theorem 33.1: `cl (Fu) = ⟨Fu, ·⟩*` going one way (so `F` must be image-closed) and
Fenchel–Moreau in the second variable going the other (so `K` must be convex-closed). Neither is
free. `saddleOfBifun` is `bracket` uncurried, added only so that the corollary can be stated as a
map.

**Corollary 33.1.3 and the polyhedral support for Corollary 33.2.2** also live here:
`polyhedralFn_bracket` (clause 1, Thm 19.2), `polyhedralFn_neg_bracket` and
`polyhedralFn_concaveBracket` (clause 2, Cor 19.3.1, each factored through a `private` auxiliary
that takes the linear functional and its defining equation as arguments — gotcha 139),
`imageClosedBifun_of_polyhedralBifun` and `eq_conj_bracket_of_polyhedralBifun` (clause 3), plus
`closedBifun_of_polyhedralBifun` and `polyhedralFn_neg_graphFn_adjointBifun` — the last being the
fact the book asserts without proof, that the adjoint of a polyhedral convex bifunction is
polyhedral concave. Support lemmas `PolyhedralFn.add_linear`, `polyhedralFn_compLin` and
`clConcave_eq_of_mem_domConcave` came with them.

**Relocation candidates.** `PolyhedralFn.add_linear` belongs in `Polyhedral/Function.lean` beside
`PolyhedralFn.add` (its proof is layer A — only `Polyhedral.comap`); `polyhedralFn_compLin` and
`clConcave_eq_of_mem_domConcave` belong in `Optimization/Perturbation.lean` beside
`polyhedralFn_mapLin` and `PolyhedralFn.clFn_eq_of_mem_dom`; `dom_concaveBracket` — and the
pre-existing `domConcave_bracket`, currently in `Saddle/Kernel.lean` — belong in `Saddle/Defs.lean`,
since neither has anything to do with relative interiors, and it is `domConcave_bracket`'s absence
from `Correspondence.lean`'s reach that forced Corollary 33.2.2 into `Kernel.lean`;
`closedBifun_of_polyhedralBifun` and `polyhedralFn_neg_graphFn_adjointBifun` belong in
`Optimization/Adjoint.lean`, which would then have to import `Polyhedral/Conjugate.lean` — already
reached transitively through `Lagrangian → Perturbation → Subgradient/Existence`.

**Cut the `Cor3312` sections finely.** Each half of the correspondence uses instances on one side
only — `saddleOfBifun` is closed for free on the `Y` side, `bifunOfSaddle` on the `X` side, and only
the two round trips need Fenchel–Moreau — so a single wide `variable` block trips the
unused-section-variable linter on three declarations at once. Six small sections, each carrying only
what its proofs use, is the fix (cf. gotcha on `omit` in `Adjoint.lean`).

**Uniqueness is Theorem 33.1's inversion formula, not a new argument.** `F u = cl (F u)` for an
image-closed `F`, and `cl (F u) = ⟨Fu, ·⟩*` (`clFn_eq_conj_bracket`), so equal brackets force equal
bifunctions in five rewriting steps. This is why the correspondence is stated against
`ImageClosedBifun` rather than `ClosedBifun`: the bracket cannot see the joint closure.

**The existence half produces a *closed* bifunction, it does not assume one.** The candidate is
`bifunOfSaddle Bx K`; its bracket is `cl₂ K = K` by Theorem 33.1 plus `hlc.convexClosedFn`, and its
slices are conjugates hence closed. Joint closedness then comes from `eq_of_bracket_eq` applied to
`clBifun F` and `F`: both are convex and image-closed, and `adjointBifun_clBifun` plus Theorem 33.2
show their brackets agree.

**The two brackets of a closed convex bifunction are a closure pair.** Splitting
`lowerClosedFn_bracket` into `partialCl₁_bracket` and `partialCl₂_concaveBracket_adjoint` is what
makes Corollary 33.3.1 and Theorem 34.2 available: the pair `(⟨Fu, y⟩, ⟨u, F*y⟩)` satisfies
`cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` on the nose, which is Corollary 33.3.1's hypothesis verbatim.

**`(Bx := Bx)` has to be supplied when the pairing appears only in an instance binder.**
`bracket_concaveAdjointBifun_eq_partialCl₂` and `partialCl₂_concaveBracket_adjointBifun` take `Bx`
implicitly; calling them leaves `IsCompatiblePairing (LinearMap.flip ?m)` stuck. Naming the pairing
in the call is the fix — the same shadowing/inference trap as in `Adjoint.lean`, seen from the other
side.

### `Tdaf/Analysis/Convex/Saddle/Equiv.lean`

§34: **Theorem 34.2** — the equivalence classes of closed saddle-functions are the order intervals
between the two brackets of a closed convex bifunction.

```lean
def SaddleEquiv (K L : U × X → EReal) : Prop :=
  partialCl₁ K = partialCl₁ L ∧ partialCl₂ K = partialCl₂ L
def ClosedSaddleFn (K : U × X → EReal) : Prop :=
  partialCl₁ (partialCl₂ K) = partialCl₁ K ∧ partialCl₂ (partialCl₁ K) = partialCl₂ K
def saddleClass (Klow Kup : U × X → EReal) : Set (U × X → EReal) := {K | Klow ≤ K ∧ K ≤ Kup}
theorem partialCl₂_eq_of_mem_saddleClass (h2 : partialCl₂ Kup = Klow)
    (hK : K ∈ saddleClass Klow Kup) : partialCl₂ K = Klow
theorem saddleEquiv_of_mem_saddleClass / closedSaddleFn_of_mem_saddleClass
theorem exists_unique_bifun_of_closedSaddleFn … (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
```

**The whole theorem is a squeeze.** If `cl₂ K̄ = K̲` then `cl₂ K̲ = cl₂ cl₂ K̄ = cl₂ K̄ = K̲`, so for
`K̲ ≤ K ≤ K̄` monotonicity gives `K̲ = cl₂ K̲ ≤ cl₂ K ≤ cl₂ K̄ = K̲`. Both closures are therefore
constant on the interval, and everything else — one equivalence class, every member closed, the
ends are the lower and upper closed representatives — is a corollary of that one fact. The only new
lemmas needed were `partialCl₁_mono`, `partialCl₂_mono` (`Saddle/Defs.lean`) and `clConcave_mono`
(`Duality/ConcaveConj.lean`).

**Closed is not lower closed.** `ClosedSaddleFn` asks the two closures to be *equivalent* to `K`,
which is Rockafellar's definition and is what allows a whole interval of closed functions with only
two distinguished members. Stating it as the two equations `cl₁ cl₂ K = cl₁ K` and
`cl₂ cl₁ K = cl₂ K` makes it match Corollary 33.3.1's closure-pair hypothesis literally, so the
converse half of Theorem 34.2 is a one-line call with `K̲ := cl₂ K` and `K̄ := cl₁ K`.

**The interval lemmas need no pairing at all.** `partialCl₂_eq_of_mem_saddleClass` uses only
monotonicity and idempotence of `cl₂`, so it lives in a section with topology on `X` alone; the
`cl₁` version needs topology on `U` alone. Keeping the two apart (rather than one section carrying
both) avoids a dozen `omit` lines, and only the last four theorems — the ones that mention a
bifunction — carry the compatible-pairing instances.

### `Tdaf/Analysis/Convex/Operations/Closed.lean`

The layer-B companion to `Operations/Image.lean`, added for §30's Theorem 30.1.

```lean
theorem lowerSemicontinuous_comp (hg : LowerSemicontinuous g) {φ : E → G} (hφ : Continuous φ) :
    LowerSemicontinuous (g ∘ φ)
theorem closedFn_compLin (hg : ClosedFn g) (hA : Continuous A) : ClosedFn (compLin g A)
```

**Mathlib has the other composition.** `Continuous.comp_lowerSemicontinuous` is `g ∘ f` with `f`
lower semicontinuous and `g` continuous *and monotone*; what convex analysis needs is
precomposition, `g ∘ φ` with `φ` continuous. It is three lines from
`lowerSemicontinuous_iff_isOpen_preimage`, and `LowerSemicontinuous.isOpen_preimage` is the form to
reach for.

**`ClosedFn` is not `LowerSemicontinuous`, so `closedFn_iff` has to be split.** The constant-`⊥`
branch survives precomposition definitionally (`(fun _ => ⊥) ∘ A` is again the constant), and the
other branch is the lemma above plus `hne (A x)`. `closedFn_iff` itself lives in `Closure.lean`'s
`section Hull`, so it needs `[AddCommGroup E] [IsTopologicalAddGroup E]` — which
`lowerSemicontinuous_compLin` does *not*, hence the `omit` in front of it.

### `Tdaf/Analysis/Convex/Saddle/Defs.lean`

§33: **Theorem 33.1** in both directions, **Corollary 33.1.1**, and §34's two effective domains.

```lean
structure ConcaveConvexFn (K : U × X → EReal) : Prop where
  concave_fst : ∀ x, ConcaveFn fun u => K (u, x)
  convex_snd : ∀ u, ConvexFn fun x => K (u, x)
def SaddleFn (K : U × X → EReal) : Prop := ConcaveConvexFn K ∨ ConvexConcaveFn K
def dom₁ (K : U × X → EReal) : Set U := {u | ∀ x, ⊥ < K (u, x)}
def dom₂ (K : U × X → EReal) : Set X := {x | ∀ u, K (u, x) < ⊤}
noncomputable def partialConj₂ (Bx) (f : U × X → EReal) : U × Y → EReal :=
  fun p => conj Bx (fun x => f (p.1, x)) p.2
noncomputable def partialCl₂ [TopologicalSpace X] (K : U × X → EReal) : U × X → EReal :=
  fun p => clFn (fun x => K (p.1, x)) p.2
noncomputable def partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : U × X → EReal :=
  fun p => clConcave (fun u => K (u, p.2)) p.1
noncomputable def bracket (Bx) (F : Bifun U X) : U → Y → EReal := fun u y => conj Bx (F u) y
noncomputable def bifunOfSaddle (Bx) (K : U × Y → EReal) : Bifun U X :=
  fun u x => conj Bx.flip (fun y => K (u, y)) x
theorem concaveFn_bracket (hF : ConvexBifun F) (Bx) (y) : ConcaveFn fun u => bracket Bx F u y
theorem clFn_eq_conj_bracket (hF : ConvexBifun F) (u) : clFn (F u) = conj Bx.flip (bracket Bx F u)
theorem convexBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (Bx) : ConvexBifun (bifunOfSaddle Bx K)
theorem bracket_bifunOfSaddle (hK : ConcaveConvexFn K) (p : U × Y) :
    bracket Bx (bifunOfSaddle Bx K) p.1 p.2 = partialCl₂ K p
theorem adjointBifun_eq_concaveConj_bracket (Bu) (Bx) (F) (y) (v) :
    adjointBifun Bu Bx F y v = concaveConj Bu (fun u => bracket Bx F u y) v
```

**`dom₁` and `dom₂` are `∀`, not `∃`.** Rockafellar §34: `dom₁ K = {u | K(u, v) > -∞, ∀ v}`, and
he says in the next sentence that it is *the intersection* of the effective domains of the concave
functions `K(·, v)`. `07-saddle-algebra.md` had recorded the existential version, under which
`dom₁ K` is a union of convex sets and need not be convex. With the universal reading
`ConcaveConvexFn.convex_dom₁` is `convex_iInter` over `ConcaveFn.convex_domConcave`.

**`cl₁` closes concavely.** `partialCl₁` is *not* `partialCl₂` with the factors swapped: for a
concave-convex `K`, `cl₂` closes `K(u, ·)` as a convex function and `cl₁` closes `K(·, y)` as a
concave one. The concave closure `clConcave g = -(cl (-g))` therefore had to exist first; it lives
in `Duality/ConcaveConj.lean`, the first file with both `ConcaveFn` and `clFn` in scope.

**Two supporting lemmas do most of the work.**
`ConvexBifun.convexFn_apply` (added to `Optimization/Perturbation.lean`) says each slice `F u` of a
convex bifunction is convex; it is *not* an instance of `convexFn_compLin`, because `x ↦ (u, x)` is
affine and not linear, so it is `epi_combo` by hand with `a • u + b • u = u`. The file-private
`convexFn_add_coe` says a convex function plus a real-valued affine coordinate is convex; it is
stated against the combination law `l (a • x + b • y) = a * l x + b * l y` rather than against
`LinearMap`, which lets one lemma serve both `p ↦ ⟨p.2, y⟩` and a product projection.

**Higher-order unification bites twice here.** `convexFn_iSup` states its conclusion as
`ConvexFn fun x => ⨆ i, f i x`; leaving `f` implicit makes Lean unfold `iSup` to `sSup (range …)`
and try `ι := ↑(Set.range …)`, which fails with a confusing "application type mismatch". Pass
`(f := fun y p => …)`. Worse, `closedFn_clFn _` against a goal stated through `partialCl₂` sends
`isDefEq` into `clFn`'s `if ∃ x, lscHull f x = ⊥` branch and **times out at 200 000 heartbeats**;
so does `convexFn_clFn` there. Both are fixed by giving the argument explicitly, and the file adds
the `rfl` lemmas `partialCl₂_slice` and `partialCl₁_slice` so `rw` performs the reduction instead
of unification. If a proof mentioning `clFn` or `clConcave` times out, this is the first thing to
suspect.

**Section variables must be minimal or the unused-variable linter fires.** `bracket`, `partialCl₂`
and friends need much less than the usual `[AddCommGroup _] [Module ℝ _]` block — `clFn` needs only
`[TopologicalSpace E]`, `closedFn_clFn` additionally `[AddCommGroup E] [IsTopologicalAddGroup E]`,
and `bracket` needs nothing at all on `U`. The file is therefore cut into many small sections
rather than carrying `omit … in` on half the declarations.

**Instance binders mentioning a section variable cannot be shadowed by an explicit argument.**
`theorem closedFn_bracket [IsContinuousPairing Bx.flip] (Bx : …)` silently refers to *two different*
`Bx`; the instance binder sees the section variable and the body sees the explicit one. Where a
hypothesis mentions the pairing (`closedFn_bracket`, `clFn_eq_conj_bracket`,
`bracket_bifunOfSaddle`) the pairing stays implicit and the instances go on the section's `variable`
line.

**`⟨Fu, ·⟩` is closed and convex with no hypothesis on `F`.** `bracket Bx F u = conj Bx (F u)`, so
`convexFn_conj` and `closedFn_conj` apply directly — properness and convexity of `F` are not
needed. Only `concaveFn_bracket` uses `ConvexBifun F`, and only through `convexFn_iInf_right`.

---

### `Tdaf/Analysis/Convex/Convergence.lean`

Rockafellar §10, Theorems 10.6–10.9, for a *family* `f : ι → E → ℝ` of convex functions on a
convex `C` in a finite-dimensional space. Every statement comes in an `interior` form and a
`_relint` form; the `ri` form is the one the book states and the one downstream sections use.

```lean
theorem exists_forall_abs_le_of_isCompact_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M
theorem exists_forall_lipschitzOnWith_of_isCompact_relint … : ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S
theorem exists_forall_abs_le_and_lipschitzOnWith_of_isCompact_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hbdd : ∀ x ∈ ri C, Bornology.IsBounded (Set.range fun i => f i x))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M) ∧ ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S
theorem exists_tendstoUniformlyOn_of_dense_relint …        -- Thm 10.8
theorem tendstoUniformlyOn_of_tendsto_relint …             -- Thm 10.8, the `∀ x` form
theorem eventually_forall_le_add_of_eventually_le_relint … -- Cor 10.8.1
theorem exists_subseq_tendstoUniformlyOn_relint …          -- Thm 10.9
theorem continuousOn_prod_of_convexOn_relint …             -- Thm 10.7
```

Also the *chart* helpers that carry every `ri`-form proof: `convexOn_chart`,
`mem_relint_of_mem_interior_chart`, `mem_interior_chart_of_mem_relint`,
`chart_subset_interior_chart`, `interior_chart_subset_closure_chart`. The pattern is: transport
along `exists_chart_retraction` into the affine hull's direction subspace, where `ri` becomes
`interior`, apply the `interior` form, transport back.

**This file strengthened `Continuity.lean`**: `exists_chart_retraction` gained a *first* conjunct
`ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V))`, and
`ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset` was factored out of (and
`ConvexOn.exists_lipschitzOnWith_of_isCompact` reproved from) the old monolithic proof.

**Missing, and wanted**: the singleton-family corollaries (`ι = Unit`) of Theorems 10.6 and 10.7.
§35 needs exactly those, and re-deriving them at each use site is the wrong shape.

### `Tdaf/Analysis/Convex/Recession/ConeHull.lean`

Rockafellar §8 Theorem 8.2 in cone form, and §9 Theorems 9.6, 9.7, 9.8 with Corollaries 9.6.1 and
9.8.1. **`PointedCone.hull ℝ` is the convex cone generated by a set** — nothing new is defined for
it, and `PointedCone ℝ E = Submodule ℝ≥0 E` brings monotonicity, idempotence,
`Submodule.span_induction` and the Galois insertion from Mathlib for free.

```lean
theorem coe_hull_of_convex (hS : Convex ℝ S) :
    (PointedCone.hull ℝ S : Set E) = insert 0 {y | ∃ t : ℝ, 0 < t ∧ y ∈ t • S}
def closedConeOver (C : Set E) : Set (ℝ × E)
theorem closure_coe_hull_prodMk_one (hC : Convex ℝ C) (hCc : IsClosed C) (hne : C.Nonempty) : …
theorem closure_coe_hull …                      -- Thm 9.6
theorem isClosed_coe_hull_of_isBounded …        -- Cor 9.6.1
noncomputable def posHomGen (f : E → EReal) : E → EReal :=
  ofEpi (PointedCone.hull ℝ (epi f) : Set (E × ℝ))
theorem posHomGen_isGreatest (f : E → EReal) :
    IsGreatest {g | PosHomogeneous g ∧ ConvexFn g ∧ g 0 ≤ 0 ∧ g ≤ f} (posHomGen f)
theorem lscHull_posHomGen_eq …, posHomGen_eq_iInf_smulRight …        -- Thm 9.7
theorem closure_convexHull_union_and_recessionCone …                 -- Thm 9.8
theorem isClosed_convexHull_union_of_recessionCone_eq …              -- Cor 9.8.1
```

`posHomGen` is **the** positively homogeneous convex function generated by `f` — the §5 operator,
canonical here and *not* redefined anywhere else. `convexFn_posHomGen`, `posHomogeneous_posHomGen`,
`posHomGen_le`, `posHomGen_apply_zero_le` and `posHomGen_isGreatest` carry **no** hypothesis on `f`;
`le_posHomGen` needs `ConvexFn g` on the minorant, because the hull description forces
`Submodule.span_induction` through sums. `Duality/Level.lean` holds the ray description
`posHomGenCone f = {0} ∪ ⋃_{a>0} a • epi f`, `posHomGenCone_eq_coe_hull` and `posHomGen_eq_ofEpi`
identifying the two for convex `f`, and all the formulas that read values off it.

Also here, and really belonging in `Operations/Epi.lean`: `epi_ofEpi_subset_of_isEpiLike`,
`ofEpi_iUnion`, `ofEpi_union` (both in *function* form, `ofEpi (⋃ i, F i) = ⨅ i, ofEpi (F i)`),
`smul_epi_ofEpi`.

**Findings.** Theorem 8.2 in cone form needs no finite-dimensionality — the proof rests on the
identity `x + a•p.2 − (a*p.1)•x ∈ C` for `0 ≤ a`, `a*p.1 ≤ 1`, which covers the `λ > 0` and the
recession branch uniformly. Theorem 9.8 does **not** need Corollary 6.5.1: only the easy inclusion
of "slice of the closure = closure of the slice" is used, and the reverse comes free from
`closedConeOver_add_eq_closure_coe_sup`. Corollary 9.2.2 (in `Recession/Closedness.lean`) is
formalised as `epi (f □ g) = epi f + epi g`, from which the book's "the infimum is attained" falls
out (`exists_add_eq_of_infConv_le`).

**Not here**: Corollary 9.2.1 and the `m`-fold forms of 9.8/9.8.1 (contentless induction, no
consumer); Corollary 9.7.1 (it is Theorem 9.7 applied to `δ(·|C) + 1`, but it is a statement about
gauges, so it belongs to §15 — three lines from `lscHull_posHomGen_eq`); Corollary 9.8.2
(superseded by `Caratheodory.lean`); Corollary 9.8.3 (needs `convHullFn` for a finite *family*,
which is §5 work).

### `Tdaf/Analysis/Convex/Duality/Level.lean`

Rockafellar §13's conjugate-and-recession part: **Theorem 13.5** (the support function of
`{x | f x ≤ 0}`), **Theorem 13.4** (the lineality space of `f*`), **Corollary 13.3.1**
(co-finiteness), and the §5 formulas for `posHomGen` stated against the ray description.

```lean
def posHomGenCone (f : E → EReal) : Set (E × ℝ) := {0} ∪ ⋃ a > (0 : ℝ), a • epi f
theorem posHomGenCone_eq_coe_hull (hf : ConvexFn f) :
    posHomGenCone f = (PointedCone.hull ℝ (epi f) : Set (E × ℝ))
theorem posHomGen_eq_ofEpi (hf : ConvexFn f) : posHomGen f = ofEpi (posHomGenCone f)
theorem posHomGen_apply_of_ne_zero (hf : ConvexFn f) (hx : x ≠ 0) :
    posHomGen f x = ⨅ a > (0 : ℝ), (a : EReal) * f (a⁻¹ • x)
theorem dom_posHomGen (hf : ConvexFn f) : dom (posHomGen f) = {0} ∪ ⋃ a > (0 : ℝ), a • dom f
theorem posHomGen_levelOneLift (hf : ConvexFn f) (hdom : (dom f).Nonempty) :
    posHomGen (levelOneLift f) = hom f
theorem conj_posHomGen (B) (f) : conj B (posHomGen f) = indicatorFn {y | conj B f y ≤ 0}
theorem clFn_posHomGen (g : F → EReal) :
    clFn (posHomGen g) = supportFn B {x | conj B.flip g x ≤ 0}
theorem supportFn_setOf_le_zero (hf : ConvexFn f) (hc : ClosedFn f) :
    supportFn B {x | f x ≤ 0} = clFn (posHomGen (conj B f))
theorem clFn_hom (hf : ConvexFn f) (hdom : (dom f).Nonempty) : …     -- Cor 13.5.1
```

`conj_posHomGen` and `clFn_posHomGen` carry **no hypothesis at all** — `posHomGen g` is positively
homogeneous, convex and nonpositive at the origin whatever `g` is, so Corollary 13.2.1 applies
directly and the improper cases are already inside it. `le_ofEpi_posHomGenCone` is the maximality
half that the ray description gives *without* convexity of the minorant, which is what
`supportSet_posHomGen` would want if `le_posHomGen` were unavailable.

Also here: `posHomogeneous_ofEpi` (a cone's `ofEpi` is positively homogeneous — no convexity),
`posHomogeneous_pairing`, `convexFn_pairing`, Theorem 13.4's `linealitySpaceFn_conj`, and Corollary
13.3.1's `Cofinite` / `cofinite_iff_dom_conj_eq_univ`.

**Theorem 13.3's dual form and Corollary 13.3.4(a) are here for the same reason.**
`recessionFn_eq_supportFn_dom_conj` — the recession function of a closed proper convex `f` is the
support function of `dom f*` — is what Corollary 13.3.1 runs on, and `zero_mem_closure_dom_conj_iff`
(**Cor 13.3.4(a)** at the origin, which is also the first sentence of **Thm 27.1(i)**) is
Theorem 13.1 for `dom f*` composed with it. `Recession/Conjugate.lean`, where they would sit more
naturally, is *below* this file in the import graph.

### `Tdaf/Analysis/Convex/Saddle/Kernel.lean`

Rockafellar §34's finite-dimensional half: Theorem 34.2's `ri` and `dom` clauses, Corollaries
34.2.1–34.2.4, Theorems 34.3–34.5 and Corollary 34.5.1. It also **reproves Theorem 34.1 without
duality** (`lowerCl_idem`, `upperCl_idem` — four lines from monotonicity and idempotence of
`cl₁`/`cl₂`), which drops it from layer C to layer B. §33's Corollaries 33.2.1 and **33.2.2** are
here too, because `domConcave_bracket` is — see the relocation note under
`Saddle/Correspondence.lean`.

**Corollary 33.2.2 splits into two halves with different hypotheses.**
`bracket_eq_concaveBracket_adjointBifun_of_mem_domBifun` (the `u`-side) needs only
`PolyhedralBifun F`, no properness: Theorem 33.2's first equation needs only convexity,
`⟨F·, y⟩` is polyhedral concave for any polyhedral convex `F`, and
`PolyhedralFn.clFn_eq_of_mem_dom` covers the improper branch.
`bracket_eq_concaveBracket_adjointBifun_of_mem_domConcaveBifun` (the `y`-side) runs through
`F** = cl F = F`, so it needs properness — and it needs `V` and `Y` finite-dimensional as well as
`U` and `X`, since the concave bracket is a partial minimisation over `V` and Corollary 19.3.1
wants both factors finite-dimensional. In `ℝⁿ` that hypothesis is invisible; this is D0 again.
`bracket_eq_bot_and_concaveBracket_eq_top` pins the book's vague "one of the quantities is `+∞`
and the other `-∞`": it is always `⟨Fu, y⟩ = -∞` with `⟨u, F*y⟩ = +∞`, and that needs neither
polyhedrality nor properness.

```lean
def domSaddle (K : U × X → EReal) : Set (U × X) := dom₁ K ×ˢ dom₂ K
def ProperSaddleFn (K : U × X → EReal) : Prop
structure ConvexSliceStructure … ; structure SaddleStructure …
theorem closedSaddleFn_iff_saddleStructure …                    -- Thm 34.3
def kernelSet (K : U × X → EReal) : Set (U × X) := ri (dom₁ K) ×ˢ ri (dom₂ K)
noncomputable def kernel (K : U × X → EReal) : U × X → EReal :=
  fun p => if p ∈ kernelSet K then K p else ⊤
theorem kernel_eq_iff …                                          -- "same rectangle ∧ EqOn there"
theorem saddleEquiv_iff_kernel_eq …                              -- Thm 34.4
def SimpleSaddleFn … ; theorem exists_unique_saddleEquiv_class_of_kernel …   -- Thm 34.5
noncomputable def lowerSimpleExt … ; noncomputable def upperSimpleExt …
theorem exists_unique_saddleEquiv_class_of_finite …              -- Cor 34.5.1
theorem mem_saddleClass_simpleExt_iff …                          -- Cor 34.2.4
theorem domConcave_bracket (Bx) (F : Bifun U X) (y : Y) :
    domConcave (fun u => bracket Bx F u y) = domBifun F
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_relint …   -- Cor 33.2.1
theorem lowerClosedFn_lowerSimpleExt … ; theorem upperClosedFn_upperSimpleExt …
theorem exists_unique_bifun_of_simpleExt …                       -- Cor 33.3.3
```

**Two §33 corollaries land here rather than in `Correspondence.lean`**, because they need this
file's machinery: Corollary 33.2.1 needs relative interiors, and Corollary 33.3.3 needs the simple
extensions. Both are short. 33.2.1 is Theorem 33.2 (the two brackets differ by `cl₁`) plus "a
concave function meets its closure on `ri` of its domain", once `domConcave_bracket` says the
concave domain of `u ↦ ⟨Fu, y⟩` is `dom F` on the nose for *every* `y` — the bracket is `⊥`
exactly where the slice `F u` is identically `⊤`. 33.3.3 is Corollary 33.3.1 applied to the closure
pair `partialCl₁_lowerSimpleExt` / `partialCl₂_upperSimpleExt`, which this file already proves for
Corollary 34.2.4.

**The kernel is a total function, not a `Set.restrict`.** Equalities of subtype-restrictions are
ill-typed unless the two rectangles are already known equal, so Theorem 34.4 would split into a
rectangle equality plus a transport. `⊤` off `kernelSet` is faithful because a proper concave-convex
`K` is finite on `ri (dom K)`. Defining the kernel as its *domain* would refute Theorem 34.4 — `K`
and `K + 1` would share a kernel without being equivalent.

**Relocation candidates.** The file carries a §6/§7 block that belongs elsewhere:
`lscHull_eq_of_eqOn_relint_dom`, `clFn_eq_of_eqOn_relint_dom`,
`clConcave_eq_of_eqOn_relint_domConcave`, `Convex.relint_eq_of_subset_of_subset_closure` (the
Cor 6.3.1 sandwich), `ConcaveFn.clConcave_eq_of_mem_relint_domConcave` and
`.clConcave_eq_of_notMem_closure_domConcave`, `clFn_eq_bot_of_eq_bot`, `clConcave_eq_top_of_eq_top`,
`clFn_const_top`, `clConcave_const_bot`, `domConcave_neg`, `concaveFn_const`,
`ConcaveFn.restrictConcave`, `dom_restrict_coe`, and the `closedFn_restrict_coe` family; plus
`dom₁/₂_saddleSwap`, `dom₁_mono`, `dom₂_anti`, `domSaddle`, `ProperSaddleFn`, `lowerCl_idem`,
`upperCl_idem` and the Cor 34.2.2 lemmas, which belong in `Saddle/{Defs,Closure,Equiv}.lean`.
The blocker for the first group is that `Duality/ConcaveConj.lean` is layer C and does not import
`RelativeInterior`; the fix is to split its `clConcave` block — which needs only `Closure.lean` and
`Concave.lean` — into a `ConcaveClosure.lean` that `RelativeInterior.lean` can import.

**Corrections.** Corollary 34.2.1's `dom L = dom K` clause needs no closedness, only
`dom₁_partialCl₂` / `dom₂_partialCl₁`. Corollary 34.2.4 needs neither Corollary 33.3.3 nor joint
continuity — separate continuity in each variable on the closed `C`, `D` suffices. Convexity of `D`
is not a hypothesis of `concaveConvexFn_lowerSimpleExt`: `ConvexOn ℝ D` already contains it
(convexity of `C` *is* needed, for the slice over `x ∉ D`). OCR: in Theorem 34.3's proof the first
two displayed relations print `K` where `K̲` is meant.

**Not here**: Corollary 33.2.2, which needs polyhedral bifunctions. Theorem 34.2's
`dom K = dom F × dom F*` is formalized in saddle-function terms (`domSaddle`, invariant under both
closures and under equivalence); the literal bifunction phrasing needs `domBifun`, which lives in
`Optimization/Perturbation.lean` and is outside this module's import closure.

### `Tdaf/Analysis/Convex/HullDirections.lean`

Rockafellar's `conv S` for a set `S` that mixes **points and directions** (§17), the object the
rest of §18 is stated in.

```lean
def convexHullPD (P : Set E) (D : Set E) : Set E := convexHull ℝ P + PointedCone.hull ℝ D
theorem isLeast_convexHullPD …    -- it *is* Rockafellar's operator: the least convex set
                                  -- containing `P` and receding in every direction of `D`
def halfLine (x y : E) : Set E    -- `conv` of one point and one direction
def coneOverPD … ; theorem convexHullPD_eq_slice …   -- the D7 homogenisation dictionary
theorem exists_of_mem_convexHullPD …                 -- Thm 17.1 in this vocabulary
theorem IsCompact.isCompact_convexHullPD …
```

`convexHullPD_eq_slice` and `Polyhedral/Defs.lean`'s `slice_hull_union` are literally the same
theorem — `liftPD P D` is definitionally `liftAt 1 P ∪ liftAt 0 D` — duplicated because
`Polyhedral/Defs.lean` imports only `Polyhedral/Cone.lean` and would have to take on
`Caratheodory` and `Recession/Cone` to reuse the §17 version. Arbitrate before adding a third.

### `Tdaf/Analysis/Convex/Representation.lean`

The rest of §18: **Theorem 18.3** (`IsFace.eq_convexHullPD`) and Corollary 18.3.1, **Theorem 18.4**
in general, **Theorem 18.5** with Corollaries 18.5.2–18.5.3, and **Straszewicz's Theorem 18.6**,
which Mathlib does not have.

```lean
def ContainsNoLine (C : Set E) : Prop
def IsExtremeDirection (C : Set E) (y : E) : Prop ; def extremeDirections (C : Set E) : Set E
def IsAffineHalf (C : Set E) : Prop
theorem IsFace.eq_convexHullPD …                              -- Thm 18.3
theorem convexHullPD_extremePoints_extremeDirections …         -- Thm 18.5
theorem extremePoints_subset_closure_exposedPoints …           -- Thm 18.6
theorem closure_exposedPoints_eq_closure_extremePoints …       -- Thm 18.6, the equality form
```

**Corrections.** Theorem 18.3 needs neither Theorem 6.4 nor the positive-coefficient description of
`ri (conv S)`: the point half is `IsExtreme.mem_convexHull_inter` and uses only the definition of an
extreme set; the direction half is an induction over the cone hull carrying a scaling parameter, and
needs only Theorem 8.3 and Corollary 18.1.1. Theorem 18.4's two exceptions are one predicate —
allowing the functional in `IsAffineHalf` to be `0` makes "affine set" the degenerate case of
"closed half of an affine set". Theorem 18.5's `dim C ≤ 1` case is *not* trivial in Lean (the
unbounded one-dimensional case needs `exists_eq_halfLine`), but the induction is simpler than the
book's: Minkowski discharges the bounded case in every dimension. Straszewicz is cleaner with a
nearest-point projection than with Rockafellar's `ε` — project `x` onto `conv (cl (exp C))`, set
`d = x - v`, `λ = (r²+1)/(2‖d‖²)`, `y = x - λ•d`; no Hahn–Banach, no Riesz, no unit normalisation.

**Layer deviation.** Straszewicz's core needs a genuine inner product; the public statements are
recovered for arbitrary finite-dimensional real normed `E` by transporting through Mathlib's
`toEuclidean`, so nothing downstream inherits the restriction.

**Not here**: Theorems 18.7, 18.8 and Corollary 18.7.1, which are in `Exposed.lean` and
`Tangent.lean`. The definition of an *exposed direction* was indeed what was missing; the
"dimension bookkeeping" this entry used to name as the second blocker turned out not to exist — see
`Exposed.lean` below. **Theorem 11.2 was never the blocker** either — it is
`exists_separates_of_isOpen_of_disjoint_affine` in `Separation.lean`.

### `Tdaf/Analysis/Convex/Exposed.lean`

**Theorem 18.7 and Corollary 18.7.1**, on the strength of a definition the book leaves informal.

```lean
def IsExposedDirection (C : Set E) (y : E) : Prop
def exposedDirections (C : Set E) : Set E
theorem exists_forall_sub_le_mul_sub …
theorem closure_convexHullPD_exposedPoints_exposedDirections …     -- Thm 18.7
theorem closure_coneHull_exposedDirections …                      -- Cor 18.7.1
```

**Theorem 18.7 needs no dimension bookkeeping and no dimension reduction.** The book opens "we can
assume for simplicity that `C` is `n`-dimensional in `Rⁿ`, and that `n ≥ 2`", then extends an
`(n-2)`-dimensional affine set inside a supporting hyperplane via Theorem 11.2. All of that is
unnecessary: the extension is *exactly* the assertion that some `g - c·f` is maximised over `C` at
`x`, and `exists_forall_sub_le_mul_sub` produces `c` by an elementary one-dimensional argument — the
difference quotients on the two sides of the slice are separated, and `c` is the sup on the far
side. The formal statement carries no dimension hypothesis at all. Its endgame is
bounded/unbounded, not the book's line/segment/half-line trichotomy: Minkowski plus Straszewicz
settle the bounded case in *every* dimension, and only the unbounded case uses `dim C' ≤ 1`.

**Corollary 18.7.1's "containing more than just the origin" is unnecessary.** For `K = {0}`,
`exposedDirections {0} = ∅` and `PointedCone.hull ℝ ∅ = {0}`. What that hypothesis really buys is
`exposedPoints K = {0}`, and that follows from Theorem 18.7 itself.

**Relocation candidate**: `exists_forall_sub_le_mul_sub` is a pure convexity/multiplier statement
with no reference to faces or exposedness, and is the finite-dimension-free substitute for "extend
a codimension-two affine set to a hyperplane". It belongs in `Separation.lean`.

### `Tdaf/Analysis/Convex/Tangent.lean`

**Theorem 18.8**: a closed convex set with the origin in its interior is the intersection of its
tangent half-spaces.

```lean
def IsSupportingAt (C : Set E) (y : F) (x : E) : Prop
def IsTangentAt (C : Set E) (y : F) (x : E) : Prop
theorem exists_isTangentAt_lt_of_zero_mem_interior …              -- Thm 18.8, separating form
theorem eq_iInter_tangent_halfSpaces …                            -- Thm 18.8
```

**Theorem 18.8 does not sit behind Theorem 18.7, and outside `Rⁿ` it needs reflexivity.** The book
applies Corollary 18.7.1 to the epigraph of the support function of `C` in one dimension higher.
This file goes through the polar instead: `C°` is compact when `0 ∈ int C`, Minkowski and
Straszewicz apply to `C°`, and the exposed points of `C°` *are* the normals of the tangent
half-spaces. Neither Theorem 18.7 nor Corollary 18.7.1 is used. The one step the book cannot see is
that an exposed point of `C° ⊆ E*` is exposed by a functional *on `E*`*, which has to be identified
with a point of `E`: that is `exists_forall_apply_eq` in `Duality/Pairing.lean`, invisible in `Rⁿ`.

`Tangent.lean` deliberately sits outside `Representation.lean`'s import closure — it is a statement
about the polar. The private `smul_div_norm_mem_closedBall` is a normed-space triviality; drop it if
Mathlib turns out to have an equivalent.

### `Tdaf/Analysis/Convex/Duality/Gauge.lean`

§15 in full except Theorem 15.3, plus **Theorems 14.6, 14.7 and Corollary 14.6.1**, which are
stated here because their content is §15's.

**Corollary 14.6.1 cannot live in `Duality/Polar.lean`.** It consumes `polarCone_linealitySpace`,
which is here, and `Gauge.lean` imports `Polar.lean`. The `finrank` API this file's docstring used
to say it would need turns out to be six lines of rank–nullity for `F → M*`
(`polarSubmodule`, `finrank_add_finrank_polarSubmodule`), and
`vectorSpan_eq_span_of_zero_mem` — Theorem 1.1 in the form the corollary uses — comes with them and
belongs in the project's §1 material.

**Rockafellar's third relation, `rank C° = rank C`, is not independent content**: it is the
difference of the other two, both of which read `n`. It is recorded as a docstring remark rather
than a theorem.

```lean
noncomputable def gaugeFn (C : Set E) : E → EReal :=
  fun x => ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal)
def IsGauge … ; def IsNorm … ; def AbsorbsAll … ; def RayFree …
noncomputable def polarGauge … ; noncomputable def polarFn … ; noncomputable def obverse …
theorem polarGauge_polarGauge …  -- Thm 15.1, `k°° = cl k`
theorem polarFn_polarFn …        -- Thm 15.4, `f°° = cl f`
theorem obverse_obverse … ; theorem conj_eq_obverse_polarFn …   -- Thm 15.5
def gaugeEquiv … ; def polarGaugeEquiv … ; def polarFnEquiv …  -- the three correspondences
```

**`gaugeFn` is a third gauge, deliberately.** Mathlib's `gauge` is `ℝ`-valued and returns
`sInf ∅ = 0` off the absorbed set, where §15 needs `+∞`; `egauge ℝ≥0` *is* Rockafellar's gauge but is
`ℝ≥0∞`-valued, and Mathlib has no lemma commuting `ENNReal.toEReal` with `iInf`, so reusing it
would mean building that bridge plus `ℝ≥0`-vs-`ℝ` smul-set glue before §15 could start.
`gaugeFn_eq_gauge` records the agreement under absorbency.

**Corrections.** Theorem 14.7 needs no closedness and neither Theorem 13.5 nor 9.7 — scale
`x ↦ (α/f x)•x` into the level set for one inclusion, Fenchel's inequality for the other; it holds
for any nonnegative convex `f` with `f 0 ≤ 0`. Theorem 15.5 needs no cone in `R^(n+2)`: it
collapses to `obverse f x = γ((x,1) | epi f)` plus one level-set comparison, the biggest
simplification in the file. Theorem 15.1's `k°° = cl k` is the special case of Theorem 15.4 in which
the `1 +` is invisible to a positively homogeneous function. Theorem 14.5's second assertion needs
only `0 ∈ C`; `gaugeFn {k ≤ 1} = k` needs only nonnegativity, positive homogeneity and `k 0 = 0`;
Theorem 14.6 needs only the bipolar theorem, via `0⁺C = (C°)°`. Rockafellar's admissible set for
`f°` is **not closed in ℝ** — at `μ = 0` the convention `0·(+∞) = 0` imposes `⟨x,y⟩ ≤ 1` where
`f x = +∞`, which nearby positive `μ` do not — so `polarFn` is defined in the epigraph form, with
`polarFn_apply_eq` proving the infima agree.

**Not here**: Theorem 15.3 and Corollaries 15.3.1–15.3.2, the one genuinely unbuilt piece of §15 —
they need the nondecreasing lsc convex functions on `[0, +∞]` and their *monotone conjugate*, a
one-dimensional theory the project does not have. Also Corollary 14.6.1 (dimension and lineality
arithmetic on top of `polarCone_linealitySpace`).

**Lemmas that belong in other files and will name-clash if added there**: `convex_polarSet`,
`polarSet_closure` (→ `Duality/Polar.lean`); `nonneg_of_mem_closure_epi`, `lscHull_nonneg`,
`clFn_eq_lscHull_of_nonneg`, `clFn_nonneg`, `epi_clFn_of_nonneg`, `isClosed_epi_of_closedFn`,
`closedFn_of_isClosed_epi`, `closedFn_iff_isClosed_epi` (→ `Closure.lean`); `mk_mem_smul_epi_iff`,
`mk_one_mem_epi_iff` (→ `Operations/Epi.lean`); `UpClosed`, `biInf_coe_le_coe_iff_forall_lt`,
`biInf_coe_le_coe_iff`, `zero_le_biInf_coe`, `le_coe_of_forall_gt_le`, `biInf_coe_pos_ge_eq`,
`eq_of_forall_pos_le_iff` (→ `Order/EReal.lean`); `mulPairing`, `epiPairing`, `epiPairing_flip`,
`vNeg` (→ `Duality/Pairing.lean`).

### `Tdaf/Analysis/Convex/Saddle/Continuity.lean`

§35's continuity half: **Theorems 35.1 and 35.2**.

```lean
structure ConcaveConvexOn (C : Set U) (D : Set X) (K : U × X → ℝ) : Prop where
  concave_fst : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)
  convex_snd  : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x)
theorem exists_forall_abs_le_and_lipschitzOnWith_prod …        -- Thm 35.2
theorem ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact …  -- Thm 35.1, Lipschitz clause
theorem ConcaveConvexOn.continuousOn …                         -- Thm 35.1, continuity clause
theorem exists_isCompact_mem_nhdsWithin_relint …               -- `ri C` is locally compact
```

`ConcaveConvexOn`'s two fields are exactly the two unbundled hypotheses `Saddle/Kernel.lean`'s
`concaveConvexFn_lowerSimpleExt` takes, so `hK.concave_fst` and `hK.convex_snd` extend `K` to all
of `U × X` when that is wanted.

**Theorem 35.2 is Theorem 10.6 applied four times.** Twice to bound the family — once in each
variable, the second time consuming the first — and twice to make it equi-Lipschitz; the families
are indexed by `ι × ↑T` in the concave variable and `ι × ↑S` in the convex one. The concave variable
reaches §10 through `-K`, which is what `bddAbove_range_neg_iff`, `bddBelow_range_neg_iff` and
`lipschitzOnWith_neg_iff` are for.

**The Lipschitz constant is `k₁ + k₂`, not the book's `2(α₁ + α₂)`.** Mathlib's product metric is the
*supremum* metric, so no factor is paid passing between the coordinate distances and the distance
on the product.

**`exists_isCompact_mem_nhdsWithin_relint` belongs in `RelativeInterior.lean`**; it is about a
single convex set, and it is what turns "Lipschitz on every compact rectangle" into "continuous on
`ri C ×ˢ ri D`".

**Theorems 35.3, 35.4 and 35.5 are here too**, with the two lemmas they run on:

```lean
theorem exists_isCompact_collar_relint (hC : Convex ℝ C) (hS : IsCompact S) (hSC : S ⊆ ri C) :
    ∃ (ε : ℝ) (S' : Set E), 0 < ε ∧ IsCompact S' ∧ S ⊆ S' ∧ S' ⊆ ri C ∧
      ∀ y ∈ ri C, ∀ x ∈ S, dist y x ≤ ε → y ∈ S'
theorem uniformCauchySeqOn_of_equiLipschitz …     -- the metric core of Thms 10.8 and 35.4
theorem continuousOn_prod_of_concaveConvexOn …    -- Thm 35.3 (and `…'`, the headline form)
theorem uniformCauchySeqOn_prod_of_dense …
theorem exists_tendstoUniformlyOn_prod_of_dense … -- Thm 35.4 (and `…'`, `tendstoUniformlyOn_…`)
theorem exists_subseq_tendstoUniformlyOn_prod …   -- Thm 35.5
```

**§10 transports to `ri` by a chart; §35 cannot.** `Convergence.lean` proves each theorem for an
*open* convex set and pulls it back along `exists_chart_retraction`. That route is closed here: the
chart of `C ×ˢ D` is not the product of the charts of `C` and of `D`, and it is the product
structure the concave-convex hypothesis lives on. So 35.3–35.5 are proved directly in `ri`, and
what replaces `IsCompact.exists_cthickening_subset_open` is `exists_isCompact_collar_relint` —
`cthickening ε S ⊆ U` is *false* relatively, since points off the affine hull of `C` are near `S`
and not in `ri C`, so the collar has to be a set rather than a thickening. Its proof is the chart
again, and it belongs in `RelativeInterior.lean` with the other one.

**Theorem 35.4 takes an arbitrary dense `A ⊆ ri C ×ˢ ri D`, not a product `C' ×ˢ D'`.** Theorem 35.2
does need a product — it bounds one variable at a time — but the diagonal extraction in Theorem 35.5
produces a *countable* dense set, and a countable dense subset of a product is not a product.
`exists_tendstoUniformlyOn_prod_of_dense'` recovers the book's form.

**Not here**: Theorems 35.6–35.10, the §23/§24/§25 half of the section; 35.9 and 35.10 additionally
need Rademacher.

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
* **Nothing in the backbone may depend on Rockafellar** (design decision D10 in `00-overview.md`).
  Names are mathematical, never bibliographic; statements are the natural general ones rather than
  the book's packaging; a module docstring leads with what the module is *about* and puts
  "Rockafellar §35" in its `## References` section. Per-declaration doc comments should still cite
  "**Rockafellar, Theorem 23.4**" — that is a citation, not a dependency — but the statement has to
  read as mathematics without it. A theorem worth having in the book's own packaging is a
  *surface* theorem, proved by specializing backbone lemmas.

---

### `Tdaf/Analysis/Convex/Saddle/Minimax.lean`

Rockafellar §36 in full, and §37 through Corollary 37.1.1: saddle-points, the two iterated
extrema, the Lagrangian of a closed convex bifunction, and the two conjugate saddle-functions.

```lean
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop
def IsSaddlePointOn (C : Set U) (D : Set X) …
noncomputable def maximin (K) : EReal := ⨆ u, ⨅ x, K (u, x)
noncomputable def minimax (K) : EReal := ⨅ x, ⨆ u, K (u, x)
def HasSaddleValue (K) : Prop := maximin K = minimax K
noncomputable def saddleLagrangian (Bu) (F : Bifun U X) : V × X → EReal   -- Thm 36.5
def flipBifun … ; noncomputable def inverseBifun …                     -- `F_*`
noncomputable def lowerConjSaddle … ; noncomputable def upperConjSaddle … -- `K̲*`, `K̄*`
def bifunSaddleClass …                                                 -- `Ω(F)`
theorem maximin_le_minimax …                                           -- Lemma 36.1
theorem isSaddlePoint_iff_attained …                                   -- Lemma 36.2
theorem maximin_eq_biSup_biInf … ; theorem minimax_eq_biInf_biSup …     -- Thm 36.3
theorem SaddleEquiv.maximin_eq … ; theorem SaddleEquiv.isSaddlePoint_iff …  -- Thm 36.4
theorem exists_unique_closedBifun_saddleLagrangian_eq …                -- Thm 36.5
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian …               -- Thm 36.6 = Cor 29.3.1
theorem isSaddlePoint_lagrangian_iff …                                 -- **Thm 29.3**
theorem isSaddlePoint_lagrangian_iff_normal_and_optimal …              -- **Cor 30.5.1**
theorem upperConjSaddle_eq_saddleLagrangian …                          -- Thm 37.1, 1st equation
theorem lowerConjSaddle_eq_bracket_inverseBifun …                      -- Thm 37.1, 2nd equation
theorem concaveConvexFn_upperConjSaddle … ; theorem upperClosedFn_upperConjSaddle …  -- Cor 37.1.1
```

**Two items other modules list as blocked come out of this one.** `Optimization/Lagrangian.lean`
records Theorem 29.3 as missing and `Optimization/Normal.lean` records Corollary 30.5.1 as
"needs §36" — both are proved here.

**`HasSaddleValue` must not build in finiteness.** The book calls the common value the saddle-value
when the two iterated extrema are *equal*, and states finiteness separately (Cor 36.3.1, Cor 37.1.3,
Thm 37.3). Folding finiteness into the definition would make Corollary 36.3.1 vacuous, so it stays a
separate conclusion (`IsSaddlePoint.exists_maximin_eq_coe`).

**The outer restriction in Theorem 36.3 is free; only the inner one costs anything.**
`maximin_eq_biSup_dom₁` and `minimax_eq_biInf_dom₂` have *zero* hypotheses, because
`u ∉ dom₁ K ↔ ∃ x, K (u, x) = ⊥`. The inner restriction to `ri` is what needs Corollary 7.3.1 and
the Theorem 34.3 sandwich.

**Rockafellar's `F_*` is a flip *composed with* a negation, and the two halves must stay
separate.** `flipBifun` preserves convexity and closedness; `inverseBifun` swaps convex ↔ concave.
Theorem 36.5 wants the first, Theorem 37.1 the second.

**`(F_*)^* = (F^*)_*` is a definition here, not a lemma.** The backbone has no adjoint of a
*concave* bifunction in the direction Rockafellar needs. Defining the object as
`inverseBifun (adjointBifun Bu Bx F)` makes his commutation a triviality and lets Theorem 33.3
(`lowerClosedFn_bracket`) apply to it verbatim. §38 should be planned the same way.

**Not here**: Corollary 37.1.2 (and so 37.1.3), which needs `K̄*` exhibited as the `concaveBracket`
of the adjoint of `F_*^*` — i.e. the biadjoint identity `(F_*^*)^* = F_*`, Theorem 30.2-flavoured
work the backbone does not have; Theorem 37.2, which needs **Theorem 6.8**; and Theorems 37.3–37.6.
The subgradient form of Kuhn–Tucker, `(0,0) ∈ ∂L(v̄, x̄)`, needs §35's `∂L = ∂₁L × ∂₂L`, which is
also absent — `isSaddlePoint_lagrangian_iff` gives the equivalent "optimal solution plus
Kuhn–Tucker vector" form instead.

**Relocation candidates.** `ConvexFn.exists_mem_relint_dom_lt` and
`ConvexFn.biInf_eq_iInf_of_relint_dom_subset` (Corollary 7.3.1) belong in `RelativeInterior.lean`;
`iSup_clConcave_eq_iSup` and `concaveConj_clConcave` (Theorem 12.2's first half, concave side)
belong in `Duality/ConcaveConj.lean`.

### `Tdaf/Analysis/Convex/Bifunction/Algebra.lean`

The **convex algebra** of bifunctions: the operations that mirror the linear algebra of linear
maps, and the inner product that adjoints move across. §38, except Theorem 38.2 with Corollary
38.2.1 and Corollaries 38.4.1 and 38.5.1.

```lean
noncomputable def infConvBifun …    -- `F₁ □ F₂`, the analogue of `A₁ + A₂`
noncomputable def smulRightBifun …  -- `Fλ`
noncomputable def imageBifun … ; noncomputable def concaveImageBifun …   -- `Ff`
noncomputable def compBifun … ; noncomputable def concaveCompBifun …     -- `GF`
def invBifun … ; noncomputable def lowerAdjointBifun …                   -- `F⫶`, `F⫶*`
noncomputable def fenchelSup … ; noncomputable def fenchelInf …
def HasFenchelPairing … ; noncomputable def fenchelPairing …             -- `⟨f, g⟩`
theorem bracket_infConvBifun …                                           -- Thm 38.1
theorem conj_imageBifun …                                                -- Thm 38.4
theorem invBifun_compBifun …                                             -- Thm 38.5
theorem fenchelPairing_conj …                                            -- Lemma 38.6
theorem fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun …           -- **Thm 38.7**
```

**Rockafellar's `⟨f, g⟩` is not §31's Fenchel setup.** His inner product pairs a convex `f` on `E`
with a concave `g` on the *paired* space `F`; §31 has both on `E`. The two differ by a concave
closure, so Lemma 38.6 cannot be derived from `fenchel_duality` and is proved from scratch.

**Weak duality is unconditional.** `fenchelSup B f g ≤ fenchelInf B f g` needs neither properness
nor exactness — both `∞ - ∞` collisions land on the correct side — which is why every "the
extremum is attained" claim in §38 reduces to one inequality, and Corollary 38.7.1's existence half
is free.

**Theorem 38.4 needs no case split.** The book splits on `y ∈ dom F*`; `IsExactSum.proper_right`
already excludes the degenerate branch, which is stated separately and unconditionally as
`conj_imageBifun_of_bracket_eq_top`.

**`(F* g*)(v) ≠ ⊤` is not automatic** — a supremum of finite terms can be `⊤` — but it is bounded
uniformly in `y`, because the two `⟨x₀, y⟩` terms cancel (`concaveImageBifun_adjointBifun_ne_top`).

**Not here**: Theorem 38.2 and Corollary 38.2.1 (`(F₁ □ F₂)* = F₁* □ F₂*`), which need the *concave*
orientation of Theorem 16.4 — `Duality/Exact.lean` has only the convex `IsExactSum.conj_add`, and
per design decision D2 the concave transfer is hand-written, which here also needs a concave
`supConv` that does not exist. Corollaries 38.4.1 and 38.5.1 assert closedness of `Ff` / `GF`
*together with* `(Ff)* = cl (F⫶* f*)`; the missing piece is "closure commutes with
`imageBifun` / `compBifun`", which is Theorem 38.2's argument again.

**Relocation candidate**: `infConv_indicatorFn` (`δ(·∣S) □ δ(·∣T) = δ(·∣S+T)`) belongs in
`Operations/InfConv.lean`, which currently has only the singleton case.

### `Tdaf/Analysis/Convex/Bifunction/Process.lean`

**Convex processes** — multivalued maps whose graph is a pointed convex cone — and the dictionary
that identifies them with indicator bifunctions. §39's Theorems 39.1, 39.2 and Corollary 39.7.1.

```lean
structure ConvexProcess (U X : Type*) … where graph : PointedCone ℝ (U × X)
def eval … ; def dom … ; def range … ; def image … ; def inv …
def ofLinearMap … ; def comp … ; instance : Add …
noncomputable def indicatorBifun … ; def adjointProcess … ; def coadjointProcess …
theorem exists_linearMap_of_isBounded …                    -- Thm 39.1
theorem coadjointProcess_adjointProcess_eq_self_iff …       -- Thm 39.2, `A** = cl A`
theorem isClosed_image …                                    -- Cor 39.7.1
```

**The graph is a `PointedCone`, not a `Set` with side conditions.** The plan sketched a structure
carrying `Convex`, `∀ a > 0, a • graph = graph` and `(0,0) ∈ graph` as fields; `PointedCone ℝ (U × X)`
is all three, and brings `Submodule` machinery with it.

**Corollary 39.7.1 is Theorem 9.1, not Theorem 39.7.** Rockafellar specializes Theorem 39.7 and
separates the barrier cone of `C` from the range of `A*`. But `A C` is the projection of
`graph A ∩ (C × X)` onto the second factor; a pointed convex cone is its own recession cone, so
`0⁺(graph A ∩ (C × X)) = graph A ∩ (0⁺C × X)`, whose intersection with the projection's kernel is
`{(v, 0) | v ∈ A⁻¹0 ∩ 0⁺C}` — exactly Theorem 9.1's hypothesis. No duality is involved; the
ingredients are `isClosed_image_of_recessionCone_inter_ker`, `recessionCone_inter`,
`recessionCone_coe_pointedCone` and `recessionCone_prod`.

**Orientation is a real sign trap, and it needs two definitions.** Rockafellar carries
"supremum- or infimum-oriented" as informal side data and says the adjoint of an infimum-oriented
process is defined "in the same way, except the inequality is reversed". Using the
supremum-oriented definition twice gives `{p | ∀ w ∈ K°, 0 ≤ ⟨p, w⟩}` rather than the bipolar `K°°`,
and `A** = cl A` becomes false. `adjointProcess` and `coadjointProcess` are separate; a boolean
orientation field would double every statement.

**Not here**: Theorems 39.3–39.6 and 39.8. 39.3 and 39.4 specialize Theorems 33.1–33.3 and
Corollary 33.2.1 to processes, all of which are now in `Saddle/Correspondence.lean` and
`Saddle/Kernel.lean`, so they should be short.

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

53. **`Submodule.toAffineSubspace` is a coercion that type ascription will not trigger.**
    `set M : AffineSubspace ℝ V := (LinearMap.graph A : Submodule ℝ V)` is a type error, not a
    coercion — the ascription binds to the inner term. Write
    `Submodule.toAffineSubspace (LinearMap.graph A)` explicitly. The two `Set` coercions
    (`AffineSubspace → Set` and `Submodule → Set`) then agree by `rfl`, so
    `have hMset : (M : Set V) = {p | p.2 = A p.1} := rfl` typechecks, but unification will *not*
    find `?M : AffineSubspace` from a goal mentioning the submodule's coercion. Pass `M` by hand.

54. **State a `rw` helper against the coercion that the caller's lemma produces.**
    `Convex.relint_image hC (LinearMap.fst ℝ E F)` yields `⇑(LinearMap.fst ℝ E F) '' …`, not
    `Prod.fst '' …`. Those are defeq but not syntactically equal, so a helper stated with
    `Prod.fst` will not fire in a `rw`. `image_fst_inter_prod_univ` is stated with
    `⇑(LinearMap.fst ℝ E F)` for exactly this reason.

55. **`epi_injective` is usually the whole proof.** Every §9 result about a *set* operation on
    epigraphs — supremum (`⋂`), composition with a linear map (preimage) — reduces to a one-line
    `refine epi_injective ?_; rw [epi_lscHull, epi_iSup, …]`. Reach for the segment-limit machinery
    only when the operation is *not* a set operation on epigraphs, which among §9's cases means
    only the sum.

56. **State `[Finite ι]`, recover `Fintype` in the proof.** `linter.unusedFintypeInType` fires
    whenever `[Fintype ι]` is a hypothesis that the *statement* does not mention — which is the
    normal situation for a theorem about `convexHull ℝ (range v)`, since the finiteness is only
    needed to build `stdSimplex ℝ ι` inside the proof. Declare `[Finite ι]` and open with
    `obtain ⟨hι⟩ := nonempty_fintype ι`. A bare `obtain` is enough: a local hypothesis whose type
    is a class is used by instance search. Do *not* write `letI := hι` — that trips
    `linter.style.haveILetI`.

57. **Look for the fixed-`ε` decomposition before formalising a "triangulate around `x`" step.**
    Rockafellar's Theorem 10.2 reduces to a vertex of the simplex by triangulating; the reduction
    is more expensive in Lean than the theorem. The general point is reachable directly because the
    weights satisfy an identity — `w = (1-ε) • μ + ε • ((w - (1-ε) • μ)/ε)` — that exhibits `z` as
    `(1-ε) x + ε y` with `y` in the same simplex, *for an `ε` fixed in advance* rather than one
    shrinking with `z`. The same shape (fix the small parameter from the target bound, then use
    compactness to find the neighbourhood) is worth trying wherever a proof reads "for `z` close
    enough to `x`, `x` is an interior point of the piece containing `z`".

58. **`Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`.** It still fires inside
    `simp only` lists copied from older files, as a deprecation warning that the verification
    standard forbids ignoring.

59. **`show` that *changes* the goal trips `linter.style.show`; use `change`.** The linter's rule
    is that `show` is for readability — restating a goal you are already looking at — and `change`
    is for defeq conversion. Every "unfold a `Set` membership to the underlying inequality" step is
    a `change`.

60. **Pointwise `+` on sets needs `open scoped Pointwise`.** Without it `convexHull ℝ P + K` fails
    with `failed to synthesize HAdd (Set E) (Set E) ?m`, which reads like a coercion problem and
    is not one.

61. **`rw [← h]` with `h : p.1 = 1` rewrites *every* `1`.** Including the `1` inside `liftAt 1 P`,
    turning it into `liftAt p.1 P`. Build the equation you actually want — `Prod.ext h rfl :
    p = (1, p.2)` — and rewrite with that instead.

62. **`PointedCone ℝ E` is `Submodule {c : ℝ // 0 ≤ c} E`, and the coercion bites twice.**
    (a) Write `Submodule.smul_mem p (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hx`, not
    `p.smul_mem ⟨a, ha⟩ hx`: with dot notation the anonymous constructor is elaborated against the
    wrong expected type and the error mentions `Real.le✝`. (b) Inside a `PointedCone` structure
    field, `a • x` for `a : ℝ≥0` is defeq to `(a : ℝ) • x` but not syntactically equal, so each
    field proof opens with a `change`. (c) To push a cone hull along a linear map, define the map
    over `{c : ℝ // 0 ≤ c}` by hand (as `inrₙ` does) and use `Submodule.map_span`;
    `LinearMap.restrictScalars` drags in an `IsScalarTower` search that is not worth the trouble.

63. **`IsCompact` is a `def` with a `∀`-body, so dot notation on it silently resolves to
    `Function.*`.** `hK.prod hL` becomes `Function.prod` and the error talks about
    `(i : ?) → ? i × ? i`; `hK.image hf` and `hK.isClosed` fail the same way. Write
    `IsCompact.prod hK hL`, `IsCompact.image hK hf`, `IsCompact.isClosed hK`. This is gotcha 50
    (`Convex`) again, in a second guise — the pattern is: *if the "structure" is really a def
    unfolding to a Pi type, dot notation is unavailable*.

64. **`if_pos`, `if_neg`, `dif_pos`, `dif_neg` are all deprecated.** Their suggested replacements
    (`ite_eq_left`, `dite_eq_right`, …) are iff-statements, not substitution rules, so they do not
    drop in. Use the `split` tactic and discharge the impossible branch with
    `exact absurd h ‹_›`.

65. **`isCompact_stdSimplex` takes `ι` explicit and `𝕜` by instances.** `isCompact_stdSimplex _`
    therefore feeds the underscore to `ι` and leaves `𝕜` a metavariable that instance search cannot
    pin down. Pass `(𝕜 := ℝ)`.

66. **`AffineSubspace`'s structure field is `smul_vsub_vadd_mem'`, with the three points
    implicit.** `smul_vsub_vadd_mem t p₁ p₂ p₃ h₁ h₂ h₃ := …` fails twice over — wrong name, and
    the points cannot be named positionally. Write `smul_vsub_vadd_mem' := by intro t p₁ p₂ p₃ h₁
    h₂ h₃; …`. Inside the proof, membership in the `carrier` set and the predicate are defeq, and
    so are `-ᵥ`/`-` and `+ᵥ`/`+` in a vector space, so the body can be a plain `have h : f (t • (p₁
    - p₂) + p₃) = c := …; exact h`.

67. **`IsCompatiblePairing B.flip.flip` is not found by instance search.** `Pairing.lean` provides
    `instIsContinuousPairingFlipFlip` for the *base* class only, deliberately. Any two-sided result
    (`IsExactSum.of_polyhedral` and friends ask for both `B` and `B.flip`) applied at `B.flip`
    therefore needs `have : IsCompatiblePairing B.flip.flip := ‹IsCompatiblePairing B›` first —
    the two are definitionally equal, so the term-level bridge always typechecks.

68. **`StrongDual ℝ E` is an `abbrev` for `E →L[ℝ] ℝ`, and `LinearMap.toContinuousLinearMap φ x = φ x`
    is `rfl`.** So `evalCLM B y` can be handed directly to anything expecting `E →L[ℝ] ℝ` (such as
    `Separates`), and in finite dimensions a bare `E →ₗ[ℝ] ℝ` obtained from a cone representation is
    promoted with `LinearMap.toContinuousLinearMap` and used without a single rewrite.

69. **`EReal.le_neg` and `EReal.neg_le` are `protected`, and `neg_le_neg_iff` needs the `_root_`
    prefix.** `a ≤ -b ↔ b ≤ -a` is `EReal.le_neg`; inside `namespace Tdaf.ConvexAnalysis` it must be
    written `_root_.EReal.le_neg`, like every other `EReal` lemma (gotcha at the top of §1). These
    two are the whole toolkit for `δ*(y | s) ≤ -δ*(-y | t)`-style statements: rewrite with
    `EReal.le_neg` to move the negation across, then use `supportFn_le_iff` /
    `supportFn_le_coe_iff`.

70. **A pointed cone's coercion to `ConvexCone` produces a double coercion that blocks `rw`.**
    `(K : ConvexCone ℝ E).convex` has type `Convex ℝ ↑↑K`, which will not match a goal mentioning
    `↑(PointedCone.hull ℝ S)`. Bind the fact to an explicitly type-ascribed
    `have hconv : Convex ℝ (PointedCone.hull ℝ S : Set E) := (… : ConvexCone ℝ E).convex` instead
    of using it inline, and do not `set K := …` first.

71. **`Filter.Tendsto.fst` / `.snd` are about product *filters*, not `𝓝` of a pair.** For
    `hlim : Tendsto u atTop (𝓝 p)` with `p : ℝ × E`, use `(continuous_fst.tendsto p).comp hlim`,
    not `hlim.fst`.

72. **`Set.insert_eq_self.2 (Or.inr h)` elaborates `insert` at `Prop`.** Bind the membership proof
    to an explicitly typed `have hmem : (0 : E) ∈ S := …` first, then apply. Relatedly,
    `change … ∈ _` with a metavariable for the set fails with "typeclass instance problem is stuck:
    `Membership (ℝ × E) ?m`" — spell the set out in full.

73. **`rw [← h]` can rewrite inside the right-hand side you are trying to build.** An `abel` that
    "should" close a goal can fail for exactly this reason; prove the rearrangement as a standalone
    `have heq : … = …` and `rw [← heq]`.

74. **Check for name clashes across the whole `Tdaf.ConvexAnalysis` namespace before naming a
    declaration, not just within the import closure of the file you are writing.** `Tdaf.lean`
    imports everything, so two same-named declarations in mutually non-importing modules build fine
    module-by-module and then collide at the top-level import. `grep -rn "theorem <name>\b" Tdaf/`
    over the whole tree catches it; a per-module `lake build` does not. This is not hypothetical:
    `posHomGen` and eight companions were independently developed in `Duality/Level.lean` and
    `Recession/ConeHull.lean`, with *different* definitions that agree only for convex `f`.

75. **Pointwise and function-level forms of the same lemma do not interchange under `rw`.**
    `ofEpi_iUnion : ofEpi (⋃ i, F i) = ⨅ i, ofEpi (F i)` rewrites a goal about
    `ofEpi (⋃ i, F i) x` to `(⨅ i, ofEpi (F i)) x`, which is *not* `⨅ i, ofEpi (F i) x` until
    `iInf_apply` is applied. Chain them: `rw [ofEpi_iUnion, iInf_apply]`.

76. **A lemma stated over `[NormedAddCommGroup E]` applied at a bare topological group times out
    rather than erroring.** `(deterministic) timeout at whnf` on an `exact` usually means an
    instance in the *cited lemma's* section variables cannot be found — check its `variable` line
    before optimizing the proof. Relaxing an over-constrained helper to `[TopologicalSpace E]` is
    often the whole fix.

77. **`refine (foo fun x => ?_).2 …` leaves `x` inaccessible** in the deferred goal ("Unknown
    identifier `x`"). Pull the side condition into a `have … := by intro x; …` first.

78. **`ContinuousOn.preimage_isClosed_of_isClosed` cannot infer `t`.** Pass it explicitly, e.g.
    `(isClosed_Iic (a := (0 : ℝ)))`.

79. **`ConcaveConvexFn`'s fields are `concave_fst` then `convex_snd`.** With `constructor` the
    *concave* goal comes first; getting the order wrong surfaces as the unhelpful
    `failed to synthesize Membership X (Set U)`.

80. **Do not check the 100-column limit with `awk length`** — it counts bytes, so every `₁`, `ℝ`
    and `×` inflates the count. Use a Python codepoint count.

81. **`io.open(p, 'w')` and `open(p, 'wb')` truncate the file before the value being written is
    evaluated.** A patch script that encodes a string containing a lone surrogate (which is what
    `"\ud835\udcdd"` is in a Python source literal — use `"\U0001D4DD"` for `𝓝`) will
    empty the target file and then raise. Encode to `bytes` in a separate statement *before*
    opening. Recovery, when the file was clean at `HEAD`:
    `git show HEAD:<path> > <path>` — not `git checkout --`, which would also discard unrelated
    working-tree edits.

82. **`Set.mem_setOf_eq` is deprecated in this Mathlib** in favour of `Set.mem_ofPred_eq`; the
    simp lemma is `Set.mem_ofPred`. Likewise `le_or_lt` → `le_or_gt`, `Set.diff_eq_empty` →
    `Set.sdiff_eq_empty`, `Set.inter_union_diff` → `Set.inter_union_sdiff`,
    `continuous_mul_right` → `continuous_mul_const`. Deprecation warnings fail the "no warnings"
    bar, so fix them rather than living with them.

83. **`rintro ⟨p, -, hp⟩` on `x ∈ a • S` yields an un-beta-reduced `hp : (fun y => a • y) p = x`,**
    against which `rw [zero_smul]` fails. `simpa using congrArg Prod.snd hp`, or a `simp only` that
    beta-reduces first, works. The same happens to `Equiv`/`Subtype` field proofs
    (`↑((fun f => ⟨…⟩) x) = ↑x`): `change` to the intended equation before rewriting.

84. **The unused-section-variable linter reports only some offenders per build.** After adding
    `omit`s, new ones surface; expect two or three rounds.

85. **`PointedCone.hull ℝ s` is an `abbrev` for `Submodule.span {c : ℝ // 0 ≤ c} s`,** so
    `induction hv using Submodule.span_induction` works directly. In the `smul` case the scalar is
    `c : {r : ℝ // 0 ≤ r}` and `c • v` is *defeq* to `(c : ℝ) • v` — use `change` to convert;
    `rw` on a `rfl` lemma between them fails.

86. **`IsExtreme` is a structure with fields `subset` and `left_mem_of_mem_openSegment`** (use the
    field names, not `.1`/`.2`), and `Set.extremePoints`'s condition concludes only `x₁ = x`; get
    the other endpoint via `openSegment_symm`. `Submodule.coe_bot` does not exist — it is
    `Submodule.bot_coe`. `isCompact_closedBall` is at root, not `Metric.isCompact_closedBall`.

87. **`toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))`**
    (`Mathlib.Analysis.InnerProductSpace.EuclideanDist`) is the tool for lifting an
    inner-product-only proof to any finite-dimensional real normed space. Pair it with
    `image_extremePoints`, `ContinuousLinearEquiv.coe_toHomeomorph` and `Homeomorph.image_closure`;
    prove convexity of the image by hand rather than via `Convex.linear_image`, to dodge the
    `⇑f` vs `⇑f.toLinearMap` coercion mismatch. The real inner-product notation `⟪·,·⟫` needs
    `open scoped RealInnerProductSpace`.

88. **Mixing layers causes `(deterministic) timeout at isDefEq`, not an instance error.** A layer-D
    lemma used inside a layer-A section hangs rather than failing cleanly. So does a lemma stated
    over `[NormedAddCommGroup E]` applied at a bare topological group — check the *cited* lemma's
    `variable` line before optimizing the proof.

89. **`refine f (fun n => g ?_) …` — a `?_` under a binder is rejected**; hoist the body into a
    `have`. Similarly `fun ⟨a, ha⟩ => …` is not accepted in term mode for an `Exists` inside an
    `exact ⟨_, _⟩` for an `Iff`; use `constructor` + `rintro`.

90. **When a lemma's implicit argument appears only in a hypothesis you are not supplying, pass it
    by name** — `not_isBounded_halfLine (x := x) hy0`.

91. **`Tdaf.EReal.coe_mul_coe` is oriented `↑a * ↑r = ↑(a*r)`.** Forward combines, `←` splits;
    getting it backwards produces "did not find an occurrence of the pattern `↑(?a * ?r)`".

92. **`epi_lscHull` lives in a section requiring `[AddCommGroup E] [IsTopologicalAddGroup E]`** even
    though `lscHull` needs only `[TopologicalSpace E]`. Split sections accordingly, or the linter
    forces long `omit` lists.

93. **Do not name a lemma `foo.negReal`-style and then use dot notation on a hypothesis whose type
    is a `def` that unfolds to a `∀`.** `LipschitzOnWith` is such a def: with `h : LipschitzOnWith
    k f S` in a position where the elaborator has already whnf'd the type, `h.negReal` resolves
    against `Function`, not `LipschitzOnWith`. Apply the lemma explicitly.

---

**`omit … in` goes before the doc comment, not after it.** `/-- … -/ omit [Inst] in theorem foo`
is a parse error (`unexpected token 'omit'; expected 'lemma'`); the modifier has to precede the
whole declaration, doc comment included.

**A definition that negates an `EReal` must be `noncomputable`.** `EReal.instNeg` is
noncomputable, so even `fun q => -(K (q.2, q.1))` needs the keyword; the error names
`EReal.instNeg` explicitly, which makes it easy to spot.

94. **A bare identifier inside `theorem Foo.bar` resolves to `Foo.bar` itself, not to the top-level
    `bar`.** During elaboration the current namespace already contains `Foo`, so
    `rw [hasSaddleValue_iff]` inside `SaddleEquiv.hasSaddleValue_iff` rewrites with the theorem
    being defined — and fails with *"fail to show termination"*, not with an ambiguity error. Write
    `_root_.hasSaddleValue_iff`, or `change` to unfold the definition.

95. **`saddleSwap_saddleSwap` is not `rfl`, and unification will not discover it.**
    `lowerClosedFn_iff_upperClosedFn_saddleSwap.1 h` produces
    `UpperClosedFn (saddleSwap (saddleSwap L))`; matching that against `UpperClosedFn L` sends
    `isDefEq` into a deterministic timeout, because `EReal`'s `neg_neg` is propositional. Land the
    term in a `have` and `rwa [saddleSwap_saddleSwap] at` it.

96. **`ClosedFn` / `ClosedBifun` / `ConvexBifun` unfold to `Eq` / `ConvexFn`, so dot notation dies
    behind a type ascription.** `(h : ClosedBifun G).imageClosedBifun` fails with *"the environment
    does not contain `Eq.imageClosedBifun`"*, because the ascription is elaborated away. Bind it
    with `have h : ClosedBifun G := …` first. Same family as gotcha 93.

97. **`rw [← h]` where `h : f X = F` and `X` itself mentions `F` rewrites inside `X` too.** In
    `bifunOfSaddle_eq_of_mem_bifunSaddleClass` the goal has `F` on both sides, so `rw [← hbase]`
    mangles it. Use `calc` with the intermediate terms spelled out.

98. **An underscore for a saddle-function argument surfaces as a stuck *instance* problem.**
    `bifunOfSaddle_partialCl₂ Bx _` leaves the type `U` a metavariable, and the error reads
    `typeclass instance problem is stuck: LocallyConvexSpace ℝ ?m`. Supply the function
    explicitly, or put the term in a `calc` step whose expected type pins it down.

99. **`omit […] in` is reported for *all* offending declarations in one build**, unlike the
    unused-section-variable linter (gotcha 84). One grep-and-patch pass suffices — no N rebuild
    cycles.

100. **`sub_eq_add_neg` does apply to `EReal`.** `simp only [sub_eq_add_neg]` is the way to expose
     `a - b` as `a + -b` before `add_assoc` / `add_comm` / `add_right_comm`; a plain
     `rw [add_assoc]` will not match through the `HSub` head. But **`zero_sub` is not available**
     — `EReal` is not a `SubtractionMonoid` — so use `change (0 : EReal) + -a = _` then `zero_add`.

101. **`Tdaf.EReal.iSup_add_coe` / `iInf_add_coe` put the constant on the *right*.** Rearranging
     `⟨u,v⟩ + ⟨x,y⟩ - K` into `(⟨x,y⟩ - K) + ⟨u,v⟩` first (via `EReal.coe_add` plus `add_assoc` /
     `add_right_comm`) is what makes them fire.

102. **`IsContinuousPairing (prodPairing Bu Bx).flip` is not found by instance search**, because
     the flip is not syntactically a `prodPairing`. Bridge it with a theorem
     (`rw [prodPairing_flip]; infer_instance`) introduced by `have` — it must not be an instance.

103. **`linter.style.haveILetI` rejects `haveI` for Prop-valued goals.** Instance-producing steps
     inside proofs use plain `have`, including for typeclass instances, since the classes here are
     Props.

104. **`iInf₂_congr` does not exist**, though `iInf₂_le` and `le_iInf₂` do, which makes it look
     like it should. Write `iInf_congr fun i => iInf_congr fun j => h i j`.

105. **A theorem binder that repeats a section variable's name silently detaches the instance
     binders before it.** `theorem foo [IsContinuousPairing B.flip] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) …`
     resolves `B.flip` against the *section* `B` and then shadows it, so the error is "failed to
     synthesize `IsContinuousPairing B.flip`". Drop the explicit binder and use the section
     variable.

106. **`Submodule.span_le.2 h` proves a `Submodule` `≤`, not a `Set` `⊆`.** With the goal
     `(PointedCone.hull ℝ S : Set F) ⊆ T`, passing it directly gives "argument has type … but is
     expected to have type `?a ⊆ ↑?b`". Bind the `≤` to a `have` with an explicit `PointedCone`
     ascription, then `exact`.

107. **`inv_inv` is false on `EReal`** — `(⊤⁻¹)⁻¹ = 0`. Push the double inverse back to `ℝ` with
     `← EReal.coe_inv` first, then use the real `inv_inv`. (`EReal` *does* have
     `DivInvOneMonoid`, so the generic `div_one` applies and there is no `EReal.div_one` to hunt
     for.)

108. **Bash heredocs here fail with "unexpected EOF while looking for matching `'`" once the body
     gets long** — roughly 120+ lines with heavy Unicode. Split the content into two or three
     shorter heredocs, or use the `Write` tool (which is what gotcha 81's rule already implies).

109. **`lscHull` is `liminf` unconditionally; `clFn` is not.** `lscHull_eq_liminf` holds for every
     `f`, but `clFn f x = liminf f (𝓝 x)` fails exactly when `clFn f x = ⊥` and `liminf = ⊤`. Use
     `clFn_eq_liminf_or`, or `clFn_eq_liminf` under `∀ z, lscHull f z ≠ ⊥`. This is the source of
     Rockafellar's "except in cases where…" in Corollary 30.2.3.

110. **Do not name a theorem `Foo.bar` when `bar` appears in its own statement.**
     `theorem PolyhedralFn.mapLin … : PolyhedralFn (mapLin A f)` makes the bare `mapLin` resolve to
     the declaration being elaborated, and the error is a baffling "application type mismatch …
     expected `PolyhedralFn f`". Rename to `polyhedralFn_mapLin`. Gotcha 94 is the same trap seen
     from the other side.

111. **Pulling a constant out of an `EReal` supremum as a *subtrahend* needs `c ≠ ⊥`, not
     `c ≠ ⊤`.** `(⨆ i, u i) - c = ⨆ i, (u i - c)` holds for `c ≠ ⊥`; the `c = ⊤` and empty-index
     cases both collapse to `⊥` on both sides, because `⊥` absorbs in `EReal` addition. This is
     *not* the mirror of `Tdaf.EReal.biSup_add_biSup`, whose hypothesis dualises the other way.

112. **`compLin (fun w => -(g w)) A` and `fun x => -(compLin g A x)` are defeq but not
     syntactically equal**, and `rw`'s trailing `rfl` runs at reducible transparency, so it will
     not unfold `compLin`. Close the gap with an explicit bare `rfl` after the rewrites.

113. **`IsEpiLike.of_isClosed` is what feeds `epi_mapLin`.** For Corollary 19.3.1 the image
     `A ×ₘ id '' epi f` is polyhedral hence closed, and closedness gives `IsEpiLike` directly —
     much cheaper than exhibiting the epigraph condition by hand.

114. **Carathéodory's elimination can be steered by a cost only in the affine case.** An affine
     dependency has coefficients summing to zero, so both signs occur and the cost may choose one;
     a conical dependency can have every coefficient of one sign, and then the sign that lowers the
     cost is unusable. This is exactly why Corollary 17.1.3 is provable and 17.1.4 / 17.1.6 are
     false.

115. **Run Carathéodory's elimination on a `Finset ι` of *indices*, never on a set of vectors.**
     Indexed elimination can only drop indices, so a "one generator per `Cᵢ`" invariant survives it
     for free and Rockafellar's post-hoc coalescing — with its re-proof of independence for the
     merged family — disappears. Merge first (`exists_coalesced_sum`), eliminate second.

116. **Instance search does not see through `LinearMap.flip`.**
     `IsCompatiblePairing (prodPairing Bu Bx)` is found; `IsCompatiblePairing (epiPairing B).flip`
     is not, even though `(epiPairing B).flip` is *definitionally* `prodPairing B.flip mulPairing`.
     State the pairing-parametrised lemma in the orientation that lets callers instantiate it at a
     **literal** `prodPairing` — `farkas_of_pairing` versus `farkas`. (Gotcha 102 is the same
     failure for a `prodPairing` flip.)

117. **`EReal` is not a cancellative ordered monoid.** `Finset.sum_lt_sum` into a strict bound, and
     "subtract the same thing from both sides", are both unavailable. Budget a factor of two —
     `ε/(2λ)` where the book writes `ε/λ` — so that every step of the chain is non-strict.

118. **`obtain ⟨…⟩ := f ?_ …` followed by focusing bullets gives "No goals to be solved".** The
     `?_` side goal is not placed where the bullets expect it. Hoist the side condition into a
     `have` before the `obtain`.

119. **`Fintype.card ↑↑t` does not rewrite to `t.card`.** `rwa [Fintype.card_coe]` reports "did not
     find an occurrence of the pattern `Fintype.card ↑?s`"; `simpa using h` closes it.

120. **Pass `(p := …)` whenever an implicit function argument occurs only under a coercion.**
     `card_le_finrank_succ_of_affineIndependent hai` fails to unify `fun i => (zz ↑i).1` against
     `fun i => ?p ↑i`; `(p := fun j => (zz j).1)` fixes it.

121. **`set x := e with h` stops abstracting once a later `rw` reintroduces `e`.** Do all the
     rewriting before the `set`, or drop the `set` and write `e` out — otherwise the goal shows
     `e` where the hypotheses show `x`.

122. **`Option.elim` is defeq but not syntactically reducible in goals produced by instances.** A
     residual `(some i).elim g f x = f i x`, or an unsolved `ClosedProperConvexFn (none.elim g f)`,
     is closed by binding the branch value as a `have` and finishing with `exact` — which unifies
     up to delta — not by `rw` or `simp`.

123. **`EReal.neg_add` produces the `Sub` form.** `-(x + y)` rewrites to `-x - y`, never to
     `-x + -y`. The two are defeq (gotcha 40), but `rw [add_comm (-a) (-b)]`, `rw [neg_neg]` and
     `rw [← EReal.coe_neg]` then all fail with "did not find an occurrence". Bind the result to an
     explicitly typed `have h : -(x + y) = -x + -y := _root_.EReal.neg_add …` — the elaborator
     accepts it up to defeq — and rewrite with `h`.

124. **`Function.Surjective.iSup_comp` leaves the reindexing visible.** After reindexing
     `⨆ p : U × X` along `Prod.swap`, the body still reads `q.swap.1` / `q.swap.2` and every later
     `rw` misses. Clear it with `simp only [Prod.fst_swap, Prod.snd_swap]` immediately.

125. **`A.graph.smul_mem c h` is `PointedCone.smul_mem`, not `Submodule.smul_mem`.** It wants a
     bare real and `0 ≤ c`; the `Submodule` form over `{c : ℝ // 0 ≤ c}` is
     `Submodule.smul_mem A.graph ⟨a, ha⟩ hx` (cf. gotcha 62). Wrap it once as
     `smul_mem_graph (ha : 0 ≤ a) (hp : p ∈ A.graph) : a • p ∈ A.graph` and never touch the subtype
     again.

126. **A one-field structure gets no usable `ext`.**
     `structure ConvexProcess where graph : PointedCone ℝ (U × X)` leaves `ext` failing on
     `A.inv.inv = A`. Add `@[ext] theorem ext (h : A.graph = B.graph) : A = B` by hand, and reach
     set-level extensionality through `SetLike.ext'`.

127. **`Prod.swap ⁻¹' s` as a `Submodule` carrier breaks `Iff.rfl`.** Membership unfolds to
     `Prod.swap p ∈ …`, the obvious `mem_…` lemmas stop being `Iff.rfl`, and `Set` versus `SetLike`
     membership instances then mismatch under `exact ⟨u, hu⟩`. Spell the carrier as
     `{p : X × U | (p.2, p.1) ∈ A.graph}`.

128. **`x ∈ Ici 0` is not reducibly `0 ≤ x`.** Anonymous constructors for `s ×ˢ Ici (0 : ℝ)` fail
     with "has type `0 ≤ ?a` but is expected to have type `p.2 ∈ Ici 0`". Go through
     `Set.mem_Ici.1` / `Set.mem_Ici.2`.

129. **Pointwise set addition eta-expands its operator.** Destructuring `x ∈ S + T` yields
     `hab : (fun x₁ x₂ => x₁ + x₂) a b = x`, and `rw [hab]` then finds nothing in a goal containing
     `a + b`; copy it with `have hab' : a + b = x := hab`. The same eta form appears in the *goal*
     after `rintro ⟨q, hq, r, hr, rfl⟩`, where a `change` is needed before `rw [Prod.mk_add_mk]`.

130. **`a • s = s` for a set-level cone is not `smul_smul` away.** In the `⊇` direction the goal
     after `refine ⟨a⁻¹ • p, _, ?_⟩` reads `(fun x => a • x) (a⁻¹ • p) = p` — the image form of
     `Set.smul_set` — and `rw [smul_smul]` finds no pattern. Insert `change a • a⁻¹ • p = p` first.

131. **`omit` cannot remove an instance a *definition* genuinely takes.**
     `def infConvBifun (F₁ F₂ : Bifun U X)` picks up `[AddCommGroup U] [Module ℝ U]` because
     `Bifun U X` mentions `U`, and `omit` then breaks the definition rather than silencing the
     linter. Split the section and give the definitions their own `variable` line.

132. **`rw [h]` rewrites only one of two differently-instantiated occurrences.**
     `rw [fenchelPairing_eq_fenchelInf]` fires on one instantiation and leaves the other; run
     `simp only [h]` first, then `rw`.

133. **`add_right_comm _ _ _` does not see through `EReal` subtraction.** On
     `↑t - g y - f x = ↑t - f x - g y` it is a type mismatch; `change ↑(B x y) + -(g y) + -(f x) =
     ↑(B x y) + -(f x) + -(g y)` first, then `exact add_right_comm _ _ _`.

134. **`EReal.neg_sub` concludes `-x + y`, not `y - x`.**
     `EReal.neg_sub (h₁ : x ≠ ⊥ ∨ y ≠ ⊥) (h₂ : x ≠ ⊤ ∨ y ≠ ⊤) : -(x - y) = -x + y`. A follow-up
     `rw [sub_eq_add_neg]` aimed at the result fails with "did not find an occurrence of the
     pattern `?a - ?b`" — the subtraction is already gone. The uses in `Fenchel.lean` compensate
     with a trailing `add_comm`, which reads as if the lemma had produced `y - x`. To reach
     `y + ↑(-c)` from `-(↑c - y)` the chain is `EReal.neg_sub`, `add_comm`, `← EReal.coe_neg`.

135. **`PolyhedralFn` and `PolyhedralBifun` do *not* carry `[FiniteDimensional ℝ E]`.** They are
     declared inside sections whose `variable` line has it, but auto-inclusion drops it from the
     definitions, so the predicates need only `[NormedAddCommGroup E] [NormedSpace ℝ E]`.
     Consumers split: `PolyhedralFn.conj`, `polyhedralFn_mapLin` and `PolyhedralFn.closedFn` need
     finite dimension, `PolyhedralFn.convexFn` and `PolyhedralBifun.polyhedralFn_apply` do not —
     so a lemma about polyhedral functions on a non-finite-dimensional dual space typechecks and
     then fails three lines later. `#check @PolyhedralFn` before guessing.

136. **`add_coe_le_coe_iff` exists three times.** Public in `Subgradient/Approx.lean`, private in
     `Saddle/Defs.lean`, private in `Saddle/Correspondence.lean`, all with the statement
     `a + ↑c ≤ ↑m ↔ a ≤ ↑(m - c)` and no import path between them — gotcha 34's near-duplicate
     hazard, realised. It belongs in `Tdaf/Order/EReal.lean`; the proof is two lines,
     `rw [EReal.coe_sub, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot c))
     (.inl (EReal.coe_ne_top c))]`, with no `induction a` case split.

137. **`rw [mapLin_fst_apply]` leaves a beta-redex that blocks the next `rw`.** The result is
     `⨅ z, (fun p => …) (y, z)`, so a later `rw [h (y, z)]` cannot find its pattern under the
     binder. State the pointwise identity as a separate `have hval : ∀ y, (⨅ z, …) = …` in
     already-projected form and finish with `exact (hval y).symm`; `exact` beta-reduces, `rw`
     does not.

138. **`-(B x y)` with `B x : Y →ₗ[ℝ] ℝ` elaborates as `(-(B x)) y`** — negation of the *linear
     map*, not `Neg.neg` at `ℝ` — and a type ascription `(-(B x y : ℝ))` does not change it
     (checked with `pp.explicit`). Usually a convenience: `hφ : ∀ p, φ p = -(B p.2 y)` is closed by
     `fun _ => rfl` for `φ = (-(B.flip y)).comp (LinearMap.snd ℝ U X)`, both sides being the same
     linear-map negation. But the head under a coercion is then `DFunLike.coe`, so do not plan a
     `rw` that expects a syntactic `↑(-r)`.

139. **Abstract a linear functional into a `private` auxiliary rather than fighting `set`.** A
     proof that must mention a `(U × X) →ₗ[ℝ] ℝ` twice cannot use `set … with h` (the unused `h`
     trips the linter) and cannot use `set` alone (the statement has no occurrence to abstract).
     Give the auxiliary lemma the functional and its defining equation as arguments and discharge
     them at the call site with `fun _ => rfl`; the map is then written exactly once.
     `polyhedralFn_neg_bracket_aux` and `polyhedralFn_concaveBracket_aux` are both this shape.

140. **A Python patch script that writes with `io.open(p, 'w')` destroys the file if the write
     raises.** `open(..., 'w')` truncates *before* encoding, so a `UnicodeEncodeError` mid-write
     leaves a 0-byte `.lean` file. Write to `p + '.tmp'` and `os.replace(tmp, p)`. The trigger was
     a mathematical letter written as a surrogate pair in a Python string literal, which is not
     encodable as UTF-8; use the `\U0001D55C` form, or keep the Lean text in a separate UTF-8 file
     and have the script only splice it.

141. **Never trim a `variable` block on the strength of an unused-section-variable warning from a
     build that also had errors.** When a proof fails partway, the linter reports the instances the
     *incomplete* term does not mention. `IsTopologicalAddGroup E`, `ContinuousSMul ℝ E` and
     `LocallyConvexSpace ℝ E` were all reported unused, removed, and then immediately needed once
     the proof compiled. Fix the errors first, then trim.

142. **`omit [...] in` must be adjacent to the next command.** A blank line between the `omit` line
     and the following doc comment trips `linter.style.emptyLine` ("do not place empty lines within
     commands") — the `omit`, the doc comment and the declaration are one command, so the `omit`
     goes *before* the doc comment, not between it and the `theorem`. And `omit` accepts only
     instances that really are section variables: `omit [SeparatingDual ℝ E] in` in a section that
     never declared it fails with "did not match any variables in the current scope".

143. **`⟨hz, le_rfl⟩` does not elaborate for `(z, 0) ∈ C ×ˢ Ici (0 : ℝ)`.** The second
     component's goal is `(z, 0).2 ∈ Ici 0`, which is not unfolded to `0 ≤ 0` during elaboration,
     so `le_rfl`'s metavariables never unify. Use `mem_Ici.2 le_rfl`. (`left_mem_Ici` is not a
     Mathlib name.)

144. **`field_simp` needs the `≠ 0` hypothesis in the *local context*, not merely derivable.**
     `(-c)⁻¹ * (β * c) = -β` is left as `-(c * β / c) = -β` unless `hcne : c ≠ 0` is a hypothesis;
     `hcneg : c < 0` alone is not enough. Add `have hcne : c ≠ 0 := ne_of_lt hcneg` first.

145. **`have h := hp.le_add_conj x z` fails with "don't know how to synthesize implicit argument
     `B`".** A lemma whose pairing `B` is a section `variable` appearing only in the conclusion
     cannot be elaborated by an expected-type-free `have`. Pass it: `hp.le_add_conj (B := B) x z`.
     The same lemma used as `exact`/`refine` against a goal is fine. The same trap catches
     `recessionFn_eq_supportFn_dom_conj (B := B) hf`.

146. **`simpa … using h.symm` when `simp` already normalises the orientation.** `simp` can rewrite
     `L (z, 0)` to `B x₀ z` inside the hypothesis, at which point `.symm` flips it *away* from the
     goal. If `simpa using h.symm` reports a mismatch that is the goal read backwards, drop the
     `.symm`.

147. **`omit … in` must be recomputed per declaration when a section spans two spaces.** In a
     section over `U` and `X`, a theorem about `argmin (F 0)` with `F 0 : X → EReal` needs
     `[FiniteDimensional ℝ X]` and *not* `[FiniteDimensional ℝ U]`, even though the neighbouring
     declarations need the opposite. Copy the linter's own list rather than the neighbour's `omit`
     line.

148. **`Submodule.span_induction` auto-reverts every hypothesis mentioning the bound variable.**
     Proving `∀ b ∈ PointedCone.hull ℝ D, 0 ≤ b.2` inside a step that already has `hab : a + b = q`
     in context turns the induction hypothesis into an implication. Hoist the claim into a
     standalone `have` outside the step.

149. **`h ▸ iInf_le f x` on `EReal` fails** with "typeclass instance problem is stuck:
     `OrderTop ?m`" — the motive of `▸` is not fixed before the instance is demanded. Use
     `by rw [← h]; exact iInf_le f x`.

150. **`Finset.sum_erase _ h` cannot infer its implicit summand.** Use
     `Finset.sum_erase_add t (fun q => …) hmem` with the function explicit, then
     `simp only [smul_zero, add_zero]`. It also leaves the summand un-beta-reduced, so a later `rw`
     against `∑ q ∈ t, w q * q.2` will not fire; restate the hypothesis with its beta-reduced type.

151. **`Submodule.mem_span_finset.1` returns a three-component existential** in this Mathlib:
     `∃ f, Function.support f ⊆ ↑t ∧ ∑ i ∈ t, f i • i = x`. Destructure as `⟨c, -, hc⟩`.

152. **To restrict an `EReal`-valued function to a set, prefer `fun x => ⨅ _ : x ∈ C, f x` over
     `f + indicatorFn C`.** The `iInf` form needs no `f x ≠ ⊥` hypothesis (`⊥ + ⊤ = ⊥` corrupts the
     sum off `C`), `iInf_pos` / `iInf_neg` evaluate it, and `⨅ x, (fun x => ⨅ _ : x ∈ C, f x) x` is
     *definitionally* `⨅ x ∈ C, f x`, so a bounded-below hypothesis transports with no rewriting at
     all. This removed a spurious hypothesis from Corollary 27.3.2. It is the same `restrict` that
     `Duality/GaugeLike.lean` uses to truncate a function to a half-line.

153. **`nlinarith` fails on rescaled separating functionals.** When an inverse of a negated value of
     the functional appears, build an explicit `calc` from `hprod : (-c)⁻¹ * (-c) = 1`,
     `mul_le_mul_of_nonneg_left`, and `rw [← mul_assoc, hprod, one_mul]`.

154. **`★` (U+2605) is not a valid Lean identifier character** — `q★` gives "expected token".
     Rockafellar's starred variables must be renamed (`qm`, `xs`, …).

155. **Before stating a lemma that is a two-line consequence of a theorem you already have, grep
     for its name.** `recessionFn_eq_supportFn_dom_conj` was written independently in
     `Recession/Conjugate.lean` while it already existed in `Duality/Level.lean`, and the collision
     surfaced only as a *type error at the old consumer* — "argument has type
     `ClosedProperConvexFn f` but is expected to have type `ConvexFn ?m`" — three files away from
     the new declaration. That is the third such collision on this project (gotcha 34's hazard,
     realised again); `grep -rn "theorem <name>" Tdaf/` costs one second.


**`rw` needs the eta-contracted form.** A hypothesis stated as `(fun p => partialCl₁ g p) = …`
will not rewrite a goal containing `partialCl₁ g`, even though the two are eta-equal. State
`have`s in the contracted form and let `funext` introduce the point.

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
