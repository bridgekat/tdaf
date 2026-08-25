# The backbone API, module by module

One record per module under `Tdaf/`, in the order the modules were written. **This file is
reference, not reading**: it is here so that `grep` answers "does this already exist, and what is
it called" without opening ninety Lean files. Nobody should read it end to end, and no agent brief
should ask them to.

Everything under `Tdaf/Analysis/Convex/` lives in `namespace Tdaf.ConvexAnalysis`; the names below
are written as they are inside it. `Tdaf/Order/EReal.lean` is `Tdaf.EReal`, deliberately outside the
topic namespace: its lemmas are general-purpose `EReal` facts with no convexity in them.

A record says what the module is *about*, lists the declarations a caller would look for, and — the
part that rots fastest and matters most — what is **not** there and why. See
[`NOTES.md`](NOTES.md) for house style, the gotcha list, and the verification bar.

> A "what is not here" note that explains *why* something is blocked is the entry a later agent
> believes and does not re-derive. Two sweeps have found such notes outliving the obstruction they
> described, pointing work away from results that already existed. Re-check them after every merge.

---
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
theorem coe_add_sub (p q : ℝ) (u : EReal) :
    ((p + q : ℝ) : EReal) - u = (((p : ℝ) : EReal) - u) + ((q : ℝ) : EReal)
theorem coe_sub_add_coe (p q : ℝ) (u : EReal) :
    ((p : ℝ) : EReal) - (u + ((q : ℝ) : EReal)) = ((p - q : ℝ) : EReal) - u
theorem iSup_add_coe {ι : Sort*} (u : ι → EReal) (r : ℝ) :
    (⨆ i, u i) + (r : EReal) = ⨆ i, (u i + (r : EReal))
theorem biInf_add_coe {α : Type*} (s : Set α) (u : α → EReal) (r : ℝ) :
    (⨅ a ∈ s, u a) + (r : EReal) = ⨅ a ∈ s, (u a + (r : EReal))
theorem add_coe_right_cancel {u v : EReal} {r : ℝ} (h : u + (r : EReal) = v + (r : EReal)) : u = v
```

`coe_add_sub` and `coe_sub_add_coe` are the pair that make **Theorem 12.3** hypothesis-free: a
*real* summand slides across a difference from either side with no side condition, because it
cannot produce `∞ - ∞`. `biInf_add_coe` and `add_coe_right_cancel` are what let Corollary 31.4.3
move its constant `⟨z, z*⟩` in and out of an infimum.

`coe_sub_le_comm` carries §12; `le_coe_sub_comm` is its mirror and carries the concave §12. Both are
unconditional because `a` is finite. `neg_iSup`/`neg_iInf` are what make the sign dictionary of
`Duality/ConcaveConj.lean` a one-line rewrite.

`add_coe_le_coe_iff : z + ↑c ≤ ↑m ↔ z ≤ ↑(m - c)` lives here because it had been written three
times over — see gotcha LIB1. `iSup_add_coe` / `iInf_add_coe` move a *real* constant in and out of a
supremum or infimum with no hypothesis at all, which is what makes the level-set arguments of §13
and §27 short.

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
theorem ConvexFn.comp_add_left {f : E → EReal} (hf : ConvexFn f) (a : E) :
    ConvexFn (fun x => f (a + x))

structure Proper (f : E → EReal) : Prop where
  dom_nonempty : (dom f).Nonempty
  ne_bot : ∀ x, f x ≠ ⊥

/-- `dom` is Rockafellar's projection of the epigraph — with no hypothesis on `f`. -/
theorem dom_eq_fst_image_epi (f : E → EReal) : dom f = Prod.fst '' epi f

/-- A real-valued affine coordinate added to a convex function keeps it convex. -/
theorem convexFn_add_coe (hf : ConvexFn f) {l : E → ℝ}
    (hl : ∀ (x y : E) (a b : ℝ), a + b = 1 → l (a • x + b • y) = a * l x + b * l y) :
    ConvexFn (fun x => f x + ((l x : ℝ) : EReal))

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

-- Jensen. Moved here from `Subgradient/Gradient.lean`: the proof is one `Convex.sum_mem` on
-- `epi f`, and a surface module that wants only Theorem 4.3 should not import the subgradient
-- tower to get it. Aliased as `jensen` in `Eponyms.lean`.
theorem ConvexFn.sum_le {ι : Type*} (hf : ConvexFn f) (t : Finset ι) (u : ι → E) (m wt : ι → ℝ)
    (hm : ∀ j ∈ t, f (u j) ≤ ((m j : ℝ) : EReal)) (hw : ∀ j ∈ t, 0 ≤ wt j)
    (hw1 : ∑ j ∈ t, wt j = 1) :
    f (∑ j ∈ t, wt j • u j) ≤ ((∑ j ∈ t, wt j * m j : ℝ) : EReal)
```

The bound is by *reals* `m j`, not by `f (u j)`. The `EReal`-valued form
`f (∑ wt j • u j) ≤ ∑ wt j • f (u j)` needs the `0 · ∞ = 0` convention where `wt j = 0` and
`f (u j) = ⊤`; §4 of the surface currently does that filtering by hand, and a backbone
`ConvexFn.sum_le'` is [scheduled](backbone/08-remediation.md).

The import cost of the move is `Mathlib.Analysis.Convex.Combination` — see gotcha EL1 for the
misleading error when it is absent.

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
@[simp] theorem indicatorFn_vadd (a : E) (s : Set E) (x : E) :
    indicatorFn (a +ᵥ s) x = indicatorFn s (x - a)
```

`indicatorFn_vadd` is what turns Rockafellar's normal form for a partial affine function,
`δ(· | L + a) + ⟨·, a*⟩ + α`, into an instance of the *translation* row of Theorem 12.3; the file
needs `open … Pointwise` for the `+ᵥ` on sets.

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
`lowerSemicontinuous_lscHull` already lives behind those instances — gotcha LINT3.

### `Tdaf/Analysis/Convex/Continuity.lean`

**Thm 10.1** as `ConvexFn.continuousOn_toReal_relint_dom` (real-valued, the working form) and
`ConvexFn.continuousOn_relint_dom` (`EReal`-valued). The chart machinery is reusable:
`intrinsicInterior_vadd` (translation invariance of `ri`, absent from Mathlib), `chart C x₀ V`,
`image_chart`, `zero_mem_chart`, `convex_chart`, `affineSpan_chart`, and
`relint_eq_vadd_image_interior` (`ri C = x₀ + ι (int (chart C x₀ V))`). Also
`ConvexFn.convexOn_toReal_dom`, the bridge from `ConvexFn f` + `Proper f` to Mathlib's
`ConvexOn ℝ (dom f) (·.toReal)`.

The subspace `V` is always a *parameter* carrying `hV : V = span ℝ (C - x₀)`, never a definition —
see gotcha EL13.

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
*every* point of a simplex — no triangulation, see gotcha LIB9),
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
`ContinuousLinearMap.precomp ℝ A` — see gotcha DEP5.

### `Tdaf/Analysis/Convex/Duality/Conjugate.lean`

`conj B f`, `biconj`; `sub_le_conj` (**unconditional**), `le_add_conj` (Fenchel's inequality —
needs properness, see gotcha ER4), `conj_le_iff` (the adjunction, unconditional), `conj_clFn`,
`eq_biSup_affineFn` (**Thm 12.1**), `biconj_eq_clFn` (**Thm 12.2, Fenchel–Moreau**), `conjEquiv`,
`gc_conj_conj`/`conjClosure`, and two instantiations, both in the space's *own* topology:
`_topDual` (a locally convex space against its continuous dual — so, a Banach space in its norm
topology) and `_inner` (Hilbert/`ℝⁿ`, via Fréchet–Riesz).

Since §31, the file also carries **Theorem 12.3**, the table of elementary conjugacy operations,
one named lemma per row and all of them **layer A with no hypothesis on `h` whatsoever**:

```lean
theorem conj_comp_sub (B) (h) (a : E) (y : F) :
    conj B (fun x => h (x - a)) y = conj B h y + ((B a y : ℝ) : EReal)
theorem conj_add_pairing (B) (h) (b : F) (y : F) :
    conj B (fun x => h x + ((B x b : ℝ) : EReal)) y = conj B h (y - b)
theorem conj_add_const (B) (h) (α : ℝ) (y : F) :
    conj B (fun x => h x + (α : EReal)) y = conj B h y - (α : EReal)
theorem conj_comp_linearEquiv (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' A A') (h : G → EReal) (y : F) :
    conj B (fun x => h (A x)) y = conj B' h (A'.symm y)
theorem conj_comp_affine (A) (A') (hA) (h) (a : E) (b : F) (α : ℝ) (y : F) :
    conj B (fun x => h (A (x - a)) + ((B x b : ℝ) : EReal) + (α : EReal)) y
      = conj B' h (A'.symm (y - b)) + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal)
```

with `conj_comp_add` and `conj_sub_pairing` for the two rows written with the opposite sign, and
`conj_comp_add_sub_pairing` for the instance §31 runs on,
`(h (z + ·) - ⟨·, z*⟩)* = h* (z* + ·) - ⟨z, ·⟩ - ⟨z, z*⟩`.

**Why every row is hypothesis-free.** What is slid across `⟨x, y⟩ - h x` is always a *real* number,
so `Tdaf.EReal.coe_add_sub` and `Tdaf.EReal.coe_sub_add_coe` apply with no side condition and the
identities hold for improper `h` too. Rockafellar's own statement asks for `h` convex; that is not
needed.

**The substitution row carries its transpose as data.** Rockafellar writes `A*⁻¹`, presuming that
`A` has an adjoint and that the adjoint is invertible. Over a general pairing neither is automatic,
so `conj_comp_linearEquiv` takes the inverse pair `A`, `A'` together with
`IsAdjointPair B B' A A'`. With `B` and `B'` separating nothing is lost. The scaling rows of the
same table are Theorem 16.1 (`conj_smul`, `conj_smulRight`, `Duality/Ops.lean`), which were already
there.

**One row of Theorem 12.3 was already in the library under another name.**
`conj_flip_conj_add_coe` in `Optimization/Minimum.lean` — "raising the conjugate by a real constant
lowers the biconjugate by the same constant" — is exactly `conj_add_const B.flip (conj B f) α x`,
and its fifteen-line `induction`-on-`EReal` proof is now that one term. Anything else in the library
that hand-rolls an `EReal` constant or linear shift under a `conj` should be checked against this
section before being written again.

### `Tdaf/Analysis/Convex/Duality/ConcaveConj.lean`

`concaveConj B g y = ⨅ x, ⟨x,y⟩ - g x` and `biconcaveConj`; the sign dictionary
`neg_concaveConj : -(concaveConj B g y) = conj B (-g) (-y)` with its two solved forms
`concaveConj_eq_neg_conj_neg` and `conj_eq_neg_concaveConj_neg` (**note the reflection on the dual
side** — `g* ≠ -(-g)*`); `concaveConj_le_sub` and `add_concaveConj_le` (**both unconditional**, see
gotcha ER2); `coe_le_concaveConj_iff`, `concaveConj_antitone`, `le_concaveConj_iff` (the adjunction),
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
`IsExactSum.of_relint_closed` (**Thm 16.4** for closed proper convex summands), plus the three steps
they are assembled from: `mem_constancySpace_conj_of_relint`,
`le_of_mk_mem_recessionCone_epi_conj`, `mk_mem_linealitySpace_epi_conj_of_relint`. Layers differ
between the two: the image rule needs `FiniteDimensional ℝ G` and `ℝ H` (Thm 9.2 runs in `H`), the
sum rule needs `FiniteDimensional ℝ F` (Cor 9.1.1 runs in `F × ℝ`); `E` is only ever a normed space.

A second section, `Closure`, removes the closedness hypothesis and so makes `IsExactSum.of_relint`
the book's Theorem 16.4 (*proper convex*, common relative interior point). It also adds
`FiniteDimensional ℝ E`, because Thm 7.4 (`ConvexFn.proper_clFn`) is finite-dimensional. The
machinery:

* `TendstoClFnAlongSegment f x₀` — `∀ y, Tendsto (fun a => f ((1-a)•x₀ + a•y)) (𝓝[<] 1)
  (𝓝 (clFn f y))`. Two producers: `ConvexFn.tendstoClFnAlongSegment` (**Thm 7.5**,
  `x₀ ∈ ri (dom f)`) and `ClosedProperConvexFn.tendstoClFnAlongSegment` (**Cor 7.5.1**,
  `x₀ ∈ dom f`). Naming the hypothesis is what lets §16 and §20 share one closure lemma.
* `conj_add_eq_conj_clFn_add_clFn` — **Thm 9.3** in conjugate form: `(f + g)* = (cl f + cl g)*`.
  The easy half is `cl ≤ id` plus `conj_antitone`; the hard half compares affine minorants through
  `conj_le_coe_iff` and one `le_of_tendsto_of_tendsto'`.
  The book's own form of Thm 9.3, `cl (f + g) = cl f + cl g`, is `clFn_add` in
  `Recession/Closedness.lean` — it was already there, and it is *not* usable in §20: it needs
  Thm 6.5 to put `x₀ ∈ ri (dom (f + g))`, hence a relative interior point of both domains, whereas
  Theorem 20.1 has only a point of `dom f`.
* `IsExactSum.of_clFn` — exactness transfers from `cl f, cl g` to `f, g` given the conjugate
  identity. Needs `[IsContinuousPairing B]` (for `conj_clFn`), nothing more.

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
height-zero lift as an `ℝ≥0`-linear map (built by hand — see gotcha SET2), `coneOver C hC` is the
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
representation uses a single index and gives `-1` or `1`. The root cause is gotcha LIB9: an *affine*
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

### `Tdaf/Analysis/Convex/Polyhedral/Recession.lean`

**Theorem 19.5 on the generator side**, and the consequence §27 consumes.

```lean
theorem recessionCone_of_finitelyGenerated
    (hPD : C = convexHull ℝ (P : Set E) + (PointedCone.hull ℝ (D : Set E) : Set E))
    (hne : C.Nonempty) : recessionCone C = (PointedCone.hull ℝ (D : Set E) : Set E)
theorem Polyhedral.recessionCone_image (hC : Polyhedral C) (hne : C.Nonempty) (A : E →ₗ[ℝ] F) :
    recessionCone (A '' C) = A '' recessionCone C
```

`Polyhedral/Ops.lean` already had Theorem 19.5 on the *inequality* side; this is the other side, and
`⊇` is `coe_hull_subset_recessionCone_of_finitelyGenerated`, already there. `⊆` is Corollary 9.1.2
(`Convex.recessionCone_add_of_neg_notMem_recessionCone`), whose hypothesis is vacuous because
`conv P` is compact and recedes in no direction at all.

**`Polyhedral.recessionCone_image` has no hypothesis on `A`, and that is the point.** Theorem 9.1
(`recessionCone_image_of_recessionCone_inter_ker`) computes `0⁺(A '' C)` only when `0⁺C ∩ ker A` is
`{0}`; for a general closed convex `C` and a general `A` the image need not even be closed. A
polyhedral `C` needs no repair, because both sides are read off generators that `A` pushes forward.
This is the *only* place polyhedrality is used in Theorem 27.3's polyhedral refinement.

The file is separate from `Polyhedral/Ops.lean` only because `Ops.lean` does not import
`Recession/Closedness.lean` and adding the import there would rebuild all of §19–§22.

### `Tdaf/Analysis/Convex/Polyhedral/Homogeneous.lean`

**Corollary 19.1.2 for functions**, the piece §21's Theorems 21.4/21.5 were named as blocked on.

```lean
noncomputable def verticalRay (E : Type*) [AddCommGroup E] [Module ℝ E] : PointedCone ℝ (E × ℝ) :=
  PointedCone.hull ℝ ({((0 : E), (1 : ℝ))} : Set (E × ℝ))
theorem epi_posHomGen_of_epi_eq {f : E → EReal} {P : Finset (E × ℝ)}
    (hepi : epi f = convexHull ℝ (P : Set (E × ℝ)) + (verticalRay E : Set (E × ℝ))) :
    epi (posHomGen f)
      = (PointedCone.hull ℝ (insert ((0 : E), (1 : ℝ)) (P : Set (E × ℝ))) : Set (E × ℝ))
theorem polyhedralFn_posHomGen_of_epi_eq … : PolyhedralFn (posHomGen f)
theorem epi_convFn_of_epi_eq {ι : Type*} [Finite ι] {g : ι → E → EReal} {p : ι → E × ℝ}
    (hg : ∀ i, epi (g i) = {p i} + (verticalRay E : Set (E × ℝ))) :
    epi (convFn g) = convexHull ℝ (Set.range p) + (verticalRay E : Set (E × ℝ))
theorem polyhedralFn_posHomGen_convFn … : PolyhedralFn (posHomGen (convFn g))
```

**The extra generator `(0, 1)` is forced.** `posHomGen f = ofEpi ↑(cone (epi f))` by definition, and
`cone (epi f)` meets the vertical axis only at the origin — for `f = δ(· | {a}) + α` it is the ray
through `(a, -α)` plus `0`. An epigraph has to contain the whole ray above each of its points, so
`epi (posHomGen f)` is strictly larger than the generating cone, and Rockafellar's generator list
for `epi k₀` carries `(0, 1)` for exactly this reason.

**The hypothesis is `epi f = conv P + cone {(0,1)}`, not `PolyhedralFn f`.** With a general
direction set the identity fails: for `f x = |x| + 1` on `ℝ`, `epi (posHomGen f) = epi |·|` contains
`(1, 1)`, while every non-negative combination of points of `epi f ∪ {(0,1)}` has second coordinate
at least `|first| + λ` with `λ > 0`. A closure is needed in general. The vertical-ray case is the
one §21 uses, because the conjugate of an affine function is a point indicator whose epigraph is a
single translated vertical ray.

**Neither inclusion needs positive homogeneity of `ofEpi K`.** `⊆` is
`epi_ofEpi_subset_of_isEpiLike` applied to `F = cone (epi f)` — nothing about the function
`ofEpi K` is checked — and `⊇` is `coe_hull_epi_subset_epi_posHomGen` plus the fact that an epigraph
absorbs the vertical ray. `IsEpiLike K` comes from `IsEpiLike.of_isClosed`: `K` is a finitely
generated cone, hence closed, and contains `(0, 1)`, hence is upward closed.

**`epi_convFn_of_epi_eq` carries it through the convex hull.** For a finite family whose members
have single translated vertical rays for epigraphs — what the conjugate of an affine function looks
like — `epi (convFn g) = conv {pᵢ} + cone {(0,1)}`, and `polyhedralFn_posHomGen_convFn` concludes.
`IsEpiLike` for a convex hull of a union is *not* automatic (`Operations/Hull.lean` carries it as a
hypothesis for that reason); here it is paid for by finite generation, since `conv P + cone {(0,1)}`
is closed and absorbs the vertical ray.

**The identification of `k₀` itself is in `HellyRefined.lean`.** `conj_affineFn` proves
`fᵢ* = δ(· ∣ aᵢ) + αᵢ` for `fᵢ = ⟨·, aᵢ⟩ - αᵢ`, using `B.SeparatingRight` to turn
`∀ x, B x (y - aᵢ) = 0` into `y = aᵢ`, and `epi_conj_affineFn` puts it in this file's shape.

**`verticalRay` and `mem_verticalRay_iff` are layer A** and live in their own section. They were
originally declared inside the normed finite-dimensional section, with `mem_verticalRay_iff`
carrying an `omit [FiniteDimensional ℝ E]`; that is a D9 violation, and it matters because
`epi_conj_affineFn` is a layer-A statement that mentions `verticalRay`.

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

**Thm 20.1** as `IsExactSum.of_polyhedral` (`f` polyhedral proper, `g` *proper convex*), with
`of_polyhedral_closed` (`g` closed proper convex) carrying the argument and `of_polyhedral_pair`
(both functions polyhedral, so only `dom f ∩ dom g ≠ ∅` is asked) as the base case. The closedness
removal is one line: `conj_add_eq_conj_clFn_add_clFn` with Cor 7.5.1 on the polyhedral side and
Thm 7.5 on the other. `of_polyhedral_pair` is `of_relint_closed`'s proof
with Corollary 9.1.1 replaced by polyhedrality: both proofs need only that `epi f* + epi g*` is
closed. `of_polyhedral_closed` follows Rockafellar — put `δ = δ(· | aff (dom g))`, apply
`of_relint_closed` to `δ + f` and `g`, the pair case to `δ` and `f`, and re-absorb `δ*` using `δ + g = g`
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

**Theorem 8.3 has a slice corollary, and it lives in `Recession/Function.lean`.**
`recessionFn_le_coe_of_slice` and `recessionFn_slice_eq` say that a closed convex function of two
variables has the *same* recession function on every slice `x ↦ G (u, x)` with non-empty effective
domain. The proof is `mem_recessionCone_of_exists_ray` — Theorem 8.3, "one half-line is enough" —
applied to `epi G` in the direction `((0, y), ν)`: the slice inequality at a single point exhibits
the half-line, and reading the resulting recession direction back at any other `u` gives the
inequality there. Neither `u` needs to be in `dom F` for the `≤` form; the equality form needs both.
It is the missing prerequisite that Theorem 30.4(g) turned out to need, and nothing weaker will do:
without closedness the slices genuinely differ (take `F 0 x = |x|`, `F u ≡ 0` for `u ∈ (0, 1]`, `⊤`
elsewhere — jointly convex, not closed, and the recession functions differ).

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
The full name table is in [`05-differential.md` §5.1](backbone/05-differential.md); the four names the rest
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

**Corollary 23.7.1 is here in both forms.** The one proved first asks for
`Bornology.IsBounded (∂f x)`, which is what `isClosed_coe_hull_of_isBounded` consumes; the book's
own hypothesis `x ∈ int (dom f)` is
`normalCone_setOf_le_eq_coe_hull_subgradient_of_mem_interior_dom`, and what gets from one to the
other is `isBounded_subgradient_iff_mem_interior_dom`.
`bddAbove_subgradient_iff_mem_interior_dom` gives only the *pairing* form of boundedness ("every
`⟨v, ·⟩` is bounded above"), and `isBounded_iff_forall_bddAbove` in `Duality/SupportRelint.lean`
supplies the upgrade — at the cost of finite-dimensionality of `F`, which the pairing form does not
need. The interior-point version assumes properness, as the book does, rather than deducing it from
`∂f x ≠ ∅`, because Theorem 23.4 needs it first.

**Theorem 23.3's second half is here too**, for the same reason Theorem 23.4 is: it is about
relative interiors, and `Subgradient/Defs.lean` cannot see them.

```lean
theorem dom_dirDeriv_subset_direction …        -- `dom (f'(x; ·)) ⊆ aff (dom f) - x`
theorem sub_mem_dom_dirDeriv …                 -- `(dom f) - x ⊆ dom (f'(x; ·))`
theorem sub_mem_relint_dom_dirDeriv …          -- `ri (dom f) - x ⊆ ri (dom (f'(x; ·)))`
theorem dirDeriv_eq_bot_of_subgradient_eq_empty …                  -- **Thm 23.3**, second half
theorem exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top …           -- its two-sided form
theorem subgradient_eq_empty_iff_exists_dirDeriv_eq_bot …          -- the criterion §27 consumes
```

**It needs no properness of `f`.** The whole argument runs inside `f'(x; ·)`, which is improper as
soon as `∂f x = ∅` (its closure is `δ*(· | ∅) ≡ −∞`, so Theorem 7.4 forbids properness), and
Theorem 7.2 is applied to *it*, never to `f`. No case split on `Proper f` is needed.

**Rockafellar's proof overshoots in its last sentence.** It concludes `f'(x; ·) = −∞` "throughout
`(dom f) - x`", where the *statement* of the theorem says `ri (dom f) - x` — and only the statement
is true. For `f y = -√y` on `[0, ∞)` at `x = 0`: `∂f 0 = ∅`, `f'(0; y) = −∞` for every `y > 0`,
but `f'(0; 0) = 0` and `0 ∈ (dom f) - x`.

**Theorem 6.4 replaces the book's `C ⊆ D ⊆ aff C` step.** Rockafellar gets `ri C ⊆ ri D` from those
inclusions by observing that both relative interiors are taken inside the same affine set. The
prolongation criterion gives it in one move: prolong a segment of `D` ending at `z - x` *inside
`dom f`*, which `z ∈ ri (dom f)` allows, and land back in `D` by `sub_mem_dom_dirDeriv`. Only
`D ⊆ aff (dom f) - x` is still needed, and that is the easy inclusion of
`dom_dirDeriv_of_mem_relint_dom`, factored out as `dom_dirDeriv_subset_direction` — it never used
`x ∈ ri (dom f)` in the first place.

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

**Theorem 24.9 is now here in full**, and its uniqueness clause is what unlocked the rest of §24:

```lean
theorem eq_add_coe_of_subgradientRel_subset …     -- Thm 24.9, uniqueness: `∂f ⊆ ∂g → g = f + α`
theorem isMaximalCyclicallyMonotone_subgradientRel …            -- Thm 24.9, maximality
theorem isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn …        -- Thm 24.9
def IsMaximalMonotoneRel …                       -- §24's maximal monotone mappings
```

**The uniqueness clause does not depend on Theorems 24.1–24.3**, contrary to the plan's dependency
order and to Rockafellar's own route. It follows from Theorem 23.5 plus the conjugate-side
repetition of the same argument; `increment_eq_of_subgradientRel_subset`, its engine, needs
**neither convexity nor closedness of `g`**, only `Proper g`. That inversion is what made Theorem
24.2's uniqueness clause reachable without any integration theory.

**§24 is now done except for the integral itself.** Theorem 24.2's existence clause turned out
to need no integration — see `Subgradient/Primitive.lean` — and Theorem 24.6's second assertion
turned out to need no `EReal`-valued Corollary 10.8.1. What is left of §24 is Rockafellar's
*construction* `f(x) = ∫ₐˣ φ` and Corollary 24.2.1, both irreducibly statements about an integral.
Corollary 31.5.2 — `∂f` is maximal *monotone* — is a different, easier statement and does not wait
on any of this.

**Relocation candidates.** `coe_sub_add_coe` belongs in `Tdaf/Order/EReal.lean`; `conj_add_coe` in
`Duality/Conjugate.lean`; `subgradient_add_coe`, `subgradientRel_add_coe` and
`exists_coe_of_subgradient_nonempty` in `Subgradient/Defs.lean`. In the other direction, `cycleVal`
and its API belong *here*, beside `chainVal`, rather than in `OneDim.lean` where they were written.

### `Tdaf/Analysis/Convex/Subgradient/OneDim.lean`

§24's one-dimensional theory: **Theorems 24.1 and 24.3**, and **Theorem 24.2's uniqueness clause**.

```lean
noncomputable def rightDeriv (f : ℝ → EReal) (x : ℝ) : EReal        -- `f'₊(x)`
noncomputable def leftDeriv  (f : ℝ → EReal) (x : ℝ) : EReal        -- `f'₋(x)`
def cycleVal …                                     -- `chainVal` specialised to `ℝ`
theorem leftDeriv_le_rightDeriv … ; theorem rightDeriv_le_leftDeriv …            -- Thm 24.1
theorem monotone_rightDeriv … ; theorem monotone_leftDeriv …
theorem mem_subgradientRel_iff …                   -- `f'₋(x) ≤ y ≤ f'₊(x)`
theorem iInf_rightDeriv_Ioi … (and three siblings) -- the one-sided limit formulas
theorem exists_eq_add_coe_of_le_le …               -- Thm 24.2, uniqueness
theorem isMaximalMonotoneRel_iff_exists_closedProperConvexFn …                   -- Thm 24.3
```

**Theorem 24.3 is stated as "maximal monotone = maximal chain".** Rockafellar's *complete
non-decreasing curves* in `ℝ²` are exactly the maximal chains of `ℝ × ℝ` for the coordinatewise
order, and `isMonotoneRel_iff_forall_le_or_le` is the bridge. `mem_subgradientRel_iff` then
describes each such curve as the region `f'₋(x) ≤ y ≤ f'₊(x)`, which is the geometric content.

**`rightDeriv_le_leftDeriv` (`f'₊(y) ≤ f'₋(z)` for `y < z`) needs only properness, not convexity.**
`dirDeriv` is an *infimum* of difference quotients rather than a limit, so the comparison across a
gap is free. Convexity enters only at a single point, in `leftDeriv_le_rightDeriv`.

**Relocation candidates.** `innerₗ_real_apply` belongs in `Duality/Pairing.lean`;
`tendsto_nhdsWithin_Ioi_of_monotone`, `tendsto_nhdsWithin_Iio_of_monotone` and
`exists_max_mem_of_ne_nil` are pure Mathlib material and belong in an order/list file; `cycleVal`
and its API belong in `Subgradient/Monotone.lean`.

**Rockafellar's two-sided finiteness condition is `x ∈ interior (dom f)`.** "`f'₊ < +∞` left of the
right endpoint and `f'₋ > -∞` right of the left endpoint" unwinds, on the line, to exactly that
(`bot_lt_leftDeriv_and_rightDeriv_lt_top_iff`), which is worth knowing because it is how §25 quotes
the condition.

### `Tdaf/Analysis/Convex/Subgradient/Differentiability.lean`

**Theorem 25.3** in full and **Theorem 25.4**'s continuity and density clauses — §25 read on the
line, where differentiability of a convex function is a statement about the jump set of a monotone
function.

```lean
theorem continuousAt_rightDeriv_iff …            -- Thm 24.1 as a criterion
theorem countable_leftDeriv_ne_rightDeriv …      -- the jump set of `f'₊` is countable
theorem differentiableAtFn_iff_leftDeriv_eq_rightDeriv …        -- Thms 25.2 + 25.3
theorem countable_not_differentiableAtFn … ; theorem continuousAt_rightDeriv_of_differentiableAtFn …
theorem subset_closure_differentiableAtFn …                     -- Thm 25.3, density
theorem convexFn_lineRestrict … ; theorem proper_lineRestrict … ; theorem dirDeriv_lineRestrict …
theorem continuousAt_dirDeriv_iff …                             -- Thm 25.4, continuity
theorem subset_closure_twoSided_dirDeriv …                      -- Thm 25.4, density
```

**Countability is Mathlib's, not a jump-summing argument.** `Monotone.countable_not_continuousAt`
applies verbatim to `EReal`-valued monotone functions — see gotcha ER9 — so the whole of Theorem
25.3's first assertion is `monotone_rightDeriv` plus that.

**Two of Theorem 25.3's three clauses need neither closedness nor the book's extension step.**
Rockafellar opens by extending `f` and then quotes Theorem 24.1 in full. Only the *easy* half of
the continuity criterion is used, and that half is the sandwich
`⨆ {f'₊(z) | z < x} ≤ f'₋(x) ≤ f'₊(x)`, whose ingredients (`rightDeriv_le_leftDeriv`,
`leftDeriv_le_rightDeriv`, `monotone_rightDeriv`) need only `ConvexFn` and `Proper`. `ClosedFn`
enters exactly once, in `continuousAt_rightDeriv_of_differentiableAtFn`. This is what lets Theorem
25.4's density clause carry no closedness hypothesis either.

**Theorem 25.3's "relative to `D`" is an artefact of the book's notation.** Rockafellar's `f'`
exists only on the set `D` where `f` is differentiable, so he can only say "continuous and
non-decreasing relative to `D`". `rightDeriv f` is defined on the whole line and agrees with `f'`
on `D`; what Theorem 24.1 proves is `ContinuousAt (rightDeriv f) x` in the ordinary sense, and
monotonicity is global — it is `monotone_rightDeriv` in `OneDim.lean`, with no restricted version
needed.

**Theorem 25.4 needs no `y ≠ 0`, no one-dimensional limit theory, and no measure zero.** At `y = 0`
both sides hold (`f'(z; 0) = 0` near an interior point, and `0 = -0`). The `⇐` direction is
Corollary 24.5.1 twice, at `y` and at `-y`; the `⇒` direction, which the book gets from
`lim_{λ↑₀} g'₊(λ) = g'₋(0)`, is a single term of *each* defining infimum —
`f'(x - λy; y) ≤ (f x - f (x - λy))/λ ≤ -f'(x; -y)` for every `λ > 0`, no limit taken and no
convexity used — so Rockafellar's identity `liminf_{z→x} f'(z; y) = -f'(x; -y)` is avoidable. And
the density clause restricts to the line through `x` in direction `y` and quotes Theorem 25.3's
countability, so `subset_closure_twoSided_dirDeriv` carries **no** `[FiniteDimensional ℝ E]`; only
the continuity clause does, through Corollary 24.5.1.

**Not here**: Theorem 25.4's measure-zero clause and its `Sₖ` decomposition. The first needs Haar
measure on `E` and Rockafellar's Fubini step. The second needs (a) upper semicontinuity of
`z ↦ f'(z; y) + f'(z; -y)` on `int (dom f)` — an `EReal`-sum-of-usc lemma, harmless because both
summands are finite there — and (b) "a monotone function bounded on `[a, b]` has finitely many
jumps of size `≥ 1/k` there", an induction over an ordered `Finset` the project does not have.
Neither is needed for the density clause, which goes a different way.

**Relocation candidates.** `convexFn_lineRestrict` and `proper_lineRestrict` belong in
`Epigraph.lean` or `Operations/Basic.lean`, and `dirDeriv_lineRestrict` in `Subgradient/Defs.lean`:
they are general facts about composing with an affine parametrisation of a line, with nothing
§25-specific about them, and `dirDeriv_lineRestrict` is the natural bridge for every future
"restrict to a line" argument. `upperSemicontinuousAt_dirDeriv_left` belongs in
`Subgradient/Convergence.lean` immediately after `upperSemicontinuousAt_dirDeriv`, of which it is a
one-line slice. `dirDeriv_sub_smul_le` belongs in `Subgradient/Defs.lean` with the rest of Theorem
23.1.

### `Tdaf/Analysis/Convex/Subgradient/Primitive.lean`

**Theorem 24.2 in full** — the existence clause included, and with no integration theory.

```lean
def monotoneCurve (φ : ℝ → EReal) : SetRel ℝ ℝ          -- Rockafellar's `Γ(φ)`
theorem isMonotoneRel_monotoneCurve … ; theorem exists_mem_monotoneCurve_sub …
theorem isMaximalMonotoneRel_monotoneCurve …
theorem subgradientRel_eq_monotoneCurve_rightDeriv …     -- the converse: every `∂f` is such a curve
theorem exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq …    -- Thm 24.2, existence
theorem exists_closedProperConvexFn_forall_le_le …                  -- Thm 24.2, in full
```

**Theorem 24.2's existence clause needs no integral.** `OneDim.lean` used to record the missing
`∫ₐˣ φ` as the obstruction, and the plan carried the dependency "Theorem 24.2 existence ⇒ improper
integral of a monotone `EReal`-valued function". Both were wrong. What Rockafellar's `f` has to be
is characterised by its *graph*, and the graph is directly constructible: `monotoneCurve φ` is the
complete non-decreasing curve filling in `φ`'s jumps, and **Theorem 24.3** — already proved, and
proved through cyclic monotonicity rather than through 24.2, so not circular — hands back a closed
proper convex `f` with `∂f = Γ(φ)`. What remains genuinely integral-shaped is only Rockafellar's
*formula* `f(x) = ∫ₐˣ φ(t) dt` and Corollary 24.2.1.

**`Γ(φ)` is a chain for every `φ`, monotone or not.** `y₀ ≤ φ⁺(x₀) ≤ φ(t) ≤ φ⁻(x₁) ≤ y₁` for any `t`
strictly between `x₀` and `x₁`, and no hypothesis on `φ` enters. Monotonicity of `φ`, and finiteness
of `φ` at one point, are used only for **maximality**.

**Maximality goes through the antidiagonal.** Rockafellar calls "`(x, x*) ↦ x + x*` is a bijection
of `Γ(φ)` onto `ℝ`" an elementary exercise and then never uses it. Only *surjectivity* is needed,
and with it maximality is three lines: two comparable points of a chain with equal coordinate sums
are equal. The direct route splits into four or five `±∞` cases and is much worse.

**Rockafellar's convention for `f'₊`/`f'₋` outside `dom f` is the project's `rightDeriv`/`leftDeriv`
exactly** — both `−∞` to the left of `dom f`, both `+∞` to the right. This is worth recording
because the definitions (an `iInf`/`iSup` guarded by an existence condition) make it look as though
the signs were swapped, and Theorem 24.2 is *false* under the swapped reading.

**Relocation candidates.** `eq_and_eq_of_forall_coe_mem_iff` and
`eq_bot_or_eq_top_of_forall_not_coe_mem` are pure `EReal` order facts and belong in
`Tdaf/Order/EReal.lean`. `monotoneCurve` and its five companions are the "complete non-decreasing
curve" material and arguably belong at the end of `OneDim.lean`, right after
`isMaximalMonotoneRel_iff_exists_closedProperConvexFn`; this module would then hold Theorem 24.2
alone.

### `Tdaf/Analysis/Convex/Subgradient/Integral.lean`

**Corollary 24.2.1**: a convex function of one variable is the integral of either of its one-sided
derivatives.

```lean
theorem sub_eq_intervalIntegral_derivWithin_Ioi …   -- in Mathlib's vocabulary
theorem rightDeriv_eq_coe_derivWithin …             -- the bridge
theorem sub_eq_intervalIntegral_rightDeriv …        -- **Cor 24.2.1**, `f'₊`
theorem sub_eq_intervalIntegral_leftDeriv …         -- **Cor 24.2.1**, `f'₋`
```

**The fundamental theorem of calculus applies with nothing to spare.**
`intervalIntegral.integral_eq_sub_of_hasDeriv_right` asks for three things — continuity on the
closed interval, a derivative *from the right* at each interior point, and interval integrability
of that derivative — and convexity supplies exactly those three: Theorem 10.1
(`ConvexOn.continuousOn_interior`), `ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`, and
`ConvexOn.monotoneOn_rightDeriv` with `MonotoneOn.intervalIntegrable`. **No a.e. differentiability
and no Lebesgue theory of monotone functions is involved**, which is worth knowing because the
plan had this corollary filed with Theorem 25.4's measure-zero clause as "needs measure theory".

**The bridge is the only real work, and it is where `interior` enters.** `rightDeriv f t` is an
`EReal` infimum of difference quotients — the right definition when `f` can be infinite — while
Mathlib's right derivative is a limit, computed as `sInf (slope f t '' {z ∈ dom f | t < z})`. The
`EReal` infimum ranges over *all* steps `a > 0`, including those landing outside `dom f`, where the
quotient is `⊤`; that is harmless but it is why `rightDeriv_eq_coe_derivWithin` asks for
`t ∈ interior (dom f)` rather than for `f t` finite. The proof is `le_antisymm`: `csInf_le` at each
admissible slope one way, and `EReal.lt_iff_exists_real_btwn` followed by `exists_lt_of_csInf_lt`
the other.

**`sub_div_eq_coe_slope` needs no order relation between the two points.** At `z = t` both sides
are `0` — Mathlib's `slope f a a` is `0 / 0 = 0`, and the `EReal` quotient divides by `0` — so the
`t < z` hypothesis that the callers have anyway is not part of the lemma.

**The left-derivative half needs no second bridge.** `f'₋` and `f'₊` differ only on the jump set of
`f'₊`, which `countable_leftDeriv_ne_rightDeriv` shows countable, hence null; the two integrals then
agree by `intervalIntegral.integral_congr_ae`.

**Not here**: Theorem 24.2's integral *formula*. The book defines `f (x) = ∫ₐˣ φ` for an arbitrary
nondecreasing `φ : ℝ → [-∞, +∞]` and proves `f` closed proper convex with `f'₋ = φ₋ ≤ φ ≤ φ₊ = f'₊`.
That needs the integral at the finite endpoints of the interval where `φ` is finite, as a limit of
Riemann integrals, and `+∞` outside — an improper integral. `Primitive.lean` already proves the
theorem's *existence* half with no integral at all, so only the formula is missing.

### `Tdaf/Analysis/Convex/Subgradient/Convergence.lean`

**Theorems 24.5 and 24.6 in full**, with **Corollary 24.5.1**.

```lean
theorem eventually_dirDeriv_lt …                          -- Thm 24.5, first half
theorem subgradient_subset_add_closedBall_of_forall_dirDeriv_le …   -- the shared endgame
theorem eventually_subgradient_subset_add_closedBall …    -- Thm 24.5, second half
theorem upperSemicontinuousAt_dirDeriv … ; theorem eventually_nhds_subgradient_subset_add_closedBall …
theorem eventually_dirDeriv_lt_of_tendsto_dir …           -- Thm 24.6, first assertion
theorem eventually_mem_interior_dom_of_tendsto_dir …      -- the step the book leaves implicit
theorem subgradient_dirDeriv …                            -- Cor 23.5.3 + Thm 23.2 + Cor 23.5.2
theorem subgradient_dirDeriv_eq_sep_normalCone … ; theorem isExposed_subgradient_dirDeriv …
theorem eventually_subgradient_subset_exposed_add_closedBall …     -- Thm 24.6, second assertion
```

**Theorem 24.6's first assertion needs neither the simplex construction nor closedness of `f`.**
Rockafellar builds a polytope (Theorems 20.5 and 10.2) only to make `f` continuous relative to it
at the point being approached. Using monotonicity of the difference quotient in its step — replace
the vanishing step `|xᵢ − x|` by a fixed larger one — moves all the continuity to *interior*
points, where Theorem 10.1 applies. `ConvexFn f` and `Proper f` suffice.

**Theorem 24.5 needs no "the sequence lies in `C`" hypothesis.** `xᵢ → x ∈ U` is enough; the proof
repairs the finitely many stray indices.

**Relocation candidates.** `supportFn_closedBall` belongs in `Duality/Support.lean`;
`tendsto_eval_of_tendsto` in `Analysis/Convex/Convergence.lean` (the §10 module of that name);
`dirDeriv_eq_bot_of_eq_top`, `dirDeriv_eq_coe_toReal_of_mem_interior_dom`,
`convexOn_toReal_dirDeriv`, `toReal_dirDeriv_smul`, `mem_interior_dom_dirDeriv` and
`proper_dirDeriv_of_ne_bot` in `Subgradient/Existence.lean`; `mem_interior_dom_smul` and
`eventually_mem_interior_dom_of_tendsto_dir` in `Epigraph.lean` or `RelativeInterior.lean`.
`subgradient_dirDeriv`, `subgradient_dirDeriv_eq_sep_normalCone` and
`isExposed_subgradient_dirDeriv` are pure §23 material — a general pairing, no sequences — and
belong in `Subgradient/Existence.lean` beside `dirDeriv_eq_supportFn_of_mem_relint_dom`;
`subgradient_subset_add_closedBall_of_forall_dirDeriv_le` has no sequences in it either and would
sit as comfortably in `Subgradient/Bounded.lean`.

**Neither of the two obstructions this entry used to record was real.** They were: an
`EReal`-valued Corollary 10.8.1 for the uniformity step, and Corollary 23.5.3 for identifying the
limit set. Both dissolved.

**The `xᵢ` are eventually interior, so the existing Corollary 10.8.1 applies verbatim.** The worry
was that `f'(xᵢ; ·)` takes `+∞` when `xᵢ` is a boundary point of `dom f`. But
`xᵢ = x + ‖xᵢ − x‖ • yᵢ` with `yᵢ → y`, and the theorem's own hypothesis `x + αy ∈ int (dom f)`
together with openness gives `x + α yᵢ ∈ int (dom f)` for large `i`; `mem_interior_dom_smul` — the
segment principle, already in this file — carries interiority back to the smaller step
`‖xᵢ − x‖`. `eventually_mem_interior_dom_of_tendsto_dir` is that step, and no subsequence
extraction or compactness argument is involved. A consequence the book does not remark on: `∂f(xᵢ)`
is **compact** for large `i`.

**Identifying the limit set is six lines, not a missing theorem.** `subgradient_dirDeriv` says
`∂(f'(x; ·))(y) = ∂f(x)_y`, and it composes `clFn_dirDeriv` (Thm 23.2), `subgradient_clFn`
(Cor 23.5.2) and `subgradient_supportFn` (Cor 23.5.3) — all three of which the library already had.
The face is delivered three ways: as `∂f(x) ∩ {y is normal there}`
(`subgradient_dirDeriv_eq_sep_normalCone`), and as Mathlib's `IsExposed`
(`isExposed_subgradient_dirDeriv`), which hands over `IsExposed.isFace` for free.

**Non-emptiness of `∂f(x)` is a consequence, not a hypothesis**, and **`f` need not be closed.**
The book writes `∂f(x)_y`, presupposing `∂f x ≠ ∅`; that follows from properness of `f'(x; ·)`
through Theorem 23.3's `subgradient_eq_empty_iff_exists_dirDeriv_eq_bot`. Both assertions of
Theorem 24.6 need only `ConvexFn f` and `Proper f`, where the book says "closed proper convex".
`hxsdom : ∀ i, xs i ∈ dom f` is likewise redundant, and is kept only because
`eventually_dirDeriv_lt_of_tendsto_dir` still asks for it.

### `Tdaf/Analysis/Convex/Subgradient/Bounded.lean`

**Theorem 24.7**: `∂f` maps compact subsets of `int (dom f)` to non-empty compact sets.

```lean
theorem exists_lipschitz_forall_pairing_le_of_isCompact …     -- the shared constant, Thm 10.4
theorem isCompact_subgradient …
theorem isCompact_image_subgradientRel …                      -- Thm 24.7
```

**Theorem 24.7 needs neither Corollary 24.5.1 nor §13**, contrary to the plan: Theorem 10.4 alone
does it, and a *single* Lipschitz constant serves all three conclusions at once.

**Relocation candidate.** `Convex.interior_subset_relint` belongs in `RelativeInterior.lean`.

### `Tdaf/Analysis/Convex/Subgradient/Gradient.lean`

§25's differentiability theory: **Theorems 25.1 and 25.2** in full, with **Corollary 25.1.1**.

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
What sufficiency gets used for is also available algebraically as
`subgradient_eq_singleton_of_dirDeriv_eq`, over an arbitrary pairing with `Function.Injective B.flip`.

**Theorem 25.2's sufficiency needs no compactness — a cross-polytope does it.** This entry and
§5.4 both used to record "Gateaux ⇒ Frechet needs uniform convergence of the difference quotients
over the compact unit sphere". It does not. Write `z - x = ∑ j, ξ j • b j` in a basis, put
`S = ∑ j, |ξ j|`, and observe that `z` is the convex combination, with weights `|ξ j| / S`, of the
`n` points `x + (S · sign (ξ j)) • b j` — all at the *same* distance `S` from `x`, along a basis
direction. One one-sided estimate therefore covers all of them and Jensen (`ConvexFn.sum_le`)
reassembles. The proof is quantitative, basis-explicit, and needs no continuity of `f`.

**So Rockafellar's strengthening is the primitive statement, not a corollary.** The estimate
consumes only the `2n` one-sided derivatives along `±b j`, so
`differentiableAtFn_of_forall_basis_dirDeriv_eq` is proved *first* and `hasGradientAt_of_dirDeriv_eq`
is that statement read at an arbitrary basis — the reverse of the book's order. Three further
hypotheses fall away with it: sufficiency needs **neither Theorem 7.2, nor Theorem 4.8, nor Theorem
23.2** (the book routes "dom `f'(x;·)` = ℝⁿ ⇒ proper ⇒ linear ⇒ `∂f x` a singleton ⇒ differentiable",
where the estimate gives `f'(x; v) ≤ ⟨v, y₀⟩` in every direction directly and Theorem 23.1 supplies
the reverse), and **neither properness nor `x ∈ int (dom f)`** — the two-sided estimate
`f x + ⟨z - x, y₀⟩ ≤ f z ≤ f x + ⟨z - x, y₀⟩ + ε‖z - x‖` produces local finiteness by itself, which
makes Corollary 25.1.1 a consequence here rather than a prerequisite.

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

**Not done**: Thms 25.5–25.7 (25.5 is Rademacher plus Thm 24.4; 25.6 and 25.7 rest on 25.5 and
Thms 10.6–10.9) — Thms 25.3 and 25.4 are in `Subgradient/Differentiability.lean` — and the
*differentiability* reading of Cors 25.1.2–25.1.3 — "the exposed points of `epi f*` are the `(x*, f*(x*))` with `f` differentiable
at some `x` and `∇f x = x*`". The geometry gives `∂f x = {x*}`; upgrading that to differentiability
is exactly **the converse half of Theorem 25.1**. The route, worked out but not started: (a) `∂f x`
a singleton ⇒ the normal cone of `dom f` at `x` is trivial ⇒ `x ∈ int (dom f)`, a
separation/normal-cone argument; (b) hence `f'(x; ·)` is finite everywhere, so convex, continuous
and closed, which removes the closure subtlety in Rockafellar's proof and lets
`clFn_dirDeriv_eq_of_subgradient_eq_singleton` (Thm 23.2) give `f'(x; ·)` linear *everywhere*;
(c) a compactness step on the unit sphere.

**Only step (a) of that route is still missing.** Step (c) is now free — it is
`hasGradientAt_of_dirDeriv_eq`, and the cross-polytope argument removed the compactness — and step
(b) follows from `clFn_dirDeriv_eq_of_subgradient_eq_singleton` once (a) holds. What (a) needs,
precisely, is: *for a convex `C` in finite dimensions and `x ∈ C`, `normalCone B C x = {0}` implies
`x ∈ interior C`* (Theorem 11.6 territory — a separation argument with a case split on whether
`interior C` is empty). Its easy companion
`subgradient B f x + normalCone B (dom f) x ⊆ subgradient B f x` is three lines from the
definitions and is not present either.

**Relocation candidates**: `mem_exposedPoints_prod_Ici_iff` is a general fact about exposed points
of a half-cylinder and belongs beside `epi_indicatorFn` in `Indicator.lean` or in a general
exposed-points module; `Proper.eq_sub_of_mem_subgradient` belongs in `Subgradient/Defs.lean` with
the rest of Theorem 23.5.

### `Tdaf/Analysis/Convex/Subgradient/Uniqueness.lean`

**Theorem 25.1's converse half**, and with it the differentiability reading of Corollaries 25.1.2
and 25.1.3.

```lean
theorem mem_dom_of_mem_subgradient …
theorem mem_interior_dom_of_subgradient_eq_singleton …     -- the step the book passes over
theorem closedFn_dirDeriv_of_mem_interior_dom …            -- removes the `cl` from Thm 23.2
theorem hasGradientAt_evalCLM_of_subgradient_eq_singleton …
theorem hasGradientAt_iff_subgradient_eq_singleton …        -- **Thm 25.1** in full
theorem mem_exposedPoints_epi_conj_iff_hasGradientAt …      -- **Cor 25.1.2**
theorem mem_exposedPoints_supportSet_iff_hasGradientAt …    -- **Cor 25.1.3**
```

**The whole difficulty is one word in Rockafellar's proof.** He assumes only "`f` finite at `x`"
and then applies Theorem 23.2, which computes `cl f'(x; ·)`, not `f'(x; ·)`. The closure is
harmless exactly when `x ∈ int (dom f)`, and *that* is what a unique subgradient has to be made to
give. Two new lemmas do it:

* `subgradient_add_normalCone_dom_subset` (`Subgradient/Calculus.lean`) —
  `∂f x + N_{dom f}(x) ⊆ ∂f x`, layer A, no convexity and no topology. A singleton `∂f x` therefore
  forces `N_{dom f}(x) = {0}` (`normalCone_dom_eq_zero_of_subgradient_eq_singleton`).
* `mem_interior_of_normalCone_eq_zero` (`Subgradient/Existence.lean`) — in finite dimensions a
  convex set is a neighbourhood of every point at which its normal cone is trivial. This is
  Corollary 11.6.1 read through the pairing, and finite-dimensionality is not decoration: the span
  of an orthonormal basis in a Hilbert space is convex, dense, has empty interior, and has trivial
  normal cone everywhere. What replaces the missing interior in finite dimensions is that a convex
  set with no interior lies in a proper affine subspace.

**Theorem 23.4's interiority clause is not a shortcut.** `bddAbove_subgradient_iff_mem_interior_dom`
says `∂f x` bounded ↔ `x ∈ int (dom f)` — but only under the hypothesis `x ∈ ri (dom f)`, which is
most of what has to be proved. A singleton is bounded, so the equivalence looks like it settles the
matter, and it does not.

**The route through Corollary 24.5.1 saves nothing here.** Upper semicontinuity of `∂f` gives the
Fréchet estimate directly — the sandwich
`0 ≤ f z - f x - ⟨z - x, y₀⟩ ≤ ⟨z - x, y - y₀⟩ ≤ ε‖z - x‖` — and that is what
`Saddle/Differential.lean` does for saddle-functions, where no `dirDeriv` API exists. It needs the
same interior step (Corollary 24.5.1 and Theorem 23.4 both want `x ∈ int (dom f)`), and it would
duplicate Theorem 25.2 rather than use it.

**The general-pairing statement is `hasGradientAt_evalCLM_of_subgradient_eq_singleton`**, whose
gradient is `evalCLM B y₀`. The `topDualPairing` corollaries are the ones with an *equivalence*,
because the forward half (`HasGradientAt.subgradient_eq`) exists only there: for a general pairing
a non-injective `evalCLM` would make `∂f x` a whole fibre rather than a point.

### `Tdaf/Analysis/Convex/Subgradient/Reconstruction.lean`

**Theorem 25.6**: for a closed proper convex `f` with `int (dom f) ≠ ∅`,

```
∂f x = cl (conv S(x)) + N_{dom f}(x)     for every x,
```

where `S(x) = gradientLimits f x` is the set of limits of gradients at points of differentiability
tending to `x`.

```lean
def gradientLimits (f : E → EReal) (x : E) : Set E                -- Rockafellar's `S (x)`
theorem gradientLimits_subset_subgradient …                       -- `S x ⊆ ∂f x`, Thm 24.4
theorem inner_add_smul_le_of_mem_subgradient …                    -- the inequality, in ℝ
theorem containsNoLine_subgradient …                              -- `∂f x` contains no line
theorem recessionCone_subgradient_subset_normalCone …             -- `0⁺(∂f x) ⊆ N_{dom f}(x)`
theorem exists_mem_interior_dom_of_forall_normalCone …            -- the separation step
theorem exists_seq_differentiableAtFn_tendsto_dir …               -- the approach sequence
theorem exposedPoints_subset_gradientLimits …                     -- the substantive step
theorem subgradient_eq_closure_convexHull_gradientLimits_add_normalCone …   -- **Thm 25.6**
```

**The recession cone of `∂f x` is never computed.** Rockafellar identifies `N_{dom f}(x)` with
`0⁺(∂f x)` and uses the identification three times. Each use follows more cheaply from the
*inclusion* `∂f x + N_{dom f}(x) ⊆ ∂f x` — `subgradient_add_normalCone_dom_subset`, which needs
neither convexity nor a topology — plus "let `λ → ∞` in the subgradient inequality", which is the
same three lines every time. `containsNoLine_subgradient` and
`recessionCone_subgradient_subset_normalCone` are those arguments; the equality of the two cones
is not stated anywhere.

**The separation step is `geometric_hahn_banach_open`.** The book deduces from "the half-line
`{x + α y}` cannot be *properly* separated from `dom f`" that it meets `int (dom f)`, citing
Theorem 11.3 and then Theorem 6.1. The contrapositive is all that is needed and Mathlib proves it
directly: if the half-line misses the open convex `int (dom f)`, the separating functional's Riesz
representative is a non-zero normal at `x` with `⟨y, y*⟩ ≥ 0`. Proper separation never enters, and
neither does §11.

**The approach sequence needs a quadratic tolerance.** Theorem 24.6 consumes the *direction*
`‖xᵢ - x‖⁻¹(xᵢ - x) → y`, not `xᵢ → x`; a point of differentiability within `εᵢ` of `x + εᵢ y`
controls the direction not at all, while one within `εᵢ²` puts the direction within `4εᵢ` of `y`.
That is the content of `exists_seq_differentiableAtFn_tendsto_dir`, and it is what the book's
half-sentence "let `xᵢ` be a point of differentiability near `x + εᵢ y`" is hiding.

**A zero exposing functional is the degenerate case, and it is the easy one.** `l = 0` exposes
`x*` exactly when `∂f x = {x*}`, and then Theorem 25.1's converse
(`hasGradientAt_of_subgradient_eq_singleton`) makes `f` differentiable at `x` itself, so `x*` is a
limit of gradients along the constant sequence. There is no ray to build — which is fortunate,
since there is no direction to build it in.

### `Tdaf/Analysis/Convex/Subgradient/GradientLimit.lean`

**Theorem 25.7**: convex functions finite and differentiable on an open convex set and converging
pointwise there to a function that is also finite and differentiable have converging gradients —
uniformly on every compact subset.

```lean
theorem dist_le_of_subgradient_subset …        -- singleton inclusion = gradient bound
theorem tendsto_of_hasGradientAt …             -- **Thm 25.7**, pointwise
theorem tendstoUniformlyOn_fderiv_toReal …     -- **Thm 25.7**, uniform on compacts
```

**Both clauses are Theorem 24.5 with the subdifferentials collapsed by Theorem 25.1.** The
pointwise clause is 24.5 at the constant sequence `xᵢ = x`; no contradiction argument, no
compactness, and — unlike the book — no appeal to Theorem 10.8, which 24.5 has already absorbed.
The uniform clause runs the contradiction **once, on the norm**, rather than one partial derivative
at a time: a failure of uniform convergence gives indices `φ n` and points `zₙ` of the compact set
with `‖∇f(zₙ) - ∇f_{φ n}(zₙ)‖ ≥ ε`, a convergent subsequence `zₙ → w` turns Theorem 24.5 (along the
subsequence) and Corollary 24.5.1 (at `w`) into two `ε/3` bounds, and the triangle inequality
closes it. Theorem 24.5 is stated for a *moving* sequence of points exactly so that this works.

### `Tdaf/Analysis/Convex/Subgradient/Rademacher.lean`

**Theorem 25.5**: a proper convex function on a finite-dimensional space is differentiable at
almost every point of `int (dom f)`, those points are dense there, and `∇f` is continuous on them.
Also **Corollary 25.5.1** and **Theorem 25.4**'s measure-zero clause.

```lean
theorem HasGradientAt.hasFDerivAt_toReal …            -- ∇f is `fderiv` of the real trace
theorem hasGradientAt_of_hasFDerivAt_toReal …         -- and conversely, at interior points
theorem exists_lipschitzOnWith_ball …                 -- Theorem 10.4 on a ball
theorem ae_differentiableAtFn …                       -- **Thm 25.5**, almost everywhere
theorem measure_diff_differentiableAtFn …             -- the same, as a null set
theorem interior_dom_subset_closure_differentiableAtFn …  -- **Thm 25.5**, density
theorem continuousOn_fderiv_toReal …                  -- **Thm 25.5**, `∇f` continuous
theorem continuousOn_fderiv_of_convexOn …             -- **Cor 25.5.1**
theorem measure_diff_twoSided_dirDeriv …              -- **Thm 25.4**, measure-zero clause
theorem mem_subgradient_innerL_iff …                  -- the Riesz bridge between the pairings
```

**Mathlib has Rademacher's theorem** — `Mathlib/Analysis/Calculus/Rademacher.lean`,
`LipschitzOnWith.ae_differentiableWithinAt_of_mem`, under `[FiniteDimensional]`, `[BorelSpace]` and
`[IsAddHaarMeasure μ]` — and that is what makes all of this cheap. Sub-plan 5 guessed as much and
the guess was right. Convexity only has to supply local Lipschitz constants:
`exists_lipschitzOnWith_ball` shrinks Theorem 10.4's *compact* set to an *open* ball, so that
`DifferentiableWithinAt` upgrades to `DifferentiableAt`, and
`TopologicalSpace.isOpen_iUnion_countable` turns countably many a.e. statements into one.

**Rockafellar's implication runs the other way.** He proves Theorem 25.4's measure-zero clause
first, by a Fubini argument over lines through the `Sₖ` decomposition, and gets Theorem 25.5 by
intersecting the `n` coordinate directions. Here 25.5 comes first and 25.4's clause is two lines,
because differentiability supplies the two-sided derivative in *every* direction at once. Neither
the `Sₖ` decomposition nor Fubini is needed anywhere.

**The density clause carries no measure in its statement.** A non-empty open set has positive Haar
measure, so it cannot sit inside a null set; the proof borrows `Module.Basis.ofVectorSpace`'s
`addHaar` and the Borel structure locally, exactly as Mathlib's `dense_differentiableAt_norm` does.

**Two pairings meet here, and the bridge between them is an isometry.** Corollary 24.5.1 is stated
for `innerₗ E`, whose subgradients are *vectors*, while `HasGradientAt` produces an element of
`StrongDual ℝ E`. `mem_subgradient_innerL_iff` translates, and because `InnerProductSpace.toDual`
is a `LinearIsometryEquiv` the `ε` of the upper-semicontinuity statement survives unchanged — which
is the entire proof of the continuity clause.

**Not here**: Theorems 25.6 and 25.7.

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

**`legendreConj` itself is deliberately not defined**: it would need a choice function for
`(∇f)⁻¹` and would then have to be proved equal to `conj B f` on `D` — `conj_eq_of_hasGradientAt`
states that equality without the detour. (`EssentiallySmooth`, `EssentiallyStrictlyConvex` and
`LegendreType` were withheld for the same reason until 26.1 became reachable; they now live in
`EssentiallySmooth.lean`, `StrictlyConvex.lean` and `LegendreType.lean`.)

The file's one private helper, `eq_coe_of_coe_add_eq_coe`, solves `(r : EReal) + c = (s : EReal)`
for `c`; the two infinities are excluded by the equation itself. Promote it to `Tdaf/Order/EReal.lean`
if a second consumer appears.

### `Tdaf/Analysis/Convex/Subgradient/LegendreType.lean`

§26's second half: **Corollary 26.4.1** and **Theorem 26.5**.

```lean
def gradientRange (f : E → EReal) : Set E                       -- Rockafellar's `D`, in vector form
def LegendreType (f : E → EReal) : Prop                         -- essentially smooth + strictly convex on `int (dom f)`
theorem hasGradientAt_toDual_iff_mem_subgradient …              -- the whole file, in one line
theorem gradientRange_eq_domSubgradient_conj …                  -- **Cor 26.4.1**: `D = dom ∂f*`
theorem legendreType_conj_iff …                                 -- **Thm 26.5**, first assertion
theorem hasGradientAt_conj_iff …                                -- **Thm 26.5**: `∇f* = (∇f)⁻¹`
theorem bijOn_gradient_of_legendreType …                        -- **Thm 26.5**: `∇f : C ≅ C*`
theorem bijOn_gradient_univ_iff …                               -- **Thm 26.6**
```

**Everything here is `hasGradientAt_toDual_iff_mem_subgradient` plus Corollary 23.5.1.** For an
essentially smooth `f`, "`v` is *the* gradient at `x`" and "`v` is *a* subgradient at `x`" are the
same statement — Theorem 25.1 inside `int (dom f)`, and outside it both sides are impossible by the
substantive half of Theorem 26.1. Composing that with `∂f* = (∂f)⁻¹` turns every assertion of
Theorem 26.5 into a rewrite. In particular `∇f* = (∇f)⁻¹` costs three rewrites and no analysis.

**Theorem 26.5's duality is Corollary 26.3.1 applied twice.** `LegendreType f` unfolds, through
`subgradient_injective_iff`, into "`∂f` is single-valued **and** injective"; inverting `∂` swaps
those two conditions, so `legendreType_conj_iff` is `and_comm` on top of
`subsingleton_subgradient_conj_iff` and `pairwise_disjoint_subgradient_conj_iff`.

**Mathlib's `gradient` needs no wrapper.** `gradient (fun w => (f w).toReal)` is literally
`(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ …)`, which is what §25 already writes out by hand,
so Theorem 26.5's bijection is stated with an existing Mathlib function.

**`D` is not claimed convex.** Corollary 26.4.1 gives `ri (dom f*) ⊆ D ⊆ dom f*` and nothing
stronger, which is exactly Rockafellar's point: `D` is only "almost convex".

**Theorem 26.6 states co-finiteness as `dom f* = E`.** Rockafellar defines it through the recession
function (`f0+` is `+∞` off the origin) and only then identifies it with `dom f* = Rⁿ`, by
Corollary 13.3.1. The recession function *is* in the library — `Cofinite` in `Duality/Level.lean`,
with `cofinite_iff_dom_conj_eq_univ` — but it does not enter Theorem 26.6's proof, so the equation
is what this file uses; `Subgradient/Cofinite.lean` (Lemma 26.7) states the `Cofinite` form.
Everything else in Theorem 26.6 is Theorem 26.5 with `interior (dom f) = E`, which also makes
essential smoothness automatic — condition (c) quantifies over points outside the interior, and
there are none.

### `Tdaf/Analysis/Convex/Optimization/MoreauGradient.lean`

The last clause of **Theorem 31.5**: `x = ∇(f* □ w) z` and `x* = ∇(f □ w) z`.

```lean
theorem subgradient_infConv_quadFn …        -- ∂(f □ w) z = {prox (z | f*)}
theorem gradient_infConv_quadFn …            -- ∇(f □ w) z = z - prox (z | f)
theorem gradient_infConv_conj_quadFn …       -- ∇(f* □ w) z = prox (z | f)
```

**Theorem 26.3 is not needed**, although every plan document said it was. The route is shorter:
Corollary 23.5.1 turns `y ∈ ∂(f □ w) z` into `z ∈ ∂((f □ w)*) y`; Theorem 16.4 in its
*unconditional* direction (`conj_infConv`) rewrites `(f □ w)*` as `f* + w`; Theorem 23.8 splits
`∂(f* + w) y` into `∂f* y + {y}`; and what is left, `z - y ∈ ∂f* y`, is `prox_eq_iff`. A singleton
subdifferential is a gradient by Theorem 25.1's converse. Essential smoothness never enters.

**The dual formula is the same theorem applied to `f*`**, using `prox (z | f*) = z - prox (z | f)`
(`prox_conj_eq`, a restatement of `prox_add_prox_conj`).

**`w` had to be untranslated.** `Prox.lean` proves everything for `w (z - ·)`, because that is what
the Moreau objective needs; the subdifferential and exactness facts for `w` itself are the `z = 0`
instances, and `quadFn_zero_sub` is the one-line bridge.

### `Tdaf/Analysis/Convex/Subgradient/BoundaryDirDeriv.lean`

§26's **Lemma 26.2**: condition (c) of essential smoothness, in directional-derivative form.

```lean
theorem closedFn_lineRestrict …                                 -- a closed `f` restricted to a line is closed
theorem proper_lineRestrict_of_mem_dom …                        -- base point need not lie in `dom f`
theorem rightDeriv_lineRestrict_eq_dirDeriv …                   -- `g'₊(t) = f'(x + t y; y)`, also where `g t = ⊤`
theorem tendsto_dirDeriv_lineRestrict …                         -- **Thm 24.1** along the segment `[x, a]`
theorem rightDeriv_lineRestrict_zero_eq_bot_iff …               -- `g'₊(0) = −∞ ↔ ∂f x = ∅`
theorem subgradient_eq_empty_iff_tendsto_norm_fderiv …          -- condition (c) at `x` is `∂f x = ∅`
theorem essentiallySmooth_iff_tendsto_dirDeriv …                -- **Lemma 26.2**
```

**Both conditions are `∂f x = ∅`, and that is the whole proof.** Condition (c) is Theorem 24.4 in
one direction (a bounded subsequence of gradients has a convergent sub-subsequence, whose limit is
a subgradient) and Theorem 25.6 in the other (a subgradient makes `S(x)` non-empty). Condition (c')
is Theorem 24.1 on the restriction `g(t) = f(x + t(a − x))` — `lim_{t ↓ 0} g'₊(t) = g'₊(0)` — plus
Theorem 23.3 with Theorem 7.2 for `g'₊(0) = f'(x; a − x)`, which is
`dirDeriv_eq_bot_of_subgradient_eq_empty`. The two halves of Theorem 26.1's own proof are exactly
`subgradient_eq_empty_iff_tendsto_norm_fderiv`, now extracted and named.

**`proper_lineRestrict` was not enough.** It asks for the *base point* of the line to lie in
`dom f`, and Lemma 26.2's base point `x` is precisely the one that may not; the line still meets
`dom f` at `t = 1`, which is what `proper_lineRestrict_of_mem_dom` asks for instead.

**The `x ∉ dom f` branch is not a degenerate case, it is half the lemma.** There `g 0 = ⊤`, so
`rightDeriv g 0 = ⊥` by fiat (`rightDeriv_eq_bot_of_eq_top`) and `∂f x = ∅` because a subgradient
would put `x` in `dom f` — both sides of the equivalence hold, with no analysis at all.

**`f` is assumed closed, where the book says "no loss of generality".** Rockafellar replaces `f` by
`cl f` because (c) and (c') see only `C = int (dom f)`; transporting both conditions across `cl f`
costs more than it saves, and every §26 consumer already carries `ClosedFn f`.

### `Tdaf/Analysis/Convex/Subgradient/Preservation.lean`

§26's **Corollaries 26.3.2 and 26.3.3**: essential smoothness under `□` and under linear images.

```lean
theorem StrictConvexOnFn.add_convexFn …                         -- layer A: strict + convex is strict
theorem StrictConvexOnFn.compLin …                              -- layer A: pull back along an injection
theorem IsExactSum.essentiallySmooth_infConv …                  -- **Cor 26.3.2**, D5 form
theorem essentiallySmooth_infConv_of_relint …                   -- **Cor 26.3.2**, the book's `ri` form
theorem IsExactImage.essentiallySmooth_mapLin …                 -- **Cor 26.3.3**, D5 form
theorem essentiallySmooth_mapLin_of_relint …                    -- **Cor 26.3.3**, the book's `ri` form
```

**The `ri` hypotheses are D5 interfaces, and the `of_relint` bridges already existed.**
`IsExactSum.of_relint` and `IsExactImage.of_relint` (`Duality/Relint.lean`) supply the instances
from Rockafellar's `ri (dom f₁*) ∩ ri (dom f₂*) ≠ ∅` and `A' y* ∈ ri (dom f*)` respectively, so no
new constraint qualification had to be built.

**Corollary 26.3.3 instantiates `IsExactImage` at the transpose, not at `A`.** The identity being
used is `A f = (f* A')*`, so the interface is `IsExactImage (innerₗ G) (innerₗ E) A' A hA f*`: the
interface's "`A`" is the transpose `A' : G →ₗ E` and its "`A'`" is `A`. The adjointness datum
`hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A` unfolds to `⟪y, A x⟫ = ⟪A' y, x⟫`, which is the
ordinary relation with the arguments in the order the interface wants.

**"`A` onto" is only `Function.Injective A'`.** That is what the strict-convexity transfer consumes,
so the interface-level theorem asks for the injectivity and
`injective_of_isAdjointPair_of_surjective` derives it for the `ri` corollary.

**Finiteness on `C` is a hypothesis of `StrictConvexOnFn.add_convexFn`.** Where `f x = ⊤` the strict
inequality for `f` is vacuous while the one for `f + g` is not, so both summands must be known real
on `C`. At the use site `C ⊆ dom ∂(f₁* + f₂*) ⊆ dom (f₁* + f₂*)` and `dom_add` splits it.

### `Tdaf/Analysis/Convex/Subgradient/Cofinite.lean`

§26's **Lemma 26.7**: co-finiteness as blow-up of `‖∇f‖` at infinity.

```lean
theorem forall_tendsto_norm_atTop_iff_isBounded …               -- sequences ↔ bounded sublevel sets of `‖g‖`
theorem isBounded_setOf_norm_gradient_le_of_dom_conj_eq_univ …  -- easy half, **Thm 24.7**
theorem gradientRange_subset_interior_dom_conj_of_isBounded …   -- `∇f(E)` is open
theorem isClosed_gradientRange_of_isBounded …                   -- `∇f(E)` is closed
theorem cofinite_iff_forall_tendsto_norm_gradient_atTop …       -- **Lemma 26.7**
```

**Recast the sequential condition first.** "`‖∇f xᵢ‖ → ∞` whenever `‖xᵢ‖ → ∞`" is equivalent to
"`{x | ‖∇f x‖ ≤ b}` is bounded for every `b`", by a lemma with no convexity in it at all
(`forall_tendsto_norm_atTop_iff_isBounded`). Doing this before touching convexity removes *every*
sequence extraction from the mathematics.

**The hard half is connectedness, not a boundary point.** Rockafellar picks a boundary point `x*`
of `dom f*` and splits on `∂f*(x*)` being empty or unbounded. Producing that boundary point in Lean
means running "the segment from an interior to an exterior point crosses the boundary", and the
empty branch then needs a sequence in `ri (dom f*)` converging to `x*` plus Theorem 24.4. Instead:
`D = ∇f(E)` is open (its normal cone in `dom f*` is trivial, Corollary 11.6.1) and closed
(continuity of `∇f`, Theorem 25.5), `D` is non-empty, and `E` is connected. The book's two cases
are the two ways `D` could fail to be clopen.

**The half-line replaces "`∂f*(x*)` is unbounded".** `subgradient_add_normalCone_dom_subset`
(`Subgradient/Calculus.lean`) says `∂f*(x*) + N_{dom f*}(x*) ⊆ ∂f*(x*)`, so a non-zero normal `n`
puts `x + t n`, `t ≥ 0`, inside `∂f*(x*)` — every one of those points has gradient `x*`, so the
sublevel set at height `‖x*‖` is unbounded. Theorem 23.4's boundedness clause is never used, which
matters because it carries an `x ∈ ri (dom f)` hypothesis that would have to be supplied for `f*`.

**Corollary 24.5.1 is not used either**, contrary to the prediction in `05-differential.md`. The
easy half is Theorem 24.7 applied to a closed ball: `{x | ‖∇f x‖ ≤ b}` *is* `∂f*` of that ball.

### `Tdaf/Analysis/Convex/Optimization/Fenchel.lean`

§31: **Theorem 31.1** (both of Rockafellar's conditions), **Theorem 31.2**, and **Theorem 31.3**
with **Corollary 31.3.1**, for a general linear map `A`.

**`smul_coe_submodule` has moved out**, to `Duality/Polar.lean` beside `smul_coe_pointedCone`: it
says that a subspace is a cone in Rockafellar's sense, which is §14's business, and §12's
partial-affine formula needs it there.

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

**Theorem 31.4's attainment clauses were missing, and one of them is free.** The file had only
the duality *equation* `iInf_mem_eq_neg_iInf_mem_neg_polarCone`. Rockafellar's "under (a) the
infimum of `f*` over `K*` is attained" is `IsExactSum.exact_le` read at the origin: exactness
supplies a splitting `0 = y₁ + y₂` with `f* y₁ + (δ(·|K))* y₂ ≤ (f + δ(·|K))* 0`, the second
conjugate is `δ(· | K°)` by Theorem 14.1, so `y₂ ∈ K°`, `y₁ = -y₂ ∈ K*`, and
`(f + δ(·|K))* 0` *is* the dual infimum (`conj_add_indicatorFn_zero_eq_iInf_mem_neg_polarCone`,
which is Theorem 27.1(a) composed with the duality equation). No separation argument at all. The
degenerate branch `y₂ ∉ K°` forces the dual infimum to be `⊤`, which the origin attains.

Attainment of the *primal* infimum — Rockafellar's condition (b) — is that statement applied with
`B.flip`, `f*` and `K*`, closed by `K** = K` (`neg_polarCone_neg_polarCone`, added to
`Duality/Polar.lean`) and by Fenchel–Moreau. `biconj B f = f` is taken as a hypothesis rather than
derived, so the statement needs no compatibility assumption on the `F` side; only the bipolar makes
`exists_mem_eq_iInf_of_isExactSum_conj` layer C rather than layer A.

`iInf_mem_eq_iInf_add_indicatorFn` was `private`; Corollary 31.4.3 needs it, so it is now public.
It is a **relocation candidate** — it says nothing about pairings and belongs with `indicatorFn`.

**Not done**: Cor 31.4.1, Thm 31.4 for the non-negative orthant of a coordinate space, which
belongs to the surface layer.

### `Tdaf/Analysis/Convex/Optimization/ConeDuality.lean`

§31's **Corollary 31.4.3**: for `h` convex, finite everywhere and co-finite and `K` a nonempty
convex cone,

```lean
theorem iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z : E) (z' : F) :
    (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = ((B z z' : ℝ) : EReal)
```

with `exists_iInf_mem_eq_of_cofinite` / `exists_iInf_mem_neg_polarCone_eq_of_cofinite` for
attainment and `exists_iInf_mem_eq_coe_of_cofinite` /
`exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite` for finiteness.

**The whole proof is Theorem 12.3 then Theorem 31.4.** `f = h (z + ·) - ⟨·, z*⟩` has `dom f = E`
because `h` is finite and `dom f* = F` because `h` is co-finite (Corollary 13.3.1), so Corollary
10.1.1 makes both `f` and `f*` continuous and `IsExactSum.of_continuousAt` discharges *both* of
Rockafellar's conditions. The constant `⟨z, z*⟩` is the `α*` of Theorem 12.3.

**A separate module, not an addition to `Fenchel.lean`.** The corollary needs `Continuity.lean`
(Theorem 10.1) and `Duality/Continuity.lean` (`IsExactSum.of_continuousAt`), neither of which
`Fenchel.lean` imports; putting it there would drag layer-D dependencies into a file whose §31
content is layer A and layer C. The general attainment lemmas *did* go into `Fenchel.lean`, because
they need nothing new.

**Closedness of `K` is used only for the primal attainment**, through the bipolar. Rockafellar
states `K` closed for the whole corollary; the identity, the finiteness of both infima and the dual
attainment hold for any nonempty convex cone.

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

**`w` is `fun z => ((B z z / 2 : ℝ) : EReal)`, and `B` is explicit in `quadFn B`.** The file was
originally written on `innerₗ E` and generalized to an arbitrary `IsInnerPairing B` for §37's sake;
`quadFn_innerL` recovers `½‖z‖²`. Most of the elementary lemmas need only `[AddCommGroup E]
[Module ℝ E]`, so they carry `omit [IsInnerPairing B] in` — and the `omit` line must come *before*
the doc-comment, not between it and the `theorem`.

**Both self-conjugacy proofs are `le_antisymm` with a `linarith`/`nlinarith` defect.** For
`conj_quadFn` the defect is `½ B (x - y) (x - y)`; for `conj_quadFn_sub` it is
`½ B ((x - z) - y) ((x - z) - y)`. Feed `self_pairing_sub` and `self_pairing_nonneg` of the right
vector; and note that `B (z - x) (z - x) = B (x - z) (x - z)` has to be supplied explicitly
(`self_pairing_sub_rev`), since `linarith` will not find it.

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

**`CompleteSpace E` is not a hypothesis; `IsCompatiblePairing B` is.** Completeness was there only
to give Riesz representation for `proper_conj`, and `IsCompatiblePairing` *is* Riesz representation
stated as a hypothesis. Making it explicit removed `CompleteSpace` from every statement in the file
and is what lets the theorem run on `U × X`.

**Not done here**: only the gradient formulas `x = ∇(f* □ w) z` and `x* = ∇(f □ w) z`, which are in
`Optimization/MoreauGradient.lean` (and which needed Theorem 25.1's converse, not Theorem 26.3).
The existence and uniqueness of the splitting `z = x + x*`, `prox`, Cor 31.5.1 and Cor 31.5.2 are
in `Optimization/Prox.lean`; existence is Theorem 27.2, so that file is finite-dimensional and this
one is not.

### `Tdaf/Analysis/Convex/Optimization/Prox.lean`

§31's Theorem 31.5, attainment and uniqueness, and **Corollaries 31.5.1 and 31.5.2**. Over a
**finite-dimensional** real normed space paired with itself by an `IsContinuousInnerPairing`,
because attainment is Theorem 27.2.

```lean
noncomputable def moreauObj (B) (f : E → EReal) (z : E) : E → EReal  -- `x ↦ f x + w (z - x)`
noncomputable def prox (B) (f : E → EReal) (z : E) : E               -- Rockafellar's `prox (z | f)`
theorem subgradient_quadFn_sub …                        -- `∂(w (z - ·)) x = {x - z}`
theorem recessionFn_quadFn_sub …                        -- `(w (z - ·))0⁺ y = ⊤` for `y ≠ 0`
theorem argmin_moreauObj_nonempty …                     -- Thm 31.5, attainment
theorem mem_argmin_moreauObj_iff …                      -- Thm 31.5, minimiser ⟺ `z - x ∈ ∂f x`
theorem eq_of_sub_mem_subgradient …                     -- Thm 31.5, uniqueness
theorem prox_add_prox_conj …                            -- Thm 31.5, `z = prox(z|f) + prox(z|f*)`
theorem pairingNorm_prox_sub_le …                       -- `prox` is nonexpansive for `‖·‖_B`
theorem continuous_prox …                               -- … hence continuous in the ambient norm
theorem lipschitzWith_prox …                            -- at `innerₗ E` the constant is `1`
noncomputable def subgradientRelHomeomorph …            -- Cor 31.5.1
theorem isMaximalMonotoneRel_subgradientRel …           -- Cor 31.5.2
```

**Attainment is Theorem 9.3 plus one line, not a growth estimate.** `recessionFn_add` splits the
recession function of `f + w (z - ·)`, and `(w (z - ·))0⁺ y = ⊤` for `y ≠ 0` falls out of testing the
recession inequality `q (x + a • y) ≤ q x + a ν` at the *single* point `x = z`, where `q z = 0`: it
reads `½ a² |y|² ≤ a ν`, false for large `a`. Since `f0⁺` never takes `-∞` (`recessionFn_ne_bot`),
the sum is `⊤` off the origin, `recessionConeFn = {0}`, and Theorem 27.2 fires. No affine minorant
and no level-set boundedness are needed.

**Uniqueness and nonexpansiveness are the same two lines.** Both are the monotonicity inequality of
Theorem 24.8 (`isMonotoneRel_subgradientRel`) at the two pairs `(xᵢ, zᵢ - xᵢ)`: with `z₁ = z₂` it
gives `B (x₁ - x₂) (x₁ - x₂) ≤ 0`, and in general `B (x₁ - x₂) (x₁ - x₂) ≤ B (x₁ - x₂) (z₁ - z₂)`,
after which Cauchy–Schwarz for `B` (`pairing_le_pairingNorm_mul`) finishes. Rockafellar's strict
convexity of `w` is never used, and neither is Theorem 26.3.

**The ambient norm appears exactly once.** `pairingNorm_prox_sub_le` is nonexpansiveness in the
norm `B` induces, and that is the statement the proof produces. `continuous_prox` converts it with
the equivalence constants of `exists_pairingNorm_le_and_le_pairingNorm`, so the Lipschitz constant
in the ambient norm is `C / c`, not `1`; only for `innerₗ E`, where the two norms agree, is it `1`
(`lipschitzWith_prox`).

**Corollary 31.5.1 needs no closedness of the graph.** Theorem 24.4 is not imported: the inverse
`z ↦ (prox f z, z - prox f z)` is continuous because `prox` is nonexpansive, and that is the whole
analytic content. The `Homeomorph` is built directly on `↑(subgradientRel (innerₗ E) f)`.

**`prox` is `Classical.epsilon`, not `dite`.** The `if h : s.Nonempty then h.choose else 0` idiom
needs `dif_pos` to unfold, and `dif_pos` is deprecated in this Mathlib (→ `dite_eq_left`), which
fails a zero-warning build. `Classical.epsilon (· ∈ argmin (moreauObj f z))` unfolds through
`Classical.epsilon_spec` with no rewriting at all.

**Relocation candidates.** `isExactSum_quadFn_sub` duplicates the `have hex` inside `moreau_add`
and belongs in `Optimization/Moreau.lean`, with `moreau_add` rewritten to use it;
`closedProperConvexFn_conj` belongs in `Duality/Conjugate.lean` beside `closedFn_conj` — the
`IsContinuousPairing B.flip` bookkeeping that blocked it is now settled by
`isContinuousPairing_flip_of_isContinuousInnerPairing`.

### `Tdaf/Analysis/Convex/Optimization/Minimum.lean`

§27: **Theorems 27.1(a), 27.1(b), 27.2 with Corollaries 27.2.1–27.2.2, Theorem 27.3 in full — the
general case, the polyhedral refinement, and Corollaries 27.3.1, 27.3.2 and 27.3.3 — and
Theorem 27.4**.

**Theorem 27.3's polyhedral refinement does not need Helly.** Rockafellar derives it from
Theorem 21.5 applied to `C` together with the level sets `lev_α h`; the proof here projects `E`
along `constancySubmodule h` (`exists_linearProj`), which leaves `h` unchanged — it is constant
along the fibres — and collapses `0⁺h ∩ 0⁺(A '' C)` to `{0}`. Polyhedrality of `C` enters exactly
once, through `Polyhedral.recessionCone_image`. The same projection, run along
`constancySubmodule h ⊓ linealitySubmodule C`, strengthens the *general* case from
`0⁺h ∩ 0⁺C = {0}` to Rockafellar's constancy/linearity hypothesis
(`exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace`); there the image of `C` is
literally `C ∩ N` and no polyhedrality is used. **Corollary 27.3.1** is
`exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn`: hypothesis
`recessionConeFn h ⊆ linealitySpaceFn h` — every direction of recession is one in which `h` is
*affine* — plus a real lower bound on `C`. A common direction of recession `y` of `h` and `C` then
satisfies `h (x + a • y) = h x + a ν` with `ν = (h0⁺) y ≤ 0` (Theorem 8.8) along a half-line that
stays in `C`, so the lower bound forces `ν = 0` and `y ∈ constancySpace h` (Corollary 8.6.1); the
polyhedral refinement applies verbatim. That slope step is
`mem_constancySpace_of_mem_linealitySpaceFn`, layer A, in `Recession/Function.lean`. The lower
bound is essential — `h(x₁, x₂) = x₁` is affine in every direction and has infimum `-∞` over
`C = {x | x₂ = 0}` — and the degenerate case `C ∩ dom h = ∅` is dispatched separately, so only
`C.Nonempty` is asked for.

**Relocation candidates.** `eq_of_sub_mem_constancySpace` and `exists_linearProj` are general facts
about `constancySpace` and about subspaces; they belong in `Recession/Function.lean` and in a linear
algebra file respectively, and are here only to avoid rebuilding the whole project from
`Recession/Function.lean`. Both are also *mis-layered*: they sit inside a
`[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` section with only
`omit [FiniteDimensional ℝ E]`, although neither proof uses a norm — `exists_linearProj` is pure
linear algebra over `Module ℝ E`. Cf. D9.

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

**Thm 27.1 (d), (g) and (h) are done too**, in `section ConjugateAtZero`.

```lean
theorem zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero …
theorem argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj …    -- Thm 27.1(d)
theorem conj_flip_conj_add_coe …                    -- (f* + α)* = f** - α
theorem supportFn_setOf_le …                        -- Thm 27.1(g), first sentence
theorem supportFn_argmin …                          -- Thm 27.1(g), second sentence
theorem epsSubgradient_conj_zero …                  -- lev_α f = ∂_ε f*(0)
theorem iInf_supportFn_setOf_le …                   -- Thm 27.1(h)
```

**Theorem 27.1(d) does not need Corollary 13.3.4**, contrary to the book's proof. Corollary 14.2.2
already says every level set is bounded exactly when the origin is interior to `dom f*`, and
Theorem 27.2 turns "no direction of recession" into existence of a minimiser; the two directions
then close through Theorem 8.7.

**Theorem 27.1(g)'s first sentence does not need a shifted-function API either.** It is Theorem
13.5 for `f - α`, but `clFn_posHomGen` (Corollary 13.2.1) computes the closure of a generated
function as a support function with *no* hypotheses, so all that is needed is
`conj_flip_conj_add_coe`, which says the level set it produces is `{x | f**(x) - α ≤ 0}`. That
avoids proving `ConvexFn`/`ClosedFn`/`Proper` stability under adding a real constant — an API the
project still does not have.

**`supportFn_setOf_le` is a §13 statement living in §27.** Its natural home is beside
`supportFn_setOf_le_zero` in `Duality/Level.lean`; it is here because that module sits *below*
`Optimization/Minimum.lean` in the import graph.

**Theorem 27.1(h) cost one import and one duplicate.** `Subgradient/Approx.lean` had to be imported
for Theorem 23.6, and that made gotcha LIB1's triple `add_coe_le_coe_iff` an actual build error —
see `Tdaf/Order/EReal.lean`.

**Thm 27.1(c) is `iInf_ne_bot_and_argmin_eq_empty_iff`**, and it is (a) and (b) composed with
Theorem 23.3's second half in its `subgradient_eq_empty_iff_exists_dirDeriv_eq_bot` packaging —
a second import, of `Subgradient/Existence.lean`. Only *one* of the book's two finiteness bounds
appears on each side of the equivalence: `f*(0) ≠ ⊥` holds for every proper `f` (`conj_ne_bot`) and
symmetrically `⨅ f ≠ ⊤` does too (`iInf_ne_top`, recorded here for exactly that reason). Stating
"finite" in full would put two redundant conjuncts into an `↔`.

**Cor 27.3.2 is done, and it does not need Helly.** `argmin_nonempty_of_polyhedralFn` runs the
finitely generated description of the epigraph (Theorem 19.1): a lower bound forces every
generating *direction* upward, so the vertical coordinate is minimised over `epi f` at one of the
finitely many generating *points*. No closedness, no properness.
`exists_forall_le_of_polyhedralFn_of_polyhedral` then restricts `f` to `C` by Rockafellar's own
vertical prism. The book derives 27.3.2 from 27.3.1 and hence from Theorem 21.5; that detour is
avoidable.

**Thm 27.1(d) is stated twice, and the level-set form is the one §30 wants.**
`argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj` is the book's sentence about
`argmin f`; `exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj` says the same
of *some* sublevel set `{x | f x ≤ α}`, and `argmin_nonempty_and_isBounded_iff_exists_setOf_le`
composes the two. The book states only the second reading, in Theorem 30.4(g); both run on
`recessionConeFn f = 0`, and the bridge in the sublevel direction is `recessionCone_setOf_le`
(Thm 8.7) rather than `recessionCone_argmin`.

**Not done**: Thm 27.1(e), which needs a reflexive pairing (`∂f*(0)` lives in `E**`), and the
polyhedral refinement of Thm 27.3, Cor 27.3.1 and the polyhedral half of Cor 27.3.3, which
genuinely do need Helly in the form of Thm 21.5.

**`argmax` sits beside `argmin` and is `argmin` at the negation.** `argmax g = {x | ∀ z, g z ≤ g x}`
with `argmax_eq_argmin_neg`; it is what "optimal solution" means for a *concave* program, and
Theorem 30.4(j) is the first consumer. The two lemmas are three lines together and buy the book's
own wording for every dual-side statement.

### `Tdaf/Analysis/Convex/Optimization/Maximum.lean`

§32 in full: **Theorems 32.1, 32.2, 32.3 and 32.4** with Corollaries 32.1.1, 32.2.1, 32.3.1,
32.3.2 (both clauses), 32.3.3, 32.3.4 and 32.4.1.

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

**Theorem 32.3 is `convexHullPD_extremePoints_extremeDirections` plus one inequality.** Split
`x ∈ C` as `u + v` with `u ∈ conv (ext C)` and `v` in the cone of the extreme directions; the
half-line `u + t • v`, `t ≥ 0`, then lies in `C`, and `ConvexFn.add_le_of_forall_add_smul_le` — a
convex function bounded above on a half-line is non-increasing along it — gives `f x ≤ f u`.
Theorem 32.2 removes the hull. The `EReal` bookkeeping is two applications of
`EReal.lt_iff_exists_real_btwn` (one to get a bound `ξ` above `f u`, a second to get a value `η`
strictly between `ξ` and `f (u + v)` to contradict) and then `t := max 1 (1 + (β - ξ) / (η - ξ))`;
`linarith` closes it once `t⁻¹ * (β - ξ) < η - ξ` is available. Boundedness above cannot be dropped
(`f x = x` on `[0, ∞)`), but `ConvexFn.iSup_extremePoints_add_coneHull`, which keeps the directions
in the index set, is unconditional.

**Corollary 32.2.1 wants `¬ IsAffineHalf C`, not `ContainsNoLine C`.** `convexHull_sdiff_relint`
is Theorem 18.4 in hull form (`convexHull ℝ (C \ ri C) = C`, three lines from
`exists_notMem_relint_mem_segment_of_not_isAffineHalf`), and the half-line shows the "no lines"
reading is false. `ConvexFn.iSup_sdiff_relint_of_containsNoLine` adds `2 ≤ dim C` and goes through
`not_containsNoLine_of_isAffineHalf`.

**The attainment clause of Cor 32.3.2 needed a hypothesis, not just Thm 10.1.** For a merely
compact convex `C ⊆ dom f` it is false: on the closed unit disc, `f = 0` on the open disc and
`f (cos θ, sin θ) = 1 - θ` for `θ ∈ (0, 2π]` is convex with unattained supremum `1`.
`exists_mem_extremePoints_isMaxOn_of_isCompact` asks for `C ⊆ ri (dom f)`, where
`ConvexFn.continuousOn_relint_dom` applies; `IsCompact.exists_isMaxOn` then works directly on the
`EReal`-valued `f`, with no `toReal` detour.

**Cors 32.3.1 and 32.3.4 were proved here before they were labelled.** The session that wrote the
file had no copy of the book and would not attach a number to a guessed statement; checked against
the text afterwards, Cor 32.3.1 is Thm 32.3's attainment clause
(`exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine`) and Cor 32.3.4 is
`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated`, "polyhedral" read through Thm 19.1.
`ConvexFn.eq_of_forall_le` (bounded above on the whole space ⇒ constant) is *not* one of them and
stays unnumbered.

```lean
def BddAboveOnRays (f : E → EReal) (C : Set E) : Prop :=
  ∀ u v : E, (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)
```

**`BddAboveOnRays` is Thm 32.3's hypothesis, and it carries `C ⊆ dom f` with it.** The degenerate
ray `v = 0` says every point of `C` is below some real, i.e. `C ⊆ dom f`
(`BddAboveOnRays.subset_dom`), which is Rockafellar's other standing hypothesis in §32; so one
predicate covers both. A uniform bound is `bddAboveOnRays_of_forall_le`.
`ConvexFn.exists_mem_convexHull_extremePoints_le` was *generalised* to it rather than duplicated:
its proof only ever used the bound on the single half-line `u + t • v` it constructs, so the proof
did not change, and Cor 32.3.4 (`exists_mem_extremePoints_isMaxOn_of_finitelyGenerated`) is now one
line off the generalised finitely-generated statement.

**Cor 32.3.3 quotients out the lineality space by intersecting, not by projecting.** Rockafellar
takes `D = C ∩ L^⊥`; `eq_add_inter_of_isCompl` (`Recession/Cone.lean`) gives `C = L + (C ∩ N)` for
*any* complement `N` of `L`, which is all the argument needs and keeps the statement free of an
inner product. `f` is constant along `L` (`ConvexFn.add_eq_of_mem_linealitySpace`: `y` and `−y` are
both in `0⁺C`, so the two applications of `ConvexFn.add_le_of_bddAboveOnRays` close on each other);
`C ∩ N` is polyhedral by `Polyhedral.inter` and `polyhedral_coe_submodule`, nonempty by the
decomposition, and contains no lines because a line direction of it lies in `L ⊓ N = ⊥`. The
maximiser is an extreme point of `C ∩ N`, not of `C`, and depends on `N` — hence the conclusion is
bare attainment, `∃ z ∈ C, ∀ w ∈ C, f w ≤ f z`. `Maximum.lean` therefore does **not** depend on
`Minimum.lean`'s `exists_linearProj`; it only gained an import of `Polyhedral/Ops.lean`.

### `Tdaf/Analysis/Convex/Face.lean`

§18's facial structure: **Theorems 18.1 and 18.2** in full, and **Theorems 18.4 and 18.5** for
compact sets.

```lean
structure IsFace (C C' : Set E) : Prop extends IsExtreme ℝ C C' where
  convex : Convex ℝ C'
```

**Rockafellar's face is not Mathlib's `IsExtreme`, even for convex `C`.** `{0, 1}` is an extreme
subset of `[0, 1]` and is not convex, so it is not a face. The convexity field is therefore real,
and everything else is inherited: `IsFace.trans`, `.inter`, `.inter_convex`, `.mono`,
`isFace_sInter`, `isFace_singleton : IsFace C {x} ↔ x ∈ C.extremePoints ℝ`, `IsExposed.isFace`.
`.inter_convex` cuts *both* the set and its face with the same convex set, which is the forward
map of the p. 166 face correspondence in `Representation.lean`.

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

§21: **Theorems 21.1, 21.2, 21.3, 21.6 and Corollaries 21.3.1, 21.3.2, 21.6.1, 21.6.2**. Theorems
21.4 and 21.5 are in `HellyRefined.lean`, which imports this file.

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
monoid, so `Finset.sum_lt_sum` is unavailable there (gotcha ER1). Tolerance `ε/(2λ)` keeps every
step non-strict and the proof goes through unchanged.

**Theorem 21.3 is split so that Theorem 21.4 can share it.**
`exists_multipliers_of_posHomGen_convFn_conj_eq_bot` takes `k(0) = -∞` as a hypothesis and runs
Corollary 17.1.3; `alternative_infinite_system_univ` supplies `k(0) = -∞` from the recession
hypothesis through Theorems 13.5 and 7.4, and `HellyRefined.lean` supplies it from a polyhedral
half-family. That is the *entire* difference between Theorems 21.3 and 21.4.
`not_forall_le_weighted_of_forall_subsystem` is likewise the contradiction step of Corollary 21.3.1,
extracted so that both versions of that corollary use it.

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

**§21 is complete.** Theorem 21.3 goes through the positively homogeneous function generated by
`conv {fᵢ* | i ∈ I}`, whose conjugate is **Theorem 13.5**, and extracts the multipliers by
**Corollary 17.1.3**, the directions half of Carathéodory; both arrived, and 21.4/21.5 followed in
`HellyRefined.lean`. What §21 still does not have is the mixed *strict/weak* infinite alternative
that §28's `ineqBifun` wants.

### `Tdaf/Analysis/Convex/HellyRefined.lean`

§21: **Theorems 21.4 and 21.5**, and Corollary 21.3.1 under Theorem 21.4's hypothesis.

```lean
theorem conj_affineFn (hB : B.SeparatingRight) (a : F) (c : ℝ) :
    conj B (affineFn B a c) = indicatorFn ({a} : Set F) + fun _ => ((c : ℝ) : EReal)
theorem epi_conj_affineFn … : epi (conj B (affineFn B a c)) = {(a, c)} + ↑(verticalRay F)
theorem conj_posHomGen_convFn_conj (hg : ∀ i, ClosedProperConvexFn (g i)) :
    conj B.flip (posHomGen (convFn fun i => conj B (g i))) = indicatorFn {x | ∀ i, g i x ≤ 0}
theorem nonempty_neg_dom_inter_relint_dom … :
    ((-dom (posHomGen (convFn fun i => conj B (g₀ i)))) ∩
      ri (dom (posHomGen (convFn fun i => conj B (g₁ i))))).Nonempty
theorem apply_zero_eq_bot_of_le_of_le … (hk : PosHomogeneous k) (hkc : ConvexFn k)
    (hle₀ : k ≤ posHomGen (convFn fun i => conj B (g₀ i)))
    (hle₁ : k ≤ posHomGen (convFn fun i => conj B (g₁ i))) : k 0 = ⊥
theorem alternative_infinite_system_univ_of_affine_tail … (I₀ : Finset ι)   -- Thm 21.4
    (haff : ∀ i ∈ I₀, ∃ (a : F) (c : ℝ), f i = affineFn B a c)
    (hrec : ∀ y : E, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i)) : …
theorem helly_of_polyhedral_tail … (I₀ : Finset ι)                          -- Thm 21.5
    (hpoly : ∀ i ∈ I₀, Polyhedral (K i))
    (hrec : ∀ y : E, (∀ i, y ∈ recessionCone (K i)) → ∀ i ∉ I₀, y ∈ linealitySpace (K i))
    (hinter : …) : (⋂ i, K i).Nonempty
```

**Theorem 21.4 changes exactly one step of Theorem 21.3.** Both run on `k = posHomGen (conv {fᵢ*})`
and both finish through `exists_multipliers_of_posHomGen_convFn_conj_eq_bot` (`Helly.lean`) once
`k(0) = -∞` is known. Theorem 21.3 gets `k(0) = -∞` from `0 ∈ ri (dom k)`; Theorem 21.4 gets it
from `apply_zero_eq_bot_of_le_of_le`, which is the book's `k₀`/`k₁` argument.

**`conv {k₀, k₁}` is never formed.** Rockafellar identifies `epi k` with `epi k₀ + epi k₁` (Thm 3.8)
and reads `k(0)` as an infimal convolution; only `k(0) ≤ k₀(-z) + k₁(z)` is used, so
`apply_zero_eq_bot_of_le_of_le` takes an *arbitrary* positively homogeneous convex `k` below both,
and `k ≤ kⱼ` is `posHomGen_mono` on the subfamily inclusion.

**Subadditivity is paid for by `≠ +∞`, not by `≠ -∞`.**
`PosHomogeneous.convexFn_iff_subadditive` (Thm 4.7) needs `∀ x, f x ≠ ⊥`, which an improper `k₁`
violates. `PosHomogeneous.add_le_add_of_ne_top` needs `f x ≠ ⊤` and `f y ≠ ⊤` instead and reads the
inequality off the epigraph cone. **Neither hypothesis is removable**: on `ℝ²` the function with
epigraph `{(s,t,μ) ∣ s > 0} ∪ {(0,0,μ) ∣ μ ≥ 0}` is positively homogeneous, convex and `0` at the
origin, yet `g(0,0) = 0 > ⊥ = g(-1,0) + g(1,0)`.

**Rockafellar's reduction to `I₀ ≠ ∅ ≠ I₁` is unnecessary.** He adjoins identically-zero functions
to both halves. In Lean neither half has to be nonempty: `posHomGen h 0 ≤ 0` whatever `h` is, so
`0 ∈ dom kⱼ` always, and for an empty family `posHomGen (convFn g) = δ(· ∣ 0)`, polyhedral with
domain `{0}` — exactly what the separation step needs. The halves are `{i // i ∈ I₀}` and `{i // i ∉ I₀}`.

**The separating hypothesis is `B.SeparatingRight`, not `IsCompatiblePairing`.** Compatibility gives
surjectivity of `evalCLM`, i.e. that every continuous functional on `E` is `⟨·, y⟩`; what
`conj_affineFn` needs is that `∀ x, B x z = 0` forces `z = 0`. In finite dimensions
`separatingRight_flip_of_separatingDual` supplies it, but it is carried explicitly, as
`Saddle/Conjugate.lean` and `LinearInequalities.lean` already do.

**Theorem 21.5 is re-indexing.** Each polyhedral `Cᵢ`, `i ∈ I₀`, is cut out by finitely many
inequalities of the pairing (`Polyhedral.exists_finset_pairing`), the family is re-indexed by
`{i ∉ I₀} ⊕ Σ (i ∈ I₀), (constraints of Cᵢ)`, and `Finset.image Sum.inr Finset.univ` is
Rockafellar's "put all these half-spaces together into one collection". The `(n+1)`-intersection
property survives because several constraints of the same `Cᵢ` project to one index of the original
family, so `Finset.card_image_le` is all the counting there is. "Linear in a direction" becomes
"constant in a direction" through `constancySpace_indicatorFn`.

**Relocation candidates.** Several declarations are general and only live here because moving them
would rebuild half the tree: `dom_convFn` → `Operations/Hull.lean`; `posHomGen_mono` and
`PosHomogeneous.add_le_add_of_ne_top` → `Recession/ConeHull.lean` / `Homogeneous.lean`;
`conj_affineFn` and `dom_conj_affineFn` → `Duality/Conjugate.lean` or `Duality/Support.lean`;
`epi_comp_neg`, `dom_comp_neg`, `Proper.comp_neg`, `conj_comp_neg`, `reflectFst` →
`Operations/Basic.lean`; `constancySpace_indicatorFn` → `Recession/Function.lean`;
`Polyhedral.exists_finset_pairing` and `mem_recessionCone_of_forall_pairing_nonpos` →
`Polyhedral/Ops.lean`; `closedProperConvexFn_affineFn` → `Duality/Pairing.lean`.

### `Tdaf/Analysis/Convex/Optimization/Perturbation.lean`

§29: **Theorem 29.1** in full, **Corollaries 29.1.1–29.1.6** and **Theorem 29.2**.

```lean
theorem supportFn_kuhnTucker …    -- Cor 29.1.1: `δ*(u ∣ KT) = cl (inf F)'(0; -u)`
theorem kuhnTucker_eq_empty_iff …                                     -- Cor 29.1.2
theorem kuhnTucker_eq_singleton_of_dirDeriv_eq …                      -- Cor 29.1.3
theorem kuhnTucker_nonempty_of_stronglyConsistent … ; theorem dirDeriv_infBifun_eq …   -- Cor 29.1.4
theorem proper_infBifun_of_stronglyConsistent … ; theorem continuousOn_infBifun_interior …
theorem isBounded_kuhnTucker_of_strictlyConsistent …                  -- Cor 29.1.5
theorem isCompact_kuhnTucker_of_strictlyConsistent …                  -- Cor 29.1.5, last clause
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

**Corollary 29.1.5's compactness clause is where the pairing form of Theorem 23.4 stops being
enough.** The three properties come from three places — non-emptiness from Theorem 23.4 through
`kuhnTucker_nonempty_of_stronglyConsistent`, closedness and convexity from Corollary 29.1.1,
boundedness from Theorem 23.4's last clause — and only the last is a problem.
`bddAbove_kuhnTucker_of_strictlyConsistent` gives Corollary 13.2.2's notion of boundedness, which is
all a general dual pair supports; Rockafellar's "closed bounded" is `Bornology.IsBounded`, and the
upgrade is `isBounded_iff_forall_bddAbove` in `Duality/SupportRelint.lean`. It is what makes this
one corollary need `FiniteDimensional ℝ V` and `IsCompatiblePairing B.flip` when nothing else in
§29 does, so it lives in its own section. **Corollary 29.1.4 has no compactness clause at all** —
it is nonemptiness plus the derivative formula, and under mere *strong* consistency the
Kuhn–Tucker set need not be bounded, because Theorem 23.4 bounds `∂f x` only at *interior* points
of `dom f`. Anything asking for "non-empty closed bounded convex" is Corollary 29.1.5.

**`convex_domBifun` is `dom_infBifun` plus `ConvexFn.convex_dom`,** and it is worth having as a
name: `domBifun F` is a `Set U` defined by an existential, so nothing about it is syntactically a
`dom`, and every `ri`/`closure` argument about it starts by rewriting.

**Not here**: Theorem 29.4, which is in `Optimization/Adjoint.lean` because `clBifun` is defined there; Theorem 29.3 is in `Saddle/Minimax.lean`, with §36.

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
half of Theorem 30.5. Also **Theorem 29.4**, which lands here rather than in
`Optimization/Perturbation.lean` because `clBifun` is defined here.

```lean
theorem domBifun_eq_image_dom_graphFn (F) :
    domBifun F = LinearMap.fst ℝ U X '' dom (graphFn F)
theorem mem_relint_slice (hS : Convex ℝ S) (hux : (u, x) ∈ ri S) :
    x ∈ ri {y | (u, y) ∈ S}                                        -- **Thm 6.4** on a slice
theorem clBifun_apply_eq_clFn (hF : ConvexBifun F) (hu : u ∈ ri (domBifun F)) :
    clBifun F u = clFn (F u)                                       -- **Thm 29.4**, first
theorem infBifun_clBifun_eq …                                      -- **Thm 29.4**, second
theorem domBifun_subset_domBifun_clBifun …                         -- **Thm 29.4**, third
theorem domBifun_clBifun_subset_closure …
```

**Theorem 29.4 never needed §36 or §37.** The plan recorded it as blocked on saddle-point
existence (Theorem 37.6); it is not, and nothing in its statement mentions a saddle-function. It is
a §6/§7 statement about closures, and the proof is Rockafellar's own: `dom F` is the projection of
`dom (graph F)` (`domBifun_eq_image_dom_graphFn`), Theorem 6.6 (`Convex.relint_image`) makes `ri`
commute with that projection and so puts some `(u, x) ∈ ri (dom (graph F))` over each
`u ∈ ri (dom F)`, the prolongation criterion (Theorem 6.4) drops `x` into `ri (dom (F u))`, and
Theorem 7.5 (`ConvexFn.tendsto_clFn_along_segment_relint`) writes `(cl F) u y` and `cl (F u) y` as
the *same* limit along the segment from `x` to `y` — the segment stays in the slice because
`(1 - a) • (u, x) + a • (u, y) = (u, (1 - a) • x + a • y)`. When `graph F` is improper,
Theorem 7.2 (`ConvexFn.eq_bot_of_mem_relint_dom`) makes it `⊥` at `(u, x)`, `lscHull_le` pushes
that onto both hulls, and `clFn_of_exists_eq_bot` makes both sides the constant `⊥`. The second
assertion is then `iInf_clFn_eq_iInf`, and the third is Theorem 7.4's two domain inclusions
(`dom_subset_dom_lscHull`, `dom_lscHull_subset_closure_dom`) pushed through `fst` with
`image_closure_subset_closure_image`.

**Corollary 29.4.1 is done**, in seven clauses: `relint_domBifun_clBifun`,
`stronglyConsistent_clBifun`, `clBifun_zero_eq_clFn`, `infBifun_clBifun_zero_eq`,
`argmin_subset_argmin_clBifun`, `eventually_infBifun_clBifun_eq`, `kuhnTucker_clBifun_eq`. Three
things the book's half-page proof does not say:

* **The Kuhn–Tucker clause does not go through the perturbation functions.** Rockafellar deduces
  it from their agreement near `0`; but `adjointBifun_clBifun` already says the adjoint never sees
  the closure, so `(P)` and `(cl P)` have the *same* dual objective, and
  `mem_kuhnTucker_iff_adjointBifun_zero_eq` plus `infBifun_clBifun_eq` at `0` closes it in three
  lines. That route also drops the properness hypothesis the neighbourhood route needs.
* **"Agree on a neighbourhood of `0`" is true but is not Theorem 29.4.** Theorem 29.4 gives
  agreement on `ri (dom F)`, a *relative* neighbourhood. What upgrades it is that `ri C` is
  relatively open (`Convex.relint_relint`, so `mem_intrinsicInterior_iff` applied to `ri C` gives
  an ambient ball meeting `aff C` only inside `ri C`) together with
  `dom (cl F) ⊆ cl (dom F) ⊆ aff (dom F)`: a point of that ball is either in `ri (dom F)`, where
  Theorem 29.4 applies, or outside `aff (dom F)`, where both perturbation functions are `+∞`.
* **That clause is false without properness**, which the corollary does not assume although its
  own Theorem 29.4 assumes it for the domain inclusions. Take `F u x = -∞` for `u` on a line `L`
  through the origin and `+∞` off it: `(P)` is strongly consistent, `cl F ≡ -∞` (Rockafellar's own
  convention for improper convex functions), so `inf (cl F) ≡ -∞` while `inf F = +∞` off `L`.
  `relint_domBifun_clBifun` fails for the same `F` — `ri (dom (cl F)) = ℝᵐ` and `ri (dom F) = L`.

**Theorem 30.1 negated is what the concave clauses of Theorem 30.4 consume.**
`convexBifun_neg_adjointBifun` and `closedBifun_neg_adjointBifun` state that `-F*` is a closed
convex bifunction with *no* hypothesis on `F`, so any statement about the concave program `(P*)`
can be routed through the convex machinery at the flipped pairings. The first of the two used to
be a private-looking restatement inside `Saddle/Minimax.lean`; it is a §30 fact and now lives
here.

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
**Theorem 30.3** in full, **Theorem 30.4** in all ten clauses, and **Theorem 30.5**.
`ConcaveKuhnTucker` and `ConcavePolyhedralBifun` are the two definitions clauses (d)–(f) need;
`forall_conj_eq_top_iff` is the single lemma both halves of Corollary 30.2.1 run on. Corollary
30.5.1 is in `Saddle/Minimax.lean`, with §36.

**Theorem 30.4(g) and (i) are here**, in `section Thm304Main`, and getting them cost a new
prerequisite.

```lean
noncomputable def shiftBifun (Bx) (F : Bifun U X) (y : Y) : Bifun U X
theorem infBifun_shiftBifun …            -- `inf (F - ⟨·, y⟩) u = -(Fu)*(y)`
theorem convexBifun_shiftBifun … ; theorem adjointBifun_shiftBifun_zero …
theorem supBifun_adjointBifun …          -- **Cor 30.2.2** at an arbitrary `y`
theorem mem_domConcaveBifun_adjointBifun …                     -- the book's "i.e."
theorem normal_of_exists_setOf_le …                            -- **Thm 30.4(g)**
theorem normal_of_argmin_nonempty_and_isBounded …              -- **Thm 30.4(i)**
```

**Rockafellar's proof of Theorem 30.4(g) hides a real argument in one "i.e.".** The proof reads:
"Condition (g) is equivalent by Theorem 27.1(d) to having `0 ∈ int (dom (F0)*)`, i.e. `(P*)`
strictly consistent." Writing `Fᵧ u x := F u x - ⟨x, y⟩`, the two sides are

```
dom ((F 0)*)         = {y | (inf Fᵧ) 0 > -∞}
domConcaveBifun F*   = {y | cl (inf Fᵧ) 0 > -∞}
```

because `adjointBifun Bu Bx F y v = adjointBifun Bu Bx Fᵧ 0 v`, so Corollary 30.2.2 applied to `Fᵧ`
gives `supBifun F* y = cl (inf Fᵧ) 0`, while `(F 0)* y = -(inf Fᵧ) 0` by definition. So the
inclusion `⊆` is free and the *reverse* one carries the content. When `(P)` is consistent — which
(g) forces — improperness of a convex function on `ri (dom)` (Theorem 7.2) turns the second set into
`{y | ∀ u, (F u)* y ≠ ⊤}`, an intersection over *all* `u` whose `u = 0` member is the first set.
Interiors of such an intersection are not automatic.

**What closes it is that all the slices have the same recession function.** For closed convex `F`
and any `u` with `F u ≢ ⊤`, `epi (F u)` is a slice of `epi F`, and the recession cone of a
non-empty slice of a closed convex set is the corresponding slice of its recession cone — the
non-obvious half being that a single ray suffices, which is `mem_recessionCone_of_exists_ray`
(Theorem 8.3). Hence `(F u)0⁺ = (F 0)0⁺` for every `u ∈ dom F`, and:

* by Theorem 27.1(d), (g) says `recessionConeFn (F 0) = 0`, i.e. `(F 0)0⁺ y > 0` for `y ≠ 0`;
* `(F 0)0⁺` is positively homogeneous and lower semicontinuous, so on the unit sphere — compact, in
  finite dimensions — it has a positive lower bound `c`;
* for `‖y*‖ < c` and every `u`, `(F u)0⁺ - ⟨·, y*⟩ = (F 0)0⁺ - ⟨·, y*⟩` is still positive off the
  origin, so `F u - ⟨·, y*⟩` has a bounded non-empty sublevel set and hence is bounded below;
* so the ball of radius `c` lies in every `dom ((F u)*)`, and `0 ∈ int (domConcaveBifun F*)`.

That is what `normal_of_exists_setOf_le` does, with `recessionFn_slice_eq` supplying the first
step. Three details the sketch hides:

* **`shiftBifun` is needed because Corollary 30.2.2 is stated at the origin only.**
  `adjointBifun Bu Bx (shiftBifun Bx F y) 0 v = adjointBifun Bu Bx F y v`, so applying the
  origin-only formula to the shifted bifunction computes the whole `y`-slice of the adjoint. The
  identity is EReal bookkeeping — `(z - c) + b = z + (b - c)` for real `b`, `c` — and the convexity
  of the shift is `convexFn_add_coe`, newly public in `Epigraph.lean`, promoted from the `private`
  copy `Saddle/Defs.lean` had carried since §33. That dedup was **forced, not optional**: gotcha LIB1
  again, `a non-private declaration … has already been declared`, reported at the private copy in a
  file nobody had touched.
* **No properness is assumed.** An improper closed convex bifunction has `inf F 0 = -∞` — by
  `ConvexFn.eq_bot_or_eq_top`, Corollary 7.2.1 — and normality then holds because `cl` cannot go
  below `-∞`. The proof case-splits on `∃ p, graphFn F p = ⊥` and disposes of that branch in four
  lines.
* **Theorem 30.4(g) is the one §30 statement that needs `FiniteDimensional ℝ U`.** It enters
  through `ConvexFn.proper_clFn`, Theorem 7.4, applied to `u ↦ -(Fu)*(y)` — not through anything
  about the perturbation space as such. `X` and `Y` are finite-dimensional already, for Theorem
  27.1(d) and Corollary 13.3.4(c).

**(i) needs properness where (g) does not.** `argmin (F0)` is a level set of `F0` at its own
minimum value, which is `argmin_nonempty_and_isBounded_iff_exists_setOf_le` — but only for proper
`F0`. Without properness "optimal solution" and "optimal value" come apart: for `F0 ≡ ⊤` over a
zero-dimensional `X` the set of optimal solutions is non-empty and bounded while no level set is,
so (i) is *not* literally contained in (g) as the book says.

**Theorem 30.4 (h) and (j) are two lines each, and the "structural obstruction" recorded here
before was not one.** The key is `concaveNormal_iff_normal_neg`: `ConcaveNormal G` is literally
`Normal (fun y v => -(G y v))`, because `clConcave` is `-(clFn (-·))` and `sup G = -(inf (-G))`, so
the two sides differ by `neg_inj`. Hence (h) is `normal_of_exists_setOf_le` and (j) is
`normal_of_argmin_nonempty_and_isBounded`, both applied to `-F*` — a bifunction from `Y` to `V`,
with `Bu := Bx.flip` and `Bx := Bu.flip` — followed by Theorem 30.3. The two hypotheses come free
from Theorem 30.1 (`convexBifun_neg_adjointBifun`, `closedBifun_neg_adjointBifun`,
`Optimization/Adjoint.lean`), and the superlevel set `{v | α ≤ (F* 0) v}` *is* the sublevel set
`{v | -(F* 0) v ≤ -α}`. No concave mirror of Theorem 27.1(d) or of Corollary 13.3.4(c) is needed;
the only price is `[FiniteDimensional ℝ V]`, which is what running the convex machinery on `V`
costs. `[FiniteDimensional ℝ X]` is *not* needed — `X` plays the role of the dual space there.

**The one new definition is `argmax`** (`Optimization/Minimum.lean`), so that (j) can say "the
optimal solutions to `(P*)`" rather than "the minimisers of `-(F* 0)`".

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
that takes the linear functional and its defining equation as arguments — gotcha LINT9),
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
what its proofs use, is the fix (cf. [`gotchas.md`](gotchas.md) LINT3).

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

### `Tdaf/Analysis/Convex/Duality/SupportRelint.lean`

**Theorem 13.1's `ri`, `int` and `aff` clauses**, and **Corollary 1.4.1** in the pointwise form the
last of them is.

```lean
theorem neg_supportFn_neg_eq_iff …            -- the "reversible direction" predicate
theorem exists_forall_eq_of_notMem_affineSpan …                       -- Cor 1.4.1
theorem mem_relint_iff_lt_supportFn …                                 -- Thm 13.1, ri
theorem mem_interior_iff_lt_supportFn …                               -- Thm 13.1, int
theorem mem_affineSpan_iff_eq_supportFn …                             -- Thm 13.1, aff
theorem isBounded_iff_forall_bddAbove …                               -- Cor 13.2.2, metric form
```

**A thin module between `Duality/Support.lean` and `Duality/Level.lean`, and it has to be.** The
closure clause of Theorem 13.1 is layer C and lives with the rest of the support-function API; these
three are layer D *and* need `intrinsicInterior`, i.e. `RelativeInterior.lean`, which is not below
`Support.lean`. Importing it there would put `Barrier`, `Gauge`, `Ops`, `Polar`,
`Polyhedral/Separation`, `Recession/Conjugate` and `Subgradient/Defs` downstream of it.
`supportFn_neg_eq_neg_iff` moved here from `Level.lean`, which only held it because Theorem 13.4
happened to be its first consumer.

**All three clauses are genuinely finite-dimensional**, and one counterexample kills all three at
once: `C = ker φ` for a discontinuous functional `φ`. Then `ri C = aff C = C`, `int C = ∅`, the
reversible directions are exactly the `y` with `⟨·, y⟩ = 0`, and `δ*(y | C) = +∞` elsewhere — so all
three stated conditions hold at *every* point of the space.

**Two corrections to the book's Theorem 13.1.** The `int` clause is false for `C = ∅` over the zero
space (the condition is vacuous while `int ∅ = ∅`), so `C.Nonempty` is assumed; and over a pairing it
needs `B.SeparatingRight`, because `y ≠ 0` and `⟨·, y⟩ ≠ 0` are different conditions once
`Rⁿ = (Rⁿ)*` is given up. The `aff` clause, on the other hand, needs **no convexity** — Corollary
1.4.1 is about arbitrary sets, and the proof separates a point from the affine subspace `aff C`.

**Corollary 13.2.2's metric form is here too**, and three later statements needed it.
`isSupportFn_bounded_iff_finite` in `Duality/Support.lean` reads "bounded" in the *pairing* sense —
every `⟨·, y⟩` is bounded above on `C` — which is all a general dual pair supports.
`isBounded_iff_forall_bddAbove` upgrades that to `Bornology.IsBounded`, and the upgrade is a
coordinate estimate against `Module.finBasis`: each `b.coord i` is continuous, hence `⟨·, yᵢ⟩` for
some `yᵢ` by `exists_pairing_eq`, and bounding those coordinates in both directions bounds `‖x‖`.
The converse direction needs no compatibility at all. Its consumers are Corollary 23.7.1 under the
book's own hypothesis, the last clause of Theorem 23.4 in the norm, and Corollary 29.1.5's
compactness clause — which is why it sits here rather than in whichever of the three came first.

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

**Corollary 13.3.4 is here in all four clauses** — `mem_closure_dom_conj_iff`,
`mem_relint_dom_conj_iff`, `mem_interior_dom_conj_iff`, `mem_affineSpan_dom_conj_iff`, with
`zero_mem_closure_dom_conj_iff` kept as a two-line specialisation so that its call sites did not
move — together with **Corollary 13.4.2** (`interior_dom_conj_nonempty_iff`) and
`separatingRight_flip_of_separatingDual`.

**Theorem 27.1(i)'s second sentence is here too**, `zero_notMem_closure_dom_conj_iff`, with
`recessionFn_le_neg_coe_iff` spelling out what `f 0⁺ y ≤ -ε` means pointwise. It is the first
sentence with the quantifier negated; the pointwise form is `recessionFn_le_coe_iff_forall`, i.e.
Theorem 8.5 through Theorem 8.1's `a = 1` test, so **no separate Theorem 8.5 work was needed**
after all. Two conditions Rockafellar states are automatic: `y ≠ 0`, because at `y = 0` the
inequality at `a = 1` would read `0 ≤ -ε` at any point of the (non-empty) effective domain; and
the restriction of `x` to `dom f`, because off `dom f` the right-hand side is `⊤ - ε = ⊤`.

**Corollary 13.3.4 needs neither Theorem 12.3 nor the translation by `-y₀`.** Rockafellar sets
`g = f - ⟨·, y₀⟩`, computes `dom g* = (dom f*) - y₀`, and applies Theorem 13.1 to that translate.
Stating the four clauses through `recessionFn f` and `⟨y, y₀⟩` instead of through `g 0⁺` makes the
translation disappear. Two further observations the book does not make: the exception set in (b),
`-(g0⁺)(-y) = (g0⁺)(y) = 0`, is **`y₀`-independent** — it is `-(f0⁺)(-y) = (f0⁺)(y)` — and its
"`= 0`" is forced by the inequality at `-y`, so (b) really is Theorem 13.1's shape verbatim.

**Corollary 13.4.2 needs no `finrank` count**, contrary to what this entry used to say by grouping
it with Corollary 13.4.1. "`dim f*` = n iff lineality `f` = 0" unwinds to
`vectorSpan (dom f*) = ⊤` iff the annihilator is trivial, which is Hahn–Banach, not dimension
arithmetic. Only Corollary 13.4.1, about *rank*, needs the count.

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
theorem isFace_recessionCone …                                 -- p. 163, the algebraic core
theorem extremeDirections_subset_extremeDirections_recessionCone …  -- p. 163
theorem IsFace.linealitySpace_subset …                         -- p. 166
def isFaceEquivInter …                                         -- p. 166, the face correspondence
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

**The p. 166 face correspondence needs nothing at all.** `isFaceEquivInter` is stated for an
arbitrary subspace `N` of the lineality space and an arbitrary complement `M`, with no closedness,
no convexity of `C` and no finite dimension; the book's `L` and `L^⊥` are one instance. Its engine
is `IsFace.linealitySpace_subset` — a face is linear in every direction in which `C` is, because
`x` is the midpoint of the segment from `x - y` to `x + y` — which is also what lets
`eq_add_inter_of_isCompl_of_le` be applied to a face.

**The p. 163 remark "every extreme direction of `C` is an extreme direction of `0⁺C`" needs no
closedness.** Rockafellar's `C' ⊆ x + 0⁺C ⊆ C` argument is purely algebraic once one knows that the
direction of the half-line face recedes in `C`; closedness only discharges that, via Theorem 8.3.
`isFace_recessionCone` states the general fact — the recession cone of a face is a face of the
recession cone, given `0⁺C' ⊆ 0⁺C` — at layer A, and simultaneously performs the book's restriction
to `x + 0⁺C` and his translation by `-x`.

**Layer deviation.** Straszewicz's core needs a genuine inner product; the public statements are
recovered for arbitrary finite-dimensional real normed `E` by transporting through Mathlib's
`toEuclidean`, so nothing downstream inherits the restriction.

**Not here**: Theorems 18.7, 18.8 and Corollary 18.7.1, which are in `Exposed.lean` and
`Tangent.lean`. The definition of an *exposed direction* was indeed what was missing; the
"dimension bookkeeping" this entry used to name as the second blocker turned out not to exist — see
`Exposed.lean` below. **Theorem 11.2 was never the blocker** either — it is
`exists_separates_of_isOpen_of_disjoint_affine` in `Separation.lean`.

### `Tdaf/Analysis/Convex/Duality/GaugeLike.lean`

**Theorem 12.4** in one dimension, and everything in **§15** that composes a nondecreasing convex
function of the half-line with a gauge: **Theorem 15.3**'s first assertion and conjugacy formula,
and **Corollaries 15.3.1–15.3.2** in full.

```lean
structure MonotoneHalfLineFn (g : ℝ → EReal) : Prop     -- +∞ on (-∞,0), monotone, convex, closed
noncomputable def monotoneConj (g : ℝ → EReal) : ℝ → EReal            -- the monotone conjugate g⁺
theorem monotoneConj_monotoneConj …                                  -- Thm 12.4: g⁺⁺ = g
noncomputable def monotoneComp (g : ℝ → EReal) (k : E → EReal) : E → EReal        -- g ∘ k
theorem conj_monotoneComp …                                         -- Thm 15.3: (g ∘ k)* = g⁺ ∘ k°
theorem closedProperConvexFn_monotoneComp …                          -- Thm 15.3, first assertion
def PosHomogeneousDeg … ; noncomputable def degGauge …
theorem posHomogeneousDeg_iff_exists_isGauge …                       -- Cor 15.3.1
theorem conj_monotoneComp_powHalfLine …                              -- Cor 15.3.1, the conjugate
theorem polarGauge_degGauge … ; theorem pairing_le_rpow_mul_rpow …    -- Cor 15.3.2, Hölder
theorem polarSet_setOf_le_inv …                                      -- Cor 15.3.2, the polar set
structure IsGaugeLike (f : E → EReal) : Prop      -- `f 0 = inf f`; the level sets are dilates
theorem IsGaugeLike.exists_isGauge_setOf_le_eq …              -- every level set is a level set of one gauge
theorem IsGaugeLike.exists_eq_monotoneComp …      -- Thm 15.3, the converse half
theorem isGaugeLike_monotoneComp …                -- Thm 15.3, the forward half, repackaged
theorem closedProperConvexFn_and_isGaugeLike_iff … -- Thm 15.3, the biconditional
theorem MonotoneHalfLineFn.exists_lt_monotoneConj … -- `g` finite at some ζ > 0 ⇒ `g⁺` non-constant
theorem isGaugeLike_conj_monotoneComp …            -- Thm 15.3, "`f*` is gauge-like too"
```

**Theorem 12.4 is stated as a genuine involution, not a bijection onto a smaller class.** The
monotone conjugate is *truncated* — `+∞` off the half-line — and that is what makes
`monotoneConj_monotoneConj` an identity. The whole proof reduces to Fenchel–Moreau for
`mulPairing` plus `iSup_sub_monotoneConj`: the negative half-line contributes nothing at
nonnegative arguments. **There is no general-cone version** — the `ℝⁿ` orthant proof uses the
lattice operation `y ↦ max(y, 0)`, which has no analogue for a general cone.

**"Non-constant" is not needed for the conjugacy formula, and is genuinely needed for the first
assertion.** `conj_monotoneComp` is proved without it. What it is consumed by is *closedness* of
`g ∘ k`, through `MonotoneHalfLineFn.exists_monotoneConj_ne_top` — which is what lets the formula
be applied a *second* time, to `g⁺ ∘ k°`. The book does not remark on this, but for constant `g`
the composite is `g(0)` on `dom k` and `+∞` off it, and `dom k` need not be closed even for a
closed gauge: for `C = {(a,b) | b ≥ a²}` in `ℝ²`, `dom γ(·|C) = {b > 0} ∪ {0}`. Not an
infinite-dimensional artefact.

**"Finite at some `ζ > 0`" is used only in the `k°(y) = +∞` branch, and cannot be dropped there.**
Same parabola: with `g = δ(·|{0})` the composite is `δ(·|{k ≤ 0})`, whose conjugate is the support
function of `0⁺C`, while the right-hand side is `+∞` off the *barrier* cone of `C` — strictly
smaller for the parabola. At `y = (1,0)` the left side is `0` and the right side is `+∞`.

**The step "λ = sup{ζ ≥ 0 | g(ζ) ≤ α} is finite and positive" needs an argument the book does not
give.** Finiteness is the Theorem 8.6 growth estimate (`bddAbove_setOf_le`); positivity is a
right-continuity statement at the origin which is *false* for a nondecreasing closed convex `g`
finite only at `0`, and needs exactly the finiteness-at-a-positive-level hypothesis already present
(`MonotoneHalfLineFn.exists_pos_le`).

**Corollary 15.3.1 does not need Theorem 15.3's characterisation**, which is why both corollaries
survive the gap below. The book says "`f` is gauge-like, so the corollary follows"; the gauge can
instead be written down directly as `(pf)^{1/p}`, whose unit level set is `{f ≤ 1/p}`, and
`gaugeFn_level_one` + `convexFn_gaugeFn` + `closedFn_gaugeFn` finish it. Corollary 15.3.1 also
silently uses `f(0) = 0` and `f ≥ 0`; closedness is genuinely required for the first, since
`f = λᵖ` on a ray and `+∞` elsewhere is convex, proper and degree-`p` homogeneous with
`f(0) = +∞` (`PosHomogeneousDeg.map_zero_eq_zero`).

**Almost none of this needs a compatible pairing.** `conj_monotoneComp` holds for an arbitrary
bilinear `B`; topology on `E` enters only through `ClosedFn k`, and only in the `≤` half, and
`ClosedFn k` itself is used only through `x ∈ k(x) • {k ≤ 1}`. Compatibility, continuity and local
convexity appear only in `closedFn_monotoneComp`, where Fenchel–Moreau is invoked.

**The converse half of Theorem 15.3 is now here too**, with the `IsGaugeLike` predicate, and the
recorded blocker — convexity of the reconstructed `g` — was not the obstacle. **One** lemma carries
the whole proof: *every* sublevel set of `f` above `inf f` is a sublevel set of a single gauge
(`IsGaugeLike.exists_isGauge_setOf_le_eq`, with `k = γ(· | {f ≤ f 0 + 1})`, since a gauge-like `f` makes any two
of its sublevel sets positive multiples of each other and `setOf_gaugeFn_le_pos` turns dilates of
one of them into sublevel sets of its gauge). From it, `k u ≤ k v ⇒ f u ≤ f v`
(`le_of_forall_setOf_le_eq`) and `k u = ⊤ ⇒ f u = ⊤` (`eq_top_of_forall_setOf_le_eq`), so `f x`
depends on `x` only through `k x`, and no `α ↦ λ_α` bijection is needed. `g` is then read off along
a ray, `f(· • x₁)` restricted to `[0, ∞)`, whose convexity and closedness are `f`'s transported by
`convexFn_compLin` / `closedFn_compLin` and `restrict`; `MonotoneOn` comes from the displayed
implication, not from convexity.

**The case split is on the gauge, not on the level sets, and it is coarser than the book's.**
Rockafellar splits on whether all the level sets are the *same* multiple of `C`. What actually
matters is whether `k` attains the value `1`
(`IsGauge.exists_eq_one_or_forall_eq_zero_or_eq_top`): a positively homogeneous `[0, ∞]`-valued
function either takes some value in `(0, ∞)` — and then `x₁ = (k x)⁻¹ • x` is a ray — or takes only
`0` and `⊤`. Rockafellar's degenerate branch is *not* the same case: `f = α₀ + δ(· | λC)` with `C`
not a cone has all its level sets equal and still admits a ray, and the ray argument covers it. The
genuinely degenerate case is only `k ∈ {0, ⊤}`, where `f` is `f 0` on a cone and `⊤` off it and the
half-line factor is the step function `f 0 + δ(· | [0, 1])`.

**Conjugacy exchanges the two side conditions on `g`.** Rockafellar's "`g⁺` satisfies the same
conditions as `g`" is two lemmas, and they cross: `g` *non-constant* gives `g⁺` *finite at a
positive level* (`exists_monotoneConj_ne_top`, through the affine minorant), and `g` *finite at a
positive level* gives `g⁺` *non-constant* (`exists_lt_monotoneConj`, because the term of the
defining supremum at that level is affine in `s` with positive slope). With both,
`isGaugeLike_conj_monotoneComp` — Theorem 15.3's second assertion, `f*` gauge-like — is
`conj_monotoneComp` followed by `isGaugeLike_monotoneComp`.

**The converse needs no pairing, no local convexity and no conjugation.** It is layer B — a
topological vector space and nothing more — whereas the forward half needs Fenchel–Moreau for
closedness. In `closedProperConvexFn_and_isGaugeLike_iff` the pairing appears only for that
direction.

**Non-constancy and finiteness at a positive level are produced, not assumed.** They are the two
conditions Rockafellar imposes on `g`, and the reconstruction has to deliver them: with `c` the
level of `k` matching `{f ≤ f 0 + 1}`, the ray function is finite at `c` and `⊤` at `c + 1`. In the
degenerate branch the step function supplies both by construction.

**`Operations/Closed.lean` is imported for one lemma.** `compLin` and `closedFn_compLin` are not
in the import closure of `Duality/Gauge.lean`, and the ray `ζ ↦ f (ζ • x₁)` is
`compLin f (LinearMap.toSpanSingleton ℝ E x₁)`, so the file now imports `Operations/Closed.lean` as
well. Nothing imports `GaugeLike.lean`, so the cost is one module's rebuild.

**Relocation candidates**: `le_of_forall_setOf_le_eq` and `eq_top_of_forall_setOf_le_eq` are about
a function whose sublevel sets are another function's, and would fit a general "level-set
comparison" module if one ever appears; `eq_top_or_exists_coe_of_nonneg` → `Tdaf/Order/EReal.lean`;
`pairing_le_mul_of_gauge`, `pairing_nonpos_of_gauge_eq_zero` and `setOf_polarGauge_le_one` →
`Duality/Gauge.lean` (all three are about a gauge and its polar, not about the composite);
`PosHomogeneousDeg` and its basic lemmas → `Homogeneous.lean`; `ClosedFn.restrict` →
`Operations/Basic.lean`; the two `mulPairing.flip` instances → beside `mulPairing` in
`Duality/Gauge.lean`; `rpow_inv_rpow`, `rpow_rpow_inv`, `rpow_inv_le_one_iff` are Mathlib-shaped
`Real.rpow` gaps and should be upstreamed or given a `Tdaf/Analysis/SpecialFunctions/` home.
`convexFn_monotoneComp` is really Rockafellar's Theorem 5.1 and belongs in `Operations/` if a
general composition module ever appears.

### `Tdaf/Analysis/Convex/Exposed.lean`

**Theorem 18.7 and Corollary 18.7.1**, on the strength of a definition the book leaves informal.

```lean
def IsExposedDirection (C : Set E) (y : E) : Prop
def exposedDirections (C : Set E) : Set E
theorem exists_forall_sub_le_mul_sub …
theorem closure_convexHullPD_exposedPoints_exposedDirections …     -- Thm 18.7
theorem closure_coneHull_exposedDirections …                      -- Cor 18.7.1
theorem isExposed_recessionCone …                                 -- p. 163, the algebraic core
theorem exposedDirections_subset_exposedDirections_recessionCone … -- p. 163
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

**The exposed half of the p. 163 remark is proved by the same functional.** `isExposed_recessionCone`
shows `0⁺` of an exposed face is exposed in `0⁺C` by the *same* `l`: a functional maximised over `C`
is non-positive on `0⁺C`, and vanishes exactly on the directions in which the face itself recedes.
Like the extreme half it needs no closedness — only `0⁺C' ⊆ 0⁺C`.

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

**Not here**: Theorem 15.3 and Corollaries 15.3.1–15.3.2, which need the nondecreasing lsc convex
functions on `[0, +∞]` and their *monotone conjugate*. They are **done**, in
`Duality/GaugeLike.lean` — this paragraph used to call them "the one genuinely unbuilt piece of
§15", and used to list Corollary 14.6.1 as absent as well, which contradicted the second paragraph
of this very record; both claims were stale and are corrected here. `polarSubmodule` and
`coe_polarSubmodule` have **moved down to `Duality/Polar.lean`**, beside `polarCone_coe_submodule`,
because §12's partial-affine formula needs them there; `finrank_add_finrank_polarSubmodule` and
Corollary 14.6.1 stay here.

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

---

### `Tdaf/Analysis/Convex/Saddle/Differential.lean`

Rockafellar §35's differential half: **Theorems 35.6, 35.7 and 35.8**, with Corollaries 35.7.1 and
35.8.1. §23/§24/§25 read for a concave-convex function of a pair on an open rectangle.

**The module is `Differential`, not `Subgradient`, because §37 owns that name.** `dirDerivReal`,
`subgradientFst`, `subgradientSnd`, `subgradientSaddle` and `HasSaddleGradientAt` are the
real-valued theory on a rectangle; `Saddle/Subgradient.lean` holds `concaveSubgradient` and
`saddleSubgradient` for `EReal`-valued saddle-functions, which is what §37's conjugacy needs. The
two notions agree where both apply. **Unifying them is a deferred clean-up**, and it is the one
place where two agents working in parallel produced the same file name for different content.

**`dirDerivReal` is a genuine limit, not an infimum.** `Subgradient/Defs.lean`'s `dirDeriv` is the
`EReal` infimum of the difference quotients, which is the right definition when the function can be
infinite. For a finite convex function on an open set the quotient is monotone and bounded, so the
limit exists, and stating it as a limit is what lets `Filter.Tendsto` machinery apply. The whole
§23 API around it — `tendsto_slope_dirDerivReal_of_convexOn`, `convexOn_dirDerivReal`,
`dirDerivReal_le_slope` — is Theorem 23.1 in real form and **is a relocation candidate**: it has
nothing to do with saddle-functions and belongs beside `dirDeriv`.

**Theorem 35.6's content is the *joint* limit.** The displayed equation
`K'(u, v; u', v') = K'(u, v; u', 0) + K'(u, v; 0, v')` presupposes that the two-variable difference
quotient converges at all, which is `tendsto_slope_dirDerivReal_prod`; the equation itself is then
the concave and convex halves meeting.

**Theorem 35.8's converse is the module's largest proof after Theorem 35.7's.** It goes through
Corollary 35.7.1, not through Theorem 35.4's rescalings as the book does: sandwich the increment at
`(u,v)`, `(u, v+b)` and `(u+a, v+b)` and read the Fréchet estimate off directly. The scaffolding for
Rockafellar's own route was written and then deleted.

**A product of inner-product spaces is not an inner-product space in Mathlib** — `Prod` carries the
supremum norm — so the gradient of a function of a pair has to be represented by hand as
`prodInnerL`. Same fact as the `k₁ + k₂` Lipschitz constant of Theorem 35.2.

**The restriction-to-a-line group has moved out**, to `Tdaf/Analysis/Convex/Line.lean`, which this
file now imports: `convexOn_comp_line`, `concaveOn_comp_line`, `isOpen_line_steps` and the two
`continuousAt_comp_line_of_*`, together with the converse `convexOn_iff_lines` /
`concaveOn_iff_lines` that was missing. Nothing outside this file used any of them, and §4 of the
surface needs the reduction to lines without the saddle tower above it.

**Relocation candidates**, beyond `dirDerivReal`: `dirDerivReal_eq_of_hasFDerivAt`, `le_add_of_hasFDerivAt_of_convexOn`
and the two `eq_of_forall_…_of_hasFDerivAt` (real forms of Theorems 25.1 and 25.2, belong in
`Subgradient/Gradient.lean`); `forall_inner_le_dirDerivReal_iff` and its partner (Theorem 23.2 at
an interior point); `prodInnerL` (Riesz representation on a product, no convexity);
`neg_add_closedBall_zero`, `prod_add_prod_subset`, `norm_sub_le_of_mem_singleton_add_closedBall`
(Mathlib-shaped gaps in pointwise-set arithmetic); `ConcaveConvexOn.negSwap` and
`tendsto_eval_prod_of_tendsto` (`Saddle/Continuity.lean`).

---

### `Tdaf/Analysis/Convex/Line.lean`

The restriction of a real-valued function to a line, `t ↦ f (x + t • d)` on `{t | x + t • d ∈ S}`.
Five of the six declarations came from `Saddle/Differential.lean`, where they had no saddle content
and no consumer outside that file; the sixth, `convexOn_iff_lines`, is new and is the one that makes
the reduction useful — it turns a convexity question on a vector space into one about functions of a
single real variable, which is how the second-derivative criterion reaches `ℝⁿ`.

**The step set is left as a preimage**, not identified with an interval. It *is* an interval for
convex `S`, but the forward lemmas do not need convexity, and the preimage form makes
`isOpen_line_steps` one line.

**The converse's direction is `y - x`.** One line carries the whole convexity inequality for the
pair `(x, y)`, at steps `0` and `1`; no hypothesis on `d` is needed.

**The `ConvexOn.2` application is a beta-redex** and `rw` cannot see into it — gotcha EL2. The proof
ascribes `hmain`'s type explicitly, which forces the reduction before any rewriting.

---

### `Tdaf/Analysis/Convex/Saddle/Rademacher.lean`

§35's last two theorems: **Theorem 35.9** (a finite concave-convex function on an open rectangle is
differentiable a.e. there, densely, with `∇K` continuous where it exists) and **Theorem 35.10**
(convergence of gradients under pointwise convergence, uniformly on compacts).

```lean
theorem ConcaveConvexOn.exists_lipschitzOnWith_ball … :
    ∃ r > 0, ball p r ⊆ C ×ˢ D ∧ ∃ k : ℝ≥0, LipschitzOnWith k K (ball p r)
theorem ae_differentiableAt_of_concaveConvexOn … : ∀ᵐ p ∂μ, p ∈ C ×ˢ D → DifferentiableAt ℝ K p
theorem measure_diff_differentiableAt_of_concaveConvexOn … :
    μ ((C ×ˢ D) \ {p | DifferentiableAt ℝ K p}) = 0
theorem subset_closure_differentiableAt_of_concaveConvexOn … :
    C ×ˢ D ⊆ closure {p | DifferentiableAt ℝ K p}
theorem continuousOn_saddleGradient … (hS : S ⊆ C ×ˢ D)
    (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) : ContinuousOn G S
theorem dist_le_of_subgradientSaddle_subset … : dist a b ≤ ε
theorem tendsto_of_hasSaddleGradientAt … : Tendsto G atTop (𝓝 G')      -- **Thm 35.10**
theorem tendstoUniformlyOn_saddleGradient … : TendstoUniformlyOn Gs G atTop S
```

**Theorem 35.9 does not go through Theorem 25.5, and it does not need the book's Fubini argument.**
Rockafellar decomposes the complement of the differentiability set into the closed sets `Sₖ` where
a one-sided partial derivative jumps by at least `1/k`, and shows each meets every coordinate line
in a finite set. All that convexity has to supply here is a *local Lipschitz constant*, and
Theorem 35.1 (`ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact`) gives one on every compact
rectangle; shrinking a closed ball to an open one makes the set simultaneously Lipschitz and open,
which is what lets `LipschitzOnWith.ae_differentiableWithinAt_of_mem` upgrade to `DifferentiableAt`.
The rest — a countable subcover from `TopologicalSpace.isOpen_iUnion_countable`, then
`Basis.addHaar` borrowed locally for the density clause — is `Subgradient/Rademacher.lean`'s proof
of Theorem 25.5 transcribed. Note that `Metric.ball p r` in `U × X` **is** the product of the two
balls (`Metric.ball_prod_same`, the supremum metric), which is why one radius does for both factors.

**The continuity clause and both clauses of Theorem 35.10 are the same two lines.**
`subgradientSaddle_eq_singleton_of_hasSaddleGradientAt` (Theorem 35.8) turns `∂K(p) ⊆ ∂K(q) + εB`
into `‖∇K(p) - ∇K(q)‖ ≤ ε`; feed it Corollary 35.7.1 and you get continuity of `∇K`, feed it
Theorem 35.7 at a constant sequence and you get Theorem 35.10's pointwise clause, feed it
Theorem 35.7 along a subsequence and Corollary 35.7.1 at the limit point and you get the uniform
clause by the contradiction argument of Theorem 25.7. Neither Theorem 35.4 nor Theorem 35.9 is used
in Theorem 35.10, and the pointwise clause needs differentiability only at the point in question,
not everywhere as the book assumes.

**`∇K` is a pair, so the statements quantify over a representing function.** There is no canonical
`∇K : U × X → U × X` without choice, so `continuousOn_saddleGradient` and
`tendstoUniformlyOn_saddleGradient` take any `G` with `HasSaddleGradientAt K (G p) p` on the set in
question. `prodInnerL` is injective, so `G` is unique there and nothing is lost.

**Relocation candidates**: `ConcaveConvexOn.exists_lipschitzOnWith_ball` belongs beside Theorem 35.1
in `Saddle/Continuity.lean` — it is Theorem 35.1 with a ball in place of a compact rectangle, and
nothing about Rademacher enters it.

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

**`convexBifun_neg_adjointBifun` moved out.** It was declared here and independently in
`Optimization/Adjoint.lean` while §30's clauses (h) and (j) were being written — gotcha LIB1 — and
the §30 file is where Theorem 30.1 lives, so the copy here is gone and
`closedFn_neg_adjointBifun_apply` and `closedBifun_inverseBifun_adjointBifun` now quote
`closedBifun_neg_adjointBifun` instead of re-deriving it.

**Relocation candidates.** `ConvexFn.exists_mem_relint_dom_lt` and
`ConvexFn.biInf_eq_iInf_of_relint_dom_subset` (Corollary 7.3.1) belong in `RelativeInterior.lean`;
`iSup_clConcave_eq_iSup` and `concaveConj_clConcave` (Theorem 12.2's first half, concave side)
belong in `Duality/ConcaveConj.lean`.

### `Tdaf/Analysis/Convex/Saddle/Subgradient.lean`

§37's subdifferential theory: the two one-sided subdifferentials of a saddle-function, their
product `∂K`, and **Theorems 37.4, 37.5** and **Corollary 37.5.3**.

```lean
def concaveSubgradient B g x …        -- the superdifferential of a concave function
def saddleSubgradient Bu Bx K p …     -- `∂K (u, x) = ∂₁K (u, x) × ∂₂K (u, x)`
def IsBifunSubgradientPair …          -- Theorem 37.5's condition (d), representative-free
def saddleTilt Bu Bx K q …            -- `K` tilted by a linear function
theorem mem_saddleSubgradient_iff_isSaddlePoint …        -- **Thm 37.4**, no hypotheses at all
theorem kernelSet_subset_domSaddleSubgradient_subset_domSaddle …  -- **Thm 37.4**, 2nd sentence
theorem mem_saddleSubgradient_iff_isBifunSubgradientPair …        -- **Thm 37.5**, (a) ⇔ (d)
theorem mem_saddleSubgradient_upperConjSaddle_iff …               -- **Thm 37.5**, (b) ⇔ (d)
theorem exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle …  -- **Thm 37.6**
```

**`∂K` is the same relation for every member of a class.** That is the content of (a) ⇔ (d), and it
is why `IsBifunSubgradientPair` is stated for the bifunction rather than for a representative;
(b) ⇔ (d) then says the subdifferentials of conjugate classes are inverse to each other, which is
what turns saddle-point existence into a statement about `0 ∈ dom ∂K*`.

The module also carries the `EReal` cancellation lemmas §37 runs on (`sub_coe_le_sub_coe_iff_le_add`
and relatives) — relocation candidates for `Tdaf/Order/EReal.lean`.

### `Tdaf/Analysis/Convex/Saddle/Conjugate.lean`

The two conjugates `K̲*`, `K̄*` of a saddle-function are the two brackets of *one* convex
bifunction, hence a closure pair: **Corollaries 37.1.2 and 37.1.3**.

```lean
theorem adjointBifun_flip_inverseBifun …                    -- `(G_*)^* = (G^*)_*`, no hypotheses
theorem adjointBifun_flip_inverseBifun_adjointBifun …        -- biadjoint identity `(F_*^*)^* = F_*`
theorem saddleLagrangian_eq_concaveBracket …                 -- `L (v, x) = ⟨v, F_* x⟩`
theorem partialCl₁_lowerConjSaddle, partialCl₂_upperConjSaddle …  -- **Cor 37.1.2**
theorem saddleClass_conjSaddle, saddleEquiv_lowerConjSaddle_upperConjSaddle …
theorem dom₁_conjSaddle_eq, dom₂_conjSaddle_eq, domSaddle_conjSaddle_eq …
theorem hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle …  -- **Cor 37.1.3**
```

**The one new algebraic fact is the biadjoint identity, and it is not a new theorem.** The inverse
operation `F ↦ F_*` intertwines the adjoint of a convex bifunction with the adjoint of a concave
one, so `(F_*^*)^* = F_*` is Theorem 30.2 (`F^{**} = cl F`) read through that intertwining.

### `Tdaf/Analysis/Convex/Saddle/Existence.lean`

The `C*` halves of §37 and the existence theorems: **Theorem 37.3 (b)**, **Theorem 37.6**,
**Corollaries 37.2.1, 37.3.1, 37.3.2, 37.6.1, 37.6.2**.

```lean
def swapAdjointBifun …                                   -- `F♯`, the bifunction of the swapped class
theorem saddleSwap_mem_bifunSaddleClass …                 -- `saddleSwap` carries `Ω (F)` onto `Ω (F♯)`
theorem upperConjSaddle_saddleSwap, lowerConjSaddle_saddleSwap …  -- it exchanges the conjugates
theorem proper_graphFn_of_properSaddleFn …                -- `ProperSaddleFn K → Proper (graphFn F)`
theorem hasSaddleValue_of_no_common_direction_of_recession_neg …  -- **Thm 37.3**, condition (b)
theorem exists_isSaddlePoint_of_no_common_direction_of_recession …  -- **Thm 37.6** on `K`
theorem exists_saddlePoint_of_isBounded …                 -- **Cor 37.6.2**, the minimax theorem
theorem isBifunSubgradientPair_iff_mem_subgradient_graphFn …      -- **Thm 37.5**, (c) ⇔ (d)
```

**The device is `saddleSwap K (y, u) = -K (u, x)`, and the swapped class is not the conjugate
class.** Under the swap `Ω (F)` becomes `Ω (F♯)` at the *negated flipped* pairings, where
`F♯ = flipBifun (inverseBifun (adjointBifun Bu Bx F))` — not `F_*^*`, which goes from `V` to `Y`
and lives on the wrong product. The `flipBifun` is load-bearing.

**Corollary 37.3.2 cannot be stated with real-valued extrema.** With only one of `C`, `D` bounded
both iterated extrema can be infinite (`C = {0}`, `D = ℝ`, `K (u, v) = v` gives
`sup_C inf_D K = -∞`), so the equality is stated in `EReal`. Corollary 37.6.2, where both are
bounded, keeps the book's real inequalities.

**`setOf_mem_saddleSubgradient_eq_preimage` is the reusable form of Theorem 37.5's (c).** The
closedness clause of Corollary 37.5.1 only needs the graph of `∂K` to be a preimage of the graph of
`∂f`; so do the homeomorphism clause and Corollary 37.5.2. Factoring the set equality out of the
closedness proof is what let `Saddle/Monotone.lean` be short.

**Not here**: Corollary 37.5.1's homeomorphism clause and Corollary 37.5.2, which are in
`Saddle/Monotone.lean` — they are Corollaries 31.5.1 and 31.5.2 at
`prodPairing (innerₗ U) (innerₗ X)`, which became possible once `Optimization/Prox.lean` was
generalized off `innerₗ E`. `Subgradient/Monotone.lean` has maximal *cyclic* monotonicity, which is
a different statement.

### Stale "what is not here" paragraphs, corrected

Five module docstrings still listed as missing results that had since landed elsewhere. Each now
names the module the result is in: §18's unbounded case in `Face.lean` (it is in
`Representation.lean`, `Exposed.lean` and `Tangent.lean`), Theorem 23.10 in
`Subgradient/Calculus.lean` (`Subgradient/Existence.lean`), §33's corollaries in `Saddle/Defs.lean`
(`Saddle/Correspondence.lean`, `Saddle/Kernel.lean`), the `C*` halves of §37 in
`Saddle/Conjugate.lean` (`Saddle/Existence.lean`), and the rest of §37 in `Saddle/Minimax.lean`.
A second sweep, after the §15 / §30 / §38–§39 merges, found four more — three of them naming a
*reason* that was wrong, rather than merely a location:

* `Optimization/Adjoint.lean` said Theorems 30.3–30.5 need §16's exactness results. They are in
  `Optimization/Normal.lean`, and rest on `clFn_zero_eq_iSup_iInf`, Fenchel–Moreau at the origin.
* `Optimization/Perturbation.lean` said Theorem 29.4 needs §36's saddle-point correspondence. It is
  in `Optimization/Adjoint.lean`, beside the closure operation it is stated in terms of, and it
  never needed §36.
* `Optimization/Lagrangian.lean` said Theorem 28.2 needs §21's theorems of the alternative wired to
  an `ineqBifun` that `Helly.lean` cannot supply for mixed inequality/equality systems. It is
  `exists_isKuhnTuckerVector_of_slater` in `Optimization/Program.lean`: Theorem 21.2 as formalized
  keeps the affine constraints in a second index type, which already *is* the mixed form. The same
  paragraph called Theorem 29.3 missing when it is `isSaddlePoint_lagrangian_iff`.
* `06-optimization.md` carried a `Cor 30.2.1 | not done` row eighty lines above the row listing the
  five declarations that prove it.

Worth a sweep after every merge, and note what the two sweeps have in common: an entry rots fastest
when it explains *why* something is blocked, because the explanation is the part a later agent
believes and does not re-derive. Three of these four had outlived the obstruction they described and
were pointing work away from results that already existed. A "what is not here" note is written
once, is never re-read by its author, and is the first thing a fresh agent reads.

### `Tdaf/Analysis/Convex/Duality/ConcaveOps.lean`

Supremal convolution and the concave Theorem 16.4, which §38 needs for the adjoint of `F₁ □ F₂`.

```lean
def supConv g h …                       -- `-((-g) □ (-h))`
theorem infConv_neg …
theorem supConv_apply …                 -- the sup formula, when neither function reaches `+∞`
theorem concaveConj_add_of_isExactSum …  -- **the concave Thm 16.4**: `(g₁ + g₂)* = g₁* □ g₂*`
```

Rockafellar writes `□` for both convolutions and calls this "the concave version of Theorem 16.4";
the hypothesis is exactly `IsExactSum B (-g₁) (-g₂)`.

### `Tdaf/Analysis/Convex/Bifunction/Algebra.lean`

The **convex algebra** of bifunctions: the operations that mirror the linear algebra of linear
maps, and the inner product that adjoints move across. All of §38 except the second equality of
Corollary 38.7.2 and the co-finiteness remark, which need a relative interior and a finite
dimension and are in `Bifunction/Cofinite.lean`.

```lean
noncomputable def infConvBifun …    -- `F₁ □ F₂`, the analogue of `A₁ + A₂`
noncomputable def infConvFstBifun … -- `H₁ ⊡ H₂`, the same in the *first* variable
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
theorem lowerAdjointBifun_infConvFstBifun …                              -- the key to Cor 38.2.1
theorem closedBifun_infConvBifun …
theorem lowerAdjointBifun_infConvBifun_eq_clBifun …                      -- **Cor 38.2.1**
theorem bracket_compBifun_eq_fenchelPairing …                            -- **Cor 38.7.2**, 1st
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

**Corollary 38.2.1 convolves in the other variable.** It is Theorem 38.2 applied to the adjoints,
which convolve in the *first* variable of the bifunction, so `infConvFstBifun` had to be built
first; following Corollaries 38.4.1 and 38.5.1 it is packaged convexly, as a convolution of the
*lower* adjoints, and the whole corollary stays between convex bifunctions with no concave closure
anywhere. The one new theorem is `lowerAdjointBifun_infConvFstBifun`, `(H₁ ⊡ H₂)⁎* = H₁⁎* □ H₂⁎*`:
with `φᵢ y = ⨅ v, (Hᵢ v y + ⟨u, v⟩)` the lower adjoint of `Hᵢ` at `u` *is* `φᵢ*`
(`lowerAdjointBifun_eq_conj_concaveBracket_invBifun`), `φ = φ₁ + φ₂` holds unconditionally
(`conj_infConv` plus one `EReal.neg_add`), and `IsExactSum.conj_add` finishes. Corollaries 38.4.1
and 38.5.1 are the same shape: each exhibits its composite as a `lowerAdjointBifun`, which is
closed with no hypothesis (`closedBifun_lowerAdjointBifun`), so "closure commutes with
`imageBifun` / `compBifun`" is never needed.

**Corollary 38.7.2's first equality is Corollary 38.7.1 at a slice.** `compBifun_slice`,
`(GF)u = G(Fu)`, is `rfl`, so `⟨GFu, z⟩ = ⟨Fu, G* z⟩` needs nothing new. Only the second equality
`⟨GFu, z⟩ = ⟨u, F* G* z⟩` is Corollary 33.2.1 and hence layer D.

**Relocation candidate**: `infConv_indicatorFn` (`δ(·∣S) □ δ(·∣T) = δ(·∣S+T)`) belongs in
`Operations/InfConv.lean`, which currently has only the singleton case.

### `Tdaf/Analysis/Convex/Bifunction/Cofinite.lean`

**Co-finite bifunctions**: the closing remark of §38, and the half of Corollary 38.7.2 that needs a
relative interior. The only finite-dimensional module in §38.

```lean
structure CofiniteBifun (F : Bifun U X) : Prop where convexBifun … ; cofinite_apply …
theorem CofiniteBifun.bracket_lt_top … ; theorem cofiniteBifun_of_forall_bracket_lt_top …
theorem cofinite_infConv …                     -- `f □ g` co-finite, a function-level lemma
theorem cofiniteBifun_infConvBifun … ; theorem adjointBifun_infConvBifun_of_cofinite …
theorem CofiniteBifun.bracket_eq_concaveBracket_adjointBifun …
theorem bracket_compBifun_eq_concaveBracket_concaveCompBifun …   -- **Cor 38.7.2**, 2nd
```

**Co-finiteness is what makes the `IsExactSum` hypotheses of §38 discharge themselves.** A
co-finite bifunction has `domBifun F = U` and `⟨Fu, y⟩` finite for every `u` and `y`
(Corollary 13.3.1, slice by slice), so `IsExactSum.of_relint` applies at the origin and
Rockafellar's relative-interior conditions become vacuous. That is the whole content of his closing
remark, and it is why this is the one place in §38 that needs `FiniteDimensional`.

**`CofiniteBifun` carries `ConvexBifun` as a field.** Rockafellar defines co-finiteness for convex
bifunctions only, and the convexity is genuinely extra data: a bifunction whose slices are all
convex need not have a convex graph function on `U × X`.

**Relocation candidate**: `cofinite_infConv` (the infimal convolution of two co-finite convex
*functions* is co-finite) has nothing to do with bifunctions and belongs in `Duality/Level.lean`
next to the rest of Corollary 13.3.1.

**Not here**: that `Fλ` is co-finite (blocked on the closedness and properness of `smulRight`,
Theorem 38.3's second clause, which the library does not have); that `GF` and `F*` are co-finite
(each needs a co-finite specialization of Theorem 38.5 with `IsExactSum` instances over four
spaces); and Theorem 34.2, "a closed convex bifunction is co-finite iff `dom F = U` and
`dom F* = Y`".

### `Tdaf/Analysis/Convex/Bifunction/Process.lean`

**Convex processes** — multivalued maps whose graph is a pointed convex cone — and the dictionary
that identifies them with indicator bifunctions. All of §39 except Theorem 39.4 and the parts of
Theorems 39.3 and 39.7 that need a topology, which are in `Bifunction/ProcessDuality.lean`. Both
orientations throughout.

```lean
structure ConvexProcess (U X : Type*) … where graph : PointedCone ℝ (U × X)
def eval … ; def dom … ; def range … ; def image … ; def inv …
def ofLinearMap … ; def comp … ; instance : Add …
noncomputable def indicatorBifun … ; def adjointProcess … ; def coadjointProcess …
def reflect … ; noncomputable def coBracket …
theorem exists_linearMap_of_isBounded …                    -- Thm 39.1
theorem coadjointProcess_adjointProcess_eq_self_iff …       -- Thm 39.2, `A** = cl A`
theorem adjointProcess_coadjointProcess_eq_self_iff …       -- Thm 39.2, other orientation
theorem coBracket_eq_neg_bracket …                          -- Thm 39.3, the sign dictionary
theorem iSup_coadjointProcess_eq_clFn …                     -- Thm 39.3, 3rd, other orientation
theorem adjointProcess_add … ; theorem coadjointProcess_add …           -- Thm 39.5
theorem isClosed_graph_add … ; theorem graph_adjointProcess_add_eq_closure …  -- Thm 39.5, closed
theorem adjointProcess_comp … ; theorem coadjointProcess_comp …         -- Thm 39.8
theorem isClosed_graph_comp … ; theorem graph_adjointProcess_comp_eq_closure … -- Thm 39.8, closed
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

**Every infimum-oriented statement is a reflection.** `reflect` sends `graph A` to `-graph A`; it
exchanges `adjointProcess` and `coadjointProcess`, commutes with sums and products, and preserves
closedness, so the mirrors of Theorems 39.2, 39.5 and 39.8 are the supremum-oriented theorems
applied to `A.reflect`. Theorem 39.3 is the exception: reflection flips only the *dual* variable of
the inner product, so `coBracket Bx A u y = -(bracket Bx A.indicatorBifun u (-y))` — same `u`,
negated `y` — and that single equation (`coBracket_eq_neg_bracket`) carries every clause of the
mirror, including the third assertion, which comes out with an honest `clFn` in `u` where the
supremum-oriented statement has `partialCl₁`.

**The closed halves of Theorems 39.5 and 39.8 do not specialize Corollaries 38.2.1 and 38.5.1**,
contrary to what this file and `07-saddle-algebra.md` used to say. For closed `A₁`, `A₂` with
exactly adding adjoints, `A₁ + A₂` is *equal* to the infimum-oriented adjoint of `A₁* + A₂*`
(`add_eq_coadjointProcess_add`), because `Aᵢ** = Aᵢ` and `coadjointProcess_add` is the open half in
the other orientation. Adjoints are closed with no hypothesis, so the closedness clause is free,
and the closure formula is the mirrored bipolar theorem. Same for `BA`. No bifunction corollary is
involved.

**Not here**: Theorem 39.4, the fourth and last assertions of Theorem 39.3, and the closed half of
Theorem 39.7 — all of them need §33's closure operations and hence a topology, and all of them are
in `Bifunction/ProcessDuality.lean`. The infimum-oriented mirrors of those two assertions of
Theorem 39.3 are not done anywhere; they belong there too.

### `Tdaf/Analysis/Convex/Bifunction/ProcessDuality.lean`

The two inner products of a convex process, `⟨Au, x*⟩` and `⟨u, A* x*⟩`: **Theorems 39.3 and 39.4**.

```lean
theorem ConvexProcess.closedBifun_indicatorBifun_iff …     -- `A` closed ⇔ `δ(·|A·)` closed
theorem ConvexProcess.partialCl₂_concaveBracket_adjointBifun_indicatorBifun …  -- **Thm 39.3**, 4th
theorem bracket_eq_concaveBracket_adjointBifun_of_mem_relint_domConcaveBifun …  -- dual **Cor 33.2.1**
theorem ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom …             -- **Thm 39.3**, last
theorem exists_unique_convexProcess_bracket_indicatorBifun_eq …                 -- **Thm 39.4**
```

**The two inner products are the bracket and the concave bracket of §33**, taken at the indicator
bifunction of `A` and at its adjoint, so everything separating them is a partial closure.
`Bifunction/Process.lean` proves what needs only Theorem 33.2's first equation; this module adds
what needs the second — closedness of `A` — and what needs relative interiors.

### `Tdaf/Analysis/Convex/Duality/InnerPairing.lean`

A space paired with **itself** by a symmetric positive definite form. Written for §37, which needs
§31's Moreau/prox machinery on `U × X`.

```lean
class IsInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Prop        -- symmetric, ≥ 0, and definite
class IsContinuousInnerPairing (B) : Prop extends IsInnerPairing B  -- `x ↦ B x x` continuous
noncomputable def pairingNorm (B) (x : E) : ℝ                   -- `√(B x x)`
theorem pairing_sq_le_mul …                                    -- Cauchy–Schwarz
theorem pairingNorm_add_le …                                   -- the triangle inequality
instance isInnerPairing_prodPairing …                          -- what §37 runs on
theorem exists_pairingNorm_le_and_le_pairingNorm …             -- ‖·‖_B ≃ ‖·‖ in finite dimensions
```

**Why not `WithLp 2 (U × X)`.** The obvious fix for "`U × X` is not an `InnerProductSpace`" is to
put the Euclidean structure on the product with `WithLp`. It does not work: `WithLp` *replaces* the
topology instance, so every `ClosedFn`, `Continuous` and `IsClosed` statement about `U × X` — which
is what §37 is made of — has to be transported across a type synonym. Generalizing the pairing
touches only `Optimization/{Moreau,Prox}.lean` and leaves the topology alone.

**Polarization makes `IsContinuousInnerPairing` subsume `IsContinuousPairing`.** From
`B x y = ½ (B (x + y) (x + y) - B x x - B y y)`, continuity of the diagonal gives continuity in
each variable; `isContinuousPairing_of_isContinuousInnerPairing` is that instance (priority 100),
and `isContinuousPairing_flip_of_isContinuousInnerPairing` supplies the flip that instance search
cannot see through `LinearMap.flip` (gotcha PAIR1). So no proof in §31 carries both classes.

**In finite dimensions `IsContinuousInnerPairing` is free, and needs no `IsContinuousPairing`.**
`continuous_self_pairing` goes through `LinearMap.toContinuousLinearMap` into `E →L[ℝ] ℝ` and
`isBoundedBilinearMap_apply`; the first attempt, through the bare `E →ₗ[ℝ] ℝ`, cannot even be
stated, since that type has no `TopologicalSpace` instance.

**`exists_pairingNorm_le_and_le_pairingNorm` is a compactness argument on the sphere**, and it is
the only place the ambient norm and `B` are compared. Both constants come from
`IsCompact.exists_isMinOn`/`exists_isMaxOn` applied to the continuous `pairingNorm B` on
`Metric.sphere 0 1`; positivity of the lower one is definiteness.

### `Tdaf/Analysis/Convex/Saddle/Monotone.lean`

**Corollary 37.5.1's homeomorphism clause and Corollary 37.5.2.**

```lean
def partialInvertEquiv …                        -- `((u, y), (v, x)) ↦ ((u, x), (v, y))`
def partialInvertNegHomeomorph …                -- the same with (c)'s sign: `v ↦ -v`
theorem prodPairing_sub_partialInvertEquiv …     -- it preserves the monotonicity form
theorem IsMaximalMonotoneRel.preimage_partialInvertEquiv …
def saddleMonotoneRel (Bu) (Bx) (K) : SetRel (U × Y) (V × X)   -- Rockafellar's `ρ`
noncomputable def saddleSubgradientHomeomorph …   -- **Cor 37.5.1**, `((u,y),(v,x)) ↦ (u - v, x + y)`
theorem isMaximalMonotoneRel_saddleMonotoneRel …  -- **Cor 37.5.2**
```

**Partial inversion needs no symmetry of the pairing.** Monotonicity on `(U × Y) × (V × X)` is
measured by `prodPairing Bu Bx.flip` and on `(U × X) × (V × Y)` by `prodPairing Bu Bx`; exchanging
the `X`/`Y` slots turns `Bx.flip (y₁ - y₂) (x₁ - x₂)` into `Bx (x₁ - x₂) (y₁ - y₂)`, the same number.
So both transfer lemmas are stated for arbitrary pairings and the inner product enters only where
Corollaries 31.5.1 and 31.5.2 do.

**Two maps, because `ρ` absorbs the sign and the graph of `∂K` does not.** `partialInvertEquiv`
carries no sign; `partialInvertNegHomeomorph` carries condition (c)'s. Corollary 37.5.2 uses the
first, 37.5.1 the second.

**`Homeomorph.sets` is the right tool** for `s ≃ₜ t` out of `s = ⇑h ⁻¹' t`; it is the abbreviation
over `Homeomorph.subtype`, and it takes the set equality in exactly the shape
`setOf_mem_saddleSubgradient_eq_preimage` produces.

**Maximality transfers because `e ⁻¹' (e.symm ⁻¹' τ) = τ`.** Given a monotone `τ` above
`e ⁻¹' σ`, the relation to feed into `σ`'s maximality is `e.symm ⁻¹' τ`, and that identity is what
brings the conclusion back.

**Corollary 37.5.2's differentiable clause needed a bridge between two `∂K`s, not a new theorem.**
`Saddle/Differential.lean` works with a real-valued `K` on an open rectangle and defines
`subgradientSaddle C D K = subgradientFst ×ˢ subgradientSnd`; §37 works with an `EReal`-valued `K`
and `saddleSubgradient Bu Bx K = concaveSubgradient ×ˢ subgradient`. At `C = D = univ` the two are
literally the same set — `concaveSubgradient_eq_subgradientFst` and `subgradient_eq_subgradientSnd`
are one `ext` plus `EReal.coe_le_coe_iff` each. Theorem 35.8 then hands over `{(∇₁K, ∇₂K)}`, and the
representing bifunction comes from `exists_bifunSaddleClass_lowerSimpleExt` at `C = D = univ`, where
`lowerSimpleExt univ univ K` *is* `K` and slice continuity is free from differentiability.

**Not here**: nothing of §37.

### `Tdaf/Analysis/Convex/Duality/Polar.lean`

§14 up to Theorem 14.5 — `polarCone`, `polarSet`, `polarPointedCone`, polarity as an antitone
Galois connection with its two closure operators, the bipolar theorems and the §14 examples — and
**the conjugate of a partial affine function**, which is §12 (the display preceding Theorem 12.3).

```lean
def polarCone (B) (K : Set E) : Set F := {y | ∀ x ∈ K, B x y ≤ 0}
def polarSet  (B) (C : Set E) : Set F := {y | ∀ x ∈ C, B x y ≤ 1}
noncomputable def polarSubmodule (B) (M : Submodule ℝ E) : Submodule ℝ F   -- from `Gauge.lean`
theorem smul_coe_submodule …                                              -- from `Fenchel.lean`
noncomputable def partialAffineFn (B) (L : Submodule ℝ E) (a : E) (b : F) (α : ℝ) : E → EReal :=
  fun x => indicatorFn (a +ᵥ (L : Set E)) x + ⟨x, b⟩ + α
theorem conj_partialAffineFn …
  -- conj B (partialAffineFn B L a b α) = partialAffineFn B.flip (polarSubmodule B L) b a
  --                                        (-α - ⟨a, b⟩)
```

**The partial-affine formula cannot live in `Duality/Conjugate.lean`.** Its dual datum is a
*polar*, so the statement cannot even be written before `polarCone` exists — which is Rockafellar's
own remark that the subspace example it generalises "will be broadened at the beginning of §14". It
is Theorem 12.3 (`conj_comp_affine`) at `h = δ(· | L)`, `A = I`, fed by
`conj_indicatorFn_eq_indicatorFn_polarCone`; the only new ingredient is `indicatorFn_vadd`.

**Stated as a self-duality, not as a formula.** Writing both sides through `partialAffineFn` makes
`conj_partialAffineFn` say that the *same* construction, read through the polar pairing and with
`a` and `a*` exchanged, is the conjugate — which is Rockafellar's point that partial affine
functions, like subspaces, come in dual pairs. Nothing here characterises the partial affine
functions intrinsically (proper convex, `dom f` affine, `f` affine on it); that needs Cor 7.4.2 and
is not done.

**Two declarations moved in.** `polarSubmodule` and `coe_polarSubmodule` came down from
`Duality/Gauge.lean`, where only Corollary 14.6.1 used them, and `smul_coe_submodule` came up from
`Optimization/Fenchel.lean`, where it had been written from scratch. Both belong beside
`polarCone_coe_submodule` and `smul_coe_pointedCone`, and §12's partial-affine formula needs them
here.
