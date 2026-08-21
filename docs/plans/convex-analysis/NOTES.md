# Working notes: current backbone API and Lean gotchas

Central record for anyone (human or agent) writing backbone modules for the convex-analysis
project. Keep it up to date: it exists so that the same obstacles are not rediscovered twice.

---

## 1. The API that already exists

### `Tdaf/Order/EReal.lean` (namespace `Tdaf.EReal`)

```lean
theorem le_coe_of_forall_lt {z : EReal} {r : ℝ} (h : ∀ q : ℝ, r < q → z < (q : EReal)) :
    z ≤ (r : EReal)
theorem exists_real_btwn_of_lt_coe {z : EReal} {r : ℝ} (h : z < (r : EReal)) :
    ∃ q : ℝ, z < (q : EReal) ∧ q < r
theorem coe_mul_coe (a r : ℝ) : (a : EReal) * (r : EReal) = ((a * r : ℝ) : EReal)
theorem eq_bot_of_forall_le_coe {z : EReal} (h : ∀ r : ℝ, z ≤ (r : EReal)) : z = ⊥
theorem exists_coe_of_ne_bot_of_lt_top {z : EReal} (h₁ : z ≠ ⊥) (h₂ : z < ⊤) :
    ∃ r : ℝ, z = (r : EReal)
```

Note the namespace clash: inside `namespace Tdaf`, plain `EReal.foo` resolves to `Tdaf.EReal.foo`
first. Write `_root_.EReal.foo` for Mathlib's lemmas when the name exists in both, and
`Tdaf.EReal.foo` for ours when the surrounding context makes plain `EReal.foo` ambiguous.

### `Tdaf/Analysis/Convex/Epigraph.lean` (namespace `Tdaf`)

No structure on `E` at all:

```lean
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
@[simp] theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal)
theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal)
theorem epi_mono {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f
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

### `Tdaf/Analysis/Convex/Indicator.lean` (namespace `Tdaf`)

```lean
noncomputable def indicatorFn (s : Set E) : E → EReal := restrict s (fun _ => 0)
@[simp] theorem indicatorFn_of_mem    (hx : x ∈ s) : indicatorFn s x = 0
@[simp] theorem indicatorFn_of_notMem (hx : x ∉ s) : indicatorFn s x = ⊤
theorem indicatorFn_ne_bot (s : Set E) (x : E) : indicatorFn s x ≠ ⊥
@[simp] theorem dom_indicatorFn (s : Set E) : dom (indicatorFn s) = s
theorem epi_indicatorFn (s : Set E) : epi (indicatorFn s) = s ×ˢ Set.Ici (0 : ℝ)
@[simp] theorem convexFn_indicatorFn {s : Set E} : ConvexFn (indicatorFn s) ↔ Convex ℝ s
theorem restrict_eq_add_indicatorFn {s : Set E} {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    restrict s f = f + indicatorFn s
```

### `Tdaf/Analysis/Convex/Concave.lean`

`hypo`, `ConcaveFn` (structure over `Convex ℝ (hypo g)`), `domConcave`, `ProperConcave`,
`restrictConcave s g = ⨆ _ : x ∈ s, g x` (extension by `⊥` — `Tdaf.restrict` extends by `⊤` and is
the wrong object for a concave function), `concaveFn_iff_convexFn_neg` (**no** side condition),
`concaveFn_iff_forall_gt`, `concaveFn_iff_le` (needs `∀ x, g x ≠ ⊤`), `ConcaveFn.convex_gt/_ge`,
`concaveOn_iff_concaveFn`.

### `Tdaf/Analysis/Convex/Homogeneous.lean`

`PosHomogeneous`, `posHomogeneous_iff_isCone_epi`, `convex_iff_add_mem_of_isCone` (Thm 2.6),
`PosHomogeneous.convexFn_iff_subadditive` (Thm 4.7), `.sum_le` (Cor 4.7.1, **needs `s.Nonempty`**),
`.neg_le` (Cor 4.7.2), `.isLinearOn_iff` / `.exists_linearMap_iff` / `.exists_linearMap_span`
(Thm 4.8), `.map_zero` (only the trichotomy `f 0 ∈ {0, ⊤, ⊥}`).

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

---

## 1a. House style

From the repository `README.md` ("Reviewing a formalization"):

* **Minimize duplication.** Before writing a lemma, check whether Mathlib or this project already
  has it.
* **Bundle *concepts*, not individual assumptions.** `Proper`, `ConvexFn`, `IsExactSum` are named
  mathematical concepts and are structures. A single side condition such as `∀ x, f x ≠ ⊥` is not a
  concept — repeat it inline rather than inventing a name for it. (An earlier `NeBotFn` wrapper was
  removed for exactly this reason.)
* Code should be idiomatic and pleasant to read, not merely correct.

---

## 2. Lean/Mathlib gotchas found so far

1. **`Convex ℝ s` unfolds to a `∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b⦄, …` chain.**
   `intro x hx y hy a b ha hb hab` leaves the goal `a • x + b • y ∈ s`.

2. **`simp only [mem_epi]` does not compute `Prod` projections of a linear combination.**
   `(a • (x,μ) + b • (y,ν)).2` is defeq to `a * μ + b * ν` but not syntactically equal, and
   `linarith` cannot see through it. Prefer `convexFn_of_epi_combo` / `ConvexFn.epi_combo`, which
   present the statement already in projected form, over unfolding `Convex` by hand.

3. **Degenerate coefficients.** Almost every convexity proof needs the `a = 0` and `b = 0` cases
   separately (the interesting argument needs `0 < a` and `0 < b`). Use `combo_of_pos`; it discharges
   both degenerate branches by `simpa`.

4. **`EReal` has no `SMul ℝ EReal` instance.** Write `(a : EReal) * z`. `Tdaf.EReal.coe_mul_coe`
   converts `(a : EReal) * (r : EReal) = ((a * r : ℝ) : EReal)`.

5. **`EReal` case analysis**: `induction z with | bot => … | coe r => … | top => …`
   (`EReal.rec` is the registered `induction_eliminator`, case names `bot`, `coe`, `top`).
   For "is it `⊤`?" use `rcases eq_top_or_lt_top z with h | h`.

6. **Useful Mathlib `EReal` lemmas** (all in `Mathlib/Data/EReal/{Basic,Operations}.lean`):
   `EReal.lt_iff_exists_real_btwn`, `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`,
   `EReal.coe_add`, `EReal.coe_mul`, `EReal.coe_lt_top`, `EReal.top_add_top`, `EReal.top_add_coe`,
   `EReal.coe_add_top`, `EReal.top_add_of_ne_bot`, `EReal.add_top_of_ne_bot`,
   `EReal.mul_top_of_pos`, `EReal.coe_mul_top_of_pos`, `EReal.sub_le_iff_le_add`,
   `EReal.le_sub_iff_add_le`, `EReal.sub_le_of_le_add`.

7. **`nlinarith` often fails on `a * p + b * q < r` given `p < r`, `q < r`, `a + b = 1`.**
   Feed it the products explicitly:
   ```lean
   have h1 : a * p < a * r := mul_lt_mul_of_pos_left hp ha
   have h2 : b * q < b * r := mul_lt_mul_of_pos_left hq hb
   have h3 : a * r + b * r = r := by linear_combination r * hab
   linarith
   ```
   `linear_combination c * hab` is the reliable way to use `a + b = 1` in a nonlinear identity.

8. **Style linters that fail the build if ignored**: the file header must be
   ```
   /-
   Copyright (c) 2026 TDAF contributors. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: TDAF contributors
   -/
   ```
   `show` may not change the goal — use `change`. `push_neg` is deprecated in favour of `push Not`.
   `if_pos`/`if_neg` are deprecated. `Set.mem_setOf_eq` is deprecated in favour of
   `Set.mem_ofPred_eq` — or just rely on definitional equality (`have hx' : f x < α := hx`).

9. **Unused section variables are a linter error-level warning.** If a lemma in a
   `variable {E} [AddCommGroup E] [Module ℝ E]` section does not use the algebraic structure, put
   ```lean
   omit [AddCommGroup E] [Module ℝ E] in
   ```
   immediately *before* the declaration — and before its docstring, not after.

10. **A `Prop`-valued `structure` with one field** is how bundled hypotheses are written here.
    Introduce it with `refine ⟨?_⟩` or `exact ⟨h⟩`, and consume it through the projection
    (`hf.convex_epi`, `hf.ne_bot x`). `structure Foo … extends Bar …` gives the coercion for free.

11. **`⨅ _ : p, f` for a `Prop` `p`** is the decidability-free way to write `if p then f else ⊤`
    in a complete lattice; `iInf_pos` and `iInf_neg` are the defining equations. Same trick with
    `⨆ _ : p, f` for `… else ⊥`.

### Added by the stage-1/2 modules

12. **Two `simp` loops, both real.** `simp [Tdaf.EReal.coe_mul_coe]` loops — it is the exact inverse
    of Mathlib's `EReal.coe_mul`, which is in the default simp set; use `rw`. And a simp set
    containing `← EReal.neg_lt_neg_iff` loops against `neg_neg`/`neg_bot`/`neg_top`. **This kills
    D2's "generate the concave API by `simp`-normalising through negation"** — each transfer is one
    or two hand-written lines.
13. **`Mathlib.Analysis.Convex.Function` imports no topology at all.** `IsClosed`, `closure`,
    `ContinuousAdd` are unknown identifiers in a file whose Mathlib reach is only `Epigraph.lean`.
    Minimal pair: `Mathlib.Topology.Instances.Real.Lemmas` + `Mathlib.Topology.Order.DenselyOrdered`.
14. **`relaxedAutoImplicit = false` turns one missing import into a landslide** — a missing
    `TopologicalSpace` produced ~12 cascading errors with `sorry`-typed hypotheses. Only the first
    error is real.
15. **`PosMulMono EReal` lives in `Mathlib/Data/EReal/Inv.lean`**, not `Operations.lean`; and there
    is **no** `PosMulStrictMono EReal`, so `le_of_mul_le_mul_left` cannot reflect an order. Multiply
    through by `(a⁻¹ : EReal)` — that is what `Tdaf.EReal.coe_mul_le_coe_iff` packages.
16. **`EReal.neg_add` concludes `-(x+y) = -x - y`, with a subtraction.** After `rw` you are left with
    `-a + -b = -a - b`, which the closing `rfl` does not discharge though it is defeq; finish with
    `sub_eq_add_neg`.
17. **`linear_combination` is not in scope** from `Mathlib.Data.EReal.*` alone. Prefer explicit
    rewriting (`rw [sub_mul, one_mul, h, sub_self]`) in `Order/EReal.lean` over adding tactic
    imports to a low-level file.
18. **`Finset` induction.** `Finset.cons_induction` (cases `empty`/`cons`) needs no `DecidableEq`.
    `Finset.Nonempty.cons_induction` has **one** major premise: write
    `induction hs using Finset.Nonempty.cons_induction`, not `induction s, hs using …`. Both
    auto-revert hypotheses mentioning `s`, so `ih` is the full implication.
19. **`WithBot` big-operator lemmas do not transfer to `EReal`** — `EReal` is a `def`, not an
    `abbrev`, over `WithBot (WithTop ℝ)`.
20. **Gotcha 2 refined.** `simp only` *does* push through `Prod` projections of a *single* scaled or
    added pair (`Prod.smul_fst`, `Prod.fst_add`, … are all `@[simp]`). The warning is specifically
    about *convex combinations* `a • p + b • q`. For sets, this works:
    `simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hF hμ hν ha.le hb.le hab`.
    Also: `rintro ⟨y, ρ⟩ hp` beats `intro p hp; obtain ⟨y, ρ⟩ := p`, which leaves `hp` phrased with
    `(y, ρ).2` and defeats `exact_mod_cast`.
21. **`ConvexCone` is half-reusable.** `ConvexCone.convex` accepts an anonymous-constructor cone
    `⟨s, _, _⟩` whose coercion is `rfl`-equal to `s`, giving "closed under `+` and positive `•` ⇒
    convex" directly. The converse is **not** in Mathlib. There is no `IsCone` predicate on bare
    sets, only the bundled structure.
22. **Pointwise cone lemmas**: `Set.smul_mem_smul_set_iff₀`, `Set.mem_smul_set_iff_inv_smul_mem₀`.
    To use `a • s = s` inside an `Iff`, `conv_lhs => rw [← hs a ha]` — a bare `rw` rewrites both
    sides and destroys the goal.
23. **`open Set` makes bare `restrict` ambiguous** with `Set.restrict`; write `Tdaf.restrict`.
24. Names: `Continuous.prodMk` (not `prod_mk`), `abs_add_le` (not `abs_add`), `iInf_lt_iff` for
    witness extraction, `iSup_pos`/`iSup_neg` as the `⨆` duals of `iInf_pos`/`iInf_neg`,
    `forall₂_congr`/`forall₃_congr` to push an `Iff` through a `∀`-chain, `EReal.coe_toReal`.
    `Set.mem_Ici`/`left_mem_Ici` do **not** exist as identifiers; close `μ ∈ Ici μ` with
    `exact le_refl μ` (`le_rfl` gets stuck on an unresolved `Preorder`).
25. **`EReal.rec` is usable as a definitional combinator**, not just an eliminator:
    `EReal.rec (⊥ : EReal) φ ⊤` defines a function by cases, with `rec_bot`/`rec_coe`/`rec_top`
    `@[simp]` and `rfl`. Write `_root_.EReal.rec` inside `namespace Tdaf`.
26. **Generic `add_le_add` works on `EReal`** (there is a `CovariantClass`); no bespoke lemma needed.

---

## 3. Review findings

The plan was reviewed adversarially at commit `1b0cc08`; see [`REVIEW-01.md`](REVIEW-01.md). Read it
before starting a module. The findings that bite hardest in day-to-day work:

* `open Pointwise` is needed by every file using `epi f + epi g`, `a • epi f` or set negation, and
  its absence shows up as an instance-synthesis failure rather than a clear error.
* `EReal` negation does **not** distribute over addition (`-(⊥ + ⊤) = ⊤` but `(-⊥) + (-⊤) = ⊥`).
  Mathlib's `EReal.neg_add` carries two hypotheses. Every concave/convex sign transfer needs them.
* `EReal.sub_le_iff_le_add`, `le_sub_iff_add_le`, `sub_le_of_le_add` already exist in Mathlib with
  *weaker* disjunctive hypotheses. Do not redefine them — inside `namespace Tdaf` ours would shadow
  Mathlib's.
* `add_iSup` / `iSup_add` / `iSup_sub` for `EReal` do **not** exist anywhere in Mathlib and must be
  written; they carry every conjugacy proof.
* `WeakBilin B` is a type synonym: `simp`/`rw` do not fire through it, and pair literals in
  `WeakBilin B × ℝ` need manual ascription.
* Mathlib already has `egauge` (`Analysis/Convex/EGauge.lean`) and a minimax theorem
  (`Topology/Sion.lean`). It does **not** have `cone : Set E → Set E` (use `PointedCone.span`),
  `IsCompact.convexHull`, or any adjoint for a linear map between arbitrary paired spaces.

## 4. Build and verification

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
