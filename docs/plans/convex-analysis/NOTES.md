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
