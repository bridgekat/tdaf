# Sub-plan 1 — Foundations: extended-real convex functions and functional operations

Covers Rockafellar §3 (the parts that feed §5), §4, §5.
Layer A of [D9](00-overview.md#d9-generality-boundaries): `[AddCommGroup E] [Module ℝ E]`. No topology.

Everything here is new relative to Mathlib. It is the base of the whole library and should be
finished and stable before anything else is attempted.

---

## 1.1 `Tdaf/Order/EReal.lean`

Support lemmas that `EReal` needs and Mathlib does not have. Written first, deliberately, because
otherwise these accumulate as ad hoc `have`s across a dozen files.

Needed (each verified to be missing, or awkward, in `Mathlib/Data/EReal/*`):

```lean
theorem EReal.sub_le_iff_le_add {a b c : EReal} (hb : b ≠ ⊥) (hb' : b ≠ ⊤) : a - b ≤ c ↔ a ≤ c + b
theorem EReal.iSup_sub_const (f : ι → EReal) (r : ℝ) : (⨆ i, f i - (r:EReal)) = (⨆ i, f i) - r
theorem EReal.add_iSup_of_ne_bot {a : EReal} (h : a ≠ ⊥) (f : ι → EReal) :
    a + (⨆ i, f i) = ⨆ i, a + f i
theorem EReal.coe_smul (a : ℝ) (r : ℝ) : ((a * r : ℝ) : EReal) = (a : EReal) * r
theorem EReal.mul_le_mul_left_of_nonneg {a : ℝ} (ha : 0 ≤ a) {x y : EReal} (h : x ≤ y) :
    (a : EReal) * x ≤ (a : EReal) * y
```

plus a `positivity`/`simp` set for the coercion `ℝ → EReal` interacting with `+`, `-`, `*`, `⨆`, `⨅`.

**Also here**: the "real scalar action" used everywhere by convexity,
`ERealSMul : ℝ≥0 → EReal → EReal` or simply the multiplication `(a : EReal) * x` with `a ≥ 0`.
Decision: **use `(a : EReal) * x` directly**, no new `SMul` instance. Reason: `0 * ⊤ = 0` in `EReal`
is exactly Rockafellar's convention, an `SMul ℝ EReal` instance would clash with nothing but buys
nothing either, and Mathlib's `Convex` API is applied to `E × ℝ` (real second coordinate), never to
`EReal` directly.

## 1.2 `Tdaf/Analysis/Convex/Epigraph.lean` — §4

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The epigraph of `f`, a subset of `E × ℝ` (Rockafellar §4). -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- A function `E → EReal` is convex iff its epigraph is convex. (Rockafellar's definition.) -/
def ConvexFn (f : E → EReal) : Prop := Convex ℝ (epi f)

/-- Effective domain: where `f < +∞`. -/
def dom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- `f` is proper if it is finite somewhere and never `-∞`. -/
structure Proper (f : E → EReal) : Prop where
  dom_nonempty : (dom f).Nonempty
  ne_bot : ∀ x, ⊥ < f x
```

Key results:

| Lean name | book |
|---|---|
| `mem_epi`, `epi_mono`, `epi_subset_epi_iff_le` | — |
| `ConvexFn.convex_dom : ConvexFn f → Convex ℝ (dom f)` | §4 (dom is a linear image of epi) |
| `convexFn_iff_forall_lt` — the `<`-form, no `∞ − ∞` | **Thm 4.2** |
| `convexFn_iff_le_of_ne_bot` — the `≤`-form for `f : E → (−∞,∞]` | **Thm 4.1** |
| `ConvexFn.inner_le_sum` — Jensen for finite convex combinations | **Thm 4.3** |
| `ConvexFn.convex_lt`, `ConvexFn.convex_le` — sublevel sets | **Thm 4.6** |
| `convex_setOf_forall_le` — solution set of a system `fᵢ ≤ αᵢ` | **Cor 4.6.1** |
| `convexOn_iff_convexFn` — bridge to Mathlib's `ConvexOn` | — |

`convexFn_iff_forall_lt` is the workhorse. Statement (Theorem 4.2, in the exact form that avoids
`∞ − ∞`):

```lean
theorem convexFn_iff_forall_lt (f : E → EReal) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal)
```

Proof sketch (both directions are a direct unfolding of `Convex` on `E × ℝ`; `<` versus `≤` is
handled by density of `ℝ` below any `EReal` value, i.e. `EReal.lt_iff_exists_real_btwn`).

`convexOn_iff_convexFn` is the Mathlib bridge and deserves care; the `if … then … else ⊤` encoding of
"restrict to `s`" recurs constantly, so give it a name:

```lean
/-- `f` restricted to `s`, extended by `+∞`. -/
def restrict (s : Set E) (f : E → EReal) : E → EReal := fun x => if x ∈ s then f x else ⊤

theorem convexOn_iff_convexFn (s : Set E) (f : E → ℝ) :
    ConvexOn ℝ s f ↔ ConvexFn (restrict s (fun x => (f x : EReal)))
```

## 1.3 `Tdaf/Analysis/Convex/Indicator.lean`

```lean
/-- The indicator `δ(· | s)`: `0` on `s`, `+∞` off it. -/
def indicatorFn (s : Set E) : E → EReal := fun x => if x ∈ s then 0 else ⊤

theorem convexFn_indicatorFn : ConvexFn (indicatorFn s) ↔ Convex ℝ s
theorem dom_indicatorFn : dom (indicatorFn s) = s
theorem restrict_eq_add_indicatorFn : restrict s f = f + indicatorFn s   -- when f ≠ ⊥ on s
```

This is what makes "sets are functions" usable: every set-level theorem in §13–§16 is an instance of
a function-level one applied to `indicatorFn`.

## 1.4 `Tdaf/Analysis/Convex/Concave.lean` — see [D2](00-overview.md#d2)

```lean
def hypo (g : E → EReal) : Set (E × ℝ) := {p | (p.2 : EReal) ≤ g p.1}
def ConcaveFn (g : E → EReal) : Prop := Convex ℝ (hypo g)
def domConcave (g : E → EReal) : Set E := {x | ⊥ < g x}
structure ProperConcave (g : E → EReal) : Prop where ...

theorem concaveFn_iff_convexFn_neg : ConcaveFn g ↔ ConvexFn (fun x => -(g x))
theorem hypo_neg : hypo g = Prod.map id Neg.neg ⁻¹' epi (fun x => -(g x))   -- up to a sign
```

The whole concave API is generated from these two lemmas by `simp`-normalising through negation;
only the *definitions* are duplicated, not the proofs.

## 1.5 `Tdaf/Analysis/Convex/Homogeneous.lean` — §4 end

```lean
def PosHomogeneous (f : E → EReal) : Prop := ∀ (a : ℝ), 0 < a → ∀ x, f (a • x) = (a : EReal) * f x

theorem posHomogeneous_iff_isCone_epi : PosHomogeneous f ↔ (∀ a > 0, a • epi f = epi f)
theorem PosHomogeneous.convexFn_iff_subadditive (hf : PosHomogeneous f) (h : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ x y, f (x + y) ≤ f x + f y                                  -- **Thm 4.7**
theorem PosHomogeneous.sum_le (…) : f (∑ i, aᵢ • xᵢ) ≤ ∑ i, (aᵢ:EReal) * f xᵢ  -- **Cor 4.7.1**
theorem PosHomogeneous.neg_le (…) : -(f x) ≤ f (-x)                            -- **Cor 4.7.2**
theorem PosHomogeneous.isLinearOn_iff (…) : … ↔ ∀ x ∈ L, f (-x) = -(f x)       -- **Thm 4.8**
```

Theorem 4.7 is the bridge between §4 and §13 (support functions) and §15 (gauges): it says a
positively homogeneous function is convex exactly when it is subadditive, i.e. its epigraph is a
convex cone. Its proof reduces to `Convex ℝ K ↔ closed under +` for a cone — Rockafellar's Theorem
2.6, for which Mathlib's `ConvexCone` already provides the content.

## 1.6 `Tdaf/Analysis/Convex/Operations/*` — §5

The operations, and the theorem in the book that introduces each:

| operation | definition | book |
|---|---|---|
| `compMonoOn φ f` | `φ ∘ f`, `φ` convex nondecreasing | Thm 5.1 |
| `f + g` | pointwise (`Pi` instance) | Thm 5.2 |
| `ofEpi F` | `fun x => ⨅ {μ : ℝ // (x,μ) ∈ F}, μ` for `F ⊆ E × ℝ` convex | **Thm 5.3** |
| `infConv f g` (`□`) | `fun x => ⨅ y, f (x - y) + g y` | Thm 5.4 |
| `smulLeft a f` | `(a : EReal) * f x`, `a ≥ 0` | §5 |
| `smulRight f a` (`fλ`) | `ofEpi (a • epi f)`, `a ≥ 0`; `= a * f (a⁻¹ • x)` for `a > 0` | §5 |
| `sSupFn` | pointwise supremum | Thm 5.5 |
| `convFn` | `ofEpi (convexHull ℝ (⋃ i, epi (fᵢ)))` | Thm 5.6 |
| `mapLin A f` (`Af`) | `fun y => ⨅ {x // A x = y}, f x` | Thm 5.7 |
| `compLin f A` (`fA`) | `f ∘ A` | Thm 5.7 |
| `partialAdd` | Thm 3.6 operation on `Set (Y × Z)` | Thm 3.6 |
| `invAdd` (`#`) | `⋃ λ ∈ [0,1], (1-λ)•C ∩ λ•D` | Thm 3.7, 3.8 |

`ofEpi` (Theorem 5.3) is the single generator: **every** other construction in §5 is `ofEpi` applied
to a convex set built from epigraphs. Stating it once and deriving the rest is the main structural
saving in this file.

```lean
/-- The function whose graph is the lower boundary of a set `F ⊆ E × ℝ` (Rockafellar Thm 5.3). -/
noncomputable def ofEpi (F : Set (E × ℝ)) : E → EReal := fun x => ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)

theorem convexFn_ofEpi (hF : Convex ℝ F) : ConvexFn (ofEpi F)          -- **Thm 5.3**
theorem infConv_eq_ofEpi : infConv f g = ofEpi (epi f + epi g)         -- Thm 5.4
theorem convFn_eq_ofEpi : convFn F = ofEpi (convexHull ℝ (⋃ i, epi (F i)))  -- Thm 5.6
theorem mapLin_eq_ofEpi : mapLin A f = ofEpi ((A.prodMap .id) '' epi f)     -- Thm 5.7
```

Note the properness side conditions: `f₁ + f₂` needs both proper to avoid `∞ − ∞` (Thm 5.2), and
infimal convolution of improper functions is *defined* through epigraph addition rather than the
infimum formula — Rockafellar makes exactly this point, so `infConv` should be **defined** as
`ofEpi (epi f + epi g)` with the infimum formula as a theorem under properness.

`Lattice.lean` then records: convex functions on `E` with the pointwise order form a complete
lattice with `⨆ = sSupFn` and `⨅ = convFn` (§5, after Theorem 5.6).

## 1.7 `Tdaf/Analysis/Convex/Homogenize.lean` — [D6](00-overview.md#d6)

```lean
/-- The positively homogeneous convex function generated by `f` on `ℝ × E`
(Rockafellar §5, "the convex function generated by `h`"). -/
noncomputable def hom (f : E → EReal) : ℝ × E → EReal :=
  fun p => if 0 ≤ p.1 then smulRight f p.1 p.2 else ⊤

theorem hom_apply_pos (ha : 0 < a) : hom f (a, x) = (a : EReal) * f (a⁻¹ • x)
theorem hom_apply_one : hom f (1, x) = f x
theorem convexFn_hom (hf : ConvexFn f) : ConvexFn (hom f)
theorem posHomogeneous_hom : PosHomogeneous (hom f)
theorem hom_isGreatest : IsGreatest {g | PosHomogeneous g ∧ g ≤ ...} (hom f)   -- §5
```

Downstream users of `hom` (each currently a separate ad hoc construction in the book):

- **gauge** of `C`: `gauge C = ofEpi (cone (epi (indicatorFn C + 1)))`, equivalently the level-`λ`
  infimum of `hom (indicatorFn C + 1)`. §5, §15.
- **recession function** `f0⁺ = (cl (hom f)) (0, ·)`. §8, Corollary 8.5.2 becomes Corollary 7.5.1
  applied to `hom f`.
- **support function of a level set** (Theorem 13.5) and **Theorem 14.4** (the two-step
  homogenisation of `epi f` in `ℝ × E × ℝ`).
- **`hom` of the graph function of a bifunction** — the "convex cone of a program" in §29/§39.

## 1.8 Left to the surface

- Concrete convex functions of one variable (exp, `xᵖ`, `−log`, `(a²−x²)^{-1/2}`) — §4 examples 1–6.
- Theorem 4.4 (`f'' ≥ 0`) and Theorem 4.5 (Hessian): Mathlib has the 1-D result
  (`Analysis/Convex/Deriv.lean`, `StrictConvexOn` via derivatives); the surface states the `ℝⁿ`
  version and proves it by restriction to lines.
- Quadratic convex functions, positive-semidefiniteness, the geometric mean, log-sum-exp,
  the Tchebycheff norm, the arithmetic–geometric mean inequality (§4, §5).
- Umbra and penumbra (§3, stated as exercises).
- Theorem 5.8's four exotic operations. The backbone provides `partialAdd` and the cone-in-`ℝ×E×ℝ`
  picture that generates all eight; the surface names the four extra ones and derives their
  convexity as instances.
