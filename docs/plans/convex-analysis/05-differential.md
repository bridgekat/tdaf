# Sub-plan 5 — Differential theory

Covers Rockafellar §23–§26.

§23 is layer C (pairing + topology) for the definitions and the basic duality, layer D for the
`ri`-based existence results. §24–§26 are layer D.

Subgradients are the single most-used piece of convex analysis in applications and the largest
absolute gap in Mathlib, so §23 is high priority — higher than Part IV.

---

## 5.1 `Subgradient/Defs.lean` — §23.1–§23.7

```lean
/-- One-sided directional derivative, meaningful when `f x` is finite.

Theorem 23.1's hypothesis ("`x` a point where `f` is finite") must be kept: `EReal` has `⊤ - ⊤ = ⊥`,
so off `dom f` this expression is `⊥` in every direction and the advertised `f'(x;0) = 0` fails.
Needs `import Mathlib.Data.EReal.Inv` for the division. -/
noncomputable def dirDeriv (f : E → EReal) (x y : E) : EReal :=
  ⨅ a ∈ Set.Ioi (0:ℝ), (f (x + a • y) - f x) / (a : EReal)

/-- The subdifferential with respect to a pairing `B`. -/
def subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set F :=
  {y | ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z}

/-- The normal cone to `C` at `x`. -/
def normalCone (B) (C : Set E) (x : E) : Set F := {y | ∀ z ∈ C, B (z - x) y ≤ 0}
```

| Lean name | statement | book |
|---|---|---|
| `dirDeriv_apply`, `monotoneOn_sub_div`, `dirDeriv_zero`, `neg_dirDeriv_neg_le` — the last three with `f x ≠ ⊤`, `f x ≠ ⊥` | difference quotient is nondecreasing in `a`; `f'(x;0)=0`; `-f'(x;-y) ≤ f'(x;y)` | **Thm 23.1** |
| `posHomogeneous_dirDeriv` (no hypothesis), `convexFn_dirDeriv` | `f'(x;·)` is a positively homogeneous convex function | **Thm 23.1** |
| `mem_subgradient_iff_le_dirDeriv`, `supportSet_dirDeriv`, `conj_dirDeriv`, `clFn_dirDeriv` | `y ∈ ∂f x ↔ ∀ v, ⟨v,y⟩ ≤ f'(x;v)`; and `cl (f'(x;·)) = δ*(·|∂f x)` | **Thm 23.2** |
| `proper_of_mem_subgradient`, `proper_of_subgradient_nonempty` | subdifferentiable ⟹ proper | **Thm 23.3** |
| `subgradient_nonempty_of_mem_relint_dom` and the rest of §5.1a — **done**, in `Subgradient/Existence.lean`, which is where `RelativeInterior.lean` may be imported. `subgradient_eq_empty_of_notMem_dom` (the `ri`-free first sentence) stays here. | `∂f x ≠ ∅` on `ri (dom f)`; `f'(x;·) = δ*(·|∂f x)`; bounded iff `x ∈ int (dom f)` | **Thm 23.4** *(finite-dim)* |
| `Proper.mem_subgradient_tfae` and its four unbundled forms `mem_subgradient_iff_forall_sub_le` / `_conj_le` / `_conj_eq` / `_add_conj_le`, plus `Proper.mem_subgradient_iff_add_conj_eq` (the Fenchel-equality one) | the four equivalent conditions, incl. `f x + f* y = ⟨x,y⟩` | **Thm 23.5** |
| `subgradientRel_conj_eq_inv`, `mem_subgradient_conj_iff_of_closedFn` | `∂f*` is the inverse relation of `∂f` for closed proper `f` | **Cor 23.5.1** |
| `subgradient_indicatorFn` (carries `x ∈ C`, see §9 of the overview), `subgradient_indicatorFn_of_notMem`, `mem_subgradient_indicatorFn_iff` | `∂δ(·|C) x = N_C(x)` | §23 |
| `subgradient_supportFn`, `subgradient_conj_indicatorFn` | `∂δ*(·|C) y` = argmax of `⟨·,y⟩` over `C` | Cor 23.5.3 |
| `mem_subgradient_indicatorFn_pointedCone` (delivered **without** the closedness Rockafellar assumes) | `y ∈ ∂δ(·|K)(x) ↔ x ∈ K, y ∈ K°, ⟨x,y⟩ = 0` | Cor 23.5.4 |
| `epsSubgradient` and `dirDeriv_eq_limit_eps` — **not written**; deferred with Thm 13.5 | ε-subgradients | Thm 23.6 |
| `normalCone_level_eq_cone_subgradient` — **not written**; blocked, see §5.1a | | Thm 23.7, Cor 23.7.1 |

`Proper.mem_subgradient_iff_add_conj_eq` (Theorem 23.5) is the pivot: it identifies `∂f` with the
equality case of Fenchel's inequality, hence with a purely conjugacy-level notion, hence gives
`Cor 23.5.1` for free. Note the definition of `subgradient` above is **layer A** — no topology at
all — and Theorem 23.5 is layer C. Only Theorem 23.4 (nonemptiness) needs finite dimensions.

## 5.1a `Subgradient/Existence.lean` — §23.4 and §23.10

Theorems 23.4 and 23.10 are the same theorem twice. Theorem 23.2 (`clFn_dirDeriv`) already gives
`cl (f'(x; ·)) = δ*(· | ∂f x)` for every convex `f` finite at `x`, so everything reduces to one
question — **is `f'(x; ·)` closed?** — and the two theorems are two different answers to it. Both
then finish through the same two lemmas, which take the closedness as a hypothesis:

```lean
theorem dirDeriv_eq_supportFn_of_closedFn [IsCompatiblePairing B] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hcl : ClosedFn (dirDeriv f x)) :
    dirDeriv f x = supportFn B.flip (subgradient B f x)
theorem subgradient_nonempty_of_closedFn_dirDeriv [IsCompatiblePairing B] (hf : ConvexFn f)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hcl : ClosedFn (dirDeriv f x)) :
    (subgradient B f x).Nonempty
```

Nonemptiness costs nothing once the support-function formula is available: `δ*(· | ∅)` is the
constant `−∞`, and `f'(x; 0) = 0`.

| Lean name | statement | book |
|---|---|---|
| `dom_dirDeriv_of_mem_relint_dom` | `dom (f'(x; ·))` is the subspace parallel to `aff (dom f)` | Thm 23.4, step 1 |
| `proper_dirDeriv_of_mem_relint_dom` | `f'(x; ·)` is proper | Thm 23.4, step 2 |
| `closedFn_dirDeriv_of_mem_relint_dom` | `f'(x; ·)` is closed (Cor 7.4.2) | Thm 23.4, step 3 |
| `dirDeriv_eq_supportFn_of_mem_relint_dom`, `subgradient_nonempty_of_mem_relint_dom` | **Thm 23.4** | |
| `dom_dirDeriv_eq_univ_iff_mem_interior_dom`, `bddAbove_subgradient_iff_mem_interior_dom` | `∂f x` bounded ⟺ `x ∈ int (dom f)` | Thm 23.4, last clause |
| `coe_hull_epi_sub_subset_epi_dirDeriv`, `epi_dirDeriv_subset_coe_hull`, `epi_dirDeriv_eq_coe_hull` | `epi (f'(x; ·))` is the cone generated by `epi f − (x, f x)`, when that cone is closed | Thm 23.10, step 1 |
| `polyhedralFn_dirDeriv`, `proper_dirDeriv_of_polyhedralFn` | `f'(x; ·)` is polyhedral and proper | Thm 23.10, steps 2–3 |
| `dirDeriv_eq_supportFn_of_polyhedralFn`, `subgradient_nonempty_of_polyhedralFn`, `polyhedral_subgradient_of_polyhedralFn` | **Thm 23.10** | |

Four things worth recording.

(i) **`f'(x; ·)` is not automatically proper**, so Rockafellar's appeal to Theorem 7.2 is doing
real work. For `f y = -√y` on `[0, ∞)` (and `+∞` elsewhere) one has `f'(0; y) = −∞` for every
`y > 0` while `f'(0; 0) = 0`. What `x ∈ ri (dom f)` buys is that `dom (f'(x; ·))` is a *subspace* —
hence relatively open — so Theorem 7.2 puts the `−∞` values at the origin, where there are none.

(ii) **The cone identity of Theorem 23.10 is false without closedness.** For `f y = y²` at `x = 0`
the cone generated by `epi f` is the open upper half plane together with the origin, whereas
`epi (f'(0; ·))` is the closed upper half plane. `epi_dirDeriv_subset_coe_hull` therefore carries
`IsClosed` as a hypothesis; **Corollary 19.7.1** discharges it in the polyhedral case, which is
exactly the role Rockafellar gives it. The reverse inclusion is unconditional and needs no
topology.

(iii) **Polyhedrality of `∂f x` comes from Theorem 19.2, not from a fresh argument.**
`conj_dirDeriv` says `(f'(x; ·))* = δ(· | ∂f x)`; `PolyhedralFn.conj` says that conjugate is
polyhedral; `PolyhedralFn.polyhedral_dom` reads `∂f x` off as its effective domain.

(iv) **Theorem 23.7 stays open, and not for want of §23.** Its proof needs the `ri` half of
Theorem 7.6 (`cl {z | f z < f x} = cl {z | f z ≤ f x}` when `f x > inf f`), which §7 leaves
undone, and Corollary 23.7.1 needs Corollary 9.6.1, which is scheduled with §15. Theorem 23.6
(ε-subgradients) remains deferred with Theorem 13.5.

## 5.2 `Subgradient/Calculus.lean` — §23.8, §23.9

**Formalized.** (Theorem 23.10 moved to `Subgradient/Existence.lean`; see §5.1a.) The two main
rules went in as planned, with the exact-sum/exact-image rules gaining the `IsExactSum`/`IsExactImage`
namespaces:

```lean
theorem subgradient_add_subset (B) (f g) (x) :
    subgradient B f x + subgradient B g x ⊆ subgradient B (f + g) x                 -- always
theorem IsExactSum.subgradient_add (h : IsExactSum B f g) (x : E) :
    subgradient B (f + g) x = subgradient B f x + subgradient B g x                 -- **Thm 23.8**
theorem image_subgradient_subset (hA : IsAdjointPair B B' A A') (g) (x) :
    A' '' subgradient B' g (A x) ⊆ subgradient B (compLin g A) x                    -- always
theorem IsExactImage.subgradient_compLin {hA} (h : IsExactImage B B' A A' hA g) (x : E) :
    subgradient B (compLin g A) x = A' '' subgradient B' g (A x)                    -- **Thm 23.9**
```

Both main rules are stated against the [`IsExactSum`/`IsExactImage`](03-relint-recession.md#36-tdafanalysisconvexdualityexactlean--d5)
interface, so the `ri` version, the polyhedral version (Theorem 23.8's second half) and the
continuity version all come from one proof. Rockafellar's own `ri` versions are now available:
compose these with `IsExactSum.of_relint` / `IsExactImage.of_relint` from `Duality/Relint.lean`.
Corollary 23.8.1 (normal cone to an intersection) is the indicator instance.

Five things worth recording.

(i) **The whole file runs on Theorem 23.5 and nothing else.** `mem_subgradient_iff_add_conj_le`
(`y ∈ ∂f x ↔ f x + f* y ≤ ⟨x, y⟩`, unconditional) turns both calculus rules into arithmetic on a
single inequality. No epigraph, no directional derivative, no separating hyperplane appears — and
the file is layer A, needing no topology, which the plan did not anticipate.

(ii) **The two rules are not symmetric in what they cost.** For sums, exactness gives one *joint*
equality in Fenchel's inequality and it has to be split into two; that is
`Tdaf.EReal.le_coe_of_add_le_coe_add` (two slack inequalities whose sum is tight must each be
tight), and it is the only place `IsExactSum`'s properness is spent. The image rule has nothing to
split; it spends its properness on a single point instead, to see that `(g A)* y` is finite and so
unlock the `< ⊤`-guarded `IsExactImage.exact_le`.

(iii) Corollary 23.8.1 needed `indicatorFn_add` (`δ(·|C) + δ(·|D) = δ(·|C ∩ D)`, unconditional),
which went into `Indicator.lean` where it belongs — `⊤` absorbs, so there is no side condition. The
unconditional half `normalCone_add_subset` is proved *directly* rather than through indicators, so
that it needs neither `x ∈ C` nor `x ∈ D`.

(v) **`IsExactImage.exact_le` had to be re-stated while wiring 23.9 up.** As first written it
demanded a point of the fibre `A' ⁻¹ {y}` at *every* `y`, which forces `A'` surjective and makes
the interface unsatisfiable for e.g. `A = 0`. It now carries the guard `(g A)* y < ⊤` — exactly
what Theorem 9.2 delivers. `subgradient_compLin` discharges the guard from `g (A x) ≠ ⊥`, which is
where its one use of properness goes.

(iv) Theorem 23.10 is a *nonemptiness* statement, not a calculus rule; it belongs with Theorem 23.4,
and now lives with it in `Subgradient/Existence.lean` (§5.1a).

## 5.3 `Subgradient/Monotone.lean` — §24

**Status: Theorems 24.4 and 24.8 are done, and the half of Theorem 24.9 that follows from 24.8.**

| Lean name | book | status |
|---|---|---|
| `ClosedFn.leftDeriv_rightDeriv_monotone` (one variable) | **Thm 24.1** | **not done** |
| `convexFn_of_monotone` (recover `f` from a nondecreasing `φ`) | **Thm 24.2**, Cor 24.2.1 | **not done** |
| `graph_subgradient_eq_completeNondecreasingCurve` | **Thm 24.3** | **not done** |
| `isClosed_subgradientRel` | **Thm 24.4** | done |
| `dirDeriv_limsup_le` | **Thm 24.5**, Cor 24.5.1 | **not done** |
| `subgradient_tendsto` | Thm 24.6 | **not done** |
| `subgradient_image_isBounded_of_isCompact` | Thm 24.7 | **not done** |
| `IsCyclicallyMonotone`, `cyclicPotential`, `isCyclicallyMonotone_subgradientRel`, `exists_convexFn_subgradientRel_of_isCyclicallyMonotone`, `isCyclicallyMonotone_iff_exists_convexFn` | **Thm 24.8** | done |
| `exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone` | **Thm 24.9**, "maximal ⇒ subdifferential" | done |
| — | **Thm 24.9**, "subdifferential ⇒ maximal", and uniqueness up to a constant | **not done** |

### What actually happened

**Cycles are `List (E × F)`, not `Fin (m+1)`-indexed families.**

```lean
def chainVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : E × F → List (E × F) → E → ℝ
  | s, [], x => B (x - s.1) s.2
  | s, q :: l, x => B (q.1 - s.1) s.2 + chainVal B q l x

def IsCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ s ∈ ρ, ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → chainVal B s l s.1 ≤ 0
```

Every proof in the file is then a list induction, and the free endpoint sitting *last* is what makes
`chainVal B s l x = ⟨x, y⟩ - c` (`exists_chainVal_eq`) — the affineness that turns Rockafellar's
supremum into a supremum of `affineFn`s, hence closed and convex by Theorem 5.5 and
`closedFn_affineFn`. A `Fin`-indexed cycle would need `Finset.sum_equiv` along `i ↦ i + 1` for the
telescoping and would buy nothing.

**The construction of Theorem 24.8 is `cyclicPotential B ρ s`**, the supremum over all chains in `ρ`
starting at a fixed `s ∈ ρ`. Its three properties come out one line each: `cyclicPotential_eq_zero`
(this is exactly where cyclic monotonicity is used, and it is the only thing that keeps the function
from being `+∞` at `s.1`), `cyclicPotential_ne_bot` (the empty chain is a real lower bound), and
`mem_subgradient_cyclicPotential`, which is `chainVal_append_singleton` plus
`EReal.le_sub_iff_add_le`.

**Necessity is a telescoping estimate over `EReal`**, `le_of_chain_mem_subgradientRel`:
`f s.1 + chainVal B s l x ≤ f x`. Stating it with `+` rather than `f x - f s.1` avoids `EReal`
subtraction entirely; properness enters only at the end, to know `f` is finite at the cycle's base
point.

**Theorem 24.4 needs the pairing to be jointly continuous.** `IsContinuousPairing B` gives only
`⟨·, y⟩` continuous for fixed `y`, and the subgradient inequality at `xᵢ` has *both* arguments
moving. `isClosed_subgradientRel` therefore takes an explicit
`Continuous fun p : E × F => B p.1 p.2`; in `ℝⁿ` it is automatic. The proof writes
`∂f` as `⋂ z, {p | f p.1 + ⟨z - p.1, p.2⟩ ≤ f z}` and each of those, when `f z` is finite, as a
preimage of `epi f` — so lower semicontinuity is used through
`lowerSemicontinuous_iff_isClosed_epi` and nothing else.

### Why the rest of §24 is deferred

Theorems 24.1–24.3 are the one-dimensional theory: `f'₊`, `f'₋` as nondecreasing functions on `ℝ`
and complete nondecreasing curves. §23 provides `dirDeriv` but no one-sided *derivatives* on `ℝ`,
and the one-dimensional machinery would have to be built first. Theorems 24.5–24.7 rest on
Theorems 10.6–10.9 (the equi-Lipschitz theory), deferred in §10. The remaining half of Theorem 24.9
needs "`∂f ⊆ ∂g` implies `g = f + const`", which Rockafellar proves from Theorem 23.4 and
Theorem 23.2 by restricting to segments in `ri (dom f)` and comparing one-dimensional derivatives —
the same material as 24.1–24.3.

Note that Corollary 31.5.2 (`∂f` is maximal *monotone*) is a different and easier statement, proved
from Moreau's theorem in §31, and does not wait on any of this.

## 5.4 `Subgradient/Gradient.lean` — §25

**Status: Theorem 25.1 is done in full, with Corollary 25.1.1 and the necessity half of
Theorem 25.2.**

| Lean name | book | status |
|---|---|---|
| `le_of_hasFDerivAt`, `eq_of_mem_subgradient_of_hasFDerivAt`, `subgradient_eq_singleton_of_hasFDerivAt` | **Thm 25.1** | done |
| `mem_interior_dom_of_eventuallyEq_coe`, `proper_of_eventuallyEq_coe` | **Cor 25.1.1** | done |
| — | Cor 25.1.2, Cor 25.1.3 (exposed points of `epi f*`) | **not done** |
| `dirDeriv_eq_of_hasFDerivAt` | **Thm 25.2**, necessity | done |
| `subgradient_eq_singleton_of_dirDeriv_eq`, `clFn_dirDeriv_eq_of_subgradient_eq_singleton` | **Thm 25.2**, the algebraic content of sufficiency | done |
| — | **Thm 25.2**, sufficiency proper (linear `f'(x; ·)` ⇒ differentiable) | **not done** |
| `countable_nondifferentiable_of_dim_one` | Thm 25.3 | **not done** |
| `ae_twoSided_dirDeriv` | Thm 25.4 | **not done** |
| `ae_differentiableAt_and_continuousOn_gradient` | **Thm 25.5**, Cor 25.5.1 | **not done** |
| `subgradient_eq_convexHull_limits_gradient` | Thm 25.6 | **not done** |
| `tendsto_gradient_of_tendsto` | Thm 25.7 | **not done** |

### What actually happened

**Differentiability of an `EReal`-valued function is a local real representative.** `HasFDerivAt`
needs a normed target, so the hypothesis carried through the file is

```lean
(hfg : f =ᶠ[𝓝 x] fun z => ((g z : ℝ) : EReal)) (hd : HasFDerivAt g f' x)
```

with `f : E → EReal`, `g : E → ℝ`, `f' : E →L[ℝ] ℝ`. This is Rockafellar's hypothesis verbatim —
his `∇f x` presupposes `f x` finite, and differentiability at `x` forces finiteness *near* `x`.
Restricting the file to `f : E → ℝ` would have been simpler and would have lost §26, whose functions
are `+∞` off an open set. It also makes **Corollary 25.1.1** fall out in two lines each:
`mem_interior_dom_of_eventuallyEq_coe` is `mem_interior_iff_mem_nhds` applied to `hfg`, and
`proper_of_eventuallyEq_coe` runs `ConvexFn.eq_bot_of_lt_one` along the segment `[u, x)` and
contradicts local finiteness at the limit — which is the piece of Theorem 7.2 that §25 needs, in a
form valid in any topological vector space rather than only in `ℝⁿ`.

**The proof of Theorem 25.1 never mentions `dirDeriv`.** Rockafellar routes it through
Theorem 23.2; here `tendsto_slope_ray_of_hasFDerivAt` — the one piece of calculus in the file —
does both halves. Convexity bounds the quotient above by `f z - f x` (`ConvexFn.epi_combo` on the
segment, transported through `hfg` by `tendsto_ray_nhdsGT`), which gives `∇f x ∈ ∂f x`; and the
subgradient inequality bounds it below by `⟨v, y⟩` for any other subgradient `y`, which applied to
`v` and `-v` gives `y = ∇f x`. **The uniqueness half uses neither convexity nor properness.**

**Theorem 25.2 splits cleanly.** Necessity (`dirDeriv_eq_of_hasFDerivAt`) is two applications of
the defining infimum: the lower bound is the gradient inequality at `x + a • v` fed through
`EReal.coe_le_sub_div_iff`, and the upper bound is the limit `a ↓ 0`, extracted with
`EReal.lt_iff_exists_real_btwn` so that no `EReal` division is ever computed. The purely algebraic
`subgradient_eq_singleton_of_dirDeriv_eq` — over an *arbitrary* pairing whose flip is injective —
delivers what sufficiency is used for: a linear `f'(x; ·)` pins `∂f x` to a single point.

### Why the rest of §25 is deferred

**Sufficiency in Theorem 25.2 is not a transcription.** Linearity of `f'(x; ·)` gives Gâteaux
differentiability; the upgrade to Fréchet differentiability is genuinely finite-dimensional (uniform
convergence of the difference quotients over the compact unit sphere) and would need
`[FiniteDimensional ℝ E]` plus a compactness argument that has no counterpart elsewhere in the
backbone yet.

Theorem 25.3 is one-dimensional and rests on Theorem 24.1; Theorem 25.4 rests on Theorem 24.5;
Theorems 25.6 and 25.7 rest on 25.5 and on §24's convergence theory (Theorems 10.6–10.9).
Corollaries 25.1.2 and 25.1.3 are statements about exposed points and exposed faces of `epi f*` in
`ℝ × E`, so they wait on §18 in the product picture.

Theorem 25.5 (a.e. differentiability) — check `Mathlib/Analysis/Calculus/Rademacher.lean` first:
a finite convex function on an open set is locally Lipschitz (Theorem 10.4), so Rademacher applies
directly and gives a.e. differentiability for free. If so, only the *continuity of `∇f` on its
domain of existence* remains, which is Theorem 24.4 plus Theorem 25.1. **This would be a substantial
saving over Rockafellar's route through Theorem 25.4.**

## 5.5 `Subgradient/Legendre.lean` — §26

**Status: Theorem 26.4 is done. Everything else in §26 is blocked on Theorem 26.1, which is blocked
on Theorem 25.6.**

| Lean name | book | status |
|---|---|---|
| `legendreDom`, `HasGradientAt.add_conj_eq`, `conj_eq_of_hasGradientAt`, `sub_eq_sub_of_hasGradientAt`, `legendreDom_subset_dom_conj` | **Thm 26.4** | done |
| `subgradient_singleValued_iff_essentiallySmooth` | **Thm 26.1**, Lemma 26.2 | **not done** |
| `essentiallyStrictlyConvex_conj_iff_essentiallySmooth` | **Thm 26.3**, Cor 26.3.1–3 | **not done** |
| — | Cor 26.4.1 | **not done** |
| `legendreType_conj_iff` and `∇f* = (∇f)⁻¹` | **Thm 26.5** | **not done** |
| `gradient_bijective_iff_strictConvex_cofinite` | **Thm 26.6**, Lemma 26.7 | **not done** |

### What actually happened

**The sub-plan's premise was wrong: §26 is not self-contained.** Rockafellar's Theorem 26.1 needs
Theorem 25.6 (a subgradient at a boundary point is a limit of gradients), which needs Theorem 25.5
(Rademacher) and §24's convergence theory; and its other direction needs the sufficiency half of
Theorem 25.2 (Gâteaux ⇒ Fréchet, finite-dimensional). Theorems 26.3, 26.5, 26.6 and Corollaries
26.3.1–26.3.3 and 26.4.1 all route through 26.1.

**Theorem 26.4 does not.** It needs only Theorem 25.1 and Theorem 23.5 (d), so it is done in full:

```lean
theorem HasGradientAt.add_conj_eq (hf : ConvexFn f) (h : HasGradientAt f y x) :
    f x + conj (topDualPairing ℝ E).flip f y = ((y x : ℝ) : EReal)
```

and from it `conj_eq_of_hasGradientAt : f* (∇f x) = ⟨x, ∇f x⟩ - f x`, which *is* "`g` is the
restriction of `f*` to `D`", plus `sub_eq_sub_of_hasGradientAt` (well-definedness: the formula does
not depend on which `x ∈ (∇f)⁻¹ y` is used) and `legendreDom_subset_dom_conj`.

**`EssentiallySmooth`, `EssentiallyStrictlyConvex` and `LegendreType` are deliberately not
defined.** A definition with no provable theorem cannot be tested, and §18 already showed the cost
of an untested guess (`IsExtreme` was assumed to be Rockafellar's face; it is not). They belong in
the same commit as Theorem 26.1.

**There is no `legendreConj` definition either.** Rockafellar's `g y = ⟨(∇f)⁻¹ y, y⟩ - f ((∇f)⁻¹ y)`
is only well-defined *because* of Theorem 26.4; in Lean it would need a choice function and would
then have to be proved equal to `conj B f` on `D` anyway. `conj_eq_of_hasGradientAt` is that
equality stated directly.

§26 remains the bridge to the classical Legendre transformation of mechanics and thermodynamics,
and it stays low priority: it is used nowhere else in the book.
