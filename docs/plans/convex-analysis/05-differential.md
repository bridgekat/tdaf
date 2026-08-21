# Sub-plan 5 — Differential theory

Covers Rockafellar §23–§26.

§23 is layer C (pairing + topology) for the definitions and the basic duality, layer D for the
`ri`-based existence results. §24–§26 are layer D.

Subgradients are the single most-used piece of convex analysis in applications and the largest
absolute gap in Mathlib, so §23 is high priority — higher than Part IV.

---

## 5.1 `Subgradient/Defs.lean` — §23.1–§23.7

```lean
/-- One-sided directional derivative. `EReal`-valued; exists for all convex `f` by Thm 23.1. -/
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
| `dirDeriv_eq_iInf`, `monotone_diffQuotient` | difference quotient is nondecreasing in `a`; `f'(x;0)=0`; `-f'(x;-y) ≤ f'(x;y)` | **Thm 23.1** |
| `posHomogeneous_dirDeriv`, `convexFn_dirDeriv` | `f'(x;·)` is a positively homogeneous convex function | **Thm 23.1** |
| `mem_subgradient_iff_le_dirDeriv` | `y ∈ ∂f x ↔ ∀ v, ⟨v,y⟩ ≤ f'(x;v)`; and `cl (f'(x;·)) = δ*(·|∂f x)` | **Thm 23.2** |
| `proper_of_subgradient_nonempty` | subdifferentiable ⟹ proper | **Thm 23.3** |
| `subgradient_nonempty_of_mem_relint_dom` | `∂f x ≠ ∅` on `ri (dom f)`; `f'(x;·) = δ*(·|∂f x)`; bounded iff `x ∈ int (dom f)` | **Thm 23.4** *(finite-dim)* |
| `mem_subgradient_iff_fenchel_eq` | the four equivalent conditions, incl. `f x + f* y = ⟨x,y⟩` | **Thm 23.5** |
| `subgradient_conj_eq_inv` | `∂f*` is the inverse relation of `∂f` for closed proper `f` | **Cor 23.5.1** |
| `subgradient_indicator_eq_normalCone` | `∂δ(·|C) x = N_C(x)` | §23 |
| `subgradient_supportFn` | `∂δ*(·|C) y` = argmax of `⟨·,y⟩` over `C` | Cor 23.5.3 |
| `subgradient_indicator_cone_iff` | `y ∈ ∂δ(·|K)(x) ↔ x ∈ K, y ∈ K°, ⟨x,y⟩ = 0` | Cor 23.5.4 |
| `epsSubgradient` and `dirDeriv_eq_limit_eps` | ε-subgradients | Thm 23.6 |
| `normalCone_level_eq_cone_subgradient` | Thm 23.7, Cor 23.7.1 |

`mem_subgradient_iff_fenchel_eq` (Theorem 23.5) is the pivot: it identifies `∂f` with the equality
case of Fenchel's inequality, hence with a purely conjugacy-level notion, hence gives
`Cor 23.5.1` for free. Note the definition of `subgradient` above is **layer A** — no topology at
all — and Theorem 23.5 is layer C. Only Theorem 23.4 (nonemptiness) needs finite dimensions.

## 5.2 `Subgradient/Calculus.lean` — §23.8–§23.10

```lean
theorem subgradient_add_subset : ∂f₁ x + ∂f₂ x ⊆ ∂(f₁+f₂) x                       -- always
theorem subgradient_add (h : IsExactSum B f₁ f₂) : ∂(f₁+f₂) x = ∂f₁ x + ∂f₂ x     -- **Thm 23.8**
theorem subgradient_compLin (h : IsExactImage B A g) : ∂(g ∘ A) x = Aᵀ '' ∂g (A x) -- **Thm 23.9**
theorem PolyhedralFn.subgradient_nonempty …                                        -- **Thm 23.10**
```

Both main rules are stated against the [`IsExactSum`/`IsExactImage`](03-relint-recession.md#36-tdafanalysisconvexdualityexactlean--d5)
interface, so the `ri` version, the polyhedral version (Theorem 23.8's second half) and the
continuity version all come from one proof. Corollary 23.8.1 (normal cone to an intersection) is the
indicator instance.

## 5.3 `Subgradient/Monotone.lean` — §24

| Lean name | book |
|---|---|
| `ClosedFn.leftDeriv_rightDeriv_monotone` (one variable) | **Thm 24.1** |
| `convexFn_of_monotone` (recover `f` from a nondecreasing `φ`) | **Thm 24.2**, Cor 24.2.1 |
| `graph_subgradient_eq_completeNondecreasingCurve` | **Thm 24.3** |
| `isClosed_graph_subgradient` | **Thm 24.4** |
| `dirDeriv_limsup_le` (convergence of directional derivatives) | **Thm 24.5**, Cor 24.5.1 |
| `subgradient_tendsto` | Thm 24.6 |
| `subgradient_image_isBounded_of_isCompact` | Thm 24.7 |
| `CyclicallyMonotone` and `exists_convexFn_of_cyclicallyMonotone` | **Thm 24.8** |
| `subgradient_iff_maximalCyclicallyMonotone` | **Thm 24.9** |

Theorems 24.8/24.9 are hard (see [overview §6](00-overview.md#6-known-hard-points)). The
construction is: given cyclically monotone `ρ` and a base point `(x₀,y₀) ∈ graph ρ`, set

```
f x = sup over finite cycles (x₀,y₀),(x₁,y₁),…,(x_m,y_m) of
      ⟨x - x_m, y_m⟩ + ⟨x_m - x_{m-1}, y_{m-1}⟩ + ⋯ + ⟨x₁ - x₀, y₀⟩
```

which is a supremum of affine functions, hence closed convex, and cyclic monotonicity is exactly
what makes `f x₀ = 0` rather than `+∞`. Reference: Rockafellar, *Characterization of the
subdifferentials of convex functions*, Pacific J. Math. **17** (1966) 497–510.

`Analysis/Convex/Monotone`-style material and `maximal monotone` do not exist in Mathlib; note that
Corollary 31.5.2 (`∂f` is maximal monotone) is a *different* and easier statement proved from
Moreau's theorem in §31, and should not wait on §24.

## 5.4 `Subgradient/Gradient.lean` — §25

| Lean name | book |
|---|---|
| `subgradient_eq_singleton_of_hasFDerivAt` | **Thm 25.1**, Cor 25.1.1–3 |
| `differentiableAt_iff_dirDeriv_linear` | **Thm 25.2** |
| `countable_nondifferentiable_of_dim_one` | Thm 25.3 |
| `ae_twoSided_dirDeriv` | Thm 25.4 |
| `ae_differentiableAt_and_continuousOn_gradient` | **Thm 25.5**, Cor 25.5.1 |
| `subgradient_eq_convexHull_limits_gradient` | Thm 25.6 |
| `tendsto_gradient_of_tendsto` | Thm 25.7 |

Theorem 25.5 (a.e. differentiability) — check `Mathlib/Analysis/Calculus/Rademacher.lean` first:
a finite convex function on an open set is locally Lipschitz (Theorem 10.4), so Rademacher applies
directly and gives a.e. differentiability for free. If so, only the *continuity of `∇f` on its
domain of existence* remains, which is Theorem 24.4 plus Theorem 25.1. **This would be a substantial
saving over Rockafellar's route through Theorem 25.4.**

## 5.5 `Subgradient/Legendre.lean` — §26

```lean
structure EssentiallySmooth (f : E → EReal) : Prop where …    -- int (dom f) ≠ ∅, differentiable there,
                                                              -- ‖∇f xᵢ‖ → ∞ along boundary sequences
structure EssentiallyStrictlyConvex (f : E → EReal) : Prop where …
structure LegendreType (f : E → EReal) : Prop extends EssentiallySmooth, EssentiallyStrictlyConvex
```

| Lean name | book |
|---|---|
| `subgradient_singleValued_iff_essentiallySmooth` | **Thm 26.1**, Lemma 26.2 |
| `essentiallyStrictlyConvex_conj_iff_essentiallySmooth` | **Thm 26.3**, Cor 26.3.1–3 |
| `legendreConj_eq_conj_restrict` | **Thm 26.4**, Cor 26.4.1 |
| `legendreType_conj_iff` and `∇f* = (∇f)⁻¹` | **Thm 26.5** |
| `gradient_bijective_iff_strictConvex_cofinite` | **Thm 26.6**, Lemma 26.7 |

§26 is self-contained and is used nowhere else in the book; low priority, high expository value
(it is the bridge to the classical Legendre transformation used in mechanics and thermodynamics).
