# Sub-plan 6 — Constrained extremum problems

Covers Rockafellar §27–§32.

This is where the library pays off for applications. The organising decision is
[D8](00-overview.md#d8): a convex program *is* a perturbation bifunction, and everything (objective,
Lagrangian, dual program, Kuhn–Tucker vectors) is obtained from it by **partial conjugation**.

---

## 6.1 `Optimization/Minimum.lean` — §27

Theorem 27.1 is a summary: nine facts about `inf f` and `argmin f`, each a restatement of an earlier
result in terms of `f*` at the origin. It is the ideal first theorem of this sub-plan because it
forces all the earlier APIs to line up.

```lean
theorem sInf_eq_neg_conj_zero (hf : ClosedFn f) (hf' : ConvexFn f) : (⨅ x, f x) = -(conj B f 0)
theorem argmin_eq_subgradient_conj_zero :
    {x | IsMinOn f Set.univ x} = subgradient B.flip (conj B f) 0
```

covering Theorem 27.1(a)–(i); (f) and (g) restate §8/§13/§14, (e) restates §25.

| Lean name | book |
|---|---|
| the `Theorem 27.1` package above | **Thm 27.1** |
| `exists_isMinOn_of_no_recession` (+ the ε–δ well-posedness clause) | **Thm 27.2**, Cor 27.2.1 |
| `exists_isMinOn_on_of_no_common_recession` (and the polyhedral weakening) | **Thm 27.3**, Cor 27.3.1–3 |
| `isMinOn_iff_exists_subgradient_normal` | **Thm 27.4** |

Theorem 27.4 (`0 ∈ ∂f x + N_C(x)`) is *the* optimality condition and the single most cited result of
the whole book in applications. State it in the `IsExactSum` style so that both the `ri` version and
the polyhedral version follow from one proof.

## 6.2 `Optimization/Perturbation.lean` — §29 (generalized convex programs)

```lean
/-- A bifunction from `U` to `X` is a curried function; convexity is convexity of the graph. -/
abbrev Bifun (U X : Type*) := U → X → EReal
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)
def domBifun (F : Bifun U X) : Set U := {u | F u ≠ fun _ => ⊤}

/-- The perturbation function `inf F`. -/
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x

/-- Kuhn–Tucker vectors: the `v` for which the perturbation is priced exactly. -/
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
       ∀ u, infBifun F 0 ≤ infBifun F u + ((B u v : ℝ) : EReal)}
```

**Check this against §29 before writing the file.** Review flagged that this may be Theorem 29.1's
*conclusion* rather than Rockafellar's definition, which would make
`kuhnTucker_iff_neg_mem_subgradient` an `Iff.rfl` — the definitional cheat that
[`08-surface.md`](08-surface.md) §8.4 item 4 forbids. Rockafellar's own definition (§29) is that
`inf_u {⟨u*,u⟩ + inf F u}` is finite and equal to the optimal value `inf F 0`; if so, `KuhnTucker`
should be stated that way and the displayed inequality becomes the first half of Theorem 29.1.

| Lean name | book |
|---|---|
| `convexFn_infBifun`, `dom_infBifun` | **Thm 29.1** |
| `kuhnTucker_iff_neg_mem_subgradient` : `v ∈ KT ↔ -v ∈ ∂(inf F)(0)` | **Thm 29.1** |
| `dirDeriv_infBifun_eq` | Cor 29.1.1 |
| `kuhnTucker_eq_empty_iff` | Cor 29.1.2 |
| `kuhnTucker_subsingleton_iff_differentiable` | Cor 29.1.3 |
| `kuhnTucker_isCompact_of_stronglyConsistent` | Cor 29.1.4 |
| `infBifun_eq_bot_on_relint` | Cor 29.1.6 |
| polyhedral case | **Thm 29.2** |
| `kuhnTucker_and_optimal_iff_isSaddlePoint` | **Thm 29.3**, Cor 29.3.1 |
| `infBifun_relint_eq` | Thm 29.4, Cor 29.4.1 |

`Consistent`, `StronglyConsistent`, `StrictlyConsistent` are `0 ∈ dom F`, `0 ∈ ri (dom F)`,
`0 ∈ int (dom F)` respectively. They are the constraint qualifications of Part VI and connect
directly to [`Exact.lean`](03-relint-recession.md#36-tdafanalysisconvexdualityexactlean--d5).

## 6.3 `Optimization/Lagrangian.lean` — §28–§29 via partial conjugation

```lean
/-- Partial conjugate in the first variable, with the sign convention producing Lagrangians. -/
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x

theorem lagrangian_eq_neg_partialConj :
    lagrangian B F v x = -(conj B (fun u => -(F u x)) (-v))
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ (⨅ x, lagrangian B F v x) = infBifun F 0
```

`lagrangian` is a partial concave conjugate; every Lagrangian fact is a partial-conjugate fact. This
is what lets §28, §29, §36 and §37 share proofs instead of repeating them four times.

**§28 splits.** The `(m+3)`-tuple packaging and the book's numbering go to the surface, but
**Theorem 28.2 (existence of Kuhn–Tucker vectors under Slater's condition) stays in the backbone** —
review finding C3. Slater for finitely many convex inequalities is not about coordinates
(`Fin m → ℝ` with the product order generalises verbatim), it is the single most-used result in
convex optimisation practice, and sending it to the surface would force applications to import a
`Rockafellar`-namespaced, `EuclideanSpace`-specific file to get strong duality — a layering
inversion. So `Optimization/Lagrangian.lean` carries "Slater ⇒ `KuhnTucker` nonempty and compact"
(Corollary 29.1.4 plus §21's theorem of the alternative).

The backbone provides the bifunction attached to a system of convex inequalities and affine
equations,

```lean
noncomputable def ineqBifun (f₀ : E → EReal) (f : Fin m → E → EReal) (r : ℕ) :
    Bifun (Fin m → ℝ) E := fun u x =>
  f₀ x + ∑ i : Fin m,
    (if (i : ℕ) < r then indicatorFn {x | f i x ≤ (u i : EReal)} x
                    else indicatorFn {x | f i x = (u i : EReal)} x)
```

and proves that its `KuhnTucker` set is exactly the set of Kuhn–Tucker coefficient vectors and that
its Lagrangian is `f₀ + Σ λᵢ fᵢ` on `C`. Then §28's Theorems 28.1, 28.3, 28.4 and the Kuhn–Tucker
theorem (Corollary 28.3.1) are surface-level specialisations of backbone results.

## 6.4 `Optimization/Adjoint.lean` — §30

```lean
/-- The adjoint bifunction: the conjugate of the graph function, with a sign flip on the first
factor. -/
noncomputable def adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ u, ⨅ x, F u x - ((Bx x y : ℝ) : EReal) + ((Bu u v : ℝ) : EReal)
```

| Lean name | book |
|---|---|
| `concaveBifun_adjointBifun`, `adjointBifun_adjointBifun_eq_cl` | **Thm 30.1** |
| `adjointBifun_zero_eq_concaveConj_neg_infBifun` — the dual objective is the **concave** conjugate of `−inf F` | **Thm 30.2** |
| `dual_inconsistent_iff` | Cor 30.2.1 |
| `weak_duality` : `sup F* 0 ≤ inf F 0` | **Cor 30.2.2** |
| `Normal` (def) and `normal_iff` | **Thm 30.3** |
| `normal_of_stronglyConsistent`, `normal_of_polyhedral` | **Thm 30.4** |
| `kuhnTucker_eq_optimalSolutions_dual` | **Thm 30.5**, Cor 30.5.1–2 |

Theorem 30.1 (`F** = cl F`) is Fenchel–Moreau applied to the graph function with the sign-flipped
pairing on `U × X` — i.e. `negFst (prodPairing Bu Bx)` from `Duality/Pairing.lean`; it should be a
two-line consequence, not a new proof. That is the whole point of [D8](00-overview.md#d8).

**Sign warning.** Theorem 30.2 is about the **concave** conjugate: the book (line 12487) says `F*0`
is the conjugate of the *concave* function `−inf F`, and `g* ≠ −(−g)*`. `inf F` is convex; its
convex conjugate is not `F*0`. Every §30 statement mixing the two must go through `concaveConj`,
which `Duality/ConcaveConj.lean` defines (D2). Its `neg_concaveConj` is the dictionary to reach for;
note that the reflection is on the *argument* as well as on the value.

## 6.5 `Optimization/Fenchel.lean` — §31

```lean
theorem fenchel_duality (hf : ConvexFn f) (hg : ConcaveFn g)
    (h : IsExactSum B f (fun x => -(g x))) :
    (⨅ x, f x - g x) = ⨆ y, concaveConj B g y - conj B f y
```

`concaveConj` (`g*(y) = ⨅ x, ⟨x,y⟩ - g x`) is **formalized**, in
`Duality/ConcaveConj.lean` rather than in `Concave.lean`: it needs a pairing, and `Concave.lean` is
a layer-A file that should not acquire separation and Hahn-Banach as dependencies. `prox` for
Theorem 31.5 still has to be built, and needs an inner-product space and a real
existence-and-uniqueness proof.

Rockafellar's hypotheses — (a) `ri (dom f) ∩ ri (dom g) ≠ ∅`, and (b) `f, g` closed with
`ri (dom g*) ∩ ri (dom f*) ≠ ∅` — are the primal-side and dual-side instances of `IsExactSum`, with
attainment of the sup under (a) and of the inf under (b). Stating the theorem against `IsExactSum`
gives all four variants, including both polyhedral ones, from one proof.

| Lean name | book |
|---|---|
| `fenchel_duality` | **Thm 31.1** |
| `fenchel_duality_comp` (with a linear map interposed) | **Thm 31.2**, Cor 31.2.1 |
| `fenchel_kuhnTucker_conditions` | **Thm 31.3**, Cor 31.3.1 |
| `fenchel_duality_cone` | **Thm 31.4**, Cor 31.4.1–3 |
| `moreau_decomposition` : `f □ w + f* □ w = w`; `x = prox f x + prox (f*) x` | **Thm 31.5 (Moreau)** |
| `subgradient_maximalMonotone` | **Cor 31.5.2** |

Moreau's theorem (31.5) needs an inner-product structure and is the source of the proximal operator.
It is high-value for applications (proximal algorithms, splitting methods) and should be prioritised
above the rest of §31. Corollary 31.5.2 gives maximal monotonicity of `∂f` without going through the
much harder §24.

## 6.6 `Optimization/Maximum.lean` — §32

Maximising a convex function. Short, self-contained, depends on §18–§19 and nothing later.

| Lean name | book |
|---|---|
| `isConstant_of_isMaxOn_relint` | **Thm 32.1**, Cor 32.1.1 |
| `sSup_convexHull_eq_sSup` | **Thm 32.2**, Cor 32.2.1 |
| `exists_isMaxOn_extremePoint` | **Thm 32.3**, Cor 32.3.1–4 |
| `subgradient_normal_of_isMaxOn` | **Thm 32.4**, Cor 32.4.1 |

Corollary 32.3.2 ("a convex function attains its maximum over a compact convex set at an extreme
point") is the practical statement; Mathlib's Krein–Milman supplies half of it.
