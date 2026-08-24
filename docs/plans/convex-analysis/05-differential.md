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
| `proper_of_mem_subgradient`, `proper_of_subgradient_nonempty` | subdifferentiable ⟹ proper | **Thm 23.3**, first half |
| `dirDeriv_eq_bot_of_subgradient_eq_empty`, `exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top`, `subgradient_eq_empty_iff_exists_dirDeriv_eq_bot` — **done**, in `Subgradient/Existence.lean` | not subdifferentiable at `x` ⟹ `f'(x; z-x) = −∞` for every `z ∈ ri (dom f)` | **Thm 23.3**, second half *(finite-dim)* |
| `subgradient_nonempty_of_mem_relint_dom` and the rest of §5.1a — **done**, in `Subgradient/Existence.lean`, which is where `RelativeInterior.lean` may be imported. `subgradient_eq_empty_of_notMem_dom` (the `ri`-free first sentence) stays here. | `∂f x ≠ ∅` on `ri (dom f)`; `f'(x;·) = δ*(·|∂f x)`; bounded iff `x ∈ int (dom f)` | **Thm 23.4** *(finite-dim)* |
| `Proper.mem_subgradient_tfae` and its four unbundled forms `mem_subgradient_iff_forall_sub_le` / `_conj_le` / `_conj_eq` / `_add_conj_le`, plus `Proper.mem_subgradient_iff_add_conj_eq` (the Fenchel-equality one) | the four equivalent conditions, incl. `f x + f* y = ⟨x,y⟩` | **Thm 23.5** |
| `subgradientRel_conj_eq_inv`, `mem_subgradient_conj_iff_of_closedFn` | `∂f*` is the inverse relation of `∂f` for closed proper `f` | **Cor 23.5.1** |
| `subgradient_indicatorFn` (carries `x ∈ C`, see §9 of the overview), `subgradient_indicatorFn_of_notMem`, `mem_subgradient_indicatorFn_iff` | `∂δ(·|C) x = N_C(x)` | §23 |
| `subgradient_supportFn`, `subgradient_conj_indicatorFn` | `∂δ*(·|C) y` = argmax of `⟨·,y⟩` over `C` | Cor 23.5.3 |
| `mem_subgradient_indicatorFn_pointedCone` (delivered **without** the closedness Rockafellar assumes) | `y ∈ ∂δ(·|K)(x) ↔ x ∈ K, y ∈ K°, ⟨x,y⟩ = 0` | Cor 23.5.4 |
| `epsSubgradient`, `shiftFn`, `epsSubgradient_eq_supportSet`, `epsSubgradient_eq_setOf_conj_le`, `supportFn_epsSubgradient`, `dirDeriv_eq_iInf_supportFn_epsSubgradient` | ε-subgradients | **Thm 23.6** — done, `Subgradient/Approx.lean` |
| `subgradient_subset_normalCone_setOf_le`, `polarCone_subgradient`, `normalCone_setOf_le_eq_closure_coe_hull_subgradient`, `normalCone_setOf_le_eq_coe_hull_subgradient` | | **Thm 23.7, Cor 23.7.1** — done, `Subgradient/Existence.lean` |

`Proper.mem_subgradient_iff_add_conj_eq` (Theorem 23.5) is the pivot: it identifies `∂f` with the
equality case of Fenchel's inequality, hence with a purely conjugacy-level notion, hence gives
`Cor 23.5.1` for free. Note the definition of `subgradient` above is **layer A** — no topology at
all — and Theorem 23.5 is layer C. Only Theorem 23.4 (nonemptiness) needs finite dimensions.

## 5.1a `Subgradient/Existence.lean` — §23.3, §23.4 and §23.10

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
| `dom_dirDeriv_subset_direction`, `sub_mem_dom_dirDeriv`, `sub_mem_relint_dom_dirDeriv` | `(dom f) - x ⊆ dom (f'(x; ·)) ⊆ aff (dom f) - x`, hence the same for relative interiors | Thm 23.3, step 1 |
| `dirDeriv_eq_bot_of_subgradient_eq_empty`, `exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top`, `subgradient_eq_empty_iff_exists_dirDeriv_eq_bot` | **Thm 23.3**, second half | |

Six things worth recording.

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

(iv) **Theorems 23.6 and 23.7 are done.** Theorem 23.7 runs on the `ri` half of Theorem 7.6
(`cl {z | f z < f x} = cl {z | f z ≤ f x}` when `f x > inf f`), which §7 now has, and Corollary
23.7.1 on Corollary 9.6.1 — which was already in place as `isClosed_coe_hull_of_isBounded`, so the
plan's claim that it "is scheduled with §15" was stale. Two hypothesis corrections: neither result
needs `f` closed, and properness is not assumed separately (it follows from `∂f x ≠ ∅` through
`proper_of_subgradient_nonempty`). `∂f x ≠ ∅` itself *is* in the book — "`f` is subdifferentiable
at `x`" — and cannot be dropped; `-√y` at `0` is the counterexample. Corollary 23.7.1 is the one
place the book's statement is not matched: it asks for `x ∈ int (dom f)`, and the version here asks
for `Bornology.IsBounded (∂f x)`, because `bddAbove_subgradient_iff_mem_interior_dom` supplies only
the pairing form of boundedness.

(v) **Theorem 23.3's second half needs no properness of `f`.** Rockafellar assumes only convexity
and finiteness at `x`, and that is enough: the argument lives entirely inside `f'(x; ·)`, which is
improper the moment `∂f x = ∅` (its closure is `δ*(· | ∅) ≡ −∞`, and Theorem 7.4 forbids a proper
convex function from having an improper closure), so Theorem 7.2 is applied to *it*, never to `f`.
No case split on `Proper f` appears.

(vi) **Rockafellar's proof of Theorem 23.3 overshoots, and Theorem 6.4 shortens it.** The proof's
last sentence concludes `f'(x; ·) = −∞` "throughout `(dom f) - x`", whereas the theorem's own
statement says `ri (dom f) - x` — and only that is true (`-√y` at `x = 0` again: `f'(0; 0) = 0`).
As for the argument, the book deduces `ri C ⊆ ri D` from `C ⊆ D ⊆ aff C` by noting that both
relative interiors are taken inside the same affine set. The prolongation criterion does it in one
move instead: prolong a segment of `D` ending at `z - x` *inside `dom f`*, which `z ∈ ri (dom f)`
allows, and land back in `D` because `(dom f) - x ⊆ D`. What survives of the book's chain is only
`D ⊆ aff (dom f) - x`, which is the easy inclusion of `dom_dirDeriv_of_mem_relint_dom` — factored
out here as `dom_dirDeriv_subset_direction`, since it never used `x ∈ ri (dom f)`.

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

## 5.3 `Subgradient/Monotone.lean`, `OneDim.lean`, `Primitive.lean`, `Convergence.lean`, `Bounded.lean` — §24

**Status: Theorems 24.1–24.9 are all done, together with Corollary 24.5.1. What is left of §24 is
Rockafellar's integral *formula* `f(x) = ∫ₐˣ φ` for the primitive, and Corollary 24.2.1 — both
irreducibly statements about an integral, and neither needed by anything downstream.**

§24 outgrew one module. `Monotone.lean` keeps the cyclic-monotonicity material (Theorems 24.4,
24.8, 24.9); `OneDim.lean` holds the one-dimensional theory (24.1, 24.3, 24.2's uniqueness);
`Primitive.lean` holds Theorem 24.2's existence clause and the complete non-decreasing curves it is
built from; `Convergence.lean` holds the limit theorems (24.5, 24.5.1, 24.6); `Bounded.lean` holds
24.7.

| Lean name | book | status |
|---|---|---|
| `rightDeriv`, `leftDeriv`, `leftDeriv_le_rightDeriv`, `rightDeriv_le_leftDeriv`, `monotone_rightDeriv`, `monotone_leftDeriv`, `mem_subgradientRel_iff`, the four one-sided limit formulas (`iInf_rightDeriv_Ioi` …) | **Thm 24.1** | done, `OneDim.lean` |
| `exists_eq_add_coe_of_le_le`, `subgradientRel_eq_of_deriv_eq` | **Thm 24.2**, uniqueness clause | done, `OneDim.lean` |
| `monotoneCurve`, `isMonotoneRel_monotoneCurve`, `exists_mem_monotoneCurve_sub`, `isMaximalMonotoneRel_monotoneCurve`, `subgradientRel_eq_monotoneCurve_rightDeriv`, `exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq`, `exists_closedProperConvexFn_forall_le_le` | **Thm 24.2**, existence clause | done, `Primitive.lean` — and it needs **no integral**: the primitive is pinned down by its *graph*, `Γ(φ)` is that graph, and Thm 24.3 (proved via cyclic monotonicity, so not circular) produces `f` from it |
| — | **Thm 24.2**'s integral formula, and Cor 24.2.1 | **not done** — the only §24 statements that genuinely need `∫ₐˣ φ` for a nondecreasing `EReal`-valued `φ`, improper at both ends |
| `isMaximalMonotoneRel_iff_exists_closedProperConvexFn`, `isMonotoneRel_iff_forall_le_or_le`, `isMaximalMonotoneRel_iff_isMaximalCyclicallyMonotone` | **Thm 24.3** | done, `OneDim.lean` |
| `isClosed_subgradientRel` | **Thm 24.4** | done |
| `eventually_dirDeriv_lt`, `eventually_subgradient_subset_add_closedBall`, `upperSemicontinuousAt_dirDeriv`, `eventually_nhds_subgradient_subset_add_closedBall` | **Thm 24.5**, Cor 24.5.1 | done, `Convergence.lean` |
| `eventually_dirDeriv_lt_of_tendsto_dir` | Thm 24.6, first assertion | done, `Convergence.lean` |
| `eventually_mem_interior_dom_of_tendsto_dir`, `subgradient_dirDeriv`, `subgradient_dirDeriv_eq_sep_normalCone`, `isExposed_subgradient_dirDeriv`, `eventually_subgradient_subset_exposed_add_closedBall` | **Thm 24.6**, second assertion | done, `Convergence.lean` — and **neither** recorded obstruction was real: the `xᵢ` are eventually *interior*, so the existing Cor 10.8.1 applies verbatim, and the exposed face is Thm 23.2 + Cor 23.5.2 + Cor 23.5.3 composed in six lines |
| `exists_lipschitz_forall_pairing_le_of_isCompact`, `isCompact_subgradient`, `isCompact_image_subgradientRel` | Thm 24.7 | done, `Bounded.lean` |
| `IsCyclicallyMonotone`, `cyclicPotential`, `isCyclicallyMonotone_subgradientRel`, `exists_convexFn_subgradientRel_of_isCyclicallyMonotone`, `isCyclicallyMonotone_iff_exists_convexFn` | **Thm 24.8** | done |
| `exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone` | **Thm 24.9**, "maximal ⇒ subdifferential" | done |
| `eq_add_coe_of_subgradientRel_subset`, `isMaximalCyclicallyMonotone_subgradientRel`, `isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn` | **Thm 24.9**, "subdifferential ⇒ maximal", and uniqueness up to a constant | done |

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

### What the rest of §24 turned out to need

**The dependency order in this plan was wrong at its root.** It had Theorem 24.9's remaining half
waiting on "`∂f ⊆ ∂g` implies `g = f + const`", and that in turn on the one-dimensional material of
24.1–24.3, following Rockafellar's own route through segments in `ri (dom f)`. In fact
`eq_add_coe_of_subgradientRel_subset` follows from **Theorem 23.5 alone**, plus the same argument
repeated on the conjugate side; and its engine,
`increment_eq_of_subgradientRel_subset`, needs neither convexity nor closedness of `g`, only
`Proper g`. Inverting the order is what made Theorem 24.2's uniqueness clause reachable *without*
any integration theory, and §24 then unravelled from the top.

**Theorem 24.7 does not need Corollary 24.5.1 or §13**, contrary to the note above: Theorem 10.4
alone does it, and a single Lipschitz constant serves all three of its conclusions.

**Theorem 24.6's first assertion needs neither the simplex/polytope construction (Theorems 20.5 and
10.2) nor closedness of `f`.** Rockafellar builds a polytope only to make `f` continuous relative
to it at the point being approached; replacing the vanishing step `|xᵢ − x|` by a fixed larger one
— legitimate because the difference quotient is monotone in its step — moves the continuity to
*interior* points, where Theorem 10.1 applies.

**Theorem 24.5 needs no "the sequence lies in `C`" hypothesis**; `xᵢ → x ∈ U` suffices, and the
proof repairs the finitely many stray indices.

Two things really are still missing. **Theorem 24.2's existence clause** needs the integral
`∫ₐˣ φ` of a nondecreasing `EReal`-valued function, improper at both ends of the interval where `φ`
is finite, plus closedness of the result — none of which the project has. **Theorem 24.6's second
assertion** needs Corollary 10.8.1 in a form that admits `EReal`-valued convex functions dominated
by a finite one (the existing form consumes finite convex functions on an open set, and
`f'(xᵢ; ·)` at a boundary point takes the value `+∞`), and **Corollary 23.5.3** to identify the
limit set `∂(f'(x; ·))(y)` with the face of `∂f x` exposed by `y`.

Note that Corollary 31.5.2 (`∂f` is maximal *monotone*) is a different and easier statement, proved
from Moreau's theorem in §31, and does not wait on any of this.

## 5.4 `Subgradient/Gradient.lean` — §25

**Status: Theorem 25.1 is done in full, with Corollary 25.1.1 and the necessity half of
Theorem 25.2.**

| Lean name | book | status |
|---|---|---|
| `le_of_hasFDerivAt`, `eq_of_mem_subgradient_of_hasFDerivAt`, `subgradient_eq_singleton_of_hasFDerivAt` | **Thm 25.1** | done |
| `mem_interior_dom_of_eventuallyEq_coe`, `proper_of_eventuallyEq_coe` | **Cor 25.1.1** | done |
| `mem_exposedPoints_prod_Ici_iff`, `Proper.eq_sub_of_mem_subgradient`, `mem_exposedPoints_epi_conj_iff`, `mem_exposedPoints_supportSet_iff` | **Cor 25.1.2, Cor 25.1.3**, subgradient form | done — with `ClosedFn`, which the book does not assume |
| — | Cor 25.1.2, Cor 25.1.3, differentiability form | **not done** — needs the converse half of Thm 25.1 |
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
Corollaries 25.1.2 and 25.1.3 **need no §18 at all**, contrary to what this plan said: the proof is
a direct supporting-hyperplane argument on `epi f*` — split the functional, show the vertical
coefficient is negative, normalise — plus Theorem 23.5. What is done is the *subgradient* form,
`∂f x = {x*}`; the *differentiability* form the book states needs the converse half of Theorem 25.1
(unique subgradient ⇒ differentiable), which the project does not have. They also need `f` (resp.
`g`) closed, which the book does not assume: Rockafellar's "we can assume `f` is closed" is only
half available in the subgradient form, since "a singleton subdifferential forces
relative-interiority" is missing. Corollary 25.1.3's "non-empty closed convex set `C`" is
unnecessary — `C` is a support set, automatically closed and convex.

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
