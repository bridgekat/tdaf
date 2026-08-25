/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Exact
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Duality.Polar
import Tdaf.Analysis.Convex.Duality.Relint
import Tdaf.Analysis.Convex.Duality.RelintSeparation
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Surface.Rockafellar.Part3.Section13

/-!
# Rockafellar, §16: Dual Operations

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §16, pp. 140–152: the dual-operations
dictionary. Every operation of §5 has a dual operation, and conjugacy exchanges the two.

## The uniform shape of the section

Each of the four theorems is really three statements, and this module keeps them apart:

* the **identity**, valid for arbitrary functions with no hypothesis and no closure
  (`theorem_16_1_left`, `theorem_16_3_image`, `theorem_16_4_infConv`, `theorem_16_5_convFn`);
* the **closure form**, `(op of closures)* = cl (dual op of conjugates)`, which is the honest
  general statement (`theorem_16_3_closure`, `theorem_16_4_closure`, `theorem_16_5_closure`);
* the **exact form**, in which a relative-interior qualification removes the closure and makes the
  infimum attained (`theorem_16_3_exact`, `theorem_16_3_attained`, `theorem_16_4_exact`,
  `theorem_16_4_attained`).

The backbone is organised the same way — `Duality/Ops.lean` for the first two rows,
`Duality/Exact.lean` and `Duality/Relint.lean` for the third — and the split is what makes both
reusable.

## Contents

| label | declaration |
|---|---|
| Theorem 16.1 | `theorem_16_1_left`, `theorem_16_1_right`, `theorem_16_1_left_zero`,
  `theorem_16_1_right_zero` |
| Corollary 16.1.1 | `corollary_16_1_1` |
| Corollary 16.1.2 | `corollary_16_1_2` |
| Lemma 16.2 | `lemma_16_2` |
| Corollary 16.2.1 | `corollary_16_2_1` |
| Corollary 16.2.2 | *omitted*, see below |
| Theorem 16.3 | `theorem_16_3_image`, `theorem_16_3_closure`, `theorem_16_3_exact`,
  `theorem_16_3_attained` |
| Corollary 16.3.1 | `corollary_16_3_1_image`, `corollary_16_3_1_closure`,
  `corollary_16_3_1_exact` |
| Corollary 16.3.2 | `corollary_16_3_2_image`, `corollary_16_3_2_preimage` |
| Theorem 16.4 | `theorem_16_4_infConv_finset`, `theorem_16_4_infConv`, `theorem_16_4_closure`,
  `theorem_16_4_exact`, `theorem_16_4_attained` |
| Corollary 16.4.1 | `corollary_16_4_1_add`, `corollary_16_4_1_add_finset`,
  `corollary_16_4_1_closure`, `corollary_16_4_1_exact` |
| Corollary 16.4.2 | `corollary_16_4_2_add` |
| Theorem 16.5 | `theorem_16_5_convFn`, `theorem_16_5_closure` |
| Corollary 16.5.1 | `corollary_16_5_1_hull`, `corollary_16_5_1_closure` |
| Corollary 16.5.2 | `corollary_16_5_2_hull`, `corollary_16_5_2_inter` |

## Notation

`A*` is `LinearMap.adjoint A` throughout: `Tdaf.Surface.Common.Euclidean`'s
`isAdjointPair_adjoint` says that Mathlib's adjoint is Rockafellar's, so no surface statement here
carries an `IsAdjointPair` hypothesis even though every backbone statement it specialises does.

`λf` is `fun x => (l : EReal) * f x` and `fλ` is `smulRight f l`, both from §5.

## What is not here

* **Corollary 16.2.2** — *omitted with a reason*. Lemma 16.2 and Corollary 16.2.1 are here, built
  on the backbone module `Tdaf.Analysis.Convex.Duality.RelintSeparation`; the many-function form is
  not. Rockafellar proves it by applying the lemma inside `ℝᵐⁿ`, to the diagonal subspace and to
  `f(x₁, …, xₘ) = f₁(x₁) + ⋯ + fₘ(xₘ)`. Three pieces of that transport are missing and none of them
  is about §16: a compatible pairing on a finite product `ι → E`, the relative interior of a
  product set as the product of the relative interiors, and the support function of a product set
  as a sum of support functions. They belong in the backbone, beside the binary
  `intrinsicInterior_prod_eq` and `instIsCompatiblePairingProd` that already exist.
* **The opening paragraph's translation rules** (book, lines 5661–5667) — *deferred by scope*:
  `(h(· - a))* = h* + ⟨a, ·⟩`, `(h + ⟨·, a*⟩)* = h*(· - a*)`, `(h + α)* = h* - α`, and
  `δ*(· | C + a) = δ*(· | C) + ⟨a, ·⟩`. Rockafellar himself says these are "already covered by
  Theorem 12.3"; the backbone has them as `conj_comp_sub`, `conj_add_pairing` and `conj_add_const`,
  and §12's module owns them.
* **The last clause of Theorem 16.5** — *omitted with a reason*. When `I` is finite and the sets
  `cl (dom fᵢ)` are all *the same* set `C` — strictly stronger than 16.4's relative-interior
  condition, and easily confused with it — the closure comes off the second formula and the
  infimum over convex combinations is attained. Its engine is **Corollary 9.8.3**, which the
  backbone explicitly declines to prove (`Recession/ConeHull.lean`: it needs the convex hull of a
  *finite family* of functions, which the project has only for a single function). Without it the
  attainment cannot be stated, let alone proved, so this is a backbone gap.
* **The second clause of Corollary 16.4.2 and of Corollary 16.5.2** (the polar of an intersection
  of closures) — *omitted with a reason*. Both are bipolar statements: they need
  `polarCone_polarCone` / `polarSet_polarSet` with their three unbundled hypotheses re-discharged
  for a sum and for a convex hull. That is §14's remediation item (bundled `PointedCone`
  bipolarity, remediation §4.3), and it is gated there rather than worked around here. The
  unconditional inclusions are `corollary_16_3_2_preimage` and `corollary_16_5_2_inter`.
* **The `m`-ary exact form of Theorem 16.4 and Corollary 16.4.1** — *omitted with a reason*.
  `IsExactSum` is a binary interface; the book states the attainment for `f₁ + ⋯ + fₘ`. The
  `m`-ary interface is remediation §4.4 and is not surface work. The `m`-ary *identity* is here
  (`theorem_16_4_infConv_finset`, `corollary_16_4_1_add_finset`), because `conj` is a monoid
  homomorphism out of `InfConvFn` and no properness is involved.
* **The worked examples of pp. 145–152** (book, lines 6042–6183) — *omitted with a reason*. Four
  computations, each an application of a theorem already stated here plus material from elsewhere:
  the distance function `d(·, C) = |·| □ δ(· | C)` (Theorem 16.4 plus §13's `supportFn_unitBall`);
  the "approximation theory" example on the non-negative orthant (Theorem 16.4 plus §12's
  `nonnegOrthant`, and Rockafellar defers the sharp form to Theorem 20.1 anyway); the negative
  entropy function on the unit simplex; and its conjugate, the log-sum-exp function. The last two
  are one-variable calculus with `Real.log` and `Real.exp` over a `Finset` sum, not convex
  analysis, and nothing later in the book cites them.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {m n : ℕ}

/-! ### The conjugate of the zero function

Rockafellar's proof of Theorem 16.1 at `λ = 0` is the single sentence "the constant function `0`
is conjugate to the indicator function `δ(· | 0)`". Both halves of that sentence are used below. -/

/-- **Rockafellar, §16, p. 141**: the conjugate of the constant function `0` is `δ(· | 0)`.

Specialises `conj_zero_eq_indicatorFn`; `Rn n` is a `SeparatingDual`, asserted in the shared
header. -/
theorem conj_zero_rn : conj (pairing n) (0 : Rn n → EReal) = indicatorFn ({0} : Set (Rn n)) := by
  have h := conj_zero_eq_indicatorFn (B := pairing n) (E := Rn n) (F := Rn n)
  rwa [conj_flip_pairing] at h

/-- The conjugate of `δ(· | 0)` is the constant function `0`, the other half of the same sentence.
Specialises `conj_indicatorFn_zero`. -/
theorem conj_indicatorFn_zero_rn :
    conj (pairing n) (indicatorFn ({0} : Set (Rn n))) = 0 :=
  conj_indicatorFn_zero (pairing n)

/-- The half-space `{x | ⟨x, x*⟩ ≤ 1}` cutting out a polar set is convex, which is why polarity
does not see a convex hull. -/
theorem convex_setOf_pairing_le_one (y : Rn n) : Convex ℝ {x : Rn n | pairing n x y ≤ 1} := by
  have hlin : IsLinearMap ℝ fun x : Rn n => pairing n x y :=
    ⟨fun a b => by simp, fun c a => by simp⟩
  exact convex_halfSpace_le hlin 1

/-! ### Theorem 16.1: scalar multiplication -/

/-- **Rockafellar, Theorem 16.1.** For any proper convex function `f` one has `(λf)* = f*λ`,
`0 ≤ λ < ∞`. This is the case `λ > 0`, where no hypothesis on `f` is needed at all.

Specialises `conj_smul`. -/
theorem theorem_16_1_left (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    conj (pairing n) (fun x => (l : EReal) * f x) = smulRight (conj (pairing n) f) l :=
  conj_smul hl (pairing n) f

/-- **Rockafellar, Theorem 16.1**, the other formula: `(fλ)* = λf*`, `0 < λ < ∞`.

Specialises `conj_smulRight`. -/
theorem theorem_16_1_right (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    conj (pairing n) (smulRight f l) = fun y => (l : EReal) * conj (pairing n) f y :=
  conj_smulRight hl (pairing n) f

/-- **Rockafellar, Theorem 16.1** at `λ = 0`: `(0f)* = f*0`. Left multiplication by `0` sends any
`f` to the constant function `0`, right multiplication by `0` sends `f*` to `δ(· | 0)`, and the two
are conjugate. This is the clause the book's proof singles out. -/
theorem theorem_16_1_left_zero {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    conj (pairing n) (fun x => (0 : EReal) * f x) = smulRight (conj (pairing n) f) 0 := by
  have hdom : (dom (conj (pairing n) f)).Nonempty :=
    (proper_conj_of_proper hf hp).dom_nonempty
  simp only [zero_mul]
  rw [smulRight_zero hdom]
  exact conj_zero_rn

/-- **Rockafellar, Theorem 16.1** at `λ = 0`, the other formula: `(f0)* = 0f*`. -/
theorem theorem_16_1_right_zero {f : Rn n → EReal} (hp : Proper f) :
    conj (pairing n) (smulRight f 0) = fun y => (0 : EReal) * conj (pairing n) f y := by
  rw [smulRight_zero hp.dom_nonempty, conj_indicatorFn_zero_rn]
  funext y
  simp

/-- **Rockafellar, Corollary 16.1.1.** For any non-empty convex set `C`,
`δ*(x* | λC) = λ δ*(x* | C)` for `0 ≤ λ < ∞`.

Convexity is not used: the identity is the indicator instance of Theorem 16.1 and holds for any
non-empty `C`. Specialises `supportFn_smul`, with the `λ = 0` case read off `0 • C = {0}`. -/
theorem corollary_16_1_1 {C : Set (Rn n)} (hC : C.Nonempty) {l : ℝ} (hl : 0 ≤ l) (y : Rn n) :
    supportFn (pairing n) (l • C) y = (l : EReal) * supportFn (pairing n) C y := by
  rcases hl.lt_or_eq with hlt | heq
  · exact supportFn_smul (pairing n) hlt C y
  · rw [← heq, zero_smul_set hC, ← Set.singleton_zero, supportFn_singleton]
    simp

/-- **Rockafellar, Corollary 16.1.2.** For any non-empty convex set `C`, `(λC)° = λ⁻¹C°` for
`0 < λ < ∞`.

The book derives it from Corollary 16.1.1 through `C° = {x* | δ*(x* | C) ≤ 1}`; here it is one
unfolding of `polarSet`, since `⟨λx, x*⟩ = ⟨x, λx*⟩`. -/
theorem corollary_16_1_2 (C : Set (Rn n)) {l : ℝ} (hl : 0 < l) :
    polarSet (pairing n) (l • C) = l⁻¹ • polarSet (pairing n) C := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv, mem_polarSet,
    mem_polarSet]
  have key : ∀ x : Rn n, pairing n (l • x) y = pairing n x (l • y) := fun x => by
    simp only [pairing_apply, real_inner_smul_left, real_inner_smul_right]
  constructor
  · intro h x hx
    have hx' := h (l • x) (Set.smul_mem_smul_set hx)
    rwa [key] at hx'
  · rintro h _ ⟨x, hx, rfl⟩
    change pairing n (l • x) y ≤ 1
    rw [key]
    exact h x hx

/-! ### Lemma 16.2: the constraint qualifications of §9, dualized

Rockafellar's proof is three theorems in a row: Theorem 11.3 separates `L` and `dom f` properly
exactly when their relative interiors are disjoint, Theorem 11.1 turns proper separation into a
pair of inequalities between the extrema of `⟨·, x*⟩`, and Theorem 13.3 identifies those extrema
over `dom f` as `f* 0⁺`. The backbone carries that assembly in
`Tdaf.Analysis.Convex.Duality.RelintSeparation`, for a subspace of any finite-dimensional space
paired with any other. -/

/-- **Rockafellar, Lemma 16.2.** Let `L` be a subspace of `ℝⁿ` and let `f` be a proper convex
function. Then `L` meets `ri (dom f)` if and only if there exists no vector `x* ∈ Lᗮ` such that
`(f* 0⁺)(x*) ≤ 0` and `(f* 0⁺)(-x*) > 0`.

Specialises `submodule_inter_relint_dom_nonempty_iff`. `Lᗮ` *is* the annihilator of `L` for the
pairing: `Submodule.mem_orthogonal` is `∀ u ∈ L, ⟨u, x*⟩ = 0` definitionally, and so is
`pairing_apply`. Properness of `f*` is discharged by `proper_conj_of_proper`, which is Theorem 12.2
read in finite dimensions. -/
theorem lemma_16_2 (L : Submodule ℝ (Rn n)) {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    ((L : Set (Rn n)) ∩ ri (dom f)).Nonempty ↔
      ¬ ∃ x' ∈ Lᗮ, recessionFn (conj (pairing n) f) x' ≤ 0 ∧
        0 < recessionFn (conj (pairing n) f) (-x') :=
  submodule_inter_relint_dom_nonempty_iff (B := pairing n) L hf hp (proper_conj_of_proper hf hp)

/-- **Rockafellar, Corollary 16.2.1.** Let `A` be a linear transformation from `ℝⁿ` to `ℝᵐ` and let
`g` be a proper convex function on `ℝᵐ`. In order that there exist no vector `y* ∈ ℝᵐ` with
`A*y* = 0`, `(g* 0⁺)(y*) ≤ 0` and `(g* 0⁺)(-y*) > 0`, it is necessary and sufficient that
`Ax ∈ ri (dom g)` for at least one `x ∈ ℝⁿ`.

Lemma 16.2 for the subspace `L = range A`, whose orthogonal complement is `ker A*`. The backbone
form asks in addition that the pairing separate on the right, which on `ℝⁿ` is
`separatingRight_pairing`. -/
theorem corollary_16_2_1 (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) :
    (¬ ∃ y' : Rn m, LinearMap.adjoint A y' = 0 ∧
        recessionFn (conj (pairing m) g) y' ≤ 0 ∧
        0 < recessionFn (conj (pairing m) g) (-y')) ↔ ∃ x, A x ∈ ri (dom g) :=
  (exists_apply_mem_relint_dom_iff (separatingRight_pairing n) (isAdjointPair_adjoint A) hg hp
    (proper_conj_of_proper hg hp)).symm

/-! ### Theorem 16.3: linear transformations -/

/-- **Rockafellar, Theorem 16.3**, first formula: for a linear transformation `A` from `ℝⁿ` to
`ℝᵐ` and any convex function `f` on `ℝⁿ`, `(Af)* = f*A*`.

Unconditional: no convexity, no properness, no closure. Specialises `conj_mapLin`, whose only
input is the adjointness datum, supplied by `isAdjointPair_adjoint`. -/
theorem theorem_16_3_image (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) :
    conj (pairing m) (mapLin A f) = compLin (conj (pairing n) f) (LinearMap.adjoint A) :=
  conj_mapLin (isAdjointPair_adjoint A) f

/-- **Rockafellar, Theorem 16.3**, second formula: `((cl g)A)* = cl(A*g*)` for any convex `g`
on `ℝᵐ`.

Specialises `conj_compLin_eq_clFn_mapLin`, applied to `cl g` (which is closed convex) and read
back through `(cl g)* = g*`. -/
theorem theorem_16_3_closure (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g) :
    conj (pairing n) (compLin (clFn g) A)
      = clFn (mapLin (LinearMap.adjoint A) (conj (pairing m) g)) := by
  rw [conj_compLin_eq_clFn_mapLin (isAdjointPair_adjoint A) (convexFn_clFn hg)
    (closedFn_clFn g), conj_clFn]

/-- **Rockafellar, Theorem 16.3**, the exact half: if there is an `x` with `Ax ∈ ri (dom g)`, the
closure operation can be omitted and `(gA)* = A*g*`.

Rockafellar's hypotheses are `g` proper convex, not closed; the reduction to the closed case is
Theorem 9.5 (`clFn_compLin`) together with Corollary 7.4.1 (`ConvexFn.relint_dom_clFn`).
Specialises `IsExactImage.of_relint` and `IsExactImage.conj_compLin`. -/
theorem theorem_16_3_exact (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom g)) :
    conj (pairing n) (compLin g A) = mapLin (LinearMap.adjoint A) (conj (pairing m) g) := by
  have hcl : ClosedProperConvexFn (clFn g) :=
    ⟨convexFn_clFn hg, closedFn_clFn g, hg.proper_clFn hp⟩
  have hri : A x₀ ∈ ri (dom (clFn g)) := by rw [hg.relint_dom_clFn hp]; exact hx₀
  have hstep := (IsExactImage.of_relint (isAdjointPair_adjoint A) hcl hri).conj_compLin
  rw [← conj_clFn (B := pairing n) (compLin g A), clFn_compLin hg hp A hx₀, hstep, conj_clFn]

/-- **Rockafellar, Theorem 16.3**, the attainment: under the same qualification, for each `x*` the
infimum `inf {g*(y*) | A*y* = x*}` is attained (or is `+∞` vacuously).

Specialises `IsExactImage.exists_conj_compLin_eq`; the backbone's guard `< ⊤` is exactly the
book's "or is `+∞` vacuously". -/
theorem theorem_16_3_attained (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom g)) {y : Rn n}
    (hy : conj (pairing n) (compLin g A) y < ⊤) :
    ∃ z : Rn m, LinearMap.adjoint A z = y ∧
      conj (pairing m) g z = conj (pairing n) (compLin g A) y := by
  have hcl : ClosedProperConvexFn (clFn g) :=
    ⟨convexFn_clFn hg, closedFn_clFn g, hg.proper_clFn hp⟩
  have hri : A x₀ ∈ ri (dom (clFn g)) := by rw [hg.relint_dom_clFn hp]; exact hx₀
  have hcomp : conj (pairing n) (compLin (clFn g) A) = conj (pairing n) (compLin g A) := by
    rw [← clFn_compLin hg hp A hx₀, conj_clFn]
  obtain ⟨z, hz, heq⟩ :=
    (IsExactImage.of_relint (isAdjointPair_adjoint A) hcl hri).exists_conj_compLin_eq
      (y := y) (by rwa [hcomp])
  exact ⟨z, hz, by rwa [conj_clFn, hcomp] at heq⟩

/-- **Rockafellar, Corollary 16.3.1**, first formula: `δ*(y* | AC) = δ*(A*y* | C)` for any convex
set `C` in `ℝⁿ`.

The indicator instance of `theorem_16_3_image`, via `mapLin_indicatorFn`. Convexity is not used. -/
theorem corollary_16_3_1_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) (y : Rn m) :
    supportFn (pairing m) (A '' C) y = supportFn (pairing n) C (LinearMap.adjoint A y) := by
  have h : supportFn (pairing m) (A '' C)
      = compLin (supportFn (pairing n) C) (LinearMap.adjoint A) := by
    rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← mapLin_indicatorFn,
      theorem_16_3_image]
  rw [h, compLin_apply]

/-- **Rockafellar, Corollary 16.3.1**, second formula: for any convex set `D` in `ℝᵐ`,
`δ*(· | A⁻¹(cl D)) = cl(A* δ*(· | D))`.

The indicator instance of `theorem_16_3_closure`, via `clFn_indicatorFn` and
`compLin_indicatorFn`. -/
theorem corollary_16_3_1_closure (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D) :
    supportFn (pairing n) (A ⁻¹' closure D)
      = clFn (mapLin (LinearMap.adjoint A) (supportFn (pairing m) D)) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← compLin_indicatorFn,
    ← clFn_indicatorFn]
  exact theorem_16_3_closure A (convexFn_indicatorFn.2 hD)

/-- **Rockafellar, Corollary 16.3.1**, the exact half: if some `Ax ∈ ri D`, the closure operation
can be omitted and `δ*(x* | A⁻¹D) = inf {δ*(y* | D) | A*y* = x*}`, the infimum being attained. -/
theorem corollary_16_3_1_exact (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D)
    (hne : D.Nonempty) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri D) :
    supportFn (pairing n) (A ⁻¹' D)
      = mapLin (LinearMap.adjoint A) (supportFn (pairing m) D) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← compLin_indicatorFn]
  refine theorem_16_3_exact A (convexFn_indicatorFn.2 hD)
    ⟨by rw [dom_indicatorFn]; exact hne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_
  rw [dom_indicatorFn]
  exact hx₀

/-- **Rockafellar, Corollary 16.3.2**, first formula: `(AC)° = A*⁻¹(C°)` for any convex set `C`
in `ℝⁿ`.

One unfolding of `polarSet` through the adjointness `⟨Ax, y*⟩ = ⟨x, A*y*⟩`. -/
theorem corollary_16_3_2_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) :
    polarSet (pairing m) (A '' C) = LinearMap.adjoint A ⁻¹' polarSet (pairing n) C := by
  ext y
  simp only [mem_polarSet, Set.mem_preimage, Set.forall_mem_image]
  exact forall₂_congr fun x _ => by rw [isAdjointPair_adjoint A x y]

/-- **Rockafellar, Corollary 16.3.2**, the unconditional half of the second formula:
`A*(D°) ⊆ (A⁻¹D)°`. Equality holds after a closure, and without one under Corollary 16.3.1's
qualification; see the module docstring for why the closed form is not here. -/
theorem corollary_16_3_2_preimage (A : Rn n →ₗ[ℝ] Rn m) (D : Set (Rn m)) :
    LinearMap.adjoint A '' polarSet (pairing m) D ⊆ polarSet (pairing n) (A ⁻¹' D) := by
  rintro _ ⟨y, hy, rfl⟩ x hx
  rw [← isAdjointPair_adjoint A x y]
  exact hy (A x) hx

/-! ### Theorem 16.4: addition and infimal convolution -/

/-- **Rockafellar, Theorem 16.4**, first formula, in the book's own `m`-ary form:
`(f₁ □ ⋯ □ fₘ)* = f₁* + ⋯ + fₘ*`.

The `□`-product is the `AddCommMonoid` sum of `InfConvFn`. Specialises `conj_sum_toInfConvFn`;
properness is *not* needed and must not be assumed at the intermediate stages, since `□` does not
preserve it. -/
theorem theorem_16_4_infConv_finset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) :
    conj (pairing n) (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)))
      = ∑ i ∈ s, conj (pairing n) (f i) :=
  conj_sum_toInfConvFn (pairing n) s f

/-- **Rockafellar, Theorem 16.4**, first formula for `m = 2`: `(f □ g)* = f* + g*`.

Specialises `conj_infConv`. -/
theorem theorem_16_4_infConv (f g : Rn n → EReal) :
    conj (pairing n) (infConv f g) = conj (pairing n) f + conj (pairing n) g :=
  conj_infConv (pairing n) f g

/-- **Rockafellar, Theorem 16.4**, second formula: `(cl f + cl g)* = cl(f* □ g*)`.

Specialises `conj_add_eq_clFn_infConv`, applied to the closures. -/
theorem theorem_16_4_closure {f g : Rn n → EReal} (hf : ConvexFn f) (hg : ConvexFn g) :
    conj (pairing n) (clFn f + clFn g)
      = clFn (infConv (conj (pairing n) f) (conj (pairing n) g)) := by
  rw [conj_add_eq_clFn_infConv (convexFn_clFn hf) (closedFn_clFn f) (convexFn_clFn hg)
    (closedFn_clFn g), conj_clFn, conj_clFn]

/-- **Rockafellar, Theorem 16.4**, the exact half: if `ri (dom f)` and `ri (dom g)` have a point in
common, the closure operation can be omitted and `(f + g)* = f* □ g*`.

Specialises `IsExactSum.of_relint` and `IsExactSum.conj_add`. Closedness is not assumed, as in the
book. -/
theorem theorem_16_4_exact {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (dom g)) :
    conj (pairing n) (f + g) = infConv (conj (pairing n) f) (conj (pairing n) g) :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).conj_add

/-- **Rockafellar, Theorem 16.4**, the attainment: under the same qualification, for each `x*` the
infimum `inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}` is attained.

Specialises `IsExactSum.exists_conj_add_eq`. -/
theorem theorem_16_4_attained {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (dom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      conj (pairing n) f y₁ + conj (pairing n) g y₂ = conj (pairing n) (f + g) y :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).exists_conj_add_eq y

/-- **Rockafellar, Corollary 16.4.1**, first formula for `m = 2`:
`δ*(· | C₁ + C₂) = δ*(· | C₁) + δ*(· | C₂)`.

Specialises `supportFn_add`. Unlike the function statement this needs no qualification: two
suprema over sets never interact through an `∞ - ∞`. -/
theorem corollary_16_4_1_add (C D : Set (Rn n)) :
    supportFn (pairing n) (C + D) = supportFn (pairing n) C + supportFn (pairing n) D :=
  supportFn_add (pairing n) C D

/-- **Rockafellar, Corollary 16.4.1**, first formula in the book's `m`-ary form:
`δ*(· | C₁ + ⋯ + Cₘ) = δ*(· | C₁) + ⋯ + δ*(· | Cₘ)`. -/
theorem corollary_16_4_1_add_finset {ι : Type*} (s : Finset ι) (C : ι → Set (Rn n)) :
    supportFn (pairing n) (∑ i ∈ s, C i) = ∑ i ∈ s, supportFn (pairing n) (C i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← Set.singleton_zero, supportFn_singleton]
    funext y
    simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, corollary_16_4_1_add, ih]

/-- **Rockafellar, Corollary 16.4.1**, second formula:
`δ*(· | cl C₁ ∩ cl C₂) = cl(δ*(· | C₁) □ δ*(· | C₂))`.

The indicator instance of `theorem_16_4_closure`: adding indicators intersects the sets. -/
theorem corollary_16_4_1_closure {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D) :
    supportFn (pairing n) (closure C ∩ closure D)
      = clFn (infConv (supportFn (pairing n) C) (supportFn (pairing n) D)) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn,
    supportFn_eq_conj_indicatorFn, ← indicatorFn_add, ← clFn_indicatorFn, ← clFn_indicatorFn]
  exact theorem_16_4_closure (convexFn_indicatorFn.2 hC) (convexFn_indicatorFn.2 hD)

/-- **Rockafellar, Corollary 16.4.1**, the exact half: if `ri C₁` and `ri C₂` have a point in
common, `δ*(x* | C₁ ∩ C₂) = inf {δ*(x₁* | C₁) + δ*(x₂* | C₂) | x₁* + x₂* = x*}`, the infimum being
attained. -/
theorem corollary_16_4_1_exact {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) {x₀ : Rn n} (hxC : x₀ ∈ ri C) (hxD : x₀ ∈ ri D) :
    supportFn (pairing n) (C ∩ D)
      = infConv (supportFn (pairing n) C) (supportFn (pairing n) D) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn,
    supportFn_eq_conj_indicatorFn, ← indicatorFn_add]
  refine theorem_16_4_exact (convexFn_indicatorFn.2 hC)
    ⟨by rw [dom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩ (convexFn_indicatorFn.2 hD)
    ⟨by rw [dom_indicatorFn]; exact hDne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_ ?_
  · rw [dom_indicatorFn]; exact hxC
  · rw [dom_indicatorFn]; exact hxD

/-- **Rockafellar, Corollary 16.4.2**, first formula: `(K₁ + K₂)° = K₁° ∩ K₂°` for non-empty
convex cones.

Read through `supportFn_eq_indicatorFn_polarCone`: the support function of a cone is the indicator
of its polar, adding indicators intersects, and an indicator function determines its set. Only the
cone property is used, not convexity. -/
theorem corollary_16_4_2_add {K L : Set (Rn n)} (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hL : ∀ a : ℝ, 0 < a → a • L = L) :
    polarCone (pairing n) (K + L)
      = polarCone (pairing n) K ∩ polarCone (pairing n) L := by
  have hdist : ∀ (a : ℝ) (s t : Set (Rn n)), a • (s + t) = a • s + a • t := by
    intro a s t
    ext z
    simp only [Set.mem_smul_set, Set.mem_add]
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨x, hx, rfl⟩, a • y, ⟨y, hy, rfl⟩, (smul_add a x y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, smul_add a x y⟩
  have hKL : ∀ a : ℝ, 0 < a → a • (K + L) = K + L := fun a ha => by
    rw [hdist, hK a ha, hL a ha]
  have h := corollary_16_4_1_add K L
  rw [supportFn_eq_indicatorFn_polarCone hKL (hKne.add hLne),
    supportFn_eq_indicatorFn_polarCone hK hKne,
    supportFn_eq_indicatorFn_polarCone hL hLne, indicatorFn_add] at h
  ext y
  have hy := congrFun h y
  constructor
  · intro h₁
    by_contra h₂
    rw [indicatorFn_of_mem h₁, indicatorFn_of_notMem h₂] at hy
    exact absurd hy (by simp)
  · intro h₂
    by_contra h₁
    rw [indicatorFn_of_notMem h₁, indicatorFn_of_mem h₂] at hy
    exact absurd hy (by simp)

/-! ### Theorem 16.5: pointwise suprema and convex hulls -/

/-- **Rockafellar, Theorem 16.5**, first formula: `(conv {fᵢ | i ∈ I})* = sup {fᵢ* | i ∈ I}` for an
arbitrary index set `I`.

Unconditional; the empty family is not an exception. Specialises `conj_convFn`. -/
theorem theorem_16_5_convFn {ι : Sort*} (f : ι → Rn n → EReal) :
    conj (pairing n) (convFn f) = ⨆ i, conj (pairing n) (f i) :=
  conj_convFn (pairing n) f

/-- **Rockafellar, Theorem 16.5**, second formula:
`(sup {cl fᵢ | i ∈ I})* = cl (conv {fᵢ* | i ∈ I})`.

Specialises `conj_iSup_eq_clFn_convFn`, applied to the closures. -/
theorem theorem_16_5_closure {ι : Sort*} {f : ι → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    conj (pairing n) (⨆ i, clFn (f i))
      = clFn (convFn fun i => conj (pairing n) (f i)) := by
  rw [conj_iSup_eq_clFn_convFn (fun i => convexFn_clFn (hf i)) (fun i => closedFn_clFn (f i))]
  simp only [conj_clFn]

/-- **Rockafellar, Corollary 16.5.1**, first formula: the support function of the convex hull `D`
of the union of the sets `Cᵢ` is `sup {δ*(· | Cᵢ) | i ∈ I}`.

Specialises `supportFn_convexHull` and `supportFn_iUnion`. -/
theorem corollary_16_5_1_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    supportFn (pairing n) (convexHull ℝ (⋃ i, C i))
      = fun y => ⨆ i, supportFn (pairing n) (C i) y := by
  rw [supportFn_convexHull, supportFn_iUnion]

/-- **Rockafellar, Corollary 16.5.1**, second formula: the support function of the intersection of
the sets `cl Cᵢ` is `cl (conv {δ*(· | Cᵢ) | i ∈ I})`.

The indicator instance of `theorem_16_5_closure`. The index set must be non-empty: over an empty
family the book's `⋂ cl Cᵢ` is all of `ℝⁿ` while `sup {δ(· | Cᵢ)}` is `-∞`. -/
theorem corollary_16_5_1_closure {ι : Sort*} [Nonempty ι] {C : ι → Set (Rn n)}
    (hC : ∀ i, Convex ℝ (C i)) :
    supportFn (pairing n) (⋂ i, closure (C i))
      = clFn (convFn fun i => supportFn (pairing n) (C i)) := by
  have hind : (⨆ i, clFn (indicatorFn (C i))) = indicatorFn (⋂ i, closure (C i)) := by
    simp only [clFn_indicatorFn]
    funext x
    rw [iSup_apply]
    by_cases hx : x ∈ ⋂ i, closure (C i)
    · rw [indicatorFn_of_mem hx]
      refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le (Classical.arbitrary ι) ?_)
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx i)]
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx _)]
    · rw [indicatorFn_of_notMem hx]
      obtain ⟨i, hi⟩ := not_forall.1 (fun h => hx (Set.mem_iInter.2 h))
      exact le_antisymm le_top (le_iSup_of_le i (by rw [indicatorFn_of_notMem hi]))
  simp only [supportFn_eq_conj_indicatorFn]
  rw [← hind]
  exact theorem_16_5_closure fun i => convexFn_indicatorFn.2 (hC i)

/-- **Rockafellar, Corollary 16.5.2**, first formula:
`(conv {Cᵢ | i ∈ I})° = ⋂ {Cᵢ° | i ∈ I}`.

Polarity is order-inverting and `{x | ⟨x, x*⟩ ≤ 1}` is convex, so the convex hull is invisible to
it; this is the book's own second proof. -/
theorem corollary_16_5_2_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    polarSet (pairing n) (convexHull ℝ (⋃ i, C i)) = ⋂ i, polarSet (pairing n) (C i) := by
  ext y
  simp only [Set.mem_iInter, mem_polarSet]
  constructor
  · intro hy i x hx
    exact hy x (subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨i, hx⟩))
  · intro hy
    have hsub : (⋃ i, C i) ⊆ {x : Rn n | pairing n x y ≤ 1} := by
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hy i x hi
    exact fun x hx => convexHull_min hsub (convex_setOf_pairing_le_one y) hx

/-- **Rockafellar, Corollary 16.5.2**, the unconditional half of the second formula: each `Cᵢ°` is
contained in `(⋂ Cⱼ)°`, hence so is the convex hull of their union. Equality with the polar of
`⋂ cl Cⱼ` holds after a closure; see the module docstring. -/
theorem corollary_16_5_2_inter {ι : Sort*} (C : ι → Set (Rn n)) (i : ι) :
    polarSet (pairing n) (C i) ⊆ polarSet (pairing n) (⋂ j, C j) :=
  polarSet_anti (Set.iInter_subset C i)

end Rockafellar
