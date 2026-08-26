/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Differentiability
import Tdaf.Analysis.Convex.Subgradient.GradientLimit
import Tdaf.Analysis.Convex.Subgradient.Reconstruction
import Tdaf.Surface.Common.Euclidean

/-!
# Rockafellar, §25: Differentiability of Convex Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §25, pp. 241–252: the relation between the
subdifferential `∂f` and the ordinary gradient `∇f`. Theorem 25.1 identifies the two where `∇f`
exists, Theorems 25.3–25.5 say that is almost everywhere on `int (dom f)`, Theorem 25.6
reconstructs the whole of `∂f` from `∇f`, and Theorem 25.7 says gradients of convex functions
converge whenever the functions do.

## `∇f(x)` is a vector, and the backbone's gradient is a functional

Rockafellar's `∇f(x)` is a point of `ℝⁿ`; the backbone's `HasGradientAt f f' x` has
`f' : StrongDual ℝ E`, because `HasFDerivAt` needs a normed target and because the backbone refuses
to identify a space with its dual (`Surface/Common/Euclidean.lean`, design notes). `linFn` is the
Fréchet–Riesz translation the surface already carries, so `HasGradientVecAt f b x` below is
`HasGradientAt f (linFn b) x` and `gradientVec f x` is the vector representing
`fderiv ℝ (fun z => (f z).toReal) x`. Both come with their bridge lemmas and nothing else unfolds
them.

**Differentiability of an extended-real-valued `f` is `DifferentiableAtFn`, not
`DifferentiableAt`.** The backbone's definition asks for a real-valued `g` agreeing with `f` near
`x` and differentiable there, which is exactly what Rockafellar's `∇f(x)` presupposes: `f` finite
at `x`, hence finite near `x`. `differentiableAtFn_iff_differentiableAt_toReal` is the dictionary
to Mathlib's `DifferentiableAt` of the real trace, and Corollary 25.5.1 below is stated in Mathlib's
`ConvexOn` / `fderiv` vocabulary because that is the form in which the rest of the library will
want it.

## How much of §25 is really finite-dimensional

`part5.md` classifies all eleven results as **C**, concrete and finite-dimensional. Three of them
are not:

* **Theorem 25.1, forward half.** `∇f(x)` is the unique subgradient at a point of
  differentiability, for a convex `f` on *any* normed space: `theorem_25_1_forward` and
  `theorem_25_1_le` specialise `Gradient.lean`'s `HasGradientAt.subgradient_eq` and
  `HasGradientAt.le`, neither of which sees a dimension. The uniqueness half of that argument does
  not even use convexity. **The converse is genuinely finite-dimensional**
  (`theorem_25_1_converse`): it goes through `Uniqueness.lean`'s interior step, where a convex set
  whose normal cone at `x` is trivial is shown to be a neighbourhood of `x` — Corollary 11.6.1, and
  false in infinite dimensions.
* **Corollary 25.1.1** is general in both halves. Local finiteness alone puts `x` in
  `int (dom f)`, and a convex function finite near a point is proper in any topological vector
  space (`Gradient.lean`'s `proper_of_eventuallyEq_coe`, which is the part of Theorem 7.2 that
  differentiability needs).
* **Theorem 25.4's density clause** needs no finite dimension either: restricting to the line
  through `x` in the direction `y` turns it into Theorem 25.3, whose countability comes from
  monotonicity of `f'₊`. Only the *continuity* clause and the *measure-zero* clause of Theorem 25.4
  are finite-dimensional.

Corollaries 25.1.2 and 25.1.3 are C only because the book states them with `∇f`; their subgradient
forms (`mem_exposedPoints_epi_conj_iff`, `mem_exposedPoints_supportSet_iff`) are general, with
`IsCompatiblePairing B.flip` doing the work finite dimension would.

## Contents

| label | declaration |
|---|---|
| Theorem 25.1 | `theorem_25_1_forward`, `theorem_25_1_le`, `theorem_25_1_converse`,
  `theorem_25_1`, `theorem_25_1_differentiableAtFn` |
| Corollary 25.1.1 | `corollary_25_1_1_proper`, `corollary_25_1_1_mem_interior` |
| Corollary 25.1.2 | `corollary_25_1_2` |
| Corollary 25.1.3 | `corollary_25_1_3` |
| Theorem 25.2 | `theorem_25_2_dirDeriv`, `theorem_25_2`, `theorem_25_2_partial` |
| Theorem 25.3 | `theorem_25_3_countable`, `theorem_25_3_dense`, `theorem_25_3_continuousAt`,
  `theorem_25_3_monotone` |
| Theorem 25.4 | `theorem_25_4_continuousAt_iff`, `theorem_25_4_dense`, `theorem_25_4_measure` |
| Theorem 25.5 | `theorem_25_5_dense`, `theorem_25_5_measure`, `theorem_25_5_continuousOn` |
| Corollary 25.5.1 | `corollary_25_5_1` |
| Theorem 25.6 | `theorem_25_6`, `mem_gradientLimits_iff`,
  `recessionCone_subgradient_eq_normalCone` |
| Theorem 25.7 | `theorem_25_7`, `theorem_25_7_uniform` |

## The section's definitions

* `Rockafellar.HasGradientVecAt f b x` — "`f` is differentiable at `x` and `∇f(x) = b`", with `b`
  a *vector*. It is `HasGradientAt f (linFn b) x` by definition, and
  `hasGradientVecAt_iff_hasGradientAt` is the bridge.
* `Rockafellar.gradientVec f x` — `∇f(x)` as a vector, namely the Riesz representative of
  `fderiv ℝ (fun z => (f z).toReal) x`. `HasGradientVecAt.gradientVec_eq` and
  `hasGradientVecAt_gradientVec` are its bridges.

## Where the book is defective

* **Corollary 25.5.1 is stated with no proof at all** (line 9829 of the source text; it is one of
  the fourteen such results listed in the surface overview §5). `corollary_25_5_1` supplies one,
  through Theorem 25.5's continuity clause applied to the extension of `g` by `+∞` off `C`.
* **Corollaries 25.1.2 and 25.1.3 are stated for an `f` that need not be closed**, and the book's
  proof opens by replacing `f` with `cl f`, justified by the remark after Corollary 25.1.1 that
  `∇(cl f) = ∇f`. That remark is asserted, not proved, and the backbone does not have it, so both
  corollaries are stated here with `ClosedFn f` — see `## Backbone gaps`.
* **Theorem 25.6's proof does not, here, verify the exercise of line 8477.** The book leaves
  `rec (∂f(x)) = N_{dom f}(x)` as an exercise in §23 and says the verification "will be given later
  as part of the proof of Theorem 25.6". The backbone's proof never computes that recession cone —
  it uses only the inclusion `rec (∂f(x)) ⊆ N_{dom f}(x)` — so §23's exercise is *not* discharged
  on the way. It is discharged here instead, as `recessionCone_subgradient_eq_normalCone`, in four
  lines and independently of Theorem 25.6.
* **Rockafellar's "`y ≠ 0`" in Theorem 25.4 is not needed**, and neither is the `Sₖ` decomposition
  it is stated with; see `## What is not here`.

## What is not here

* **Theorem 25.4's `Sₖ` decomposition** — *omitted with a reason*. The book's full statement adds
  that the complement of `D` in `int (dom f)` "can be expressed as a countable union of sets `Sₖ`
  closed relative to `int (dom f)`, such that no bounded interval of a line in the direction of `y`
  contains more than finitely many points of any one `Sₖ`". That decomposition exists solely to
  prove the measure-zero clause by a Fubini argument over lines; `Rademacher.lean` obtains the
  measure-zero clause from Rademacher's theorem instead, and the density clause from the
  one-dimensional Theorem 25.3, so nothing in the section depends on it. Both clauses it supports
  are stated (`theorem_25_4_measure`, `theorem_25_4_dense`).
* **The `G_δ` remark after Corollary 25.5.1** (line 9831) is unnumbered and is a remark about
  Rockafellar's own proof of Theorem 25.5, which is not the proof used here.
* **Theorem 25.3 is stated over `ℝ`, not over `Rn 1`.** The book says "an open interval `I` of the
  real line", and `Subgradient/OneDim.lean` develops `f'₊` and `f'₋` for `f : ℝ → EReal`; a
  transport across `Rn 1 ≃ ℝ` would buy nothing and would hide the one-dimensional content. The
  book's `I` is `interior (dom f)` here, which is exactly an open interval on which `f` is finite,
  and the book's own first move — "extend `f` to a closed proper convex function on `R`" — is
  needed only for the continuity clause, which is the only one carrying `ClosedProperConvexFn`.

## Backbone gaps

* **`∇(cl f) = ∇f` for a proper convex `f`.** Wanted:
  `HasGradientAt (clFn f) f' x ↔ HasGradientAt f f' x`, or at least the `DifferentiableAtFn`
  version. Rockafellar states it as an aside after Corollary 25.1.1 and uses it to drop closedness
  from Corollaries 25.1.2 and 25.1.3. The forward direction is short — `clFn f` and `f` agree on
  `int (dom f)` by `ConvexFn.clFn_eq_of_mem_relint_dom`, which is a neighbourhood of `x` — but the
  converse needs `int (dom (clFn f)) = int (dom f)`, which is Theorem 7.4's companion for
  *interiors* rather than relative interiors and is not in the library. It belongs in
  `Tdaf/Analysis/Convex/Subgradient/Uniqueness.lean`, next to the other two consumers of
  Theorem 25.1's converse.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25.
-/

open Filter MeasureTheory Topology
open scoped Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ}

/-! ### `∇f(x)` as a vector

The backbone's gradient is a continuous linear functional; Rockafellar's is a vector. `linFn` is
the translation, and these four declarations are the whole of it. -/

section GradientVector

variable {f : Rn n → EReal} {b x : Rn n}

/-- **`linFn` is the Fréchet–Riesz map.** `linFn b = ⟨·, b⟩` is what
`InnerProductSpace.toDual ℝ (Rn n)` sends `b` to, so the surface's vector-to-functional
translation and the one the backbone's `Subgradient/Rademacher.lean` uses are the same map. -/
theorem linFn_eq_toDual (b : Rn n) : linFn b = InnerProductSpace.toDual ℝ (Rn n) b := by
  ext y
  simp [linFn]

/-- **Rockafellar's `∇f(x) = b`**, with `b` a vector of `ℝⁿ`: `f` agrees near `x` with a
real-valued function whose Fréchet derivative at `x` is `⟨·, b⟩`. -/
def HasGradientVecAt (f : Rn n → EReal) (b x : Rn n) : Prop :=
  HasGradientAt f (linFn b) x

/-- **The bridge to the backbone**: the vector reading and the functional reading of `∇f(x)` are
the same statement. -/
theorem hasGradientVecAt_iff_hasGradientAt :
    HasGradientVecAt f b x ↔ HasGradientAt f (linFn b) x := Iff.rfl

/-- Differentiability in the sense of §25 is the existence of a gradient *vector*. -/
theorem differentiableAtFn_iff_exists_hasGradientVecAt :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, HasGradientVecAt f b x := by
  constructor
  · rintro ⟨f', hf'⟩
    obtain ⟨b, hb⟩ := exists_linFn f'
    refine ⟨b, ?_⟩
    rw [hasGradientVecAt_iff_hasGradientAt, hb]
    exact hf'
  · rintro ⟨b, hb⟩
    exact ⟨linFn b, hb⟩

/-- **`∇f(x)` as a vector**, defined for every `x` and correct where `f` is differentiable: the
Riesz representative of Mathlib's derivative of the real trace of `f`. -/
noncomputable def gradientVec (f : Rn n → EReal) (x : Rn n) : Rn n :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x)

/-- `gradientVec` read back as a functional is Mathlib's `fderiv` of the real trace. -/
theorem linFn_gradientVec (f : Rn n → EReal) (x : Rn n) :
    linFn (gradientVec f x) = fderiv ℝ (fun z => (f z).toReal) x := by
  rw [linFn_eq_toDual]
  exact (InnerProductSpace.toDual ℝ (Rn n)).apply_symm_apply _

/-- The gradient vector is unique where it exists, and `gradientVec` computes it. -/
theorem HasGradientVecAt.gradientVec_eq (h : HasGradientVecAt f b x) : gradientVec f x = b := by
  have hfd : fderiv ℝ (fun z => (f z).toReal) x = linFn b :=
    HasGradientAt.fderiv_toReal_eq (hasGradientVecAt_iff_hasGradientAt.1 h)
  have hg : gradientVec f x
      = (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x) := rfl
  rw [hg, hfd, linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply]

/-- Where `f` is differentiable, `gradientVec f x` **is** its gradient. -/
theorem hasGradientVecAt_gradientVec (h : DifferentiableAtFn f x) :
    HasGradientVecAt f (gradientVec f x) x := by
  have hd := DifferentiableAtFn.hasGradientAt_fderiv h
  rw [← linFn_gradientVec f x] at hd
  exact hd

end GradientVector

/-! ### Theorem 25.1 and its corollaries -/

section Theorem251

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Rockafellar, Theorem 25.1**, forward half — **the general fragment of §25**. Let `f` be a
convex function and `x` a point where `f` is finite. If `f` is differentiable at `x`, then
`∇f(x)` is the *unique* subgradient of `f` at `x`.

Nothing here is finite-dimensional: `Gradient.lean` proves it for a convex function on an arbitrary
normed space, and the uniqueness half of the argument
(`eq_of_mem_subgradient_of_hasFDerivAt`) uses neither convexity nor properness — only that the
difference quotient along the rays `±v` has a common limit. The converse, `theorem_25_1_converse`,
is where the finite dimension enters. Rockafellar's "let `f` be finite at `x`" is weaker only in
appearance: a gradient at `x` forces `f` to be finite near `x`, which is Corollary 25.1.1. -/
theorem theorem_25_1_forward (hf : ConvexFn f) (h : HasGradientVecAt f b x) :
    subgradient (pairing n) f x = {b} := by
  have hs := subgradient_innerL_eq_singleton (E := Rn n) hf
    (hasGradientVecAt_iff_hasGradientAt.1 h)
  rwa [linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply] at hs

/-- **Rockafellar, Theorem 25.1**, the displayed inequality: `f(z) ≥ f(x) + ⟨∇f(x), z - x⟩` for
every `z`. Like the forward half it is general — it is the gradient inequality of
`Gradient.lean`'s `HasGradientAt.le`. -/
theorem theorem_25_1_le (hf : ConvexFn f) (h : HasGradientVecAt f b x) (z : Rn n) :
    f x + ((pairing n (z - x) b : ℝ) : EReal) ≤ f z := by
  have hle := HasGradientAt.le hf (hasGradientVecAt_iff_hasGradientAt.1 h) z
  rwa [linFn_apply] at hle

/-- **Rockafellar, Theorem 25.1**, converse half — **the finite-dimensional half**. If a proper
convex `f` has a unique subgradient at `x`, then `f` is differentiable at `x` and that subgradient
is `∇f(x)`.

`Uniqueness.lean` carries it, and the step that needs `ℝⁿ` is the one Rockafellar passes over: a
lone subgradient leaves no room for a normal direction to `dom f`, and *in finite dimensions* a
convex set is a neighbourhood of every point whose normal cone is trivial (Corollary 11.6.1). Only
then is `f'(x; ·)` finite in every direction, so that Theorem 23.2 computes it rather than its
closure. -/
theorem theorem_25_1_converse (hf : ConvexFn f) (hp : Proper f)
    (h : subgradient (pairing n) f x = {b}) : HasGradientVecAt f b x := by
  have hg := hasGradientAt_toDual_of_subgradient_eq_singleton (E := Rn n) hf hp h
  rw [hasGradientVecAt_iff_hasGradientAt, linFn_eq_toDual]
  exact hg

/-- **Rockafellar, Theorem 25.1**, in full: for a proper convex function on `ℝⁿ`, having gradient
`b` at `x` and having `b` as sole subgradient at `x` are the same thing. -/
theorem theorem_25_1 (hf : ConvexFn f) (hp : Proper f) :
    HasGradientVecAt f b x ↔ subgradient (pairing n) f x = {b} :=
  ⟨theorem_25_1_forward hf, theorem_25_1_converse hf hp⟩

/-- **Rockafellar, Theorem 25.1**, as the sentence at line 8423 states it: `∂f(x)` consists of a
single vector exactly when `f` is differentiable at `x`. -/
theorem theorem_25_1_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, subgradient (pairing n) f x = {b} := by
  rw [differentiableAtFn_iff_exists_hasGradientVecAt]
  exact exists_congr fun _ => theorem_25_1 hf hp

/-- **Rockafellar, Corollary 25.1.1**, second half: a convex function finite and differentiable at
`x` is proper. General — it holds in any topological vector space, being the piece of Theorem 7.2
that differentiability needs. -/
theorem corollary_25_1_1_proper (hf : ConvexFn f) (h : HasGradientVecAt f b x) : Proper f :=
  HasGradientAt.proper hf (hasGradientVecAt_iff_hasGradientAt.1 h)

/-- **Rockafellar, Corollary 25.1.1**, first half: `x ∈ int (dom f)`. General, and it uses neither
convexity nor differentiability — only that `f` is finite near `x`, which the definition of
`∇f(x)` presupposes. -/
theorem corollary_25_1_1_mem_interior (h : HasGradientVecAt f b x) : x ∈ interior (dom f) :=
  HasGradientAt.mem_interior_dom (hasGradientVecAt_iff_hasGradientAt.1 h)

/-- **Rockafellar, Corollary 25.1.2**: for a proper convex `f` on `ℝⁿ`, the exposed points of
`epi f*` in `ℝⁿ⁺¹` are the points `(x*, f*(x*))` such that `f` is differentiable at some `x` with
`∇f(x) = x*`.

The exposedness half (`mem_exposedPoints_epi_conj_iff`) is general; Theorem 25.1 is what renames
its conclusion from "the only subgradient" to "the gradient", and that is the finite-dimensional
step.

**The hypothesis `ClosedFn f` is not the book's.** Rockafellar reduces to the closed case by
replacing `f` with `cl f`, on the strength of the unproved remark `∇(cl f) = ∇f`; see
`## Backbone gaps` in the module docstring. -/
theorem corollary_25_1_2 (hf : ConvexFn f) (hp : Proper f) (hc : ClosedFn f) {y : Rn n} {μ : ℝ} :
    (y, μ) ∈ (epi (conj (pairing n) f)).exposedPoints ℝ ↔
      conj (pairing n) f y = (μ : EReal) ∧ ∃ x : Rn n, HasGradientVecAt f y x := by
  rw [mem_exposedPoints_epi_conj_iff (B := pairing n) hf hp hc]
  exact and_congr_right fun _ => exists_congr fun _ => (theorem_25_1 hf hp).symm

/-- **Rockafellar, Corollary 25.1.3**: let `C` be a non-empty closed convex set and `g` any
positively homogeneous proper convex function with `C = {z | ⟨y, z⟩ ≤ g(y) for all y}` — the
support function of `C`, for instance. Then `z` is an exposed point of `C` if and only if there is
a `y` at which `g` is differentiable with `∇g(y) = z`.

`supportSet (pairing n) g` is the book's `{z | ⟨y, z⟩ ≤ g(y) ∀ y}` verbatim, and its non-emptiness
and closedness are consequences of the other hypotheses rather than extra assumptions, so they do
not appear. As in Corollary 25.1.2 the hypothesis `ClosedFn g` is the book's implicit reduction to
`cl g`. -/
theorem corollary_25_1_3 {g : Rn n → EReal} {C : Set (Rn n)} (hgh : PosHomogeneous g)
    (hgc : ConvexFn g) (hgp : Proper g) (hgcl : ClosedFn g)
    (hC : C = supportSet (pairing n) g) {z : Rn n} :
    z ∈ C.exposedPoints ℝ ↔ ∃ y : Rn n, HasGradientVecAt g z y := by
  subst hC
  have h := mem_exposedPoints_supportSet_iff (B := pairing n) hgh hgc hgp hgcl (z := z)
  simp only [supportSet_flip_pairing, subgradient_flip_pairing] at h
  rw [h]
  exact exists_congr fun _ => (theorem_25_1 hgc hgp).symm

end Theorem251

/-! ### Theorem 25.2 -/

section Theorem252

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Rockafellar, Theorem 25.2**, necessity: at a point of differentiability the directional
derivative is the linear function `y ↦ ⟨∇f(x), y⟩`. General, like Theorem 25.1's forward half. -/
theorem theorem_25_2_dirDeriv (hf : ConvexFn f) (h : HasGradientVecAt f b x) (v : Rn n) :
    dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  have hd := HasGradientAt.dirDeriv_eq hf (hasGradientVecAt_iff_hasGradientAt.1 h) v
  rwa [linFn_apply] at hd

/-- **Rockafellar, Theorem 25.2**: for a convex `f` finite at `x`, a necessary and sufficient
condition for `f` to be differentiable at `x` is that `f'(x; ·)` be linear.

Sufficiency is where `ℝⁿ` is used, and the backbone's route is not Rockafellar's: instead of
Theorems 23.2, 7.2 and 4.8 it runs a cross-polytope estimate in a basis, which consumes only the
`2n` one-sided derivatives along `± bⱼ` — i.e. exactly the strengthening the book's last sentence
announces (`theorem_25_2_partial`). -/
theorem theorem_25_2 (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    DifferentiableAtFn f x ↔
      ∃ b : Rn n, ∀ v : Rn n, dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 h
    exact ⟨c, theorem_25_2_dirDeriv hf hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨linFn c, hasGradientAt_of_dirDeriv_eq hf ht hb fun v => ?_⟩
    rw [hc v, linFn_apply]

/-- **Rockafellar, Theorem 25.2**, last sentence: differentiability at `x` is already assured if
the `n` two-sided partial derivatives `∂f/∂ξⱼ` exist at `x` and are finite.

"Two-sided and finite" is spelled out as the book spells it: the one-sided derivative along `eⱼ` is
the real number `cⱼ` and the one along `-eⱼ` is `-cⱼ`, where `eⱼ = EuclideanSpace.single j 1` is
the `j`th row of the identity matrix. -/
theorem theorem_25_2_partial (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (c : Fin n → ℝ)
    (hpos : ∀ j, dirDeriv f x (EuclideanSpace.single j (1 : ℝ)) = ((c j : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-EuclideanSpace.single j (1 : ℝ)) = ((-c j : ℝ) : EReal)) :
    DifferentiableAtFn f x :=
  differentiableAtFn_of_forall_basis_dirDeriv_eq (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hf
    ht hb c (fun j => by simpa using hpos j) fun j => by simpa using hneg j

end Theorem252

/-! ### Theorem 25.3, on the line

Rockafellar's `I` is an open interval of `ℝ` on which `f` is finite; it is `interior (dom f)` here,
and his opening move — extend `f` to a closed proper convex function on `ℝ` — is needed only for
the continuity clause. His `f'` is defined on `D` only; `rightDeriv f` is defined everywhere and
agrees with `f'` on `D`, so the clauses below are the book's, strengthened. -/

section Theorem253

variable {f : ℝ → EReal}

/-- **Rockafellar, Theorem 25.3**, first assertion: `D` contains all but perhaps countably many
points of `I`. -/
theorem theorem_25_3_countable (hf : ConvexFn f) (hp : Proper f) :
    {x ∈ interior (dom f) | ¬DifferentiableAtFn f x}.Countable :=
  countable_not_differentiableAtFn hf hp

/-- **Rockafellar, Theorem 25.3**, the parenthesis: `D` is dense in `I`. -/
theorem theorem_25_3_dense (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} :=
  subset_closure_differentiableAtFn hf hp

/-- **Rockafellar, Theorem 25.3**, second assertion: `f'` is continuous relative to `D`.

Stronger than the book's: `rightDeriv f` is continuous at each point of `D` in the ordinary sense,
not merely relative to `D`. This is the clause that wants the book's extension of `f` to a closed
proper convex function on the whole line. -/
theorem theorem_25_3_continuousAt (hf : ClosedProperConvexFn f) {x : ℝ}
    (hx : x ∈ interior (dom f)) (hd : DifferentiableAtFn f x) : ContinuousAt (rightDeriv f) x :=
  continuousAt_rightDeriv_of_differentiableAtFn hf hx hd

/-- **Rockafellar, Theorem 25.3**, third assertion: `f'` is non-decreasing relative to `D`.

Again stronger: `rightDeriv f` is monotone on the whole line, so no restriction to `D` is
needed. -/
theorem theorem_25_3_monotone (hf : ConvexFn f) (hp : Proper f) : Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

end Theorem253

/-! ### Theorem 25.4 -/

section Theorem254

variable {f : Rn n → EReal} {x : Rn n}

/-- **Rockafellar, Theorem 25.4**, first assertion: for a proper convex `f` and a fixed direction
`y`, the points of `int (dom f)` where the two-sided directional derivative exists are exactly the
points where `x ↦ f'(x; y)` is continuous.

Rockafellar's `y ≠ 0` is not needed: at `y = 0` both sides hold. -/
theorem theorem_25_4_continuousAt_iff (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (y : Rn n) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) :=
  continuousAt_dirDeriv_iff hf hp hx y

/-- **Rockafellar, Theorem 25.4**, density — **and this clause is general**. Restricting `f` to the
line through `x` in the direction `y` makes it Theorem 25.3, whose countability comes from
monotonicity of `f'₊`; no measure and no finite dimension are involved. -/
theorem theorem_25_4_dense (hf : ConvexFn f) (hp : Proper f) (y : Rn n) :
    interior (dom f) ⊆
      closure {z ∈ interior (dom f) | dirDeriv f z y = -dirDeriv f z (-y)} :=
  subset_closure_twoSided_dirDeriv hf hp y

/-- **Rockafellar, Theorem 25.4**, the measure-zero clause.

The implication runs the other way here: Rockafellar proves this first, by a Fubini argument over
lines through the `Sₖ` decomposition, and deduces Theorem 25.5 by intersecting the `n` coordinate
directions. With Rademacher's theorem available, Theorem 25.5 comes first and this is its trivial
consequence, since differentiability at `z` supplies the two-sided derivative in every direction at
once. -/
theorem theorem_25_4_measure (hf : ConvexFn f) (hp : Proper f) (y : Rn n) :
    volume (interior (dom f) \ {z | dirDeriv f z y = -dirDeriv f z (-y)}) = 0 :=
  measure_diff_twoSided_dirDeriv hf hp y

end Theorem254

/-! ### Theorem 25.5 and its corollary -/

section Theorem255

variable {f : Rn n → EReal}

/-- **Rockafellar, Theorem 25.5**, density: the set `D` of points where a proper convex function is
differentiable is dense in `int (dom f)`.

No measure appears in the statement; the proof borrows one, as Mathlib's
`dense_differentiableAt_norm` does. -/
theorem theorem_25_5_dense (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : Rn n | DifferentiableAtFn f z} :=
  interior_dom_subset_closure_differentiableAtFn hf hp

/-- **Rockafellar, Theorem 25.5**, measure zero: the complement of `D` in `int (dom f)` is null.

This is Rademacher's theorem; convexity contributes only the local Lipschitz constants, through
Theorem 10.4. -/
theorem theorem_25_5_measure (hf : ConvexFn f) (hp : Proper f) :
    volume (interior (dom f) \ {z : Rn n | DifferentiableAtFn f z}) = 0 :=
  measure_diff_differentiableAtFn hf hp

/-- **Rockafellar, Theorem 25.5**, continuity: the gradient mapping `x ↦ ∇f(x)` is continuous on
`D`.

This is Corollary 24.5.1 — upper semicontinuity of `∂f` — with both subdifferentials collapsed to
singletons by Theorem 25.1; the Riesz map is an isometry, so nothing is lost passing from
functionals to vectors. -/
theorem theorem_25_5_continuousOn (hf : ConvexFn f) (hp : Proper f) :
    ContinuousOn (gradientVec f) {z : Rn n | DifferentiableAtFn f z} :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp_continuousOn
    (continuousOn_fderiv_toReal hf hp)

/-- **Rockafellar, Corollary 25.5.1**: a finite convex function differentiable on an open convex
set `C` is *continuously* differentiable on `C`.

**The book states this with no proof at all.** The proof here extends `g` by `+∞` off `C`, which
changes no gradient because `C` is open, and applies Theorem 25.5's continuity clause. The book's
`C` is non-empty by its convention that a convex function has non-empty effective domain; the
statement is true and proved for `C = ∅` as well, so no such hypothesis appears. -/
theorem corollary_25_5_1 {C : Set (Rn n)} {g : Rn n → ℝ} (hC : IsOpen C) (hg : ConvexOn ℝ C g)
    (hd : DifferentiableOn ℝ g C) : ContinuousOn (fderiv ℝ g) C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact continuousOn_empty _
  · exact continuousOn_fderiv_of_convexOn hC hne hg hd

end Theorem255

/-! ### Theorem 25.6 -/

section Theorem256

variable {f : Rn n → EReal} {x : Rn n}

/-- **Rockafellar's `S(x)`**, in the book's own words: the set of limits of sequences of gradients
`∇f(xᵢ)` taken at points of differentiability `xᵢ → x`. `gradientLimits` is the backbone's name for
it, and this is its unfolding in the surface's vector vocabulary. -/
theorem mem_gradientLimits_iff {v : Rn n} :
    v ∈ gradientLimits f x ↔ ∃ xs vs : ℕ → Rn n, Tendsto xs atTop (𝓝 x) ∧
      (∀ i, HasGradientVecAt f (vs i) (xs i)) ∧ Tendsto vs atTop (𝓝 v) := by
  constructor
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    rw [hasGradientVecAt_iff_hasGradientAt, linFn_eq_toDual]
    exact h2 i
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    have hi := h2 i
    rw [hasGradientVecAt_iff_hasGradientAt, linFn_eq_toDual] at hi
    exact hi

/-- **The exercise of line 8477**: for `x` with `∂f(x) ≠ ∅`, the recession cone of `∂f(x)` is the
normal cone to `dom f` at `x`.

Rockafellar leaves this as an exercise in §23 and says the verification "will be given later as
part of the proof of Theorem 25.6". **It is not**, here: the backbone's proof of Theorem 25.6 uses
only the inclusion `⊆` (`recessionCone_subgradient_subset_normalCone`), because each of
Rockafellar's three uses of the identification follows more cheaply from
`∂f(x) + N_{dom f}(x) ⊆ ∂f(x)`. So the exercise is discharged here, on its own, and the other
inclusion is exactly that containment read at a single normal direction. -/
theorem recessionCone_subgradient_eq_normalCone (hp : Proper f) {v : Rn n}
    (hv : v ∈ subgradient (pairing n) f x) :
    recessionCone (subgradient (pairing n) f x) = normalCone (pairing n) (dom f) x :=
  Set.Subset.antisymm (recessionCone_subgradient_subset_normalCone hp hv)
    fun _ hw _ hv' _ ha => add_smul_mem_subgradient hv' hw ha

/-- **Rockafellar, Theorem 25.6**: let `f` be a closed proper convex function such that `dom f` has
non-empty interior. Then for every `x`,

```
∂f(x) = cl (conv S(x)) + K(x),
```

where `K(x)` is the normal cone to `dom f` at `x` and `S(x)` is the set of limits of sequences of
gradients at points of differentiability tending to `x`.

`normalCone` is total here, so it is `∅` for `x ∉ dom f` only in the sense that the whole equation
degenerates: the book declares `K(x)` empty off `dom f`, while the backbone's normal cone is the
pointed cone `{y | ⟨z - x, y⟩ ≤ 0 for all z ∈ dom f}` for every `x`. The two readings agree
wherever both sides are non-empty, and off `dom f` the left side is empty, which forces
`cl (conv S(x))` to be empty too. -/
theorem theorem_25_6 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty) :
    subgradient (pairing n) f x
      = closure (convexHull ℝ (gradientLimits f x)) + normalCone (pairing n) (dom f) x :=
  subgradient_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne

end Theorem256

/-! ### Theorem 25.7 -/

section Theorem257

variable {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal} {x : Rn n}

/-- **Rockafellar, Theorem 25.7**: let `C` be an open convex set, `g` a convex function finite and
differentiable on `C`, and `f₁, f₂, …` convex functions finite and differentiable on `C` with
`fᵢ(x) → g(x)` for every `x ∈ C`. Then `∇fᵢ(x) → ∇g(x)` for every `x ∈ C`.

For arbitrary differentiable functions this is false; convexity supplies it through the upper
semicontinuity of `∂f` under pointwise convergence (Theorem 24.5), at the constant sequence
`xᵢ = x`. Both subdifferentials are singletons by Theorem 25.1, so the inclusion
`∂fᵢ(x) ⊆ ∂g(x) + εB` *is* the bound `‖∇fᵢ(x) - ∇g(x)‖ ≤ ε`, and neither Theorem 10.8 nor a
contradiction argument is needed.

"Finite on `C`" is `C ⊆ dom ·` together with properness. -/
theorem theorem_25_7 (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, Proper (f i)) (hfC : ∀ i, C ⊆ dom (f i)) (hg : ConvexFn g) (hgp : Proper g)
    (hgC : C ⊆ dom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) (hx : x ∈ C)
    {b : ℕ → Rn n} {b' : Rn n} (hb : ∀ i, HasGradientVecAt (f i) (b i) x)
    (hb' : HasGradientVecAt g b' x) : Tendsto b atTop (𝓝 b') := by
  have h := tendsto_of_hasGradientAt hC hCc hf hfp hfC hg hgp hgC hconv hx
    (G := fun i => linFn (b i)) (G' := linFn b') (fun i => hb i) hb'
  have hc := ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.tendsto (linFn b')).comp h
  simpa [linFn_eq_toDual] using hc

/-- **Rockafellar, Theorem 25.7**, the sentence after it: the mappings `∇fᵢ` converge to `∇g`
uniformly on every closed bounded subset of `C`.

Rockafellar reduces to one partial derivative at a time and argues by contradiction on each; the
backbone runs the contradiction once, on the norm, using a convergent subsequence supplied by
compactness. "Closed and bounded" is `IsCompact` in `ℝⁿ`. -/
theorem theorem_25_7_uniform (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, Proper (f i)) (hfC : ∀ i, C ⊆ dom (f i)) (hg : ConvexFn g) (hgp : Proper g)
    (hgC : C ⊆ dom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hfd : ∀ i, ∀ z ∈ C, DifferentiableAtFn (f i) z)
    (hgd : ∀ z ∈ C, DifferentiableAtFn g z) {S : Set (Rn n)} (hS : IsCompact S) (hSC : S ⊆ C) :
    TendstoUniformlyOn (fun i => gradientVec (f i)) (gradientVec g) atTop S := by
  have h := tendstoUniformlyOn_fderiv_toReal hC hCc hf hfp hfC hg hgp hgC hconv hfd hgd hS hSC
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi z hz
  have hdist : dist (gradientVec g z) (gradientVec (f i) z)
      = dist (fderiv ℝ (fun w => (g w).toReal) z) (fderiv ℝ (fun w => (f i w).toReal) z) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.dist_map _ _
  rw [hdist]
  exact hi z hz

end Theorem257

end Rockafellar
