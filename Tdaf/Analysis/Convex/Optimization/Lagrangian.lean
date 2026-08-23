/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.ConcaveConj
import Tdaf.Analysis.Convex.Optimization.Perturbation

/-!
# Lagrangians of generalized convex programs

Rockafellar's §29, the Lagrangian half. The **Lagrangian** of the program associated with a
bifunction `F` is

`L(v, x) = ⨅ u (⟨u, v⟩ + F u x)`,

the partial *concave* conjugate of `F` in the perturbation variable. Every fact about Lagrangians
in §§28–29, §36 and §37 is a fact about partial conjugation, which is why this file proves the
identification first and everything else through it.

## Main definitions

* `lagrangian B F` — the Lagrangian `L` of the program associated with `F`.

## Main results

* `lagrangian_eq_concaveConj` — `L(·, x)` *is* the concave conjugate of `-F(·)(x)`. This is the
  whole design: no separate theory of Lagrangians is needed.
* `iInf_lagrangian` — `⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)`, the identity Rockafellar states
  right after the definition.
* `mem_kuhnTucker_iff_iInf_lagrangian` — the Kuhn–Tucker vectors described through `L`: the `v`
  for which `⨅ x L(v, x)` is finite and equal to the optimal value.

## Design notes

**The Lagrangian is a concave conjugate, not a new construction.** `concaveConj B g v` is
`⨅ u (⟨u, v⟩ - g u)`, so `L(v, x) = concaveConj B (fun u => -(F u x)) v` on the nose — the only
step is `a - (-b) = a + b`, which on `EReal` is `sub_eq_add_neg` plus `neg_neg`. Concavity of `L`
in `v`, its closedness, and the biconjugation `L** = cl L` are then `Duality/ConcaveConj.lean`
lemmas applied pointwise in `x`.

**Swapping the two infima is where the real content sits.** `⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)`
needs `iInf_comm` and the fact that a *real* constant moves through an infimum
(`Tdaf.EReal.iInf_add_coe`). Once it is available, the Lagrangian description of Kuhn–Tucker
vectors is a rewrite of `Perturbation.lean`'s definition.

## What is not here

**Theorem 28.2 (Slater) and the ordinary-convex-program bifunction `ineqBifun`.** The plan reserves
a place in the backbone for "Slater implies a Kuhn–Tucker vector exists" — it is not about
coordinates, and applications need it — but it also needs §21's theorems of the alternative wired
to `ineqBifun`, and `Helly.lean` has those only for finite systems of *inequalities*, not for the
mixed inequality/equality systems §28 allows. `kuhnTucker_nonempty_of_stronglyConsistent`
(`Perturbation.lean`) is the qualification-free half that is available now.

**Theorem 29.3 (saddle-points) and Theorem 28.3.** They need `IsSaddlePoint` and the §36
correspondence between Lagrangians and concave-convex minimax problems.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §29.
-/

namespace Tdaf.ConvexAnalysis

section Defs

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {x : X}

/-- The **Lagrangian** of the generalized convex program associated with `F`:
`L(v, x) = ⨅ u (⟨u, v⟩ + F u x)`. -/
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x

theorem lagrangian_apply (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = ⨅ u, ((B u v : ℝ) : EReal) + F u x := rfl

/-- **The Lagrangian is a partial concave conjugate.** For each fixed `x`, `L(·, x)` is the concave
conjugate of the concave function `u ↦ -(F u x)`. -/
theorem lagrangian_eq_concaveConj (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = concaveConj B (fun u => -(F u x)) v := by
  rw [lagrangian_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- The Lagrangian is never above the objective it comes from, taken at `u = 0`. -/
theorem lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x ≤ F 0 x := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero, zero_add]

/-- **Rockafellar, §29**: minimising the Lagrangian over `x` is the same as pricing the
perturbations. This is the identity that lets the definition of a Kuhn–Tucker vector be stated
either through `inf F` or through `L`. -/
theorem iInf_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) = ⨅ u, (((B u v : ℝ) : EReal) + infBifun F u) := by
  rw [show (⨅ x, lagrangian B F v x) = ⨅ x, ⨅ u, (((B u v : ℝ) : EReal) + F u x) from rfl,
    iInf_comm]
  refine iInf_congr fun u => ?_
  rw [infBifun_apply, add_comm, Tdaf.EReal.iInf_add_coe]
  exact iInf_congr fun x => add_comm _ _

/-- **Rockafellar, §29**: the Lagrangian description of Kuhn–Tucker vectors. `v` is a Kuhn–Tucker
vector exactly when the infimum of `L(v, ·)` is finite and equal to the optimal value. -/
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      (⨅ x, lagrangian B F v x) = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, iInf_lagrangian]

/-- The infimum of `L(v, ·)` is never above the optimal value, whatever the price `v`. This is weak
duality for the Lagrangian. -/
theorem iInf_lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) ≤ infBifun F 0 := by
  rw [iInf_lagrangian]
  exact iInf_add_infBifun_le B F v

end Defs

section Concave

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {x : X}

/-- **The Lagrangian is concave in the price variable**, with no hypothesis on `F` at all: it is a
concave conjugate, and concave conjugates are concave. -/
theorem concaveFn_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (x : X) :
    ConcaveFn (fun v => lagrangian B F v x) := by
  have h : (fun v => lagrangian B F v x) = concaveConj B (fun u => -(F u x)) :=
    funext fun v => lagrangian_eq_concaveConj B F v x
  rw [h]
  exact concaveFn_concaveConj B _

end Concave

end Tdaf.ConvexAnalysis
