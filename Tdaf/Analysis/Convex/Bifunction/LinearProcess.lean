/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.Process

/-!
# Linear transformations inside the convex algebra

A linear transformation is a single-valued convex process, and `ConvexProcess.ofLinearMap` is that
embedding. This module is the dictionary it induces: every operation of the convex algebra
restricts along the embedding to the corresponding operation on linear maps. The image of a set is
the linear image, composition is composition, the image of a function under the associated
bifunction is `mapLin`, and the adjoint of the process is a transpose of the linear map.

## Main results

* `ConvexProcess.image_ofLinearMap`, `ConvexProcess.range_ofLinearMap`,
  `ConvexProcess.comp_ofLinearMap`, `ConvexProcess.ofLinearMap_injective` — the set-level entries.
* `ConvexProcess.imageBifun_indicatorBifun_ofLinearMap` — the image of a function under a linear
  process is its image under the linear map: `A f = mapLin A f`. This is the identity the
  definition of `imageBifun` claims in its own doc comment.
* `ConvexProcess.adjointProcess_ofLinearMap` and `ConvexProcess.coadjointProcess_ofLinearMap` — the
  adjoint of a linear process is a transpose of the linear map, in *both* orientations.

## Design notes

**The adjoint entry is the only place in the convex algebra where a transpose occurs.** The adjoint
of a convex process, of a convex bifunction and of a convex function are all defined outright from
a pair of pairings — `adjointProcess`, `coadjointProcess`, `adjointBifun`, `lowerAdjointBifun`,
`conj` — and none of them mentions a linear map. A transpose enters only here, where the process
happens to be linear, and then it enters as what it is: a hypothesis `IsAdjointPair Bu Bx T T'`
supplying the datum, because between arbitrarily paired spaces a linear map need not have a
transpose at all.

**Which is why the transpose is not bundled into a class.** Making it an instance — a
`HasTranspose B B' A` class with a `transpose` field and a finite-dimensional inner-product
instance, so that search supplies `A'` — has been proposed and measured, and declined on three
grounds. *It is not canonical*: the field is data, unique only when `B` is right-separating
(`IsAdjointPair.unique`), so two instances could disagree and every statement written with `Aᵀ`
would silently depend on which one search found. *It would make a type depend on an instance*:
`IsExactImage B B' A A' hA g` takes the transpose as an index, so bundling would put an instance
inside the structure's type and let two syntactically different instances give two incompatible
structures. *And it would buy almost nothing*: the datum reaches **32** declarations in the whole
library, all of them in the conjugate-of-an-image family — `Duality/{Conjugate, Exact, Ops, Relint,
RelintSeparation}.lean`, `Optimization/Fenchel.lean`, `Subgradient/{Calculus, Preservation}.lean`,
`EuclideanProd.lean` — where it costs one hypothesis binder each and nothing else, the transpose
itself already being a section variable in every one of those files. Nothing in `Bifunction/`
carries it except the two theorems below.

**Both orientations give the same answer.** `adjointProcess` and `coadjointProcess` differ by the
direction of the defining inequality and must be kept apart — that is what makes `A** = cl A` come
out right — but on a linear process the graph is a *subspace*, so applying the inequality at `-u`
reverses it and both conditions collapse to the equation `⟨T u, y⟩ = ⟨u, v⟩`. This is why the
adjoint of a linear transformation can be spoken of without mentioning an orientation.

**Right-separation of `Bu`, not of `Bx`, is what pins the answer.** The defining condition fixes
`⟨u, v⟩` for every `u`, so it determines `v` exactly when `Bu` separates the points of `V`. Without
that hypothesis the adjoint process is still single-valued *up to* the annihilator of `U` in `V`,
which is exactly the ambiguity `IsAdjointPair.unique` records for the transpose itself.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39.
-/

open Set

namespace Tdaf.ConvexAnalysis

namespace ConvexProcess

/-! ### The set-level dictionary -/

section Sets

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

/-- The image of a set under a linear process is the linear image. -/
theorem image_ofLinearMap (T : U →ₗ[ℝ] X) (C : Set U) : (ofLinearMap T).image C = T '' C := by
  ext x
  constructor
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, (mem_graph_ofLinearMap.1 hx).symm⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, mem_graph_ofLinearMap.2 hx.symm⟩

/-- The range of a linear process is the range of the linear map. -/
theorem range_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).range = Set.range T := by
  rw [← image_univ, image_ofLinearMap, Set.image_univ]

/-- The product of two linear processes is the composite linear map. -/
theorem comp_ofLinearMap (S : X →ₗ[ℝ] Z) (T : U →ₗ[ℝ] X) :
    (ofLinearMap S).comp (ofLinearMap T) = ofLinearMap (S ∘ₗ T) := by
  ext p
  constructor
  · rintro ⟨x, hx, hz⟩
    exact (mem_graph_ofLinearMap.1 hz).trans (congrArg S (mem_graph_ofLinearMap.1 hx))
  · intro h
    exact ⟨T p.1, rfl, mem_graph_ofLinearMap.2 (mem_graph_ofLinearMap.1 h)⟩

/-- The embedding of linear maps into convex processes is injective. -/
theorem ofLinearMap_injective :
    Function.Injective (ofLinearMap : (U →ₗ[ℝ] X) → ConvexProcess U X) := fun T S h => by
  ext u
  have hu : (u, T u) ∈ (ofLinearMap S).graph := h ▸ mem_graph_ofLinearMap.2 rfl
  exact mem_graph_ofLinearMap.1 hu

end Sets

/-! ### The image of a function under a linear process -/

section Image

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- **The image of a function under a linear process is its image under the linear map.** This is
the identity `imageBifun`'s doc comment claims: Rockafellar's `Ff` at the indicator bifunction of
a linear transformation `T` is `T f` in the sense of §5.

The hypothesis that `f` is nowhere `⊥` is not a convenience: off the fibre of `T` the summand is
`⊤`, and `⊥ + ⊤ = ⊥` would drag the infimum down to `⊥` at every point of `X`. -/
theorem imageBifun_indicatorBifun_ofLinearMap (T : U →ₗ[ℝ] X) {f : U → EReal}
    (hbf : ∀ u, f u ≠ ⊥) :
    imageBifun (ofLinearMap T).indicatorBifun f = mapLin T f := by
  funext x
  rw [imageBifun_apply]
  refine le_antisymm (le_mapLin fun u hu => ?_) (le_iInf fun u => ?_)
  · refine (iInf_le _ u).trans (le_of_eq ?_)
    rw [indicatorBifun_apply, eval_ofLinearMap,
      indicatorFn_of_mem (Set.mem_singleton_iff.2 hu.symm), add_zero]
  · by_cases h : T u = x
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_mem (Set.mem_singleton_iff.2 h.symm), add_zero]
      exact mapLin_le h
    · rw [indicatorBifun_apply, eval_ofLinearMap,
        indicatorFn_of_notMem fun hc => h (Set.mem_singleton_iff.1 hc).symm,
        _root_.EReal.add_top_of_ne_bot (hbf u)]
      exact le_top

end Image

/-! ### The adjoint of a linear process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {T : U →ₗ[ℝ] X} {T' : Y →ₗ[ℝ] V}
  {y : Y} {v : V}

/-- On a linear process the supremum-oriented adjoint condition is an *equation*: the graph is a
subspace, so the inequality at `-u` reverses the one at `u`. -/
private theorem pairing_eq_of_forall_le (h : ∀ u : U, Bx (T u) y ≤ Bu u v) (u : U) :
    Bx (T u) y = Bu u v := by
  refine le_antisymm (h u) ?_
  have hn := h (-u)
  simp only [map_neg, LinearMap.neg_apply] at hn
  linarith

/-- The infimum-oriented mirror of `pairing_eq_of_forall_le`. -/
private theorem pairing_eq_of_forall_ge (h : ∀ u : U, Bu u v ≤ Bx (T u) y) (u : U) :
    Bx (T u) y = Bu u v := by
  refine le_antisymm ?_ (h u)
  have hn := h (-u)
  simp only [map_neg, LinearMap.neg_apply] at hn
  linarith

/-- A vector paired with every `⟨T u, y⟩` the way `T' y` is *is* `T' y`, when `Bu` separates the
points of `V`. -/
private theorem eq_of_forall_pairing_eq (hB : Bu.SeparatingRight)
    (hA : IsAdjointPair Bu Bx T T') (h : ∀ u : U, Bx (T u) y = Bu u v) : v = T' y := by
  refine sub_eq_zero.1 (hB _ fun u => ?_)
  rw [map_sub (Bu u) v (T' y), sub_eq_zero, ← hA u y, h u]

/-- **The adjoint of a linear process is a transpose of the linear map.** With `T'` adjoint to `T`
for the two pairings, the supremum-oriented adjoint of `T` read as a convex process is `T'` read as
a convex process.

`Bu.SeparatingRight` is what makes the answer unique; it is the same hypothesis under which the
transpose itself is unique (`IsAdjointPair.unique`). -/
theorem adjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    adjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  ext q
  constructor
  · intro h
    exact eq_of_forall_pairing_eq hB hA
      (pairing_eq_of_forall_le fun u => h (u, T u) (mem_graph_ofLinearMap.2 rfl))
  · intro h p hp
    have hp' : p.2 = T p.1 := mem_graph_ofLinearMap.1 hp
    have hq : q.2 = T' q.1 := mem_graph_ofLinearMap.1 h
    rw [hp', hq, hA p.1 q.1]

/-- **The infimum-oriented adjoint of a linear process is the same transpose.** The two
orientations disagree on a general convex process and agree on a linear one, because the defining
inequality holds in both directions on a subspace. -/
theorem coadjointProcess_ofLinearMap (hB : Bu.SeparatingRight) (hA : IsAdjointPair Bu Bx T T') :
    coadjointProcess Bu Bx (ofLinearMap T) = ofLinearMap T' := by
  ext q
  constructor
  · intro h
    exact eq_of_forall_pairing_eq hB hA
      (pairing_eq_of_forall_ge fun u => h (u, T u) (mem_graph_ofLinearMap.2 rfl))
  · intro h p hp
    have hp' : p.2 = T p.1 := mem_graph_ofLinearMap.1 hp
    have hq : q.2 = T' q.1 := mem_graph_ofLinearMap.1 h
    rw [hp', hq, hA p.1 q.1]

end Adjoint

end ConvexProcess

end Tdaf.ConvexAnalysis
