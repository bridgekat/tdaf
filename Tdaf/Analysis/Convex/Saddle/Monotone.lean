/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Prox
import Tdaf.Analysis.Convex.Saddle.Existence

/-!
# Corollaries 37.5.1 and 37.5.2: the geometry of the subdifferential of a saddle-function

Rockafellar's **Corollary 37.5.1**, homeomorphism clause — the graph of `∂K` is homeomorphic to
the space under `(u, v, u*, v*) ↦ (u - u*, v + v*)` — and **Corollary 37.5.2** — the mapping
`(u, v) ↦ {(-u*, v*) | (u*, v*) ∈ ∂K (u, v)}` is *maximal monotone*.

Both come from Theorem 37.5's condition (c), which says that `∂K` is the **partial inversion** of
`∂f`, where `f` is the graph function of the convex bifunction `F` representing the equivalence
class of `K` (`Saddle/Existence.lean`, `setOf_mem_saddleSubgradient_eq_preimage`). Composing that
with a geometric fact about `∂f` gives the corollary: Corollary 31.5.1 for the first,
Corollary 31.5.2 for the second, both in `Optimization/Prox.lean`.

## Main definitions

* `partialInvertEquiv` — the involution `((u, y), (v, x)) ↦ ((u, x), (v, y))` exchanging the
  second component of the argument of a relation with the second component of its value.
* `partialInvertNegHomeomorph` — the same exchange carrying condition (c)'s sign flip,
  `((u, y), (v, x)) ↦ ((u, x), (-v, y))`. It is linear, hence a homeomorphism.
* `saddleMonotoneRel Bu Bx K` — Rockafellar's `ρ`, the graph of
  `(u, y) ↦ {(-v, x) | (v, x) ∈ ∂K (u, y)}`.

## Main results

* `prodPairing_sub_partialInvertEquiv` — **partial inversion preserves the monotonicity form**.
* `isMonotoneRel_preimage_partialInvertEquiv`,
  `IsMaximalMonotoneRel.preimage_partialInvertEquiv` — monotonicity and maximal monotonicity
  therefore transfer across it.
* `saddleSubgradientHomeomorph`, `saddleSubgradientHomeomorph_apply` — **Corollary 37.5.1**,
  homeomorphism clause: `((u, y), (v, x)) ↦ (u - v, x + y)`.
* `isMaximalMonotoneRel_saddleMonotoneRel` — **Corollary 37.5.2**.

## Design notes

**Partial inversion needs no symmetry.** Monotonicity of a relation on `(U × Y) × (V × X)` is
measured by `prodPairing Bu Bx.flip`, and of a relation on `(U × X) × (V × Y)` by
`prodPairing Bu Bx`. Exchanging the two `X`/`Y` slots turns `Bx.flip (y₁ - y₂) (x₁ - x₂)` into
`Bx (x₁ - x₂) (y₁ - y₂)`, which is the same number by `LinearMap.flip_apply` — so the transfer
lemmas hold for arbitrary pairings, and the inner product enters only where Corollaries 31.5.1 and
31.5.2 do.

**Two maps, one idea.** `partialInvertEquiv` has no sign in it and `partialInvertNegHomeomorph`
does, because `ρ` already absorbs condition (c)'s sign into its own definition while the graph of
`∂K` does not. They are the two ways of writing the same identification, and the two corollaries
need one each.

**Self-pairing, not inner product.** Corollaries 31.5.1 and 31.5.2 are stated in
`Optimization/Prox.lean` for a symmetric positive definite self-pairing `B`, precisely so that
they can be used here: `U × X` carries the supremum norm and is not an `InnerProductSpace`, but
`prodPairing (innerₗ U) (innerₗ X)` is an `IsContinuousInnerPairing` on it
(`Duality/InnerPairing.lean`).

## What is not here

**Corollary 37.5.2's "in particular" clause**, that `(u, v) ↦ (-∇₁K (u, v), ∇₂K (u, v))` is
maximal monotone for a finite differentiable `K`. It is `isMaximalMonotoneRel_saddleMonotoneRel`
together with the statement that `∂K (u, v)` is the single point `(∇₁K, ∇₂K)`, which is Theorem
25.1's converse applied to each of the two slices — a `Saddle/Differential.lean` statement about
saddle-functions that this development does not have.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §37 (Corollary 37.5.1,
  Corollary 37.5.2).
-/

namespace Tdaf.ConvexAnalysis

/-! ### Partial inversion -/

section PartialInversion

variable {U V X Y : Type*}

/-- **Partial inversion**, Rockafellar's word in §37: the involution that exchanges the second
component of the argument of a relation with the second component of its value,
`((u, y), (v, x)) ↦ ((u, x), (v, y))`. Theorem 37.5 says that `∂K` and `∂f` are partial inversions
of each other. -/
def partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)) where
  toFun r := ((r.1.1, r.2.2), (r.2.1, r.1.2))
  invFun s := ((s.1.1, s.2.2), (s.2.1, s.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem partialInvertEquiv_apply (r : (U × Y) × (V × X)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (r.2.1, r.1.2)) := rfl

@[simp] theorem partialInvertEquiv_symm_apply (s : (U × X) × (V × Y)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))).symm s
      = ((s.1.1, s.2.2), (s.2.1, s.1.2)) := rfl

variable [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Partial inversion preserves the monotonicity form.** No symmetry is needed: the `X`-half of
the form on the source is `Bx.flip (y₁ - y₂) (x₁ - x₂)` and on the target `Bx (x₁ - x₂) (y₁ - y₂)`,
which is the same number. -/
theorem prodPairing_sub_partialInvertEquiv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (r s : (U × Y) × (V × X)) :
    prodPairing Bu Bx.flip (r.1 - s.1) (r.2 - s.2)
      = prodPairing Bu Bx ((partialInvertEquiv r).1 - (partialInvertEquiv s).1)
          ((partialInvertEquiv r).2 - (partialInvertEquiv s).2) := by
  simp only [partialInvertEquiv_apply, prodPairing_apply, LinearMap.flip_apply, map_sub,
    LinearMap.sub_apply]
  ring

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {σ : SetRel (U × X) (V × Y)}

/-- Monotonicity transfers across partial inversion. -/
theorem isMonotoneRel_preimage_partialInvertEquiv :
    IsMonotoneRel (prodPairing Bu Bx.flip) (partialInvertEquiv ⁻¹' σ)
      ↔ IsMonotoneRel (prodPairing Bu Bx) σ := by
  constructor
  · intro h p hp q hq
    have hp' : (partialInvertEquiv.symm p : (U × Y) × (V × X)) ∈ partialInvertEquiv ⁻¹' σ := by
      rwa [Set.mem_preimage, Equiv.apply_symm_apply]
    have hq' : (partialInvertEquiv.symm q : (U × Y) × (V × X)) ∈ partialInvertEquiv ⁻¹' σ := by
      rwa [Set.mem_preimage, Equiv.apply_symm_apply]
    have hkey := h _ hp' _ hq'
    rwa [prodPairing_sub_partialInvertEquiv, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at hkey
  · intro h r hr s hs
    rw [prodPairing_sub_partialInvertEquiv]
    exact h _ hr _ hs

/-- **Maximal** monotonicity transfers across partial inversion. This is the whole content of
Corollary 37.5.2 once Theorem 37.5 has identified `ρ` with `∂f`. -/
theorem IsMaximalMonotoneRel.preimage_partialInvertEquiv
    (h : IsMaximalMonotoneRel (prodPairing Bu Bx) σ) :
    IsMaximalMonotoneRel (prodPairing Bu Bx.flip) (partialInvertEquiv ⁻¹' σ) := by
  refine ⟨isMonotoneRel_preimage_partialInvertEquiv.2 h.1, fun τ hτ hsub => ?_⟩
  have hcomp : (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)))
      ⁻¹' (partialInvertEquiv.symm ⁻¹' τ) = τ := by
    ext r
    rw [Set.mem_preimage, Set.mem_preimage, Equiv.symm_apply_apply]
  have hτ' : IsMonotoneRel (prodPairing Bu Bx) (partialInvertEquiv.symm ⁻¹' τ) := by
    refine isMonotoneRel_preimage_partialInvertEquiv.1 ?_
    rw [hcomp]
    exact hτ
  have hsub' : σ ⊆ partialInvertEquiv.symm ⁻¹' τ := fun s hs =>
    hsub (by rwa [Set.mem_preimage, Equiv.apply_symm_apply])
  have hfin := h.2 _ hτ' hsub'
  intro r hr
  exact hfin (by rwa [Set.mem_preimage, Equiv.symm_apply_apply])

end PartialInversion

/-! ### The partial inversion of Theorem 37.5, as a homeomorphism -/

section Homeo

variable {U V X Y : Type*} [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace Y]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- **The map of Theorem 37.5's condition (c)**: partial inversion together with the sign flip
that (c) carries on the first dual component, `((u, y), (v, x)) ↦ ((u, x), (-v, y))`. It is its own
inverse up to that sign, and continuous both ways. -/
def partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y)) where
  toFun r := ((r.1.1, r.2.2), (-r.2.1, r.1.2))
  invFun s := ((s.1.1, s.2.2), (-s.2.1, s.1.2))
  left_inv r := by
    obtain ⟨⟨u, y⟩, ⟨v, x⟩⟩ := r
    simp
  right_inv s := by
    obtain ⟨⟨u, x⟩, ⟨v, y⟩⟩ := s
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem partialInvertNegHomeomorph_apply (r : (U × Y) × (V × X)) :
    (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (-r.2.1, r.1.2)) := rfl

end Homeo

/-! ### Rockafellar's `ρ` -/

section Rho

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Rockafellar's `ρ` of Corollary 37.5.2**: the subdifferential of `K` with the sign of its
concave half reversed, `ρ (u, y) = {(-v, x) | (v, x) ∈ ∂K (u, y)}`. The sign is what makes `ρ`
monotone rather than "monotone in one variable and antitone in the other". -/
def saddleMonotoneRel (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    SetRel (U × Y) (V × X) :=
  {r | (-r.2.1, r.2.2) ∈ saddleSubgradient Bu Bx.flip K r.1}

@[simp] theorem mem_saddleMonotoneRel {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
    {K : U × Y → EReal} {r : (U × Y) × (V × X)} :
    r ∈ saddleMonotoneRel Bu Bx K ↔ (-r.2.1, r.2.2) ∈ saddleSubgradient Bu Bx.flip K r.1 :=
  Iff.rfl

end Rho

/-! ### Corollaries 37.5.1 and 37.5.2 -/

section Corollaries

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

/-- Theorem 37.5's condition (c) as an equality of sets, with the identification written as the
homeomorphism `partialInvertNegHomeomorph`. -/
theorem setOf_mem_saddleSubgradient_eq_preimage_homeomorph (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    {r : (U × Y) × (V × X) | r.2 ∈ saddleSubgradient Bu Bx.flip K r.1}
      = (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) :=
  setOf_mem_saddleSubgradient_eq_preimage Bu Bx hF hcl hK

/-- **`ρ` is the graph of `∂f`, partially inverted.** This is Theorem 37.5's condition (c) with
the sign flip absorbed into `ρ`, which is why no sign survives on the right. -/
theorem saddleMonotoneRel_eq_preimage (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    saddleMonotoneRel Bu Bx K
      = (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) := by
  have h := setOf_mem_saddleSubgradient_eq_preimage Bu Bx hF hcl hK
  ext r
  have hr := Set.ext_iff.1 h (r.1, (-r.2.1, r.2.2))
  rw [Set.mem_ofPred_eq, Set.mem_preimage] at hr
  rw [mem_saddleMonotoneRel, Set.mem_preimage, hr]
  simp

end Corollaries

/-! ### The inner-product instance -/

section Inner

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {F : Bifun U X} {K : U × X → EReal}

/-- Theorem 37.5's condition (c) for a space paired with itself, where `Bx.flip` is `Bx`. -/
theorem setOf_mem_saddleSubgradient_innerL_eq_preimage (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    {r : (U × X) × (U × X) | r.2 ∈ saddleSubgradient (innerₗ U) (innerₗ X) K r.1}
      = (partialInvertNegHomeomorph : ((U × X) × (U × X)) ≃ₜ ((U × X) × (U × X)))
        ⁻¹' subgradientRel (prodPairing (innerₗ U) (innerₗ X)) (graphFn F) := by
  have h := setOf_mem_saddleSubgradient_eq_preimage_homeomorph (innerₗ U) (innerₗ X) hF hcl hK
  rwa [flip_eq_self] at h

/-- **Rockafellar, Corollary 37.5.1**, homeomorphism clause: the graph of `∂K` is homeomorphic to
`U × X` under `((u, y), (v, x)) ↦ (u - v, x + y)`.

Theorem 37.5 identifies that graph with the graph of `∂f` through the linear homeomorphism
`partialInvertNegHomeomorph`, and Corollary 31.5.1 (`subgradientRelHomeomorph`) maps the graph of
`∂f` onto `U × X` by `(z, z*) ↦ z + z*`. The composite is Rockafellar's map. -/
noncomputable def saddleSubgradientHomeomorph (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubgradient (innerₗ U) (innerₗ X) K r.1} ≃ₜ (U × X) :=
  (partialInvertNegHomeomorph.sets
      (setOf_mem_saddleSubgradient_innerL_eq_preimage hF hcl hK)).trans
    (subgradientRelHomeomorph (B := prodPairing (innerₗ U) (innerₗ X)) ⟨hF, hcl, hpr⟩)

@[simp] theorem saddleSubgradientHomeomorph_apply (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F)
    (r : ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubgradient (innerₗ U) (innerₗ X) K r.1}) :
    saddleSubgradientHomeomorph hF hcl hpr hK r
      = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) := by
  refine Prod.ext ?_ ?_ <;> simp [saddleSubgradientHomeomorph, sub_eq_add_neg]

/-- **Rockafellar, Corollary 37.5.2**: `ρ : (u, v) ↦ {(-u*, v*) | (u*, v*) ∈ ∂K (u, v)}` is a
maximal monotone mapping.

Theorem 37.5 makes `ρ` the partial inversion of `∂f`, partial inversion preserves the monotonicity
form, and `∂f` is maximal monotone by Corollary 31.5.2. -/
theorem isMaximalMonotoneRel_saddleMonotoneRel (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    IsMaximalMonotoneRel (prodPairing (innerₗ U) (innerₗ X))
      (saddleMonotoneRel (innerₗ U) (innerₗ X) K) := by
  have h := (isMaximalMonotoneRel_subgradientRel
    (B := prodPairing (innerₗ U) (innerₗ X)) ⟨hF, hcl, hpr⟩).preimage_partialInvertEquiv
  rw [flip_eq_self] at h
  rwa [saddleMonotoneRel_eq_preimage (innerₗ U) (innerₗ X) hF hcl hK]

end Inner

end Tdaf.ConvexAnalysis
