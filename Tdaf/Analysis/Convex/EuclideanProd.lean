/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.RelativeInterior
import Tdaf.Analysis.Convex.Subgradient.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concatenating coordinates: `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ`

`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (m + n))` are
different types, and a text written in `ℝⁿ` moves between them without comment. This module is that
move: the concatenation `(x, y) ↦ (x₁, …, x_m, y₁, …, y_n)`, together with the transport of the
three operations a convexity statement is made of — `conj`, `subgradient` and `ri`.

## Main definitions

* `euclideanProdIsometry m n` — the concatenation as a **linear isometry**
  `WithLp 2 (ℝᵐ × ℝⁿ) ≃ₗᵢ[ℝ] ℝᵐ⁺ⁿ`.
* `euclideanProdEquiv m n` — the same map as a **continuous linear equivalence**
  `ℝᵐ × ℝⁿ ≃L[ℝ] ℝᵐ⁺ⁿ` out of the plain product.

## Main results

* `euclideanProdEquiv_apply_castAdd`, `euclideanProdEquiv_apply_natAdd`,
  `euclideanProdEquiv_symm_apply` — the coordinates, which is what every consumer actually uses.
* `inner_euclideanProdEquiv` — concatenation adds the two inner products, so the pairing on the
  product that the backbone's bifunction theory is stated against (`prodPairing`) *is* the inner
  product of `ℝᵐ⁺ⁿ` read through the concatenation.
* `isAdjointPair_euclideanProdEquiv` — the previous line as the backbone's adjointness datum,
  which is the hypothesis every transport below discharges.
* `conj_comp_euclideanProdEquiv`, `subgradient_comp_euclideanProdEquiv` — a function on the
  product and its transport to `ℝᵐ⁺ⁿ` have the same conjugate and the same subgradients, read
  through the concatenation.
* `relint_image_euclideanProdEquiv`, `relint_image_euclideanProdEquiv_symm` — the relative
  interior commutes with the concatenation, in both directions.
* `subgradient_comp_linearEquiv` — the general lemma the subgradient transport is a case of: the
  companion of `conj_comp_linearEquiv` for the subdifferential.

## Design notes

**The isometry is out of `WithLp 2 (ℝᵐ × ℝⁿ)`, not out of `ℝᵐ × ℝⁿ`.** Mathlib's norm on a product
is the *supremum* norm (`gotchas.md` SET4), so concatenation of coordinates is not an isometry of
the plain product — `‖(x, y)‖ = max ‖x‖ ‖y‖` while `‖(x₁, …, y_n)‖ = (‖x‖² + ‖y‖²)^(1/2)`. The
Euclidean structure on the product is `WithLp 2`, and that is where the isometry lives. This is a
statement about `Fin m ⊕ Fin n ≃ Fin (m + n)` and `EuclideanSpace`, not about `Prod`.

**Everything else uses the plain product.** `conj`, `subgradient` and `ri` need only the linear
structure and the topology, and those the two norms share: `ℝᵐ × ℝⁿ ≃L[ℝ] ℝᵐ⁺ⁿ` is the object the
transport lemmas are stated against, so that no consumer has to move a `Convex`, a `ConvexFn` or an
`IsClosed` across a type synonym. `euclideanProdEquiv_eq_isometry` records that the two maps agree.

**The pairing is the point.** The backbone pairs `E × F` with itself through `prodPairing`, and
`ℝᵐ⁺ⁿ` with itself through its inner product; `inner_euclideanProdEquiv` says these are the same
form, and `isAdjointPair_euclideanProdEquiv` packages it as the datum of design decision D3. Every
transport below is `conj_comp_linearEquiv` or its subgradient analogue applied to that datum, which
is why none of them has a proof longer than three lines.

## What is not here

* **A transport for `ℝ` as a one-dimensional factor.** `ℝ` is not `EuclideanSpace ℝ (Fin 1)`, so
  `ℝⁿ × ℝ ≃ ℝⁿ⁺¹` needs `ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)` prepended. Nothing here obstructs it;
  it has simply had no consumer.
* **A general `WithLp` on sigma types.** `PiLp.sumPiLpEquivProdLpPiLp` and
  `LinearIsometryEquiv.piLpCongrLeft` are the two Mathlib facts this module is built from, and
  everything beyond them is coordinate bookkeeping for `Fin (m + n)`.
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The concatenation -/

section Defs

variable (m n : ℕ)

/-- **Concatenation of coordinates**, `(x, y) ↦ (x₁, …, x_m, y₁, …, y_n)`, as a linear isometry.

The source is `WithLp 2 (ℝᵐ × ℝⁿ)` and not `ℝᵐ × ℝⁿ`: Mathlib's product norm is the supremum norm,
and concatenation is an isometry only for the Euclidean one. See the module docstring. -/
noncomputable def euclideanProdIsometry :
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

/-- **Concatenation of coordinates** out of the plain product, which carries the supremum norm.
It is no longer an isometry, but it is still a linear homeomorphism, and that is all the transport
of `conj`, `subgradient` and `ri` needs. -/
noncomputable def euclideanProdEquiv :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin n))).symm.trans (euclideanProdIsometry m n).toContinuousLinearEquiv

variable {m n}

/-- The two concatenations are the same map. -/
theorem euclideanProdEquiv_eq_isometry
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    euclideanProdEquiv m n p = euclideanProdIsometry m n (WithLp.toLp 2 p) := rfl

@[simp] theorem euclideanProdEquiv_apply_castAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    euclideanProdEquiv m n p (Fin.castAdd n i) = p.1 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

@[simp] theorem euclideanProdEquiv_apply_natAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanProdEquiv m n p (Fin.natAdd m i) = p.2 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

theorem euclideanProdEquiv_symm_apply (z : EuclideanSpace ℝ (Fin (m + n))) :
    (euclideanProdEquiv m n).symm z =
      (WithLp.toLp 2 fun i => z (Fin.castAdd n i), WithLp.toLp 2 fun i => z (Fin.natAdd m i)) := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

@[simp] theorem euclideanProdEquiv_symm_apply_fst (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin m) : ((euclideanProdEquiv m n).symm z).1 i = z (Fin.castAdd n i) := by
  rw [euclideanProdEquiv_symm_apply]

@[simp] theorem euclideanProdEquiv_symm_apply_snd (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin n) : ((euclideanProdEquiv m n).symm z).2 i = z (Fin.natAdd m i) := by
  rw [euclideanProdEquiv_symm_apply]

/-- **Concatenation adds the two inner products.** This is the whole content of the transport: the
form the backbone pairs a product with, `prodPairing`, is the inner product of `ℝᵐ⁺ⁿ` read through
the concatenation. -/
theorem inner_euclideanProdEquiv
    (p q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) : ℝ)
      = inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_add]

end Defs

/-! ### The adjointness datum

The backbone keeps the transpose of a linear map as data (design decision D3). Concatenation is
its own transpose, in the sense that it carries `prodPairing` to the inner product, and that is
the datum every transport below consumes. -/

section Pairing

variable {m n : ℕ}

/-- The inner product of `ℝᵐ⁺ⁿ` pulled back along the concatenation is `prodPairing`. -/
theorem prodPairing_euclideanProdEquiv_symm (z : EuclideanSpace ℝ (Fin (m + n)))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n)))
        ((euclideanProdEquiv m n).symm z) q
      = innerₗ (EuclideanSpace ℝ (Fin (m + n))) z (euclideanProdEquiv m n q) := by
  have h := inner_euclideanProdEquiv ((euclideanProdEquiv m n).symm z) q
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Concatenation is an adjoint pair for the two pairings.** This is the hypothesis that
`conj_comp_linearEquiv` and `subgradient_comp_linearEquiv` take, and it is the only mathematical
input the transport has. -/
theorem isAdjointPair_euclideanProdEquiv :
    IsAdjointPair (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
      (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n))))
      ((euclideanProdEquiv m n).symm.toLinearEquiv : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
      ((euclideanProdEquiv m n).toLinearEquiv :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + n))) :=
  fun z q => prodPairing_euclideanProdEquiv_symm z q

end Pairing

/-! ### Transporting the subdifferential along a linear isomorphism

`Duality/Conjugate.lean` has `conj_comp_linearEquiv`, Rockafellar's substitution row for the
conjugate. The subdifferential obeys the same rule and has no such lemma; it is proved here,
in the generality of an arbitrary adjoint pair of isomorphisms, because that is what the
concatenation is an instance of. -/

section SubgradientTransport

variable {E F G H : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Precomposing with a linear isomorphism moves the subdifferential along the transpose.**
The companion of `conj_comp_linearEquiv` for `∂f`: if `A` and `A'` are adjoint isomorphisms, then
`∂(g ∘ A)(x) = A' (∂g (A x))`. -/
theorem subgradient_comp_linearEquiv {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (g : G → EReal) (x : E) :
    subgradient B (fun u => g (A u)) x = A' '' subgradient B' g (A x) := by
  ext y
  constructor
  · intro hy
    refine ⟨A'.symm y, fun w => ?_, A'.apply_symm_apply y⟩
    have hw : g (A x) + ((B (A.symm w - x) y : ℝ) : EReal) ≤ g (A (A.symm w)) := hy (A.symm w)
    rw [LinearEquiv.apply_symm_apply] at hw
    have h2 := hA (A.symm w - x) (A'.symm y)
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (A.symm w - x) = w - A x := by simp
    have h3 : A' (A'.symm y) = y := A'.apply_symm_apply y
    rw [h1, h3] at h2
    rw [h2]
    exact hw
  · rintro ⟨v, hv, rfl⟩
    intro w
    have hw : g (A x) + ((B' (A w - A x) v : ℝ) : EReal) ≤ g (A w) := hv (A w)
    have h2 := hA (w - x) v
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (w - x) = A w - A x := map_sub A w x
    rw [h1] at h2
    rw [← h2]
    exact hw

end SubgradientTransport

/-! ### The transport -/

section Transport

variable {m n : ℕ}

/-- **The conjugate transports along the concatenation.** A function `f` on `ℝᵐ × ℝⁿ` read as a
function on `ℝᵐ⁺ⁿ` has, as its conjugate for the inner product of `ℝᵐ⁺ⁿ`, the conjugate of `f` for
`prodPairing` read the same way. -/
theorem conj_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    conj (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = conj (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  conj_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The subdifferential transports along the concatenation.** -/
theorem subgradient_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) ×
    EuclideanSpace ℝ (Fin n) → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    subgradient (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = euclideanProdEquiv m n '' subgradient (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  subgradient_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The relative interior transports along the concatenation.** -/
theorem relint_image_euclideanProdEquiv
    {C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) :
    ri (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' ri C :=
  Convex.relint_image hC (euclideanProdEquiv m n).toLinearEquiv.toLinearMap

/-- **The relative interior transports along the concatenation**, read the other way. -/
theorem relint_image_euclideanProdEquiv_symm {D : Set (EuclideanSpace ℝ (Fin (m + n)))}
    (hD : Convex ℝ D) :
    ri ((euclideanProdEquiv m n).symm '' D) = (euclideanProdEquiv m n).symm '' ri D :=
  Convex.relint_image hD (euclideanProdEquiv m n).symm.toLinearEquiv.toLinearMap

/-- The closure transports along the concatenation, because it is a homeomorphism. -/
theorem closure_image_euclideanProdEquiv
    (C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    closure (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' closure C :=
  ((euclideanProdEquiv m n).toHomeomorph.image_closure C).symm

end Transport

end Tdaf.ConvexAnalysis
