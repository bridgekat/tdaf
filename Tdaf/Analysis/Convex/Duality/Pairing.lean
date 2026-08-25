/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Polar
import Tdaf.Analysis.Convex.Closure

/-!
# Dual pairs

All of Rockafellar's duality theory — conjugacy (§12), support functions (§13), polarity (§14,
§15), the dual operations (§16), normal cones (§23) and the whole of Parts VI–VIII — is a theory
about a *pairing*

`B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`

between two real vector spaces, not about `ℝⁿ` and not about a space and its topological dual.
This file collects the vocabulary that the rest of the development is stated against.

## Main definitions

* `affineFn B y c` — the affine function `x ↦ ⟨x, y⟩ - c` determined by `y : F` and `c : ℝ`.
  Conjugacy is entirely a bookkeeping device for the affine functions below a given convex
  function, and these are they.
* `IsContinuousPairing B` — every `⟨·, y⟩` is continuous, so the pairing lands in the
  continuous dual of `E`; `continuous_pairing` is its unbundled field and `evalCLM B` is
  the resulting linear map `F →ₗ[ℝ] StrongDual ℝ E`.
* `IsCompatiblePairing B` — the topology on `E` is compatible with the pairing:
  `evalCLM B` is moreover *onto*, so the continuous linear functionals on `E` are exactly the
  `⟨·, y⟩`. This is the class all of Rockafellar's duality theory is stated over, and
  `exists_pairing_eq` is its unbundled field.
* `IsAdjointPair B B' A A'` — `A : E →ₗ[ℝ] G` and `A' : H →ₗ[ℝ] F` are adjoint with respect
  to the pairings `B` and `B'`.
* `prodPairing Bu Bx`, `negFst B` — the pairing of `U × X` with `V × Y`, and the sign
  flip on the first factor that the adjoint of a convex bifunction (§30) is stated against.

## Main results

* `convexFn_affineFn`, `closedFn_affineFn`, `affineFn_le_iff` — the affine functions
  of the pairing are closed, proper and convex, and `affineFn B y c ≤ f` is the inequality that the
  conjugate of `f` at `y` measures.
* `isAdjointPair_adjoint`, `isAdjointPair_topDualPairing` — the two instantiations that
  supply the adjoint datum: a real inner-product space paired with itself, and a topological vector
  space paired with its topological dual.
* `instIsContinuousPairingProd`, `instIsCompatiblePairingProd` — a product of continuous
  (resp. compatible) pairings is continuous (resp. compatible). This is what lets the bifunction
  conjugacy of §30 apply Fenchel–Moreau on `U × X` with hypotheses stated only about `U` and `X`.
* `isContinuousPairing_prodPairing_flip` — the same on the dual side, for the flipped product
  pairing that every closedness statement about an adjoint (§30, §37, §38) asks for.
* `exists_unique_dual_prod` — a continuous linear functional on `E × ℝ` is `(x, μ) ↦ y x + c μ`
  for a *unique* pair `(y, c)`. Mathlib does not provide this, and Fenchel–Moreau needs it twice:
  the separating functional of `E × ℝ` must be split into a horizontal part and a vertical
  coefficient before it can be recognised as an affine minorant.

Imported and used throughout, rather than proved here: `Tdaf.EReal.coe_sub_le_comm` from
`Tdaf/Order/EReal.lean` — `a - z ≤ w ↔ a - w ≤ z` for a *real* `a`, with no side condition.
`⟨x, y⟩ - f x` always has a real first argument, so that single unconditional fact is what lets the
whole of §12 be developed without properness hypotheses.

## Design notes

**There is no transpose.** For `A : E →ₗ[ℝ] G` between spaces carrying arbitrary pairings, `Aᵀ`
does not exist: Mathlib's `LinearMap.adjoint` needs `RCLike` inner-product spaces and finite
dimension, `ContinuousLinearMap.adjoint` needs completeness, and in general the transpose exists
only when `A` is weakly continuous, in which case it is extra *data*. `IsAdjointPair` follows
the shape of Mathlib's `LinearMap.IsAdjointPair`, which cannot be reused directly because it pairs
a module with *itself* (`B : M →ₗ[R] M →ₛₗ[I] M₃`), whereas a dual pair has two different spaces.

**Separating pairings are Mathlib's `LinearMap.Nondegenerate`**, which is by definition
`SeparatingLeft B ∧ SeparatingRight B`; no new predicate is introduced here.

**Whatever topology `E` already carries.** The duality theorems ask only that the continuous dual
of `E` be the `F` side of the pairing, which is the class `IsCompatiblePairing`; no change of
topology on `E` is involved. What the pairing is *for* is the freedom to let `E` and `F` be
different spaces, which §30 (adjoint bifunctions) and §33 (saddle-functions) need.

**Infinite dimensions cost hypotheses, not generality.** In the category of topological vector
spaces the arrows are the *continuous* linear maps, and a discontinuous linear functional is simply
not a morphism; likewise a subspace that is to behave like a finite-dimensional one has to be
assumed closed. Both are automatic in finite dimensions, which is why Rockafellar never writes
them. Where a statement of his fails here — `exists_affine_le_of_closed_proper` needs `f`
closed, `exists_ne_zero_forall_le_of_closure_ne_univ` needs `closure C ≠ univ` — the missing
hypothesis is always of one of those two kinds.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12 (the classification
  of the half-spaces of `Rⁿ⁺¹` preceding Theorem 12.1).
* H. H. Schaefer, *Topological Vector Spaces*, Springer, 1966, Chapter IV (dual pairs).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The affine functions of a pairing -/

section Affine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- The affine function `x ↦ ⟨x, y⟩ - c` of the pairing `B`, as an `EReal`-valued function.

These are Rockafellar's "upper half-spaces" of §12 read as functions: an affine function lies below
`f` exactly when its epigraph contains `epi f`, and the conjugate of `f` records, for each `y`, the
least `c` for which that happens. -/
noncomputable def affineFn (y : F) (c : ℝ) : E → EReal :=
  fun x => ((B x y : ℝ) : EReal) - (c : EReal)

variable {B}

@[simp] theorem affineFn_apply (y : F) (c : ℝ) (x : E) :
    affineFn B y c x = ((B x y : ℝ) : EReal) - (c : EReal) := rfl

/-- An affine function of the pairing takes only real values. -/
theorem affineFn_eq_coe (y : F) (c : ℝ) (x : E) :
    affineFn B y c x = ((B x y - c : ℝ) : EReal) := by
  rw [affineFn_apply, _root_.EReal.coe_sub]

/-- An affine function of the pairing never takes the value `⊥`. -/
theorem affineFn_ne_bot (y : F) (c : ℝ) (x : E) : affineFn B y c x ≠ ⊥ := by
  rw [affineFn_eq_coe]; exact _root_.EReal.coe_ne_bot _

/-- An affine function of the pairing never takes the value `⊤`. -/
theorem affineFn_ne_top (y : F) (c : ℝ) (x : E) : affineFn B y c x ≠ ⊤ := by
  rw [affineFn_eq_coe]; exact _root_.EReal.coe_ne_top _

/-- An affine function of the pairing is proper: it is finite everywhere. -/
theorem proper_affineFn (y : F) (c : ℝ) : Proper (affineFn B y c) :=
  ⟨⟨0, lt_top_iff_ne_top.2 (affineFn_ne_top y c 0)⟩, affineFn_ne_bot y c⟩

/-- A multiple of one affine function plus another is again an affine function. This is the
algebraic content of the "vertical half-space" step in the proof of Rockafellar's Theorem 12.1: a
vertical half-space is absorbed by adding a large multiple of it to a known affine minorant. -/
theorem affineFn_smul_add (a : ℝ) (y y' : F) (c c' : ℝ) (x : E) :
    affineFn B (a • y + y') (a * c + c') x = ((a * (B x y - c) + (B x y' - c') : ℝ) : EReal) := by
  rw [affineFn_eq_coe, map_add, map_smul, smul_eq_mul]
  congr 1
  ring

/-- An affine function of the pairing is convex. -/
theorem convexFn_affineFn (y : F) (c : ℝ) : ConvexFn (affineFn B y c) := by
  refine convexFn_of_epi_combo fun x x' μ ν hx hx' a b ha hb hab => ?_
  rw [affineFn_eq_coe, _root_.EReal.coe_le_coe_iff] at hx hx'
  rw [affineFn_eq_coe, _root_.EReal.coe_le_coe_iff, map_add, map_smul, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : a * (B x y - c) ≤ a * μ := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * (B x' y - c) ≤ b * ν := mul_le_mul_of_nonneg_left hx' hb
  have e1 : a * (B x y - c) = a * B x y - a * c := by ring
  have e2 : b * (B x' y - c) = b * B x' y - b * c := by ring
  have h3 : a * c + b * c = c := by linear_combination c * hab
  linarith

/-- **The inequality that the conjugate measures.** `affineFn B y c ≤ f` says exactly that `c`
dominates every value of `⟨x, y⟩ - f x`; `Tdaf.EReal.coe_sub_le_comm` is what makes the two forms
interchangeable with no properness hypothesis. -/
theorem affineFn_le_iff {f : E → EReal} {y : F} {c : ℝ} :
    affineFn B y c ≤ f ↔ ∀ x, ((B x y : ℝ) : EReal) - f x ≤ (c : EReal) :=
  forall_congr' fun _ => EReal.coe_sub_le_comm.symm

end Affine

/-! ### Affine functions and topology -/

section AffineTopology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {y : F} {c : ℝ}

/-- An affine function of the pairing is continuous as soon as the pairing is. -/
theorem continuous_affineFn (h : Continuous fun x => B x y) : Continuous (affineFn B y c) := by
  simp only [funext (affineFn_eq_coe (B := B) y c)]
  exact _root_.EReal.continuous_coe_iff.2 (h.sub continuous_const)

/-- An affine function of the pairing is lower semicontinuous as soon as the pairing is
continuous. -/
theorem lowerSemicontinuous_affineFn (h : Continuous fun x => B x y) :
    LowerSemicontinuous (affineFn B y c) := (continuous_affineFn h).lowerSemicontinuous

variable [IsTopologicalAddGroup E]

/-- An affine function of the pairing is a closed convex function as soon as the pairing is
continuous. In `WeakBilin B` — and hence in any finer topology — this holds for every `y`. -/
theorem closedFn_affineFn (h : Continuous fun x => B x y) : ClosedFn (affineFn B y c) :=
  (closedFn_iff_lowerSemicontinuous (affineFn_ne_bot y c)).2 (lowerSemicontinuous_affineFn h)

end AffineTopology

/-! ### Adjoint pairs -/

section AdjointPair

variable {E F G H K L : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup K] [Module ℝ K] [AddCommGroup L] [Module ℝ L]

/-- `A : E →ₗ[ℝ] G` and `A' : H →ₗ[ℝ] F` are *adjoint* with respect to the pairings
`B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` and `B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ` when `⟨A x, z⟩' = ⟨x, A' z⟩`.

This is the four-space version of Mathlib's `LinearMap.IsAdjointPair`, which pairs a module with
itself and therefore does not apply to a dual pair. It is *data*, not a property of `A`: between
arbitrarily paired spaces a transpose need not exist, and when it does it need not be unique unless
`B` is right-separating (`IsAdjointPair.unique`). -/
def IsAdjointPair (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) : Prop := ∀ x z, B' (A x) z = B x (A' z)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ} {B'' : K →ₗ[ℝ] L →ₗ[ℝ] ℝ}

/-- The identity is self-adjoint for any pairing. -/
theorem isAdjointPair_id : IsAdjointPair B B LinearMap.id LinearMap.id := fun _ _ => rfl

/-- Adjointness is symmetric under flipping both pairings: `A'` is adjoint to `A` for the flipped
pair. This is what makes the duality between `E` and `F` symmetric. -/
theorem IsAdjointPair.flip {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} (h : IsAdjointPair B B' A A') :
    IsAdjointPair B'.flip B.flip A' A := fun z x => (h x z).symm

/-- Adjoints compose contravariantly. -/
theorem IsAdjointPair.comp {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {C : G →ₗ[ℝ] K} {C' : L →ₗ[ℝ] H}
    (h : IsAdjointPair B B' A A') (h' : IsAdjointPair B' B'' C C') :
    IsAdjointPair B B'' (C ∘ₗ A) (A' ∘ₗ C') := fun x w => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h' (A x) w, h x (C' w)]

/-- Sums of adjoint pairs are adjoint. -/
theorem IsAdjointPair.add {A C : E →ₗ[ℝ] G} {A' C' : H →ₗ[ℝ] F} (h : IsAdjointPair B B' A A')
    (h' : IsAdjointPair B B' C C') : IsAdjointPair B B' (A + C) (A' + C') := fun x z => by
  simp only [LinearMap.add_apply, map_add, h x z, h' x z]

/-- Scalar multiples of adjoint pairs are adjoint. -/
theorem IsAdjointPair.smul {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} (a : ℝ)
    (h : IsAdjointPair B B' A A') : IsAdjointPair B B' (a • A) (a • A') := fun x z => by
  simp only [LinearMap.smul_apply, map_smul, h x z, smul_eq_mul]

/-- The adjoint is unique when the pairing `B` is right-separating — which is half of Mathlib's
`LinearMap.Nondegenerate`, the condition that makes `B` a genuine *dual pair*. -/
theorem IsAdjointPair.unique (hB : B.SeparatingRight) {A : E →ₗ[ℝ] G} {A' C' : H →ₗ[ℝ] F}
    (h : IsAdjointPair B B' A A') (h' : IsAdjointPair B B' A C') : A' = C' := by
  ext z
  refine sub_eq_zero.1 (hB _ fun x => ?_)
  rw [map_sub, sub_eq_zero, ← h x z, ← h' x z]

end AdjointPair

/-! ### Adjoint pairs from Mathlib's adjoints -/

section InnerProduct

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **A real Hilbert space paired with itself.** `ContinuousLinearMap.adjoint` supplies the adjoint
datum for a continuous linear map between complete real inner-product spaces. -/
theorem isAdjointPair_clm_adjoint [CompleteSpace E] [CompleteSpace G] (A : E →L[ℝ] G) :
    IsAdjointPair (innerₗ E) (innerₗ G) (A : E →ₗ[ℝ] G)
      ((ContinuousLinearMap.adjoint A : G →L[ℝ] E) : G →ₗ[ℝ] E) := fun x z => by
  simpa using (ContinuousLinearMap.adjoint_inner_right A x z).symm

/-- **Rockafellar's `ℝⁿ`.** In finite dimension every linear map has an adjoint, and
`LinearMap.adjoint` supplies the datum. -/
theorem isAdjointPair_adjoint [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] (A : E →ₗ[ℝ] G) :
    IsAdjointPair (innerₗ E) (innerₗ G) A (LinearMap.adjoint A) := fun x z => by
  simpa using (LinearMap.adjoint_inner_right A x z).symm

end InnerProduct

section TopDual

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]

/-- **A space paired with its topological dual.** For `topDualPairing` the adjoint datum of a
*continuous* linear map is precomposition; no completeness or finite-dimensionality is needed.

The adjoint datum is Mathlib's `ContinuousLinearMap.precomp ℝ A`, which is precomposition by `A`
as a *continuous* linear map of topological duals; `IsAdjointPair` only asks for the underlying
linear map. (The lemma to look for is `precomp`, not `dualMap`: `LinearMap.dualMap` is the
algebraic-dual version, and there is no `ContinuousLinearMap.dualMap`.) -/
theorem isAdjointPair_topDualPairing (A : E →L[ℝ] G) :
    IsAdjointPair (topDualPairing ℝ E).flip (topDualPairing ℝ G).flip (A : E →ₗ[ℝ] G)
      ((ContinuousLinearMap.precomp ℝ A : (G →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :
        (G →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ)) := fun _ _ => rfl

end TopDual

/-! ### Products of pairings -/

section Prod

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The pairing of `U × X` with `V × Y` determined by pairings of the factors. This is the pairing
that a convex bifunction `U → X → EReal` is conjugated against (§29–§30). -/
def prodPairing (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun p q => Bu p.1 q.1 + Bx p.2 q.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]; ring)

@[simp] theorem prodPairing_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (p : U × X) (q : V × Y) : prodPairing Bu Bx p q = Bu p.1 q.1 + Bx p.2 q.2 := rfl

/-- Flipping a product pairing flips the factors. -/
theorem prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (prodPairing Bu Bx).flip = prodPairing Bu.flip Bx.flip :=
  LinearMap.ext fun q => LinearMap.ext fun p => by
    simp

/-- The **sign flip on the first factor**: `negFst B p q = B (-p.1, p.2) q`.

This is the convention that Rockafellar's adjoint `F*` of a convex bifunction (§30) is stated
against; `prodPairing` alone has the wrong sign, and the mismatch is the source of the
several incompatible sign conventions Part VI juggles. -/
def negFst (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ :=
  B.comp (LinearMap.prodMap (-LinearMap.id) LinearMap.id)

@[simp] theorem negFst_apply (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) (p : U × X) (q : V × Y) :
    negFst B p q = B (-p.1, p.2) q := rfl

@[simp] theorem negFst_prodPairing_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (p : U × X) (q : V × Y) :
    negFst (prodPairing Bu Bx) p q = -Bu p.1 q.1 + Bx p.2 q.2 := by
  rw [negFst_apply, prodPairing_apply, map_neg, LinearMap.neg_apply]

/-- The sign flip is an involution. -/
@[simp] theorem negFst_negFst (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) : negFst (negFst B) = B :=
  LinearMap.ext fun p => LinearMap.ext fun q => by
    simp

/-- **The sign flip of a product pairing is a product pairing**, with the first factor negated.

`negFst_prodPairing_apply` says this pointwise, which is enough to rewrite inside a `conj` but not
enough to hand to instance search: the pairing classes are stated about a `LinearMap`, not about its
values. This is the equation of linear maps, and it is what lets `negFst (prodPairing Bu Bx)` — the
pairing Rockafellar's adjoint `F*` is conjugated against throughout §30 — inherit continuity and
compatibility from the factors instead of carrying them as hypotheses. -/
theorem negFst_prodPairing (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    negFst (prodPairing Bu Bx) = prodPairing (-Bu) Bx :=
  LinearMap.ext fun p => LinearMap.ext fun q => by
    simp

/-- Flipping the sign-flipped product pairing, in the form instance search meets it. -/
theorem negFst_prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (negFst (prodPairing Bu Bx)).flip = prodPairing (-Bu.flip) Bx.flip :=
  LinearMap.ext fun q => LinearMap.ext fun p => by
    simp

end Prod

/-! ### The topological dual of `E × ℝ`

Mathlib does not decompose a continuous linear functional on a product; Fenchel–Moreau needs it
twice, and so does the support-function theory of §13. -/

section ProdDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The decomposition of a continuous linear functional on `E × ℝ` into its horizontal part and its
vertical coefficient. -/
theorem dual_prod_apply (g : (E × ℝ) →L[ℝ] ℝ) (x : E) (μ : ℝ) :
    g (x, μ) = g.comp (ContinuousLinearMap.inl ℝ E ℝ) x + g (0, 1) * μ := by
  have h : ((x, μ) : E × ℝ) = (x, 0) + μ • ((0 : E), (1 : ℝ)) := by simp
  rw [h, map_add, map_smul, smul_eq_mul]
  simp [ContinuousLinearMap.inl, mul_comm]

/-- **A continuous linear functional on `E × ℝ` is `(x, μ) ↦ y x + c μ`, for a unique `(y, c)`.**

The horizontal part is the restriction along `ContinuousLinearMap.inl` and the vertical
coefficient is the value at `(0, 1)`. Rockafellar's classification of the closed half-spaces of
`E × ℝ` into *vertical* (`c = 0`), *upper* (`c < 0`) and *lower* (`c > 0`) — the paragraph
preceding Theorem 12.1 — is read off from this decomposition. -/
theorem exists_unique_dual_prod (g : (E × ℝ) →L[ℝ] ℝ) :
    ∃! p : (E →L[ℝ] ℝ) × ℝ, ∀ (x : E) (μ : ℝ), g (x, μ) = p.1 x + p.2 * μ := by
  refine ⟨(g.comp (ContinuousLinearMap.inl ℝ E ℝ), g (0, 1)), dual_prod_apply g, ?_⟩
  rintro ⟨y, c⟩ h
  have hc : c = g (0, 1) := by simpa using (h 0 1).symm
  subst hc
  have hy : y = g.comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    ext x
    have hx := h x 0
    simp only [mul_zero, add_zero] at hx
    simpa using hx.symm
  simp [hy]

end ProdDual


/-! ### Continuous and compatible topologies

Rockafellar works in `ℝⁿ`, where the continuous dual is the algebraic dual and there is nothing to
say. Here the topology on `E` has to be *compatible* with the pairing: the continuous linear
functionals on `E` must be exactly the `⟨·, y⟩`. That is one condition in each direction, and
Mathlib's way of packaging such a pair of conditions is a `Prop`-valued class whose second field
uses the first — the shape of `LinearMap.IsContPerfPair`, of which this is the weakening we need.

`IsContPerfPair` itself is *not* usable: it asks for joint continuity of `(x, y) ↦ B x y` (so `F`
would need a topology) and for bijectivity on both sides where surjectivity on one is enough, and
its only `topDualPairing` instance carries `[FiniteDimensional 𝕜 E] [T2Space E]`.

**The two conditions are two classes, and the split is not bookkeeping.** Half of the theory — the
conjugate is closed, the polar is closed, the subdifferential is closed, `f*` does not see `cl f` —
needs only that `⟨·, y⟩` be continuous. The decisive example is a Banach space `E` paired with
`F = StrongDual ℝ E` in the dual's **norm** topology: every `x : E` is a continuous functional on
`E'`, so `IsContinuousPairing` holds on that side, while surjectivity of the evaluation
`E → E''` is reflexivity and fails in general. "The conjugate is lower semicontinuous on the norm
dual" is therefore a theorem about the weaker class, and that setting is the most standard one in
the subject. `IsCompatiblePairing` extends it by the surjectivity, which is not even
expressible until the evaluation map exists — hence the order below: base class, then
`evalCLM`, then the extension. -/

section Compatible

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- The pairing `B` is **continuous** in its first variable: every `⟨·, y⟩` is a continuous linear
functional on `E`.

This is all that closedness needs — `closedFn_conj`, `conj_clFn`,
`isClosed_polarCone`, `isClosed_subgradient` — and it is strictly weaker than
`IsCompatiblePairing`: a Banach space and its norm-topology dual are a continuous pairing
in both directions, but compatible only on the side where the evaluation `E → E''` is onto, i.e.
only when `E` is reflexive. -/
class IsContinuousPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop where
  /-- Every `⟨·, y⟩` is continuous. -/
  continuous_left (B) (y : F) : Continuous fun x : E => B x y

/-- Every `⟨·, y⟩` is continuous. The unbundled form of
`IsContinuousPairing.continuous_left`. -/
theorem continuous_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] (y : F) :
    Continuous fun x : E => B x y :=
  IsContinuousPairing.continuous_left B y

/-- **The evaluation map of a continuous pairing**, `y ↦ ⟨·, y⟩`, into the continuous dual of `E`.

It is what turns the half-space characterisations of §11 — which quantify over `StrongDual ℝ E` —
into statements about `F`, and it is the map whose surjectivity `IsCompatiblePairing`
asserts. -/
def evalCLM (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] : F →ₗ[ℝ] StrongDual ℝ E where
  toFun y := ⟨B.flip y, continuous_pairing B y⟩
  map_add' y₁ y₂ := ContinuousLinearMap.ext fun x => map_add (B x) y₁ y₂
  map_smul' a y := ContinuousLinearMap.ext fun x => map_smul (B x) a y

/-- `evalCLM` evaluates as the pairing does. -/
@[simp] theorem evalCLM_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] (y : F) (x : E) :
    evalCLM B y x = B x y := rfl

/-- `B.flip.flip` is `B` definitionally, but not syntactically, and instance search does not unfold
`LinearMap.flip`. Every result stated for one side of the pairing and then used at `B.flip` —
`biconj_le_clFn`, `conjEquiv`, `isClosed_supportSet`, `polarCone_polarCone` —
asks for this instance, and without it the class would have to be passed by hand there.
`instIsCompatiblePairingFlipFlip` below is the same bridge for the stronger class, which §34 needs:
Theorem 34.1's lower half is its upper half applied to the swapped saddle-function, and the
swapped pairings are `Bx.flip` and `Bu.flip`. -/
instance instIsContinuousPairingFlipFlip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing B.flip.flip :=
  ‹IsContinuousPairing B›

/-- The topology on `E` is **compatible** with the pairing `B`: on top of continuity, `evalCLM`
is onto, so that every continuous linear functional on `E` is `⟨·, y⟩` for some `y : F`.

This is the hypothesis under which conjugacy is an involution — see `biconj_eq_clFn`. It says
nothing about *which* compatible topology `E` carries: the weak topology `σ(E, F)` is the coarsest
one, but a Banach space paired with its own dual satisfies it in the norm topology, and that is the
instance applications use. -/
class IsCompatiblePairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop
    extends IsContinuousPairing B where
  /-- Every continuous linear functional on `E` arises as some `⟨·, y⟩`. -/
  surjective_eval (B) : Function.Surjective (evalCLM B)

/-- Every continuous linear functional on `E` arises as some `⟨·, y⟩`. The unbundled form of
`IsCompatiblePairing.surjective_eval`. -/
theorem exists_pairing_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] (g : StrongDual ℝ E) :
    ∃ y : F, ∀ x, g x = B x y := by
  obtain ⟨y, hy⟩ := IsCompatiblePairing.surjective_eval B g
  exact ⟨y, fun x => by rw [← hy, evalCLM_apply]⟩

/-- The compatible counterpart of `instIsContinuousPairingFlipFlip`: `B.flip.flip` is `B`
definitionally, but instance search does not unfold `LinearMap.flip`. -/
instance instIsCompatiblePairingFlipFlip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing B.flip.flip :=
  ‹IsCompatiblePairing B›

/-! #### Negated pairings

`-B` is a pairing of the same two spaces, and Rockafellar's minimax development uses it constantly:
the concave argument of a saddle-function pairs against `-Bu`, so §36's Lagrangian correspondence
and §37's conjugates are all stated at negated pairings. These are instances rather than theorems
because every such statement would otherwise open with the same `have`. -/

omit [TopologicalSpace E] in
/-- Negation commutes with flipping. Needed because `(-B).flip` is not syntactically `-(B.flip)`,
so instance search cannot get from one to the other on its own. -/
theorem flip_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (-B).flip = -B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- A negated pairing is still continuous. -/
instance isContinuousPairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (-B) :=
  ⟨fun y => (continuous_pairing B y).neg⟩

/-- A negated pairing is still compatible: `g = ⟨·, y⟩` for `-B` exactly when `-g = ⟨·, y⟩`
for `B`. -/
instance isCompatiblePairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (-B) where
  surjective_eval := fun g => by
    obtain ⟨y, hy⟩ := exists_pairing_eq B (-g)
    refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
    have h : (-B) x y = -(B x y) := rfl
    rw [evalCLM_apply, h, ← hy]
    exact neg_neg _

/-- The flip of a negated pairing, which `flip_neg` puts back in reach of the instance above.
Every §34/§37 statement that conjugates on both sides of a negated pairing asks for this. -/
instance isCompatiblePairing_flip_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [TopologicalSpace F]
    [IsCompatiblePairing B.flip] : IsCompatiblePairing (-B).flip := by
  rw [flip_neg]
  infer_instance

end Compatible

section CompatibleInstances

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A topological vector space is compatibly paired with its own continuous dual, in its own
topology. This is the instance that Fenchel–Moreau is applied through in practice. -/
instance instIsCompatiblePairingTopDual :
    IsCompatiblePairing (topDualPairing ℝ E).flip where
  continuous_left y := y.continuous
  surjective_eval g := ⟨g, rfl⟩

/-- A normed space is *continuously* paired with its continuous dual in the **norm** topology of
that dual. Compatibility fails here unless `E` is reflexive — the dual of `StrongDual ℝ E` in its
norm topology is `E''`, not `E` — which is exactly why the closedness results are stated over
`IsContinuousPairing` and not over `IsCompatiblePairing`. -/
instance instIsContinuousPairingTopDualNorm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : IsContinuousPairing (topDualPairing ℝ E) :=
  ⟨fun x => (ContinuousLinearMap.apply ℝ ℝ x).continuous⟩

/-- **Every continuous linear functional on the dual of a finite-dimensional normed space is
evaluation at a point.** This is reflexivity, in the elementary form that the half-space arguments
of §18 and §25 need: an exposed point of a set of *functionals* is exposed by a functional on the
dual, and this lemma turns that functional back into a point of `E`.

It is `Module.evalEquiv` for the *continuous* dual, obtained by transporting along the
finite-dimensional identification of `E →ₗ[ℝ] ℝ` with `E →L[ℝ] ℝ`. Equivalently it says that
`topDualPairing ℝ E` — as opposed to its flip, `instIsCompatiblePairingTopDual` — is a compatible
pairing when `E` is finite-dimensional. -/
theorem exists_forall_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : StrongDual ℝ (StrongDual ℝ E)) :
    ∃ y : E, ∀ g : StrongDual ℝ E, Λ g = g y := by
  set φ : Module.Dual ℝ (Module.Dual ℝ E) :=
    (Λ : StrongDual ℝ E →ₗ[ℝ] ℝ).comp
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap with hφ
  refine ⟨(Module.evalEquiv ℝ E).symm φ, fun g => ?_⟩
  have h := Module.apply_evalEquiv_symm_apply (R := ℝ) (M := E) (g : E →ₗ[ℝ] ℝ) φ
  have hg : LinearMap.toContinuousLinearMap (g : E →ₗ[ℝ] ℝ) = g :=
    ContinuousLinearMap.ext fun x => rfl
  rw [hφ] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, ContinuousLinearMap.coe_coe] at h
  exact h.symm

/-- A **finite-dimensional** normed space is compatibly paired with its continuous dual from the
dual's side as well: by `exists_forall_apply_eq` every continuous linear functional on
`StrongDual ℝ E` is evaluation at a point of `E`.

Together with `instIsCompatiblePairingTopDual` this makes both `topDualPairing ℝ E` and its flip
compatible pairings, which is what lets the duality theory be applied on the dual side — a
conjugate `f*` treated as a function in its own right, with `f** = f`. -/
instance instIsCompatiblePairingTopDualFinite {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : IsCompatiblePairing (topDualPairing ℝ E) where
  continuous_left x := (ContinuousLinearMap.apply ℝ ℝ x).continuous
  surjective_eval Λ := by
    obtain ⟨y, hy⟩ := exists_forall_apply_eq Λ
    exact ⟨y, ContinuousLinearMap.ext fun g => (hy g).symm⟩

/-- A real Hilbert space is compatibly paired with itself by the inner product (Fréchet–Riesz). -/
instance instIsCompatiblePairingInner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : IsCompatiblePairing (innerₗ E) where
  continuous_left y := by simpa using (continuous_id.inner continuous_const : _)
  surjective_eval g := ⟨(InnerProductSpace.toDual ℝ E).symm g, by
    ext x
    rw [evalCLM_apply, innerₗ_apply_apply, real_inner_comm,
      InnerProductSpace.toDual_symm_apply]⟩

end CompatibleInstances

section ProdInstances

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [TopologicalSpace X]

/-- A product of continuous pairings is continuous. This is what lets §30's bifunction
conjugation — which pairs `U × X` with `V × Y` — inherit its topological hypotheses from the
factors. -/
instance instIsContinuousPairingProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu] [IsContinuousPairing Bx] :
    IsContinuousPairing (prodPairing Bu Bx) where
  continuous_left q := by
    simp only [prodPairing_apply]
    exact ((continuous_pairing Bu q.1).comp continuous_fst).add
      ((continuous_pairing Bx q.2).comp continuous_snd)

/-- A product of compatible pairings is compatible: a continuous linear functional on `U × X`
splits as `g (u, x) = g (u, 0) + g (0, x)`, and each summand is represented by the corresponding
factor. -/
instance instIsCompatiblePairingProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] :
    IsCompatiblePairing (prodPairing Bu Bx) where
  toIsContinuousPairing := instIsContinuousPairingProd Bu Bx
  surjective_eval g := by
    obtain ⟨v, hv⟩ := exists_pairing_eq Bu (g.comp (ContinuousLinearMap.inl ℝ U X))
    obtain ⟨y, hy⟩ := exists_pairing_eq Bx (g.comp (ContinuousLinearMap.inr ℝ U X))
    refine ⟨(v, y), ContinuousLinearMap.ext fun p => ?_⟩
    have hsplit : ((p.1, 0) : U × X) + ((0, p.2) : U × X) = p := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [evalCLM_apply, prodPairing_apply, ← hv, ← hy]
    simpa using (map_add g ((p.1, 0) : U × X) ((0, p.2) : U × X)).symm.trans (by rw [hsplit])

/-- The pairing §30's adjoint is conjugated against is continuous whenever the factors are. -/
instance instIsContinuousPairingNegFstProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu] [IsContinuousPairing Bx] :
    IsContinuousPairing (negFst (prodPairing Bu Bx)) := by
  rw [negFst_prodPairing]
  infer_instance

/-- The pairing §30's adjoint is conjugated against is compatible whenever the factors are.

Without this, every statement about `adjointBifun` — and so every §29–§30 surface statement — would
have to carry the two classes for `negFst (prodPairing Bu Bx)` explicitly, because instance search
cannot see past `negFst`. -/
instance instIsCompatiblePairingNegFstProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] :
    IsCompatiblePairing (negFst (prodPairing Bu Bx)) := by
  rw [negFst_prodPairing]
  infer_instance

end ProdInstances

section ProdDualInstances

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [TopologicalSpace Y]

/-- The pairing of the two *dual* factors is continuous whenever each of its two halves is. The
statement is not an instance because `(prodPairing Bu Bx).flip` is not syntactically a
`prodPairing`; `prodPairing_flip` is what turns it into one.

Every closedness statement about an adjoint — §30's `closedConcaveFn_graphFn_adjointBifun`, §37's
`closedBifun_inverseBifun_adjointBifun`, §38's `closedBifun_lowerAdjointBifun` — asks for this
instance on the dual side, and this is the only way to obtain it from hypotheses on the factors. -/
theorem isContinuousPairing_prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] :
    IsContinuousPairing (prodPairing Bu Bx).flip := by
  rw [prodPairing_flip]
  infer_instance

/-- The dual side of §30's pairing. Unlike `isContinuousPairing_prodPairing_flip` this *is* an
instance, because `(negFst (prodPairing Bu Bx)).flip` is a syntactic match — instance search meets
it in exactly this shape whenever a §30 statement conjugates on both sides. -/
instance instIsContinuousPairingNegFstProdFlip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] :
    IsContinuousPairing (negFst (prodPairing Bu Bx)).flip := by
  rw [negFst_prodPairing_flip]
  infer_instance

/-- The compatible counterpart of `instIsContinuousPairingNegFstProdFlip`. -/
instance instIsCompatiblePairingNegFstProdFlip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip] :
    IsCompatiblePairing (negFst (prodPairing Bu Bx)).flip := by
  rw [negFst_prodPairing_flip]
  infer_instance

end ProdDualInstances


end Tdaf.ConvexAnalysis
