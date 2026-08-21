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

* `Tdaf.affineFn B y c` — the affine function `x ↦ ⟨x, y⟩ - c` determined by `y : F` and `c : ℝ`.
  Conjugacy is entirely a bookkeeping device for the affine functions below a given convex
  function, and these are they.
* `Tdaf.IsAdjointPair B B' A A'` — `A : E →ₗ[ℝ] G` and `A' : H →ₗ[ℝ] F` are adjoint with respect
  to the pairings `B` and `B'`.
* `Tdaf.prodPairing Bu Bx`, `Tdaf.negFst B` — the pairing of `U × X` with `V × Y`, and the sign
  flip on the first factor that the adjoint of a convex bifunction (§30) is stated against.

## Main results

* `Tdaf.convexFn_affineFn`, `Tdaf.closedFn_affineFn`, `Tdaf.affineFn_le_iff` — the affine functions
  of the pairing are closed, proper and convex, and `affineFn B y c ≤ f` is the inequality that the
  conjugate of `f` at `y` measures.
* `Tdaf.EReal.coe_sub_le_comm` — `a - z ≤ w ↔ a - w ≤ z` for a *real* `a`, with no side condition.
  This single fact is what lets the whole of §12 be developed without properness hypotheses.
* `Tdaf.isAdjointPair_adjoint`, `Tdaf.isAdjointPair_topDualPairing` — the two instantiations that
  supply the adjoint datum: a real inner-product space paired with itself, and a topological vector
  space paired with its topological dual.
* `Tdaf.exists_unique_dual_prod` — a continuous linear functional on `E × ℝ` is `(x, μ) ↦ y x + c μ`
  for a *unique* pair `(y, c)`. Mathlib does not provide this, and Fenchel–Moreau needs it twice:
  the separating functional of `E × ℝ` must be split into a horizontal part and a vertical
  coefficient before it can be recognised as an affine minorant.

## Design notes

**There is no transpose.** For `A : E →ₗ[ℝ] G` between spaces carrying arbitrary pairings, `Aᵀ`
does not exist: Mathlib's `LinearMap.adjoint` needs `RCLike` inner-product spaces and finite
dimension, `ContinuousLinearMap.adjoint` needs completeness, and in general the transpose exists
only when `A` is weakly continuous, in which case it is extra *data*. `Tdaf.IsAdjointPair` follows
the shape of Mathlib's `LinearMap.IsAdjointPair`, which cannot be reused directly because it pairs
a module with *itself* (`B : M →ₗ[R] M →ₛₗ[I] M₃`), whereas a dual pair has two different spaces.

**Separating pairings are Mathlib's `LinearMap.Nondegenerate`**, which is by definition
`SeparatingLeft B ∧ SeparatingRight B`; no new predicate is introduced here.

**No weak topology.** An earlier design made the weak topology `σ(E, F)` — Mathlib's type synonym
`WeakBilin B` — the mechanism by which the duality theorems were to be proved and then transported
out. It is not needed: the duality theorems hold in whatever topology `E` already carries, provided
its continuous dual is the `F` side of the pairing, and that is stated as a hypothesis rather than
engineered by a change of type. What the pairing is *for* is the freedom to let `E` and `F` be
different spaces, which §30 (adjoint bifunctions) and §33 (saddle-functions) need.

**Infinite dimensions cost hypotheses, not generality.** In the category of topological vector
spaces the arrows are the *continuous* linear maps, and a discontinuous linear functional is simply
not a morphism; likewise a subspace that is to behave like a finite-dimensional one has to be
assumed closed. Both are automatic in finite dimensions, which is why Rockafellar never writes
them. Where a statement of his fails here — `Tdaf.exists_affine_le_of_closed_proper` needs `f`
closed, `Tdaf.exists_ne_zero_forall_le_of_closure_ne_univ` needs `closure C ≠ univ` — the missing
hypothesis is always of one of those two kinds.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12 (the classification
  of the half-spaces of `Rⁿ⁺¹` preceding Theorem 12.1).
* H. H. Schaefer, *Topological Vector Spaces*, Springer, 1966, Chapter IV (dual pairs).
-/

open Set

namespace Tdaf

/-! ### Subtracting from a real number in `EReal`

`⟨x, y⟩ - f x` is the expression conjugacy is built from, and its first argument is always a *real*
number. That is enough to make the facts below unconditional, which is why the conjugacy API can
avoid `∞ - ∞` side conditions almost everywhere. -/


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
`B` is right-separating (`Tdaf.IsAdjointPair.unique`). -/
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

/-- Precomposition with a continuous linear map, as a linear map of topological duals. Mathlib has
`LinearMap.dualMap` for algebraic duals but no continuous counterpart, so it is built here. -/
def dualPrecomp (A : E →L[ℝ] G) : (G →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) where
  toFun z := z.comp A
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem dualPrecomp_apply (A : E →L[ℝ] G) (z : G →L[ℝ] ℝ) (x : E) :
    dualPrecomp A z x = z (A x) := rfl

/-- **A space paired with its topological dual.** For `topDualPairing` the adjoint datum of a
*continuous* linear map is precomposition; no completeness or finite-dimensionality is needed. -/
theorem isAdjointPair_topDualPairing (A : E →L[ℝ] G) :
    IsAdjointPair (topDualPairing ℝ E).flip (topDualPairing ℝ G).flip (A : E →ₗ[ℝ] G)
      (dualPrecomp A) := fun _ _ => rfl

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
against; `Tdaf.prodPairing` alone has the wrong sign, and the mismatch is the source of the
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


end Tdaf
