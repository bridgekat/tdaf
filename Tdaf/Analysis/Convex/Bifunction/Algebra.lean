/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.ConcaveOps
import Tdaf.Analysis.Convex.Duality.Exact
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Optimization.Fenchel
import Tdaf.Analysis.Convex.Saddle.Defs

/-!
# The algebra of bifunctions

Rockafellar's §38. The adjoint of a convex bifunction generalizes the adjoint of a linear
transformation; this section generalizes the rest of the linear algebra — addition, scalar
multiplication, application to a vector, composition, and the inner product — and describes how
each behaves under taking adjoints.

| operation | here | linear-algebra analogue |
|---|---|---|
| `F₁ □ F₂` | `infConvBifun` | `A₁ + A₂` |
| `Fλ` | `smulRightBifun` | `λ A` |
| `Ff` | `imageBifun` | `A x` |
| `GF` | `compBifun` | `B ∘ A` |
| `F⁎`, `F⁎*` | `invBifun`, `lowerAdjointBifun` | `A⁻¹`, `(A⁻¹)*` |
| `⟨f, g⟩` | `fenchelSup` / `fenchelInf` / `HasFenchelPairing` | `⟨x, y⟩` |

## Main definitions

* `infConvBifun F₁ F₂` — Rockafellar's `F₁ □ F₂`, infimal convolution in the second variable.
* `supConvBifun G₁ G₂` — the concave mirror, supremal convolution in the second variable; this is
  the shape the adjoint of `F₁ □ F₂` takes.
* `smulRightBifun F l` — Rockafellar's `Fλ`.
* `imageBifun F f` — Rockafellar's `Ff`, and `concaveImageBifun` for the concave orientation.
* `compBifun G F` — Rockafellar's product `GF`, and `concaveCompBifun` for the concave one.
* `invBifun F` — Rockafellar's inverse `F⁎`, the *concave* bifunction `(F⁎ x)(u) = -(Fu)(x)`.
* `lowerAdjointBifun Bu Bx F` — Rockafellar's `F⁎*`.
* `fenchelSup B f g`, `fenchelInf B f g` — the two extrema whose common value is Rockafellar's
  inner product `⟨f, g⟩`; `HasFenchelPairing` says they agree, `fenchelPairing` is the value.

## Main results

* `domBifun_infConvBifun`, `convexBifun_infConvBifun`, `bracket_infConvBifun` — **Theorem 38.1**.
* `adjointBifun_infConvBifun`, `adjointBifun_infConvBifun_eq_supConvBifun` — **Theorem 38.2**:
  `(F₁ □ F₂)* = F₁* □ F₂*`, the right-hand `□` being supremal convolution of concave bifunctions.
* `convexBifun_smulRightBifun`, `bracket_smulRightBifun` — **Theorem 38.3**.
* `convexFn_imageBifun`, `conj_imageBifun`, `exists_conj_imageBifun_eq` — **Theorem 38.4**:
  `(Ff)* = F⁎* f*` with the infimum attained. `conj_imageBifun_of_bracket_eq_top` is
  Rockafellar's degenerate branch.
* `lowerAdjointBifun_lowerAdjointBifun_eq_clBifun`, `conj_imageBifun_lowerAdjointBifun`,
  `closedFn_imageBifun`, `exists_imageBifun_eq`, `conj_imageBifun_eq_clFn` —
  **Corollary 38.4.1**: for closed proper convex `F` and `f`, `Ff` is closed, the infimum defining
  it is attained, and `(Ff)* = cl (F⁎* f*)`.
* `convexBifun_compBifun`, `invBifun_compBifun` — **Theorem 38.5** and `(GF)⁎ = F⁎ G⁎`.
* `fenchelSup_le_fenchelInf` — weak duality for the inner product, with no hypothesis.
* `hasFenchelPairing_conj`, `fenchelPairing_conj` — **Lemma 38.6**: `⟨f*, g*⟩ = -⟨f, g⟩`.
* `hasFenchelPairing_adjointBifun`, `conj_imageBifun_eq_fenchelPairing` — **Corollary 38.7.1**:
  `⟨Ff, y⟩ = ⟨f, F* y⟩`.
* `fenchelSup_imageBifun_lowerAdjointBifun`,
  `fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun` — **Theorem 38.7**: adjoints move across
  the inner product.

## Design notes

**Every relative-interior hypothesis of §38 is an `IsExactSum`.** Rockafellar's conditions are
always "`ri (dom …)` and `ri (dom …)` have a point in common", which is Theorem 16.4; the D5
interface `IsExactSum` (`Duality/Exact.lean`) is exactly that conclusion, and `IsExactSum.of_relint`
(`Duality/Relint.lean`) produces it from the relative-interior condition in finite dimensions.
Stating §38 against `IsExactSum` keeps the whole section in layer A: no topology, no local
convexity, no finite dimension. Theorem 38.4 is Fenchel's duality theorem applied to `f` and the
concave function `u ↦ ⟨Fu, y⟩`, and nothing else.

**`IsExactSum` already carries Rockafellar's case distinction.** His proof of Theorem 38.4 splits
on whether `y ∈ dom F*`, i.e. on whether `u ↦ ⟨Fu, y⟩` is proper. `IsExactSum Bu f (-⟨F·, y⟩)`
demands `Proper (-⟨F·, y⟩)`, so the main branch is the only one it covers;
`conj_imageBifun_of_bracket_eq_top` states the other branch separately, and unconditionally.

**`F⁎*` is `-F*` read backwards, and that is a theorem, not the definition.**
`lowerAdjointBifun Bu Bx F v y = -(adjointBifun Bu Bx F y v)`, and
`lowerAdjointBifun_eq_concaveAdjointBifun` identifies it with the concave adjoint of the inverse
bifunction `F⁎` for the flipped pairings. Defining it by the reflection avoids carrying a second
adjoint through every statement, and the identification costs one `Prod.swap` reindexing.

**Corollary 38.4.1 needs no concave closure.** Rockafellar reads the biadjoint as `F** = cl F`
for the *concave* adjoint of `F*`, which would demand a concave `clBifun` before the corollary
could be stated. Taking `F⁎*` twice is the same computation with the two negations moved to the
outside, so `lowerAdjointBifun_lowerAdjointBifun_eq_clBifun` states `F⁎*⁎* = cl F` between
*convex* bifunctions, and the whole corollary stays in the convex world: it is Theorem 38.4 applied
to the pair `(F⁎*, f*)`, whose adjoint and conjugate are `F` and `f` again. The proof is one
`Prod.swap` reindexing and one `EReal.neg_add`.

**The inner product is two extrema, not one number.** Rockafellar leaves `⟨f, g⟩` *undefined* when
the sup side and the inf side differ, so the formalization keeps them apart: `fenchelSup`,
`fenchelInf`, and the predicate `HasFenchelPairing` that they agree. Weak duality
`fenchelSup ≤ fenchelInf` is unconditional, which makes every existence statement a single
inequality — that is how the existence half of Corollary 38.7.1 comes out free from Theorem 38.4.

**Rockafellar's domain-restricted extrema are the unrestricted ones for proper functions.** He
defines `⟨f, g⟩` by extrema over `dom f ∩ dom g*` so that improper `f` or `g` cause no `∞ - ∞`.
For proper `f` and proper concave `g` the excluded terms are `⊥` on the sup side and `⊤` on the inf
side, so they do not move the extremum, and the plain `⨆`/`⨅` definitions used here agree with his.
Every theorem below that needs the agreement carries the properness hypothesis explicitly.

**Theorem 38.2 needs no image-closedness.** Rockafellar proves it by closing the image of a sum
of epigraphs. Here `adjointBifun Bu Bx F y` is *by construction* `concaveConj Bu ⟨F·, y⟩`
(`adjointBifun_eq_concaveConj_bracket`), so Theorem 38.2 is Theorem 38.1 followed by the concave
orientation of Theorem 16.4 (`concaveConj_add_of_isExactSum`, `Duality/ConcaveOps.lean`), and the
closure step never arises. The price is that the hypothesis is an `IsExactSum` on the two brackets,
one for each `y`, rather than his single relative-interior condition; see the blocked note there.

**`HasFenchelPairing` is a `def` unfolding to an equation, so dot notation is unavailable.**
`h.conj` for `h : HasFenchelPairing B f g` resolves against `Eq`; the lemma is therefore named
`hasFenchelPairing_conj` rather than `HasFenchelPairing.conj`.

## What is not here

* The adjoint formula of **Theorem 38.3**, `(Fλ)* = F*λ`. It needs the concave mirror of the
  §16 row on right scalar multiplication, which the library does not have; by gotcha 9 the mirror
  is not obtainable by `simp`-normalising through negation.
* The adjoint formula of **Theorem 38.5**, `(GF)* = F* G*`. Unlike Theorem 38.3 this is *not*
  blocked on a concave mirror: `adjointBifun_eq_concaveConj_bracket` turns it into a minimax
  interchange between the convex `x ↦ ⨅ u, (⟨u, v⟩ + F u x)` and the concave `x ↦ ⟨G x, w⟩`, i.e.
  into Fenchel's duality theorem, exactly as `exists_pairing_sandwich` handles Theorem 39.8. What
  is missing is the `EReal` bookkeeping that splits the triple infimum defining `(GF)*(w)(v)` into
  `⨅ x, (f x - g x)`; a piece of work, not a missing prerequisite.
* **Corollary 38.2.1**, `(F₁ □ F₂)* = cl (F₁* □ F₂*)` with `F₁ □ F₂` closed. It is Theorem 38.2
  applied to the adjoints, which convolve in the *first* variable of the bifunction; `infConvBifun`
  convolves in the second, so the mirror operation and its adjoint formula have to be built first.
  Following Corollary 38.4.1, the right packaging is the convex one — a first-variable convolution
  of the `Fᵢ⁎*`, closed with `clBifun` — so no concave closure is needed for it either.
* **Corollary 38.5.1**, which is Theorem 38.5's adjoint formula applied to `F⁎*` and `G⁎*`
  together with `lowerAdjointBifun_lowerAdjointBifun_eq_clBifun`. It is blocked only on that
  formula.
* Corollary 38.7.2 and the co-finiteness discussion at the end of the section.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §38.
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Infimal convolution of bifunctions -/

section InfConvBifunDefs

variable {U X : Type*} [AddCommGroup X]

/-- Rockafellar's `F₁ □ F₂`: infimal convolution in the second variable, pointwise in the first.

This is the bifunction analogue of the *sum* of two linear transformations: if `Fᵢ` is the convex
indicator bifunction of `Aᵢ`, then `F₁ □ F₂` is the convex indicator bifunction of `A₁ + A₂`. -/
noncomputable def infConvBifun (F₁ F₂ : Bifun U X) : Bifun U X := fun u => infConv (F₁ u) (F₂ u)

/-- The defining equation of `infConvBifun`, slice by slice. -/
theorem infConvBifun_apply (F₁ F₂ : Bifun U X) (u : U) :
    infConvBifun F₁ F₂ u = infConv (F₁ u) (F₂ u) := rfl

/-- `□` is commutative, because infimal convolution is. -/
theorem infConvBifun_comm (F₁ F₂ : Bifun U X) : infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  funext fun u => infConv_comm (F₁ u) (F₂ u)

/-- `□` is associative, because infimal convolution is. -/
theorem infConvBifun_assoc (F₁ F₂ F₃ : Bifun U X) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  funext fun u => infConv_assoc (F₁ u) (F₂ u) (F₃ u)

omit [AddCommGroup X] in
/-- Membership in `domBifun` is nonemptiness of the effective domain of the slice. -/
theorem mem_domBifun_iff_dom_nonempty {F : Bifun U X} {u : U} :
    u ∈ domBifun F ↔ (dom (F u)).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, lt_top_iff_ne_top.2 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, hx.ne⟩

/-- **Rockafellar, Theorem 38.1**: `dom (F₁ □ F₂) = dom F₁ ∩ dom F₂`.

No hypothesis at all is needed: `dom (f □ g) = dom f + dom g` is unconditional, and a sum of sets
is nonempty exactly when both summands are. -/
theorem domBifun_infConvBifun (F₁ F₂ : Bifun U X) :
    domBifun (infConvBifun F₁ F₂) = domBifun F₁ ∩ domBifun F₂ := by
  ext u
  rw [Set.mem_inter_iff, mem_domBifun_iff_dom_nonempty, mem_domBifun_iff_dom_nonempty,
    mem_domBifun_iff_dom_nonempty, infConvBifun_apply, dom_infConv]
  exact Set.add_nonempty

end InfConvBifunDefs

section InfConvBifunConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F₁ F₂ : Bifun U X}

/-- The linear map `((u, x), y) ↦ (u, x - y)`, the left half of the change of variables that turns
a partial infimal convolution into a partial minimisation. -/
def infConvSubLeft (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X)
    (LinearMap.snd ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X - LinearMap.snd ℝ (U × X) X)

@[simp] theorem infConvSubLeft_apply (q : (U × X) × X) :
    infConvSubLeft U X q = (q.1.1, q.1.2 - q.2) := rfl

/-- The linear map `((u, x), y) ↦ (u, y)`, the right half of the same change of variables. -/
def infConvSubRight (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] :
    (U × X) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U X ∘ₗ LinearMap.fst ℝ (U × X) X) (LinearMap.snd ℝ (U × X) X)

@[simp] theorem infConvSubRight_apply (q : (U × X) × X) :
    infConvSubRight U X q = (q.1.1, q.2) := rfl

/-- The graph function of `F₁ □ F₂` is a *partial minimisation* of a convex function on
`(U × X) × X`: the infimum formula for `□`, read jointly in `(u, x)`. -/
theorem graphFn_infConvBifun (hb₁ : ∀ u x, F₁ u x ≠ ⊥) (hb₂ : ∀ u x, F₂ u x ≠ ⊥) (p : U × X) :
    graphFn (infConvBifun F₁ F₂) p
      = ⨅ y : X, (compLin (graphFn F₁) (infConvSubLeft U X)
          + compLin (graphFn F₂) (infConvSubRight U X)) (p, y) := by
  change infConv (F₁ p.1) (F₂ p.1) p.2 = _
  rw [infConv_apply (fun x => hb₁ p.1 x) (fun x => hb₂ p.1 x)]
  rfl

/-- **Rockafellar, Theorem 38.1**, first assertion: `F₁ □ F₂` is a convex bifunction.

Rockafellar reads `F₁ □ F₂` as a *partial* infimal convolution of the graph functions. Here that
is `convexFn_iInf_right` (Theorem 5.7) applied to the sum of the two graph functions after the
linear change of variables `((u, x), y) ↦ ((u, x - y), (u, y))`. -/
theorem convexBifun_infConvBifun (hb₁ : ∀ u x, F₁ u x ≠ ⊥) (hb₂ : ∀ u x, F₂ u x ≠ ⊥)
    (hF₁ : ConvexBifun F₁) (hF₂ : ConvexBifun F₂) : ConvexBifun (infConvBifun F₁ F₂) := by
  have hh : ConvexFn (compLin (graphFn F₁) (infConvSubLeft U X)
      + compLin (graphFn F₂) (infConvSubRight U X)) :=
    ConvexFn.add (convexFn_compLin _ hF₁) (convexFn_compLin _ hF₂)
      (fun q => hb₁ _ _) (fun q => hb₂ _ _)
  have hmin := convexFn_iInf_right hh
  have hgr : graphFn (infConvBifun F₁ F₂)
      = fun p : U × X => ⨅ y : X, (compLin (graphFn F₁) (infConvSubLeft U X)
          + compLin (graphFn F₂) (infConvSubRight U X)) (p, y) :=
    funext (graphFn_infConvBifun hb₁ hb₂)
  rw [ConvexBifun, hgr]
  exact hmin

omit [AddCommGroup U] [Module ℝ U] in
/-- **Rockafellar, Theorem 38.1**, the inner-product identity
`⟨(F₁ □ F₂) u, x*⟩ = ⟨F₁ u, x*⟩ + ⟨F₂ u, x*⟩`.

This is Theorem 16.4's unconditional row, `conj_infConv`, read slice by slice; no hypothesis is
needed, and Rockafellar's convention `∞ - ∞ = -∞` is `EReal`'s own `⊤ + ⊥ = ⊥`. -/
theorem bracket_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X) (u : U) :
    bracket Bx (infConvBifun F₁ F₂) u = bracket Bx F₁ u + bracket Bx F₂ u :=
  conj_infConv Bx (F₁ u) (F₂ u)

end InfConvBifunConvex

/-! ### Theorem 38.2: the adjoint of an infimal convolute -/

section SupConvBifun

variable {V Y : Type*} [AddCommGroup V]

/-- The concave analogue of `infConvBifun`: `(G₁ □ G₂) y = G₁ y □ G₂ y`, with the *supremal*
convolution in the second variable. Rockafellar writes `□` for both, the orientation of the
bifunction deciding which is meant. -/
noncomputable def supConvBifun (G₁ G₂ : Bifun Y V) : Bifun Y V := fun y => supConv (G₁ y) (G₂ y)

theorem supConvBifun_apply (G₁ G₂ : Bifun Y V) (y : Y) :
    supConvBifun G₁ G₂ y = supConv (G₁ y) (G₂ y) := rfl

end SupConvBifun

section Thm382

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Rockafellar, Theorem 38.2**: `(F₁ □ F₂)* = F₁* □ F₂*`, one dual vector at a time.

The whole theorem is the concave Theorem 16.4 (`concaveConj_add_of_isExactSum`) applied to the two
concave functions `u ↦ ⟨Fᵢ u, y⟩`: the adjoint at `y` *is* their concave conjugate
(`adjointBifun_eq_concaveConj_bracket`), and Theorem 38.1 says the bracket of `F₁ □ F₂` is their
sum. Rockafellar's opening paragraph — that `(F₁ □ F₂)*` is image-closed, so `(F₁ □ F₂)* y` is the
conjugate of `cl_u ⟨(F₁ □ F₂)u, y⟩` — is not needed here, because the adjoint is *defined* as that
conjugate.

The hypothesis is Rockafellar's exactly. Its two properness fields say that neither
`u ↦ ⟨Fᵢ u, y⟩` takes the value `+∞`, which is his branch condition
`y ∈ dom F₁* ∩ dom F₂*`; the exactness field is what his relative-interior condition supplies. -/
theorem adjointBifun_infConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F₁ F₂ : Bifun U X) {y : Y}
    (hex : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y))) :
    adjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = supConv (adjointBifun Bu Bx F₁ y) (adjointBifun Bu Bx F₂ y) := by
  have hadj : ∀ F : Bifun U X,
      adjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    fun F => funext fun v => adjointBifun_eq_concaveConj_bracket Bu Bx F y v
  have hbr : (fun u => bracket Bx (infConvBifun F₁ F₂) u y)
      = fun u => bracket Bx F₁ u y + bracket Bx F₂ u y :=
    funext fun u => congrFun (bracket_infConvBifun Bx F₁ F₂ u) y
  calc adjointBifun Bu Bx (infConvBifun F₁ F₂) y
      = concaveConj Bu (fun u => bracket Bx (infConvBifun F₁ F₂) u y) := hadj _
    _ = concaveConj Bu (fun u => bracket Bx F₁ u y + bracket Bx F₂ u y) := by rw [hbr]
    _ = supConv (concaveConj Bu fun u => bracket Bx F₁ u y)
          (concaveConj Bu fun u => bracket Bx F₂ u y) := concaveConj_add_of_isExactSum hex
    _ = supConv (adjointBifun Bu Bx F₁ y) (adjointBifun Bu Bx F₂ y) := by
          rw [hadj F₁, hadj F₂]

/-- **Rockafellar, Theorem 38.2** as an identity of bifunctions, `(F₁ □ F₂)* = F₁* □ F₂*`. -/
theorem adjointBifun_infConvBifun_eq_supConvBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F₁ F₂ : Bifun U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx F₁ u y))
      (fun u => -(bracket Bx F₂ u y))) :
    adjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (adjointBifun Bu Bx F₁) (adjointBifun Bu Bx F₂) :=
  funext fun y => adjointBifun_infConvBifun Bu Bx F₁ F₂ (hex y)

end Thm382

/-! ### `EReal` bookkeeping -/

section ERealAux

/-- Negation turns a difference around, provided neither of the two `∞ - ∞` collisions occurs. -/
private theorem neg_sub_swap {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) : -(a - b) = b - a := by
  rw [_root_.EReal.neg_sub (.inl ha) (.inr hb), sub_eq_add_neg, add_comm]

/-- The companion of `neg_sub_swap` with the other pair of side conditions. -/
private theorem neg_sub_swap' {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊥) : -(a - b) = b - a := by
  rw [_root_.EReal.neg_sub (.inr hb) (.inl ha), sub_eq_add_neg, add_comm]

/-- A constant that is not `⊤` moves inside a supremum. The hypothesis is exactly what rules out
`(⨆ i, u i) + ⊤` collapsing differently from `⨆ i, (u i + ⊤)`. -/
private theorem iSup_add_of_ne_top {ι : Sort*} [Nonempty ι] (u : ι → EReal) {c : EReal}
    (hc : c ≠ ⊤) : (⨆ i, u i) + c = ⨆ i, (u i + c) := by
  induction c with
  | bot => simp
  | coe r => exact Tdaf.EReal.iSup_add_coe u r
  | top => exact absurd rfl hc

/-- Splitting off one summand of a difference, when neither summand is `⊥`. -/
private theorem coe_sub_add (r : ℝ) {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    (r : EReal) - (a + b) = ((r : EReal) - b) - a := by
  have h : -(a + b) = -b + -a := by
    rw [add_comm a b]
    exact _root_.EReal.neg_add (.inl hb) (.inr ha)
  change (r : EReal) + -(a + b) = ((r : EReal) + -b) + -a
  rw [h, ← add_assoc]

/-- The mirror of `iSup_add_of_ne_top`, with the constant on the left. -/
private theorem add_iSup_of_ne_top {ι : Sort*} [Nonempty ι] (u : ι → EReal) {c : EReal}
    (hc : c ≠ ⊤) : c + (⨆ i, u i) = ⨆ i, (c + u i) := by
  rw [add_comm, iSup_add_of_ne_top u hc]
  exact iSup_congr fun i => add_comm _ _

/-- A constant that is not `⊥` moves inside a supremum, as a subtrahend. -/
private theorem iSup_sub_of_ne_bot {ι : Sort*} [Nonempty ι] (u : ι → EReal) {c : EReal}
    (hc : c ≠ ⊥) : (⨆ i, u i) - c = ⨆ i, (u i - c) :=
  iSup_add_of_ne_top u (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact hc)

/-- A constant that is not `⊤` turns an infimum into a supremum of differences. -/
private theorem sub_iInf_of_ne_top {ι : Sort*} [Nonempty ι] (u : ι → EReal) {c : EReal}
    (hc : c ≠ ⊤) : c - (⨅ i, u i) = ⨆ i, (c - u i) := by
  change c + -(⨅ i, u i) = _
  rw [Tdaf.EReal.neg_iInf, add_iSup_of_ne_top _ hc]
  rfl

/-- Adding a real constant cannot create `⊤`. -/
private theorem add_coe_ne_top {a : EReal} (ha : a ≠ ⊤) (c : ℝ) : a + (c : EReal) ≠ ⊤ := by
  induction a with
  | bot => simp
  | coe p => rw [← _root_.EReal.coe_add]; exact _root_.EReal.coe_ne_top _
  | top => exact absurd rfl ha

/-- Moving a subtrahend out of a difference of differences. -/
private theorem sub_sub_eq_add_sub {a b c : EReal} (ha : a ≠ ⊥) (hc : c ≠ ⊤) :
    b - (a - c) = (b + c) - a := by
  have h : -(a - c) = c - a := neg_sub_swap ha hc
  change b + -(a - c) = b + c + -a
  rw [h]
  change b + (c + -a) = b + c + -a
  rw [← add_assoc]

/-- A real constant minus an infimum is the supremum of the differences. -/
private theorem coe_sub_iInf {ι : Sort*} (r : ℝ) (u : ι → EReal) :
    (r : EReal) - ⨅ i, u i = ⨆ i, ((r : EReal) - u i) := by
  rw [sub_eq_add_neg, Tdaf.EReal.neg_iInf, add_comm, Tdaf.EReal.iSup_add_coe]
  exact iSup_congr fun i => by rw [add_comm, ← sub_eq_add_neg]

end ERealAux

/-! ### The image of a convex function under a bifunction -/

section ImageBifunDefs

variable {U X : Type*}

/-- `Prod.swap` as a linear map. -/
def swapLin (E G : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G] :
    E × G →ₗ[ℝ] G × E := LinearMap.prod (LinearMap.snd ℝ E G) (LinearMap.fst ℝ E G)

@[simp] theorem swapLin_apply {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G]
    [Module ℝ G] (q : E × G) : swapLin E G q = (q.2, q.1) := rfl

/-- Rockafellar's `Ff`, the **image of a convex function under a convex bifunction**:
`(Ff)(x) = ⨅ u, f u + (Fu)(x)`.

When `F` is the convex indicator bifunction of a linear map `A`, this is the image `Af` of `f`
under `A`. -/
noncomputable def imageBifun (F : Bifun U X) (f : U → EReal) : X → EReal :=
  fun x => ⨅ u, f u + F u x

theorem imageBifun_apply (F : Bifun U X) (f : U → EReal) (x : X) :
    imageBifun F f x = ⨅ u, f u + F u x := rfl

/-- The image of a concave function under a *concave* bifunction: the mirror of `imageBifun`, with
the infimum replaced by a supremum. Rockafellar's `Gg` for concave `G` and `g`. -/
noncomputable def concaveImageBifun (G : Bifun U X) (g : U → EReal) : X → EReal :=
  fun x => ⨆ u, g u + G u x

theorem concaveImageBifun_apply (G : Bifun U X) (g : U → EReal) (x : X) :
    concaveImageBifun G g x = ⨆ u, g u + G u x := rfl

end ImageBifunDefs

section ImageBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable {F : Bifun U X} {f : U → EReal}

/-- **Rockafellar, Theorem 38.4**, first assertion: `Ff` is a convex function on `X`.

`(u, x) ↦ f u + (Fu)(x)` is convex on `U × X` (Theorem 5.2), and `Ff` is its image under the
projection `(u, x) ↦ x` (Theorem 5.7). -/
theorem convexFn_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥)
    (hF : ConvexBifun F) (hf : ConvexFn f) : ConvexFn (imageBifun F f) := by
  have hh : ConvexFn (compLin f (LinearMap.snd ℝ X U) + compLin (graphFn F) (swapLin X U)) :=
    ConvexFn.add (convexFn_compLin _ hf) (convexFn_compLin _ hF)
      (fun q => hbf _) (fun q => hbF _ _)
  exact convexFn_iInf_right hh

end ImageBifunConvex

/-! ### The inverse of a bifunction and its adjoint -/

section InvBifun

variable {U X : Type*}

/-- The **inverse** `F⁎` of a convex bifunction `F` from `U` to `X`: the *concave* bifunction from
`X` to `U` given by `(F⁎ x)(u) = -(Fu)(x)`.

Rockafellar writes `F_*`; the sign flip is what turns the convex orientation into the concave one,
and it is what makes `(Ff)(x) = inf (f - F⁎ x)` agree with `⨅ u, f u + (Fu)(x)`. -/
noncomputable def invBifun (F : Bifun U X) : Bifun X U := fun x u => -(F u x)

@[simp] theorem invBifun_apply (F : Bifun U X) (x : X) (u : U) : invBifun F x u = -(F u x) := rfl

/-- Inversion is an involution. -/
theorem invBifun_invBifun (F : Bifun U X) : invBifun (invBifun F) = F :=
  funext fun _ => funext fun _ => neg_neg _

end InvBifun

section LowerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Rockafellar's `F⁎*`: the adjoint of the inverse of `F`, a *convex* bifunction from `V` to `Y`.

It is the reflected negative of the adjoint, `(F⁎* v)(y) = -(F* y)(v)`; that identity is
`lowerAdjointBifun_eq_concaveAdjointBifun`, and it is the reason `F⁎*` needs no separate
construction. -/
noncomputable def lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun V Y := fun v y => -(adjointBifun Bu Bx F y v)

@[simp] theorem lowerAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y = -(adjointBifun Bu Bx F y v) := rfl

/-- `F⁎*` really is the adjoint of the inverse bifunction `F⁎`: the concave adjoint of `F⁎`,
taken for the flipped pairings, is the reflected negative of `F*`.

Both sides are the same extremum over `U × X`, read once through `Prod.swap`; the only arithmetic
is `-(z + c) = -z + (-c)` for a real constant `c`, which needs no side condition. -/
theorem lowerAdjointBifun_eq_concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = concaveAdjointBifun Bu.flip Bx.flip (invBifun F) := by
  funext v y
  rw [lowerAdjointBifun_apply, adjointBifun_apply, Tdaf.EReal.neg_iInf, concaveAdjointBifun_apply]
  rw [← Function.Surjective.iSup_comp (f := (Prod.swap : X × U → U × X)) Prod.swap_surjective]
  refine iSup_congr fun q => ?_
  simp only [Prod.fst_swap, Prod.snd_swap, invBifun_apply, LinearMap.flip_apply]
  have h1 : -(F q.2 q.1 + ((Bu q.2 v - Bx q.1 y : ℝ) : EReal))
      = -(F q.2 q.1) + -(((Bu q.2 v - Bx q.1 y : ℝ) : EReal)) :=
    _root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _)) (.inr (_root_.EReal.coe_ne_bot _))
  have hr : (-(Bu q.2 v - Bx q.1 y) : ℝ) = Bx q.1 y - Bu q.2 v := by ring
  rw [h1, ← _root_.EReal.coe_neg, hr]

/-- `F⁎*` is a convex bifunction, with no hypothesis on `F`: it is the negative of the concave
`F*`, read through the swap of the two factors. -/
theorem convexBifun_lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (lowerAdjointBifun Bu Bx F) := by
  have hc : ConvexFn (fun p : Y × V => -(graphFn (adjointBifun Bu Bx F) p)) :=
    concaveFn_iff_convexFn_neg.1 (concaveFn_graphFn_adjointBifun Bu Bx F)
  exact convexFn_compLin (swapLin V Y) hc

end LowerAdjoint

/-! ### Theorem 38.4: the conjugate of an image -/

section ImageBifunConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

omit [AddCommGroup U] [Module ℝ U] in
/-- The conjugate of the image `Ff` is the supremum over `u` of the bracket `⟨Fu, y⟩` offset by
`f u`. This is the whole computational content of Rockafellar's proof of Theorem 38.4; what
remains there is Fenchel's duality theorem applied to the concave function `u ↦ ⟨Fu, y⟩`. -/
theorem conj_imageBifun_eq_iSup (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) (y : Y) :
    conj Bx (imageBifun F f) y = ⨆ u, (bracket Bx F u y - f u) := by
  have hstep : ∀ u : U, (⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)))
      = bracket Bx F u y - f u := by
    intro u
    have hnt : -(f u) ≠ ⊤ := by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact hbf u
    have hbody : ∀ x : X, ((Bx x y : ℝ) : EReal) - (f u + F u x)
        = (((Bx x y : ℝ) : EReal) - F u x) + -(f u) := fun x => by
      rw [coe_sub_add _ (hbf u) (hbF u x), sub_eq_add_neg]
    rw [iSup_congr hbody, ← iSup_add_of_ne_top _ hnt, ← sub_eq_add_neg]
    rfl
  rw [conj_apply]
  calc (⨆ x : X, (((Bx x y : ℝ) : EReal) - imageBifun F f x))
      = ⨆ x : X, ⨆ u : U, (((Bx x y : ℝ) : EReal) - (f u + F u x)) :=
        iSup_congr fun x => coe_sub_iInf _ _
    _ = ⨆ u : U, ⨆ x : X, (((Bx x y : ℝ) : EReal) - (f u + F u x)) := iSup_comm
    _ = ⨆ u : U, (bracket Bx F u y - f u) := iSup_congr hstep

omit [AddCommGroup U] [Module ℝ U] in
/-- The same supremum as `conj_imageBifun_eq_iSup`, turned around: when no bracket value is `⊤`,
`(Ff)*(y)` is minus the infimum of `f - ⟨F·, y⟩`, which is the primal side of Fenchel's duality
theorem. -/
theorem conj_imageBifun_eq_neg_iInf (hbF : ∀ u x, F u x ≠ ⊥) (hbf : ∀ u, f u ≠ ⊥) {y : Y}
    (hgt : ∀ u, bracket Bx F u y ≠ ⊤) :
    conj Bx (imageBifun F f) y = -(⨅ u, (f u - bracket Bx F u y)) := by
  rw [conj_imageBifun_eq_iSup hbF hbf y, Tdaf.EReal.neg_iInf]
  exact iSup_congr fun u => (neg_sub_swap (hbf u) (hgt u)).symm

/-- **Rockafellar, Theorem 38.4**: `(Ff)* = F⁎* f*`, in the pointwise form
`(Ff)*(y) = ⨅ v, f*(v) - (F* y)(v)`.

The hypothesis is that Fenchel's duality theorem applies to `f` and to the concave function
`u ↦ ⟨Fu, y⟩` — which is Rockafellar's "`ri (dom f)` and `ri (dom F)` have a point in common",
packaged as the D5 interface `IsExactSum` (Theorem 16.4). Note that `IsExactSum` already carries
`Proper (-⟨F·, y⟩)`, i.e. Rockafellar's side condition `y ∈ dom F*`; his degenerate branch is
`conj_imageBifun_of_bracket_eq_top`. -/
theorem conj_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = ⨅ v, (conj Bu f v - adjointBifun Bu Bx F y v) := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.proper_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hex'.proper_right.dom_nonempty
  have h1 : conj Bx (imageBifun F f) y = -(⨅ u, (f u - g u)) :=
    conj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt
  have h2 : (⨅ u, f u - g u) = ⨆ v, (concaveConj Bu g v - conj Bu f v) := fenchel_duality hex'
  have h4 : -(⨆ v, (concaveConj Bu g v - conj Bu f v))
      = ⨅ v, (conj Bu f v - concaveConj Bu g v) := by
    rw [Tdaf.EReal.neg_iSup]
    exact iInf_congr fun v =>
      neg_sub_swap' (concaveConj_ne_top hgd v) (conj_ne_bot hf.dom_nonempty v)
  rw [h1, h2, h4]
  exact iInf_congr fun v => by rw [adjointBifun_eq_concaveConj_bracket]

/-- **Rockafellar, Theorem 38.4**, the attainment clause: under the same hypothesis the infimum
defining `(F⁎* f*)(y)` is attained. -/
theorem exists_conj_imageBifun_eq (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    ∃ v : V, conj Bu f v - adjointBifun Bu Bx F y v = conj Bx (imageBifun F f) y := by
  set g : U → EReal := fun u => bracket Bx F u y with hg
  have hex' : IsExactSum Bu f (-g) := hex
  have hgt : ∀ u, g u ≠ ⊤ := by
    intro u hu
    exact hex'.proper_right.ne_bot u (by simp [Pi.neg_apply, hu])
  have hgd : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hex'.proper_right.dom_nonempty
  obtain ⟨v, hv⟩ := exists_concaveConj_sub_conj_eq hex'
  refine ⟨v, ?_⟩
  rw [conj_imageBifun_eq_neg_iInf hbF hf.ne_bot hgt, ← hv,
    neg_sub_swap' (concaveConj_ne_top hgd v) (conj_ne_bot hf.dom_nonempty v),
    adjointBifun_eq_concaveConj_bracket]

/-- **Rockafellar's degenerate branch of Theorem 38.4**, `y ∉ dom F*`: if the bracket `⟨Fu, y⟩` is
`+∞` at some `u` where `f` is finite, both sides of the theorem are `+∞`.

Rockafellar reaches this case from Theorem 7.2 — an improper concave function is `+∞` throughout
the relative interior of its domain — together with the relative-interior hypothesis. Stated as it
is here, with the finiteness of `f u₀` as an explicit hypothesis, it is unconditional. -/
theorem conj_imageBifun_of_bracket_eq_top (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {u₀ : U}
    {y : Y} (htop : bracket Bx F u₀ y = ⊤) (hfin : f u₀ ≠ ⊤) :
    conj Bx (imageBifun F f) y = ⊤ ∧
      imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y = ⊤ := by
  obtain ⟨r, hr⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf.ne_bot u₀) (lt_top_iff_ne_top.2 hfin)
  constructor
  · rw [conj_imageBifun_eq_iSup hbF hf.ne_bot y]
    refine eq_top_iff.2 (le_trans (le_of_eq ?_) (le_iSup _ u₀))
    rw [htop, hr]
    simp
  · have hbot : ∀ v : V, adjointBifun Bu Bx F y v = ⊥ := by
      intro v
      rw [adjointBifun_eq_concaveConj_bracket,
        concaveConj_of_eq_top (B := Bu) (g := fun u => bracket Bx F u y) htop]
    rw [imageBifun_apply]
    refine le_antisymm le_top (le_iInf fun v => ?_)
    have hv : conj Bu f v + lowerAdjointBifun Bu Bx F v y = ⊤ := by
      rw [lowerAdjointBifun_apply, hbot v, _root_.EReal.neg_bot,
        _root_.EReal.add_top_of_ne_bot (conj_ne_bot hf.dom_nonempty v)]
    exact le_of_eq hv.symm

end ImageBifunConj

/-! ### Corollary 38.4.1: the closed case -/

section Cor3841

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {f : U → EReal}

/-- The adjoint of a bifunction that is finite somewhere is nowhere `⊤`: the infimum defining it
is bounded above by the single term at `(u₀, x₀)`. -/
theorem adjointBifun_ne_top {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (v : V) : adjointBifun Bu Bx F y v ≠ ⊤ :=
  ne_top_of_le_ne_top (add_coe_ne_top hF _) (iInf_le _ (u₀, x₀))

/-- `F⁎*` never takes the value `-∞` when `F` is finite somewhere. This is the hypothesis
`hbF` of Theorem 38.4, for the bifunction `F⁎*`. -/
theorem lowerAdjointBifun_ne_bot {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y ≠ ⊥ := by
  rw [lowerAdjointBifun_apply]
  simpa using adjointBifun_ne_top hF Bu Bx y v

/-- **Rockafellar, Theorem 38.4** packaged as the identity `(Ff)* = F⁎* f*` rather than as a
formula for its values. The two sides differ only by `a - b = a + (-b)`. -/
theorem conj_imageBifun_eq_imageBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y := by
  rw [conj_imageBifun hbF hf hex]
  rfl

end Cor3841

section Cor3841Closed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X} {f : U → EReal}

/-- **`F⁎*⁎* = cl F`**, the biadjoint identity in the `F⁎*` packaging.

Rockafellar states the biadjoint as `F** = cl F` for the *concave* adjoint of `F*`; taking `F⁎*`
twice is the same computation with the two negations moved to the outside, so nothing concave has
to be built. Both sides are the same supremum over `V × Y`, read once through `Prod.swap`, and the
only arithmetic is `-(-z + c) = z - c` for a real constant `c`. -/
theorem lowerAdjointBifun_lowerAdjointBifun_eq_clBifun (hF : ConvexBifun F) :
    lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = clBifun F := by
  rw [← concaveAdjointBifun_adjointBifun_eq_clBifun (Bu := Bu) (Bx := Bx) hF]
  funext u x
  rw [lowerAdjointBifun_apply, adjointBifun_apply, Tdaf.EReal.neg_iInf, concaveAdjointBifun_apply,
    ← Function.Surjective.iSup_comp (f := (Prod.swap : V × Y → Y × V)) Prod.swap_surjective]
  refine iSup_congr fun q => ?_
  simp only [Prod.fst_swap, Prod.snd_swap, lowerAdjointBifun_apply, LinearMap.flip_apply]
  have h1 : -(-(adjointBifun Bu Bx F q.2 q.1) + ((Bu u q.1 - Bx x q.2 : ℝ) : EReal))
      = -(-(adjointBifun Bu Bx F q.2 q.1)) + -(((Bu u q.1 - Bx x q.2 : ℝ) : EReal)) :=
    _root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _)) (.inr (_root_.EReal.coe_ne_bot _))
  have hr : (-(Bu u q.1 - Bx x q.2) : ℝ) = Bx x q.2 - Bu u q.1 := by ring
  rw [h1, neg_neg, ← _root_.EReal.coe_neg, hr]

/-- **Rockafellar, Corollary 38.4.1**, the identity everything else follows from:
`(F⁎* f*)* = Ff` for a closed proper convex `F` and a closed proper convex `f`.

This is Theorem 38.4 applied to `F⁎*` and `f*`, whose own adjoint and conjugate are `F` and `f`
again (`lowerAdjointBifun_lowerAdjointBifun_eq_clBifun` and Fenchel–Moreau). Rockafellar's
relative-interior condition `ri (dom f*) ∩ ri (dom F⁎*) ≠ ∅` is the `IsExactSum` hypothesis, for
the same reason as in Theorem 38.4. -/
theorem conj_imageBifun_lowerAdjointBifun (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) x = imageBifun F f x := by
  have hbid : conj Bu.flip (conj Bu f) = f :=
    (biconj_eq_clFn (B := Bu) hf.convex).trans hf.closed
  have h := conj_imageBifun_eq_imageBifun (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (proper_conj hf) hex
  rw [h, lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF, hFcl.clBifun_eq, hbid]

/-- **Rockafellar, Corollary 38.4.1**, first assertion: `Ff` is closed. It is a conjugate. -/
theorem closedFn_imageBifun (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ClosedFn (imageBifun F f) := by
  have hfun : imageBifun F f
      = conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    funext fun x => (conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact closedFn_conj

/-- **Rockafellar, Corollary 38.4.1**, middle assertion: the infimum defining `(Ff)(x)` is
attained. This is Theorem 38.4's attainment clause read at `F⁎*` and `f*`. -/
theorem exists_imageBifun_eq (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    ∃ u : U, f u + F u x = imageBifun F f x := by
  have hbid : conj Bu.flip (conj Bu f) = f :=
    (biconj_eq_clFn (B := Bu) hf.convex).trans hf.closed
  have hlow : lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = F :=
    (lowerAdjointBifun_lowerAdjointBifun_eq_clBifun hF).trans hFcl.clBifun_eq
  obtain ⟨u, hu⟩ := exists_conj_imageBifun_eq (Bu := Bu.flip) (Bx := Bx.flip)
    (lowerAdjointBifun_ne_bot hFp Bu Bx) (proper_conj hf) hex
  refine ⟨u, ?_⟩
  have hadj : adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u = -(F u x) := by
    rw [← neg_neg (adjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) x u)]
    exact congrArg Neg.neg (congrFun (congrFun hlow u) x)
  rw [hbid, hadj] at hu
  have hval : f u - -(F u x) = f u + F u x := by
    change f u + -(-(F u x)) = f u + F u x
    rw [neg_neg]
  rw [← conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf hex, ← hu, hval]

variable [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] [IsCompatiblePairing Bx.flip]

/-- **Rockafellar, Corollary 38.4.1**, last assertion: `(Ff)* = cl (F⁎* f*)`.

`Ff` is the conjugate of `F⁎* f*`, so `(Ff)*` is its biconjugate, which is its closure. -/
theorem conj_imageBifun_eq_clFn (hF : ConvexBifun F) (hFcl : ClosedBifun F)
    {u₀ : U} {x₀ : X} (hFp : F u₀ x₀ ≠ ⊤) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (conj Bu f)
      (fun v => -(bracket Bx.flip (lowerAdjointBifun Bu Bx F) v x))) :
    conj Bx (imageBifun F f)
      = clFn (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) := by
  have hconv : ConvexFn (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    convexFn_imageBifun (lowerAdjointBifun_ne_bot hFp Bu Bx)
      (proper_conj hf).ne_bot (convexBifun_lowerAdjointBifun Bu Bx F) (convexFn_conj Bu f)
  have hfun : imageBifun F f
      = conj Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) :=
    funext fun x => (conj_imageBifun_lowerAdjointBifun hF hFcl hFp hf (hex x)).symm
  rw [hfun]
  exact biconj_eq_clFn (B := Bx.flip) hconv

end Cor3841Closed



/-! ### The inner product of a convex and a concave function -/

section FenchelPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- The **sup side** of Rockafellar's inner product `⟨f, g⟩` of a convex `f` on `E` and a concave
`g` on the paired space `F`: `sup_x {g*(x) - f(x)}`. -/
noncomputable def fenchelSup (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨆ x : E, (concaveConj B.flip g x - f x)

/-- The **inf side** of `⟨f, g⟩`: `inf_y {f*(y) - g(y)}`. -/
noncomputable def fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  ⨅ y : F, (conj B f y - g y)

theorem fenchelSup_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g = ⨆ x : E, (concaveConj B.flip g x - f x) := rfl

theorem fenchelInf_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelInf B f g = ⨅ y : F, (conj B f y - g y) := rfl

/-- Rockafellar's inner product `⟨f, g⟩` **exists** exactly when the two extrema agree; when they
do not, `⟨f, g⟩` is undefined. -/
def HasFenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : Prop :=
  fenchelSup B f g = fenchelInf B f g

/-- The value of Rockafellar's `⟨f, g⟩`, represented by the inf side.

Only under `HasFenchelPairing` is this Rockafellar's inner product;
`HasFenchelPairing.fenchelSup_eq` is the statement that the sup side then agrees. -/
noncomputable def fenchelPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) : EReal :=
  fenchelInf B f g

theorem HasFenchelPairing.fenchelSup_eq (h : HasFenchelPairing B f g) :
    fenchelSup B f g = fenchelPairing B f g := h

theorem fenchelPairing_eq_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelPairing B f g = fenchelInf B f g := rfl

/-- **Weak duality for the inner product**: the sup side never exceeds the inf side.

No hypothesis at all; both `∞ - ∞` collisions are absorbed on the correct side, exactly as in
`concaveConj_sub_conj_le_sub`. -/
theorem fenchelSup_le_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (g : F → EReal) :
    fenchelSup B f g ≤ fenchelInf B f g := by
  refine iSup_le fun x => le_iInf fun y => ?_
  have hsub : ∀ {p q r : EReal}, p ≤ q → p - r ≤ q - r := fun h => add_le_add h le_rfl
  have h1 : concaveConj B.flip g x ≤ ((B x y : ℝ) : EReal) - g y := concaveConj_le_sub B.flip g y x
  have h2 : ((B x y : ℝ) : EReal) - f x ≤ conj B f y := sub_le_conj B f x y
  calc concaveConj B.flip g x - f x
      ≤ (((B x y : ℝ) : EReal) - g y) - f x := hsub h1
    _ = (((B x y : ℝ) : EReal) - f x) - g y := by
        change ((B x y : ℝ) : EReal) + -(g y) + -(f x)
          = ((B x y : ℝ) : EReal) + -(f x) + -(g y)
        exact add_right_comm _ _ _
    _ ≤ conj B f y - g y := hsub h2

/-- A pairing exists as soon as the reverse of weak duality holds. -/
theorem hasFenchelPairing_of_le (h : fenchelInf B f g ≤ fenchelSup B f g) :
    HasFenchelPairing B f g :=
  le_antisymm (fenchelSup_le_fenchelInf B f g) h

end FenchelPairing

/-! ### Lemma 38.6: conjugation reverses the inner product -/

section Lemma386

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {g : F → EReal}

/-- One of the two outer steps of Rockafellar's four-term chain in Lemma 38.6: the inf side of
`⟨f*, g*⟩` is at most `-⟨f, g⟩` read on the sup side. It rests only on `f** ≤ f`. -/
theorem fenchelInf_conj_le_neg_fenchelSup (hf : Proper f) (hg : ProperConcave g) :
    fenchelInf B.flip (conj B f) (concaveConj B.flip g) ≤ -(fenchelSup B f g) := by
  have hneg : -(fenchelSup B f g) = ⨅ x : E, (f x - concaveConj B.flip g x) := by
    rw [fenchelSup_apply, Tdaf.EReal.neg_iSup]
    exact iInf_congr fun x =>
      neg_sub_swap' (concaveConj_ne_top hg.domConcave_nonempty x) (hf.ne_bot x)
  rw [hneg, fenchelInf_apply]
  exact iInf_mono fun x => add_le_add (biconj_le B f x) le_rfl

/-- The other outer step: `-⟨f, g⟩` read on the inf side is at most the sup side of `⟨f*, g*⟩`.
It rests only on `g ≤ g**`. -/
theorem neg_fenchelInf_le_fenchelSup_conj (hf : Proper f) (hg : ProperConcave g) :
    -(fenchelInf B f g) ≤ fenchelSup B.flip (conj B f) (concaveConj B.flip g) := by
  have hneg : -(fenchelInf B f g) = ⨆ y : F, (g y - conj B f y) := by
    rw [fenchelInf_apply, Tdaf.EReal.neg_iInf]
    exact iSup_congr fun y => neg_sub_swap (conj_ne_bot hf.dom_nonempty y) (hg.ne_top y)
  rw [hneg, fenchelSup_apply]
  exact iSup_mono fun y => add_le_add (le_biconcaveConj B.flip g y) le_rfl

/-- **Rockafellar, Lemma 38.6**: if `⟨f, g⟩` exists then so does `⟨f*, g*⟩`.

The proof is Rockafellar's chain `-⟨f, g⟩ ≤ ⟨f*, g*⟩_sup ≤ ⟨f*, g*⟩_inf ≤ -⟨f, g⟩` with the
middle link supplied by weak duality (`fenchelSup_le_fenchelInf`); when the two ends coincide all
four terms do.

Note the name: `HasFenchelPairing` is a `def` unfolding to an equation, so dot notation on a
hypothesis of that type would resolve against `Eq`. -/
theorem hasFenchelPairing_conj (hf : Proper f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    HasFenchelPairing B.flip (conj B f) (concaveConj B.flip g) := by
  refine hasFenchelPairing_of_le (le_trans (fenchelInf_conj_le_neg_fenchelSup hf hg) ?_)
  rw [h]
  exact neg_fenchelInf_le_fenchelSup_conj hf hg

/-- **Rockafellar, Lemma 38.6**, the value: `⟨f*, g*⟩ = -⟨f, g⟩`. -/
theorem fenchelPairing_conj (hf : Proper f) (hg : ProperConcave g)
    (h : HasFenchelPairing B f g) :
    fenchelPairing B.flip (conj B f) (concaveConj B.flip g) = -(fenchelPairing B f g) := by
  refine le_antisymm ?_ ?_
  · refine le_trans (fenchelInf_conj_le_neg_fenchelSup hf hg) (le_of_eq ?_)
    rw [fenchelPairing_eq_fenchelInf, ← h]
  · simp only [fenchelPairing_eq_fenchelInf]
    rw [← hasFenchelPairing_conj hf hg h]
    exact neg_fenchelInf_le_fenchelSup_conj hf hg

end Lemma386

/-! ### Corollary 38.7.1 and Theorem 38.7 -/

section Thm387

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- `⟨f*, g⟩` read on the sup side is minus `⟨f, g*⟩` read on the inf side.

This is pure sign bookkeeping, and it is the step that lets an adjoint move across the inner
product in Theorem 38.7. -/
theorem fenchelSup_conj_eq_neg_fenchelInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f h : E → EReal}
    (hd : (dom f).Nonempty) (hh : (domConcave h).Nonempty) :
    fenchelSup B.flip (conj B f) h = -(fenchelInf B f (concaveConj B h)) := by
  rw [fenchelSup_apply, fenchelInf_apply, Tdaf.EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [LinearMap.flip_flip]
  exact (neg_sub_swap (conj_ne_bot hd y) (concaveConj_ne_top hh y)).symm

end Thm387

section Thm387Bifun

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- The bracket `⟨Fu, y⟩` is below the concave biconjugate that `⟨f, F* y⟩` sees. This is
`le_biconcaveConj` after `adjointBifun_eq_concaveConj_bracket`, and it is what makes the existence
half of Corollary 38.7.1 free. -/
theorem bracket_le_concaveConj_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U) :
    bracket Bx F u y ≤ concaveConj Bu.flip (adjointBifun Bu Bx F y) u := by
  have hrw : adjointBifun Bu Bx F y = concaveConj Bu (fun u => bracket Bx F u y) :=
    funext fun v => adjointBifun_eq_concaveConj_bracket Bu Bx F y v
  rw [hrw]
  exact le_biconcaveConj Bu (fun u => bracket Bx F u y) u

/-- **Rockafellar, Corollary 38.7.1**, existence: `⟨f, F* y⟩` exists.

Weak duality gives one inequality for free; the other is Theorem 38.4 together with
`bracket_le_concaveConj_adjointBifun`. -/
theorem hasFenchelPairing_adjointBifun (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    HasFenchelPairing Bu f (adjointBifun Bu Bx F y) := by
  refine hasFenchelPairing_of_le ?_
  have h1 : fenchelInf Bu f (adjointBifun Bu Bx F y) = ⨆ u, (bracket Bx F u y - f u) := by
    rw [fenchelInf_apply, ← conj_imageBifun hbF hf hex, conj_imageBifun_eq_iSup hbF hf.ne_bot y]
  rw [h1, fenchelSup_apply]
  exact iSup_mono fun u =>
    add_le_add (bracket_le_concaveConj_adjointBifun Bu Bx F y u) le_rfl

/-- **Rockafellar, Corollary 38.7.1**: `⟨Ff, y⟩ = ⟨f, F* y⟩` — an adjoint moves across the inner
product.

The left-hand side is Rockafellar's `⟨Ff, x*⟩`, i.e. `(Ff)*(x*)`; the right-hand side is the
inner product of the convex `f` with the concave function `F* x*`. -/
theorem conj_imageBifun_eq_fenchelPairing (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    conj Bx (imageBifun F f) y = fenchelPairing Bu f (adjointBifun Bu Bx F y) :=
  conj_imageBifun hbF hf hex

end Thm387Bifun

section Thm387Main

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
variable {f : U → EReal} {g : X → EReal}

/-- The image `F* g*` of a concave conjugate under the adjoint is nowhere `⊤`, provided `F` is
finite at some `(u₀, x₀)` at which `g` is finite.

The bound is uniform in `y` because the two occurrences of `⟨x₀, y⟩` cancel: the pair
`(concaveConj_le_sub, iInf_le)` bounds every term of the supremum by
`F u₀ x₀ + ⟨u₀, v⟩ - g x₀`. -/
theorem concaveImageBifun_adjointBifun_ne_top (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥)
    (hgt : g x₀ ≠ ⊤) (v : V) :
    concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g) v ≠ ⊤ := by
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hgb (lt_top_iff_ne_top.2 hgt)
  have hbound : ∀ y : Y, concaveConj Bx g y + adjointBifun Bu Bx F y v
      ≤ F u₀ x₀ + ((Bu u₀ v - r : ℝ) : EReal) := by
    intro y
    have h1 : concaveConj Bx g y ≤ ((Bx x₀ y : ℝ) : EReal) - g x₀ := concaveConj_le_sub Bx g x₀ y
    have h2 : adjointBifun Bu Bx F y v ≤ F u₀ x₀ + ((Bu u₀ v - Bx x₀ y : ℝ) : EReal) :=
      iInf_le _ (u₀, x₀)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    rw [hr, ← _root_.EReal.coe_sub, add_left_comm, ← _root_.EReal.coe_add]
    congr 2
    ring
  exact ne_top_of_le_ne_top (add_coe_ne_top hF _) (iSup_le hbound)

/-- **Rockafellar, Theorem 38.7**, the "by definition" identity: `⟨F⁎* f*, g⟩` on the sup side is
minus `⟨f, F* g*⟩` on the inf side.

Both unwind to the same double extremum over `V × Y`, term by term
`⟨F* y, g*⟩ - f*(v) = (g*(y) + (F* y)(v)) - f*(v)`; the only content is the `EReal` bookkeeping,
and `iSup_comm`. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun (hf : Proper f) (hgd : (domConcave g).Nonempty)
    {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = -(fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g))) := by
  have hane : ∀ v : V, conj Bu f v ≠ ⊥ := fun v => conj_ne_bot hf.dom_nonempty v
  have hbne : ∀ y : Y, concaveConj Bx g y ≠ ⊤ := fun y => concaveConj_ne_top hgd y
  have hcne : ∀ (y : Y) (v : V), adjointBifun Bu Bx F y v ≠ ⊤ :=
    fun y v => adjointBifun_ne_top hF Bu Bx y v
  have hL : fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = ⨆ y : Y, ⨆ v : V,
        (concaveConj Bx g y - (conj Bu f v - adjointBifun Bu Bx F y v)) := by
    rw [fenchelSup_apply]
    refine iSup_congr fun y => ?_
    rw [LinearMap.flip_flip]
    have hH : imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) y
        = ⨅ v : V, (conj Bu f v - adjointBifun Bu Bx F y v) := rfl
    rw [hH, sub_iInf_of_ne_top _ (hbne y)]
  have hR : -(fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g)))
      = ⨆ v : V, ⨆ y : Y,
        ((concaveConj Bx g y + adjointBifun Bu Bx F y v) - conj Bu f v) := by
    rw [fenchelInf_apply, Tdaf.EReal.neg_iInf]
    refine iSup_congr fun v => ?_
    rw [neg_sub_swap (hane v)
        (concaveImageBifun_adjointBifun_ne_top Bu Bx hF hgb hgt v),
      concaveImageBifun_apply, iSup_sub_of_ne_bot _ (hane v)]
  rw [hL, hR, iSup_comm]
  exact iSup_congr fun v => iSup_congr fun y => sub_sub_eq_add_sub (hane v) (hcne y v)

omit [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X] in
/-- If `f` and `F` are both finite at some common `u₀`, the image `Ff` is not identically `⊤`. -/
theorem dom_imageBifun_nonempty (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f) {u₀ : U} {x₀ : X}
    (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) : (dom (imageBifun F f)).Nonempty := by
  refine ⟨x₀, ?_⟩
  have hle : imageBifun F f x₀ ≤ f u₀ + F u₀ x₀ := iInf_le _ u₀
  have hne : imageBifun F f x₀ ≠ ⊤ := ne_top_of_le_ne_top
    ((_root_.EReal.add_ne_top_iff_ne_top₂ (hf.ne_bot u₀) (hbF u₀ x₀)).2 ⟨hfu, hF⟩) hle
  exact lt_top_iff_ne_top.2 hne

/-- **Rockafellar, Theorem 38.7**, third equality: `⟨F⁎* f*, g⟩ = -⟨Ff, g*⟩`.

This is `fenchelSup_conj_eq_neg_fenchelInf` composed with Theorem 38.4. -/
theorem fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (hbF : ∀ u x, F u x ≠ ⊥) (hf : Proper f)
    (hgd : (domConcave g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelSup Bx.flip (imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f)) g
      = -(fenchelInf Bx (imageBifun F f) (concaveConj Bx g)) := by
  have h38 : conj Bx (imageBifun F f) = imageBifun (lowerAdjointBifun Bu Bx F) (conj Bu f) :=
    funext fun y => conj_imageBifun hbF hf (hex y)
  rw [← h38]
  exact fenchelSup_conj_eq_neg_fenchelInf Bx (dom_imageBifun_nonempty hbF hf hF hfu) hgd

/-- **Rockafellar, Theorem 38.7**: adjoints move across the inner product,
`⟨Ff, g*⟩ = ⟨f, F* g*⟩`.

Rockafellar's route is `⟨Ff, g*⟩ = ⟨f, F* g*⟩ = -⟨f*, F⁎ g⟩ = -⟨F⁎* f*, g⟩`, and the step he calls
remarkable is the last one, which he obtains "by definition" — here
`fenchelSup_imageBifun_lowerAdjointBifun`. The other bridge is Theorem 38.4 plus the sign
bookkeeping of `fenchelSup_conj_eq_neg_fenchelInf`. The relative-interior hypothesis of the book is
carried by `hex` (the `IsExactSum` interface of Theorem 16.4) together with the common point
`(u₀, x₀)` at which `f`, `F` and `g` are all finite.

The equation is stated between the two *inf* sides; each of them is Rockafellar's inner product as
soon as the corresponding pairing exists, which for the right-hand side is
`hasFenchelPairing_adjointBifun` in the specialisation of Corollary 38.7.1. -/
theorem fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (hbF : ∀ u x, F u x ≠ ⊥)
    (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Y, IsExactSum Bu f (fun u => -(bracket Bx F u y))) :
    fenchelInf Bx (imageBifun F f) (concaveConj Bx g)
      = fenchelInf Bu f (concaveImageBifun (adjointBifun Bu Bx F) (concaveConj Bx g)) := by
  have h1 := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg hbF hf hgd hF hfu hex
  rw [fenchelSup_imageBifun_lowerAdjointBifun hf hgd hF hgb hgt] at h1
  have h2 := congrArg (fun z : EReal => -z) h1
  simpa using h2.symm

end Thm387Main

/-! ### Theorem 38.3: right scalar multiplication -/

section SmulRightBifun

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X} {l : ℝ}

/-- Rockafellar's `Fλ`: right scalar multiplication of a bifunction,
`((Fλ) u)(x) = λ (Fu)(λ⁻¹ x)`, applied slice by slice. -/
noncomputable def smulRightBifun (F : Bifun U X) (l : ℝ) : Bifun U X := fun u => smulRight (F u) l

omit [AddCommGroup U] [Module ℝ U] in
/-- The defining equation of `smulRightBifun`, slice by slice. -/
theorem smulRightBifun_apply (F : Bifun U X) (l : ℝ) (u : U) :
    smulRightBifun F l u = smulRight (F u) l := rfl

/-- The linear map `(u, x) ↦ (l • u, x)`. -/
def scaleFst (X : Type*) [AddCommGroup X] [Module ℝ X] (l : ℝ) : U × X →ₗ[ℝ] U × X :=
  LinearMap.prod (l • LinearMap.fst ℝ U X) (LinearMap.snd ℝ U X)

@[simp] theorem scaleFst_apply (l : ℝ) (p : U × X) : scaleFst X l p = (l • p.1, p.2) := rfl

/-- The graph function of `Fλ` is a right scalar multiple of the graph function of `F`, read after
the shear `(u, x) ↦ (λu, x)`. This is the linear change of variables `(u, x, μ) ↦ (u, λx, λμ)` of
Rockafellar's proof. -/
theorem graphFn_smulRightBifun (hl : 0 < l) (F : Bifun U X) :
    graphFn (smulRightBifun F l) = smulRight (compLin (graphFn F) (scaleFst X l)) l := by
  funext p
  rw [smulRight_apply_pos hl]
  change smulRight (F p.1) l p.2 = _
  rw [smulRight_apply_pos hl, compLin_apply, scaleFst_apply]
  congr 2
  exact (smul_inv_smul₀ hl.ne' p.1).symm

/-- **Rockafellar, Theorem 38.3**, first assertion: `Fλ` is convex when `F` is. -/
theorem convexBifun_smulRightBifun (hl : 0 < l) (hF : ConvexBifun F) :
    ConvexBifun (smulRightBifun F l) := by
  rw [ConvexBifun, graphFn_smulRightBifun hl F]
  exact convexFn_smulRight l (convexFn_compLin _ hF)

omit [AddCommGroup U] [Module ℝ U] in
/-- **Rockafellar, Theorem 38.3**, the inner-product identity
`⟨(Fλ) u, x*⟩ = λ ⟨Fu, x*⟩`. It is Theorem 16.1's row `conj_smulRight`, slice by slice. -/
theorem bracket_smulRightBifun (hl : 0 < l) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    bracket Bx (smulRightBifun F l) u = fun y => (l : EReal) * bracket Bx F u y :=
  conj_smulRight hl Bx (F u)

end SmulRightBifun

/-! ### Theorem 38.5: composition -/

section CompBifun

section Defs

variable {U X Y : Type*}

/-- Rockafellar's product `GF` of bifunctions: `((GF) u)(y) = ⨅ x, (Fu)(x) + (Gx)(y)`.

When `F` and `G` are the convex indicator bifunctions of linear maps `A` and `B`, `GF` is the
indicator bifunction of `B ∘ A`. -/
noncomputable def compBifun (G : Bifun X Y) (F : Bifun U X) : Bifun U Y :=
  fun u y => ⨅ x, F u x + G x y

theorem compBifun_apply (G : Bifun X Y) (F : Bifun U X) (u : U) (y : Y) :
    compBifun G F u y = ⨅ x, F u x + G x y := rfl

/-- The composition of *concave* bifunctions: the same formula with a supremum. -/
noncomputable def concaveCompBifun (G : Bifun Y X) (F : Bifun X U) : Bifun Y U :=
  fun y u => ⨆ x, G y x + F x u

theorem concaveCompBifun_apply (G : Bifun Y X) (F : Bifun X U) (y : Y) (u : U) :
    concaveCompBifun G F y u = ⨆ x, G y x + F x u := rfl

/-- **Rockafellar, §38**: `(GF)⁎ = F⁎ G⁎`. The inverse of a product is the product of the inverses
in the opposite order, with the concave orientation. -/
theorem invBifun_compBifun (G : Bifun X Y) (F : Bifun U X) (hbF : ∀ u x, F u x ≠ ⊥)
    (hbG : ∀ x y, G x y ≠ ⊥) :
    invBifun (compBifun G F) = concaveCompBifun (invBifun G) (invBifun F) := by
  funext y u
  rw [invBifun_apply, compBifun_apply, Tdaf.EReal.neg_iInf, concaveCompBifun_apply]
  refine iSup_congr fun x => ?_
  have h : -(F u x + G x y) = -(F u x) + -(G x y) :=
    _root_.EReal.neg_add (.inl (hbF u x)) (.inr (hbG x y))
  rw [h, invBifun_apply, invBifun_apply, add_comm]

end Defs

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X} {G : Bifun X Y}

/-- The linear map `((u, y), x) ↦ (u, x)`. -/
def compLeft (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] U × X :=
  LinearMap.prod (LinearMap.fst ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X) (LinearMap.snd ℝ (U × Y) X)

@[simp] theorem compLeft_apply (q : (U × Y) × X) : compLeft U X Y q = (q.1.1, q.2) := rfl

/-- The linear map `((u, y), x) ↦ (x, y)`. -/
def compRight (U X Y : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] : (U × Y) × X →ₗ[ℝ] X × Y :=
  LinearMap.prod (LinearMap.snd ℝ (U × Y) X) (LinearMap.snd ℝ U Y ∘ₗ LinearMap.fst ℝ (U × Y) X)

@[simp] theorem compRight_apply (q : (U × Y) × X) : compRight U X Y q = (q.2, q.1.2) := rfl

/-- **Rockafellar, Theorem 38.5**, first assertion: `GF` is a convex bifunction.

`(u, x, y) ↦ (Fu)(x) + (Gx)(y)` is convex on `U × X × Y` (Theorem 5.2), and the graph function of
`GF` is its image under `(u, x, y) ↦ (u, y)` (Theorem 5.7). -/
theorem convexBifun_compBifun (hbF : ∀ u x, F u x ≠ ⊥) (hbG : ∀ x y, G x y ≠ ⊥)
    (hF : ConvexBifun F) (hG : ConvexBifun G) : ConvexBifun (compBifun G F) := by
  have hh : ConvexFn (compLin (graphFn F) (compLeft U X Y)
      + compLin (graphFn G) (compRight U X Y)) :=
    ConvexFn.add (convexFn_compLin _ hF) (convexFn_compLin _ hG)
      (fun q => hbF _ _) (fun q => hbG _ _)
  exact convexFn_iInf_right hh

end CompBifun

end Tdaf.ConvexAnalysis
