/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.GaugeLike
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Surface.Rockafellar.Part2.Section07

/-!
# Rockafellar, §12: Conjugates of Convex Functions

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §12, pp. 102–111: the conjugacy
correspondence `f ↦ f*`, its involutivity on closed proper convex functions, and the elementary
table of operations under which the conjugate transforms by a change of variable. Every numbered
result of the section is here, stated in the book's own terms over `Rn n = ℝⁿ` and closed by
specialising the backbone.

## Contents

| label | declaration |
|---|---|
| Theorem 12.1 | `theorem_12_1` |
| Corollary 12.1.1 | `corollary_12_1_1` |
| Corollary 12.1.2 | `corollary_12_1_2` |
| Theorem 12.2 | `theorem_12_2_convex`, `theorem_12_2_closed`, `theorem_12_2_proper`, |
| | `theorem_12_2_conj_clFn`, `theorem_12_2_biconj` |
| Corollary 12.2.1 | `corollary_12_2_1` |
| Corollary 12.2.2 | `corollary_12_2_2` |
| Theorem 12.3 | `theorem_12_3` |
| Corollary 12.3.1 | `corollary_12_3_1` |
| Theorem 12.4 | `theorem_12_4_mem`, `theorem_12_4_involutive` |

## The section's definitions

* **The conjugate `f*`** (p. 104) is `conj (pairing n) f`, the backbone's `conj` against the
  Euclidean self-pairing. Rockafellar defines it by the same supremum, for an *arbitrary*
  `f : ℝⁿ → [-∞, +∞]`.
* **Fenchel's inequality** (p. 105) is `Proper.le_add_conj`, transcribed as
  `fenchel_inequality`. It is stated for a proper `f`, exactly as the book does, and the
  hypothesis is not removable: see the backbone's design note.
* **Symmetry with respect to a set `G` of orthogonal transformations** (p. 109) is transcribed
  literally as `SymmetricWrt`, with `IsOrthogonalEquiv` for "orthogonal linear transformation of
  `ℝⁿ` onto itself" — a linear bijection preserving the inner product.
* **The monotone conjugate `g⁺`** (p. 111) is `monotoneConjOrthant`, and the class of functions it
  acts on is `MonotoneOrthantFn`: a function that is `+∞` off the non-negative orthant (the book's
  §4 convention for "a function given on a set"), non-decreasing for the componentwise order,
  convex, closed and finite at the origin. `monotoneConjOrthant_apply` is Rockafellar's formula
  `g⁺(z*) = sup {⟨z, z*⟩ - g z ∣ z ≥ 0}`.

## Theorem 12.4 is printed with no proof

The book asserts it (p. 111) and supplies no argument at all. The proof below is direct: it avoids
the symmetrisation `f x = g (abs x)` that the surrounding prose suggests, and with it the whole
question of whether `x ↦ g (abs x)` is convex. Writing `K` for the non-negative orthant and `f`
for a function that is `+∞` off `K` and non-decreasing on `K`, the one fact that makes the
truncation `g⁺ = restrict K f*` harmless is

`conj_posPart` : `f* (y⁺) = f* y`,

where `y⁺` is the componentwise positive part. `≤` is `conj_mono_of_top_of_notMem`, monotonicity of
`f*` in `y`; `≥` zeroes, in any competitor `z ≥ 0`, the coordinates on which `y` is negative, which
lowers `f z` because `f` is non-decreasing and leaves `⟨z, y⁺⟩` unchanged (`maskNonneg`). With that,
the supremum defining `f**` may be taken over `K` alone, and Fenchel–Moreau finishes. This is the
same device as `iSup_sub_monotoneConj` in `Duality/GaugeLike.lean`, which is the `n = 1` case
(`MonotoneHalfLineFn`, `monotoneConj`); the two should be unified — see the report's friction list.

## What is not here

* **The classification of the closed half-spaces of `ℝⁿ⁺¹` into vertical, upper and lower**
  (pp. 102–103) — *omitted with a reason*. It is the prose that motivates the definition of `f*`;
  the backbone's proof of Theorem 12.1 (`exists_affineFn_le_of_lt`) carries out exactly this
  trichotomy internally, so transcribing it here would duplicate a completed argument rather than
  state a result.
* **The `W`-of-"best-inequalities" discussion** (pp. 105–106) — *omitted with a reason*. The claim
  that the maximal pairs of `{(f, g) | ⟨x, y⟩ ≤ f x + g y}` are exactly the mutually conjugate
  pairs is Corollary 12.2.1 restated; the book proves it by quoting what is `conj_le_iff` in the
  backbone, verbatim.
* **The worked conjugate pairs** (pp. 106–108): `exp` against the entropy function,
  `|ξ|^p / p` against `|ξ*|^q / q`, `-log`, `-(1 - ξ²)^(1/2)`, and the rest of the table —
  *deferred by scope*. These are unnumbered running text. The power pair is Corollary 15.3.2 and
  is already in the backbone (`monotoneConj_powHalfLine`, `pairing_le_rpow_mul_rpow`); the
  remainder are one-variable calculus computations with no downstream use in the book.
* **Tucker representations of a partial affine function** (p. 109) — *deferred by scope*. The
  dual pair of tableaux is a restatement of Theorem 12.3 in coordinates and depends on §1's
  Tucker machinery, which the surface's §1 records as deferred.
* **The pseudo-inverse `Q′` of a singular positive semi-definite `Q`** (p. 109) — *deferred by
  scope*. Rockafellar calls its verification "an exercise in linear algebra" and gives neither the
  construction nor the proof. `Q′` is the Moore–Penrose inverse; Mathlib has no Moore–Penrose
  inverse for a symmetric positive semi-definite operator, so the statement
  `h* = δ(· ∣ L) + (1/2)⟨·, Q′ ·⟩` cannot be made without first building it. That is spectral
  theory, not convex analysis.
* **Partial quadratic convex functions and their conjugates** (pp. 109–110) — *deferred by scope*,
  for the same reason: the class is defined through the elementary form
  `h z = (1/2) Σ λⱼ ζⱼ²` with `λⱼ ∈ [0, +∞]`, whose conjugate is the same expression with
  `λⱼ* = 1/λⱼ`, and the reduction of a general partial quadratic function to that form is the
  simultaneous diagonalisation `Q′` needs.
* **The one-dimensional monotone conjugate** (p. 110), `g⁺(ζ*) = sup {ζζ* - g ζ ∣ ζ ≥ 0}` for
  `g` on `[0, +∞)`, and the radial representation `f x = g (‖x‖)` that produces it — *omitted with
  a reason*: the one-dimensional monotone conjugate is already in the backbone as `monotoneConj`
  (`Duality/GaugeLike.lean`, §15), with its involution `monotoneConj_monotoneConj`, and
  duplicating it here would give two spellings of one notion. The radial representation itself is
  Theorem 15.3, in §15.
* **The concave companion `g⁻` of Theorem 12.4** (p. 111) — *deferred by scope*. Rockafellar
  asserts it in a parenthesis, with a proof sketch and no statement number of its own. It belongs
  with the concave conjugacy of §30 (`Duality/ConcaveConj.lean`), not with `conj`, and stating it
  here would fix a sign convention ahead of the section that owns it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Theorem 12.1 -/

/-- **Theorem 12.1.** A closed convex function `f` on `ℝⁿ` is the pointwise supremum
of the collection of all affine functions `h` such that `h ≤ f`.

An affine function on `ℝⁿ` is `x ↦ ⟨x, b⟩ - β`, indexed here by the pair `(b, β)`; that every affine
function has this form is the identification of `ℝⁿ` with its own dual that `pairing n` makes. -/
theorem theorem_12_1 (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

/-- **Corollary 12.1.1.** If `f` is any function from `ℝⁿ` to `[-∞, ∞]`, then
`cl (conv f)` is the pointwise supremum of the collection of all affine functions on `ℝⁿ`
majorized by `f`.

Specialises `eq_biSup_affineFn` again, with the book's own proof: `conj_convHullFn` and
`conj_clFn` say that the affine minorants of `cl (conv f)` are exactly those of `f`. -/
theorem corollary_12_1_1 (f : Rn n → EReal) :
    clFn (convHullFn f) = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x := by
  have hset : {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ clFn (convHullFn f)}
      = {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f} := by
    ext p
    simp only [Set.mem_ofPred_eq, ← conj_le_coe_iff, conj_clFn, conj_convHullFn]
  rw [eq_biSup_affineFn (B := pairing n) (convexFn_clFn (convexFn_convHullFn f))
    (closedFn_clFn _), hset]

/-- **Corollary 12.1.2.** Given any proper convex function `f` on `ℝⁿ`, there exists
some `b ∈ ℝⁿ` and `β ∈ ℝ` such that `f x ≥ ⟨x, b⟩ - β` for every `x`.

`cl f` is a closed proper convex function (Theorem 7.4), so `(cl f)*` is proper, and a point where
`(cl f)* = f*` is finite is exactly an affine minorant of `f`. The book states this corollary with
no proof of its own. -/
theorem corollary_12_1_2 (hf : ConvexFn f) (hp : Proper f) :
    ∃ (b : Rn n) (β : ℝ), ∀ x, ((inner ℝ x b : ℝ) : EReal) - (β : EReal) ≤ f x := by
  have hcl : ClosedProperConvexFn (clFn f) :=
    ⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp⟩
  obtain ⟨⟨b, hb⟩, -⟩ := proper_conj (B := pairing n) hcl
  rw [mem_dom, conj_clFn] at hb
  obtain ⟨β, hβ, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
  exact ⟨b, β, conj_le_coe_iff.1 hβ.le⟩

/-! ### Theorem 12.2: Fenchel–Moreau -/

/-- **Theorem 12.2**, first clause: the conjugate of a convex function is convex.

Convexity of `f` is not needed — `f*` is a pointwise supremum of affine functions whatever `f` is —
so the hypothesis of the book's statement is dropped. -/
theorem theorem_12_2_convex (f : Rn n → EReal) : ConvexFn (conj (pairing n) f) :=
  convexFn_conj _ f

/-- **Theorem 12.2**, second clause: the conjugate of a convex function is closed.

Again no hypothesis on `f` is needed. -/
theorem theorem_12_2_closed (f : Rn n → EReal) : ClosedFn (conj (pairing n) f) :=
  closedFn_conj

/-- **Theorem 12.2**, third clause: `f*` is proper if and only if `f` is.

Strengthens `proper_conj_iff`, which asks for `f` closed as well as convex: on `ℝⁿ` the closure of
a proper convex function is again proper (Theorem 7.4), so the hypothesis can be discharged, and
`conj_clFn` transports the conclusion back. -/
theorem theorem_12_2_proper (hf : ConvexFn f) : Proper (conj (pairing n) f) ↔ Proper f := by
  refine ⟨proper_of_proper_conj, fun hp => ?_⟩
  have h := proper_conj (B := pairing n)
    ⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp⟩
  rwa [conj_clFn] at h

/-- **Theorem 12.2**, fourth clause: `(cl f)* = f*`.

Convexity is not needed. -/
theorem theorem_12_2_conj_clFn (f : Rn n → EReal) :
    conj (pairing n) (clFn f) = conj (pairing n) f :=
  conj_clFn f

/-- **Theorem 12.2**, the Fenchel–Moreau theorem: `f** = cl f` for convex `f`.

On `ℝⁿ` the two sides of the pairing coincide, so `f**` is literally `conj (pairing n)` applied
twice; `conj_flip_pairing` is what removes the backbone's `B.flip`. -/
theorem theorem_12_2_biconj (hf : ConvexFn f) :
    conj (pairing n) (conj (pairing n) f) = clFn f := by
  simpa using biconj_eq_clFn (B := pairing n) hf

/-- **Corollary 12.2.1.** The conjugacy operation `f ↦ f*` induces a symmetric
one-to-one correspondence in the class of all closed proper convex functions on `ℝⁿ`.

"Symmetric" is `corollary_12_2_1_symm_apply` below: the inverse of the correspondence is the
correspondence itself. -/
noncomputable def corollary_12_2_1 (n : ℕ) :
    {f : Rn n → EReal // ClosedProperConvexFn f} ≃ {g : Rn n → EReal // ClosedProperConvexFn g} :=
  conjEquiv (pairing n)

@[simp] theorem corollary_12_2_1_apply (f : {f : Rn n → EReal // ClosedProperConvexFn f}) :
    ((corollary_12_2_1 n f : {g : Rn n → EReal // ClosedProperConvexFn g}) : Rn n → EReal)
      = conj (pairing n) f := rfl

/-- The correspondence of Corollary 12.2.1 is **symmetric**: its inverse is itself. -/
@[simp] theorem corollary_12_2_1_symm_apply
    (g : {g : Rn n → EReal // ClosedProperConvexFn g}) :
    (((corollary_12_2_1 n).symm g : {f : Rn n → EReal // ClosedProperConvexFn f}) : Rn n → EReal)
      = conj (pairing n) g := by
  simp [corollary_12_2_1, conjEquiv]

/-- **Corollary 12.2.2.** For any convex function `f` on `ℝⁿ`,
`f* x* = sup {⟨x, x*⟩ - f x ∣ x ∈ ri (dom f)}`.

The book's proof, transcribed: the right-hand side is `g*` for the function `g` that agrees with
`f` on `ri (dom f)` and is `+∞` elsewhere; `cl g = cl f` by Corollary 7.3.4, and `conj_clFn`
finishes. -/
theorem corollary_12_2_2 (hf : ConvexFn f) (y : Rn n) :
    conj (pairing n) f y = ⨆ x ∈ ri (dom f), ((inner ℝ x y : ℝ) : EReal) - f x := by
  have hdomconv : Convex ℝ (dom f) := hf.convex_dom
  have hsub : ri (dom f) ⊆ dom f := intrinsicInterior_subset
  have hg : ConvexFn (restrict (ri (dom f)) f) := hf.restrict hdomconv.relint
  have hdomg : dom (restrict (ri (dom f)) f) = ri (dom f) := by
    ext x
    by_cases hx : x ∈ ri (dom f)
    · simp only [mem_dom, restrict_of_mem hx]
      exact ⟨fun _ => hx, fun _ => hsub hx⟩
    · simp [hx]
  have hri : ri (dom (restrict (ri (dom f)) f)) = ri (dom f) := by
    rw [hdomg, hdomconv.relint_relint]
  have hcl : clFn (restrict (ri (dom f)) f) = clFn f :=
    corollary_7_3_4 hg hf hri fun x hx => restrict_of_mem (hri ▸ hx)
  have hconj : conj (pairing n) (restrict (ri (dom f)) f) = conj (pairing n) f := by
    rw [← conj_clFn (B := pairing n) (restrict (ri (dom f)) f), hcl, conj_clFn]
  rw [← hconj, conj_apply]
  refine le_antisymm (iSup_le fun x => ?_) (iSup₂_le fun x hx => ?_)
  · by_cases hx : x ∈ ri (dom f)
    · rw [restrict_of_mem hx]
      exact le_iSup₂ (f := fun x (_ : x ∈ ri (dom f)) =>
        ((inner ℝ x y : ℝ) : EReal) - f x) x hx
    · rw [restrict_of_notMem hx]
      simp
  · rw [← restrict_of_mem (f := f) hx]
    exact le_iSup (fun x : Rn n => ((pairing n x y : ℝ) : EReal)
      - restrict (ri (dom f)) f x) x

/-! ### Fenchel's inequality -/

/-- **Fenchel's inequality** (Rockafellar, §12, p. 105): `⟨x, x*⟩ ≤ f x + f* x*` for any proper
convex function `f` and its conjugate.

Properness is the book's hypothesis and it is not removable: for `f ≡ +∞` the right-hand side is `⊤
+ ⊥ = ⊥`. -/
theorem fenchel_inequality (hp : Proper f) (x y : Rn n) :
    ((inner ℝ x y : ℝ) : EReal) ≤ f x + conj (pairing n) f y :=
  hp.le_add_conj (B := pairing n) x y

/-! ### Theorem 12.3 -/

/-- **Theorem 12.3.** Let `h` be a convex function on `ℝⁿ` and
`f x = h (A (x - a)) + ⟨x, a*⟩ + α` with `A` a one-to-one linear transformation from `ℝⁿ` onto
`ℝⁿ`. Then `f* x* = h* (A*⁻¹ (x* - a*)) + ⟨x*, a⟩ + α*`, where `α* = -α - ⟨a, a*⟩`.

The book writes `A*⁻¹`; the backbone takes the adjoint as data, so `A'` and the adjointness relation
`⟨A x, z⟩ = ⟨x, A' z⟩` are hypotheses. Over `ℝⁿ` the adjoint exists and is unique, so nothing is
added — but it does have to be supplied. No convexity of `h` is needed. -/
theorem theorem_12_3 (A A' : Rn n ≃ₗ[ℝ] Rn n)
    (hA : ∀ x z : Rn n, (inner ℝ (A x) z : ℝ) = inner ℝ x (A' z))
    (h : Rn n → EReal) (a b : Rn n) (α : ℝ) (y : Rn n) :
    conj (pairing n) (fun x => h (A (x - a)) + ((inner ℝ x b : ℝ) : EReal) + (α : EReal)) y
      = conj (pairing n) h (A'.symm (y - b)) + ((inner ℝ a y : ℝ) : EReal)
        + ((-α - inner ℝ a b : ℝ) : EReal) :=
  conj_comp_affine (B := pairing n) (B' := pairing n) A A' (fun x z => hA x z) h a b α y

/-! ### Corollary 12.3.1 -/

/-- **An orthogonal linear transformation of `ℝⁿ` onto itself** (Rockafellar, §12, p. 109): a
linear bijection preserving the inner product. The bridge to the backbone's `IsAdjointPair` is
`orthogonalEquiv_adjoint` below, which is Rockafellar's `A*⁻¹ = A`. -/
def IsOrthogonalEquiv (A : Rn n ≃ₗ[ℝ] Rn n) : Prop :=
  ∀ x y : Rn n, (inner ℝ (A x) (A y) : ℝ) = inner ℝ x y

/-- The bridge for `IsOrthogonalEquiv`: for an orthogonal `A` the adjoint `A*` is `A⁻¹`. -/
theorem orthogonalEquiv_adjoint {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A) (x z : Rn n) :
    (inner ℝ (A x) z : ℝ) = inner ℝ x (A.symm z) := by
  rw [← hA x (A.symm z), LinearEquiv.apply_symm_apply]

/-- **Symmetry with respect to a set `G` of transformations** (Rockafellar, §12, p. 109):
`f (A x) = f x` for every `x` and every `A ∈ G`. -/
def SymmetricWrt (f : Rn n → EReal) (G : Set (Rn n ≃ₗ[ℝ] Rn n)) : Prop :=
  ∀ A ∈ G, ∀ x, f (A x) = f x

/-- The half of Corollary 12.3.1 that needs no closedness: if `f` is symmetric under the
orthogonal transformation `A`, so is `f*`. This is Theorem 12.3 with `h = f`, `a = 0 = a*`,
`α = 0`, together with `A*⁻¹ = A`. -/
theorem conj_comp_orthogonal {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A)
    (hfA : ∀ x, f (A x) = f x) (y : Rn n) :
    conj (pairing n) f (A y) = conj (pairing n) f y := by
  have h := conj_comp_linearEquiv (B := pairing n) (B' := pairing n) A A.symm
    (orthogonalEquiv_adjoint hA) f y
  rw [LinearEquiv.symm_symm] at h
  rw [← h]
  exact congrArg (fun g => conj (pairing n) g y) (funext hfA)

/-- **Corollary 12.3.1.** A closed convex function `f` is symmetric with respect to a
given set `G` of orthogonal linear transformations if and only if `f*` is symmetric with respect
to `G`.

The book's proof: `conj_comp_orthogonal` is the forward implication, and the converse is the same
implication applied to `f*`, whose biconjugate is `f` because `f` is closed and convex. -/
theorem corollary_12_3_1 (hf : ConvexFn f) (hc : ClosedFn f) {G : Set (Rn n ≃ₗ[ℝ] Rn n)}
    (hG : ∀ A ∈ G, IsOrthogonalEquiv A) :
    SymmetricWrt f G ↔ SymmetricWrt (conj (pairing n) f) G := by
  refine ⟨fun h A hA => conj_comp_orthogonal (hG A hA) (h A hA), fun h A hA => ?_⟩
  have hb : conj (pairing n) (conj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf, hc]
  have hsym := conj_comp_orthogonal (f := conj (pairing n) f) (hG A hA) (h A hA)
  rw [hb] at hsym
  exact hsym

/-! ### Theorem 12.4: monotone conjugacy on the non-negative orthant -/

section MonotoneConjugacy

/-- The **non-negative orthant** of `ℝⁿ` (Rockafellar, §12, p. 111): the set `{z | z ≥ 0}` for the
componentwise order. -/
def nonnegOrthant (n : ℕ) : Set (Rn n) := {z : Rn n | ∀ j, 0 ≤ z j}

theorem mem_nonnegOrthant {z : Rn n} : z ∈ nonnegOrthant n ↔ ∀ j, 0 ≤ z j := Iff.rfl

/-- The inner product of `ℝⁿ` in coordinates, which is what the componentwise order interacts
with. -/
theorem inner_rn (x y : Rn n) : (inner ℝ x y : ℝ) = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem convex_nonnegOrthant (n : ℕ) : Convex ℝ (nonnegOrthant n) := by
  intro x hx y hy a b ha hb _ j
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))

theorem isClosed_nonnegOrthant (n : ℕ) : IsClosed (nonnegOrthant n) := by
  have hset : nonnegOrthant n = ⋂ j, (fun z : Rn n => z j) ⁻¹' Set.Ici (0 : ℝ) := by
    ext z; simp [nonnegOrthant]
  rw [hset]
  exact isClosed_iInter fun j =>
    isClosed_Ici.preimage (PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) j)

theorem zero_mem_nonnegOrthant (n : ℕ) : (0 : Rn n) ∈ nonnegOrthant n := fun _ => le_rfl

/-- The componentwise **positive part** of `y`, which is `y` itself on the orthant. -/
noncomputable def posPart (y : Rn n) : Rn n := WithLp.toLp 2 fun j => max (y j) 0

@[simp] theorem posPart_apply (y : Rn n) (j : Fin n) : posPart y j = max (y j) 0 := rfl

theorem posPart_mem (y : Rn n) : posPart y ∈ nonnegOrthant n := fun _ => le_max_right _ _

theorem le_posPart (y : Rn n) (j : Fin n) : y j ≤ posPart y j := le_max_left _ _

theorem posPart_of_mem {y : Rn n} (hy : y ∈ nonnegOrthant n) : posPart y = y := by
  ext j; exact max_eq_left (hy j)

/-- `z` with the coordinates on which `y` is negative set to zero. It is the competitor that makes
the truncation in `monotoneConjOrthant` harmless. -/
noncomputable def maskNonneg (y z : Rn n) : Rn n :=
  WithLp.toLp 2 fun j => if 0 ≤ y j then z j else 0

@[simp] theorem maskNonneg_apply (y z : Rn n) (j : Fin n) :
    maskNonneg y z j = if 0 ≤ y j then z j else 0 := rfl

theorem maskNonneg_mem {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) :
    maskNonneg y z ∈ nonnegOrthant n := by
  intro j
  rw [maskNonneg_apply]
  split
  · exact hz j
  · exact le_rfl

theorem maskNonneg_le {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) (j : Fin n) :
    maskNonneg y z j ≤ z j := by
  rw [maskNonneg_apply]
  split
  · exact le_rfl
  · exact hz j

theorem inner_maskNonneg (y z : Rn n) :
    (inner ℝ (maskNonneg y z) y : ℝ) = inner ℝ z (posPart y) := by
  rw [inner_rn, inner_rn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [maskNonneg_apply, posPart_apply]
  split_ifs with hj
  · rw [max_eq_left hj]
  · rw [max_eq_right (le_of_not_ge hj), zero_mul, mul_zero]

theorem inner_le_inner_posPart {z : Rn n} (hz : z ∈ nonnegOrthant n) (y : Rn n) :
    (inner ℝ y z : ℝ) ≤ inner ℝ (posPart y) z := by
  rw [inner_rn, inner_rn]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_posPart y j) (hz j)

/-- **A non-decreasing closed convex function on the non-negative orthant**, in the encoding the
book's §4 convention prescribes: a function on all of `ℝⁿ` that is `+∞` off the orthant.
Rockafellar's hypotheses on `g` (p. 111) are exactly these. -/
structure MonotoneOrthantFn (f : Rn n → EReal) : Prop where
  /-- `f` is `+∞` off the non-negative orthant; the book's "function on the orthant". -/
  top_of_notMem : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤
  /-- `f z ≤ f z'` whenever `0 ≤ z ≤ z'`: the book's *non-decreasing*. -/
  mono : ∀ ⦃z z' : Rn n⦄, z ∈ nonnegOrthant n → (∀ j, z j ≤ z' j) → f z ≤ f z'
  /-- `f` is convex. -/
  convex : ConvexFn f
  /-- `f` is lower semicontinuous, i.e. closed. -/
  closed : ClosedFn f
  /-- `f 0` is finite: not `+∞` … -/
  zero_ne_top : f 0 ≠ ⊤
  /-- … and not `-∞`. -/
  zero_ne_bot : f 0 ≠ ⊥

theorem MonotoneOrthantFn.zero_le {f : Rn n → EReal} (hf : MonotoneOrthantFn f)
    {z : Rn n} (hz : z ∈ nonnegOrthant n) : f 0 ≤ f z :=
  hf.mono (zero_mem_nonnegOrthant n) fun j => hz j

theorem MonotoneOrthantFn.proper {f : Rn n → EReal} (hf : MonotoneOrthantFn f) : Proper f := by
  refine ⟨⟨0, lt_of_le_of_ne le_top hf.zero_ne_top⟩, fun z hz => ?_⟩
  by_cases hzm : z ∈ nonnegOrthant n
  · exact hf.zero_ne_bot (le_bot_iff.1 (hz ▸ hf.zero_le hzm))
  · exact absurd (hf.top_of_notMem hzm) (hz ▸ bot_ne_top)

/-- The **monotone conjugate** `g⁺` of Rockafellar's p. 111: the conjugate, truncated back to the
non-negative orthant so that the correspondence is one between functions on the orthant. -/
noncomputable def monotoneConjOrthant (f : Rn n → EReal) : Rn n → EReal :=
  restrict (nonnegOrthant n) (conj (pairing n) f)

/-- Rockafellar's formula `g⁺(z*) = sup {⟨z, z*⟩ - g z ∣ z ≥ 0}` (p. 111), on the orthant. -/
theorem monotoneConjOrthant_apply {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y : Rn n} (hy : y ∈ nonnegOrthant n) :
    monotoneConjOrthant f y = ⨆ z ∈ nonnegOrthant n, ((inner ℝ z y : ℝ) : EReal) - f z := by
  rw [monotoneConjOrthant, restrict_of_mem hy, conj_apply]
  refine le_antisymm (iSup_le fun z => ?_) (iSup₂_le fun z hz => ?_)
  · by_cases hz : z ∈ nonnegOrthant n
    · exact le_iSup₂ (f := fun z (_ : z ∈ nonnegOrthant n) =>
        ((inner ℝ z y : ℝ) : EReal) - f z) z hz
    · rw [htop hz]; simp
  · exact le_iSup (fun z : Rn n => ((pairing n z y : ℝ) : EReal) - f z) z

theorem monotoneConjOrthant_of_notMem (f : Rn n → EReal) {y : Rn n}
    (hy : y ∉ nonnegOrthant n) : monotoneConjOrthant f y = ⊤ :=
  restrict_of_notMem hy

theorem conj_le_monotoneConjOrthant (f : Rn n → EReal) (y : Rn n) :
    conj (pairing n) f y ≤ monotoneConjOrthant f y := by
  by_cases hy : y ∈ nonnegOrthant n
  · rw [monotoneConjOrthant, restrict_of_mem hy]
  · rw [monotoneConjOrthant_of_notMem f hy]; exact le_top

/-- The conjugate of an orthant function is monotone in the dual variable. -/
theorem conj_mono_of_top_of_notMem {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y y' : Rn n} (h : ∀ j, y j ≤ y' j) :
    conj (pairing n) f y ≤ conj (pairing n) f y' := by
  rw [conj_apply, conj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_ (le_iSup (fun z : Rn n => ((pairing n z y' : ℝ) : EReal) - f z) z)
    refine _root_.EReal.sub_le_sub ?_ le_rfl
    rw [_root_.EReal.coe_le_coe_iff]
    change (inner ℝ z y : ℝ) ≤ inner ℝ z y'
    rw [inner_rn, inner_rn]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hz j)
  · rw [htop hz]; simp

/-- **The one fact that makes the truncation harmless**: `f*` does not distinguish `y` from its
positive part. See the module docstring. -/
theorem conj_posPart {f : Rn n → EReal} (hf : MonotoneOrthantFn f) (y : Rn n) :
    conj (pairing n) f (posPart y) = conj (pairing n) f y := by
  refine le_antisymm ?_ (conj_mono_of_top_of_notMem hf.top_of_notMem (le_posPart y))
  rw [conj_apply, conj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_
      (le_iSup (fun w : Rn n => ((pairing n w y : ℝ) : EReal) - f w) (maskNonneg y z))
    refine _root_.EReal.sub_le_sub (le_of_eq ?_)
      (hf.mono (maskNonneg_mem y hz) (maskNonneg_le y hz))
    rw [_root_.EReal.coe_eq_coe_iff]
    exact (inner_maskNonneg y z).symm
  · rw [hf.top_of_notMem hz]; simp

/-- **Theorem 12.4**, first half: the monotone conjugate `g⁺` of a non-decreasing
lower semicontinuous convex function on the non-negative orthant, finite at the origin, is another
such function.

The book states Theorem 12.4 with **no proof at all**. Convexity and closedness are inherited from
the conjugate (`convexFn_conj`, `closedFn_conj`) through `ConvexFn.restrict` and
`ClosedFn.restrict`; monotonicity is `conj_mono_of_top_of_notMem`; and `g⁺(0) = -g(0)` because `g`
attains its infimum over the orthant at the origin. -/
theorem theorem_12_4_mem {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    MonotoneOrthantFn (monotoneConjOrthant f) := by
  have hzero : monotoneConjOrthant f 0 = -f 0 := by
    rw [monotoneConjOrthant, restrict_of_mem (zero_mem_nonnegOrthant n), conj_apply]
    refine le_antisymm (iSup_le fun z => ?_) ?_
    · by_cases hz : z ∈ nonnegOrthant n
      · have h0 : ((pairing n z 0 : ℝ) : EReal) = 0 := by
          rw [map_zero, _root_.EReal.coe_zero]
        rw [h0, zero_sub, _root_.EReal.neg_le_neg_iff]
        exact hf.zero_le hz
      · rw [hf.top_of_notMem hz]; simp
    · refine le_trans (le_of_eq ?_)
        (le_iSup (fun z : Rn n => ((pairing n z 0 : ℝ) : EReal) - f z) 0)
      rw [map_zero, _root_.EReal.coe_zero, zero_sub]
  refine ⟨fun y hy => monotoneConjOrthant_of_notMem f hy, ?_,
    (convexFn_conj (pairing n) f).restrict (convex_nonnegOrthant n),
    (closedFn_conj (B := pairing n) (f := f)).restrict ?_ (isClosed_nonnegOrthant n),
    ?_, ?_⟩
  · intro y y' hy hyy'
    have hy' : y' ∈ nonnegOrthant n := fun j => le_trans (hy j) (hyy' j)
    rw [monotoneConjOrthant, restrict_of_mem hy, restrict_of_mem hy']
    exact conj_mono_of_top_of_notMem hf.top_of_notMem hyy'
  · exact fun y => conj_ne_bot hf.proper.dom_nonempty y
  · rw [hzero]
    exact fun h => hf.zero_ne_bot (_root_.EReal.neg_eq_top_iff.1 h)
  · rw [hzero]
    exact fun h => hf.zero_ne_top (_root_.EReal.neg_eq_bot_iff.1 h)

/-- **Theorem 12.4**, second half: the monotone conjugate of `g⁺` is in turn `g`.

The book states Theorem 12.4 with **no proof at all**; this is the argument described in the
module docstring. `≤` is `conj_antitone` applied to `f* ≤ g⁺`; for `≥`, `conj_posPart` replaces
each competitor `y` by `y⁺`, at which `g⁺` and `f*` agree, so the supremum over the orthant is
already the whole biconjugate — and that is `f` by Fenchel–Moreau. -/
theorem theorem_12_4_involutive {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    monotoneConjOrthant (monotoneConjOrthant f) = f := by
  have hbi : conj (pairing n) (conj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf.convex, hf.closed]
  funext z
  by_cases hz : z ∈ nonnegOrthant n
  · have hLHS : conj (pairing n) (conj (pairing n) f) z
        = ⨆ y : Rn n, ((pairing n y z : ℝ) : EReal) - conj (pairing n) f y := conj_apply _ _ _
    have hRHS : conj (pairing n) (monotoneConjOrthant f) z
        = ⨆ w : Rn n, ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w := conj_apply _ _ _
    have hge : conj (pairing n) (conj (pairing n) f) z
        ≤ conj (pairing n) (monotoneConjOrthant f) z := by
      rw [hLHS, hRHS]
      refine iSup_le fun y => ?_
      refine le_trans ?_
        (le_iSup (fun w : Rn n => ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w)
          (posPart y))
      refine _root_.EReal.sub_le_sub ?_ (le_of_eq ?_)
      · rw [_root_.EReal.coe_le_coe_iff]
        exact inner_le_inner_posPart hz y
      · rw [monotoneConjOrthant, restrict_of_mem (posPart_mem y), conj_posPart hf]
    have hle := conj_antitone (pairing n) (conj_le_monotoneConjOrthant f) z
    rw [hbi] at hge hle
    rw [monotoneConjOrthant, restrict_of_mem hz]
    exact le_antisymm hle hge
  · rw [monotoneConjOrthant_of_notMem _ hz, (hf.top_of_notMem hz).symm]

end MonotoneConjugacy

end Rockafellar
