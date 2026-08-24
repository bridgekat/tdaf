/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Conjugate
import Tdaf.Analysis.Convex.Operations.InfConv
import Tdaf.Analysis.Convex.Operations.Image

/-!
# Exact duality: when the closure may be omitted

Almost every "exact" duality statement in Rockafellar has the shape

> if `ri (dom f₁) ∩ … ∩ ri (dom fₘ) ≠ ∅` then the closure operation can be dropped and the
> infimum defining the dual operation is attained

(Theorems 16.3, 16.4, 16.5, 20.1, 23.8, 23.9, 31.1, 38.2, 38.4, 38.5, 39.5, 39.7 …). The relative
interior condition is one sufficient condition among several — there are polyhedral variants (§20),
a continuity variant valid in any topological vector space, and, outside the book,
Attouch–Brezis/Rockafellar–Robinson conditions in Banach spaces.

This file names the **conclusion**. `IsExactSum` and `IsExactImage` are hypothesis-only interfaces;
the sufficient conditions for them are proved elsewhere, each in the module that owns its
hypothesis (`IsExactSum.of_relint` in `Duality/Relint.lean`, `IsExactSum.of_polyhedral` in
`Polyhedral/Duality.lean`, and so on; each has an `…_closed` variant carrying the argument, and the
unprimed name is the book's proper-convex statement). Downstream — Theorems 16.3 and 16.4,
Theorems 23.8 and 23.9, Fenchel's duality theorem, and §38 — every consumer is reduced to these two
interfaces once and for all.

## Main definitions

* `IsExactSum B f g` — `f` and `g` **add exactly**: both are proper, and the infimal convolution
  defining `(f + g)*` is attained.
* `IsExactImage B B' A A' hA g` — `g` **pulls back exactly** along `A`: `g` is proper, and the
  infimum defining `(g A)*` over the fibres of the transpose `A'` is attained.

## Main results

* `conj_add_le_infConv` — the *unconditional* half: `(f + g)* ≤ f* □ g*`, with no hypothesis
  whatsoever on `f` and `g`.
* `conj_compLin_le_mapLin` — the unconditional half on the image side: `(g A)* ≤ A' (g*)`.
* `IsExactSum.conj_add`, `IsExactSum.exists_conj_add_eq` — **Rockafellar's Theorem 16.4**,
  exact half: `(f + g)* = f* □ g*`, with the infimal convolution attained.
* `IsExactImage.conj_compLin`, `IsExactImage.exists_conj_compLin_eq` — **Rockafellar's
  Theorem 16.3**, exact half: `(g A)* = A' (g*)`, with the infimum over the fibre attained.
* `IsExactSum.proper_add`, `IsExactImage.proper_compLin` — the interfaces are not vacuous, and
  they are unsatisfiable when the effective domains miss each other.

## Design notes

**The equality is a theorem, not a field.** The inequality `(f + g)* ≤ f* □ g*` holds for arbitrary
`f` and `g` (`conj_add_le_infConv`), so an interface asking for both inequalities would be
redundant. Worse, an interface *stating the equality* would be unsatisfiable exactly where it looks
most innocent: when `dom f ∩ dom g = ∅` we have `f + g ≡ +∞`, hence `(f + g)* ≡ -∞`, while the
conjugate of a proper function is never `-∞`. What the interface must carry is the *attainment*,
which is `exact_le`.

**Properness is a genuine hypothesis**, not decoration. It is Rockafellar's own hypothesis in
Theorems 16.3 and 16.4, it is what keeps the pointwise sum `f + g` from hiding an `∞ - ∞`, and it
is what makes `f*` and `g*` never `-∞` — without which the infimal convolution of the conjugates is
not given by the infimum formula. Properness of `f` and `g` *individually* is assumed; properness
of `f + g` is then a consequence (`IsExactSum.proper_add`).

**The image interface must be guarded by `< ⊤`.** `IsExactImage.exact_le` asks for a point of the
fibre `A' ⁻¹' {y}` only where `(g A)* y` is finite. Dropping the guard makes the interface
*unsatisfiable whenever `A'` is not surjective*, for a reason that has nothing to do with convexity:
at a `y` outside the range of `A'` there is no `z` to produce at all, while both sides of Theorem
16.3 are legitimately `+∞` there (`mapLin_of_notMem_range`). Taking `A = 0` between nonzero spaces
already breaks it. The guard costs nothing downstream: every consumer, from
`exists_conj_compLin_eq` to `IsExactImage.subgradient_compLin`, is looking at a point where the
value is finite anyway, and
properness of `g A` supplies the missing `≠ ⊥` on the other side.

**The transpose is data, not a function of `A`.** Between arbitrarily paired spaces a linear map
need not have an adjoint, so `IsExactImage` carries `A'` and the adjointness datum
`hA : IsAdjointPair B B' A A'` as parameters. See the design notes of `Duality/Pairing.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16 (Theorem 16.3,
  Theorem 16.4), §20 (Theorem 20.1), §23 (Theorem 23.8, Theorem 23.9), §31 (Theorem 31.1).
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

/-! ### Sums: the unconditional half -/

section Sum

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {y₁ y₂ : F} {c₁ c₂ : ℝ}

/-- An affine minorant of `f` and an affine minorant of `g` add to an affine minorant of `f + g`.
Read through `conj_le_coe_iff`, this is the whole unconditional content of Rockafellar's
Theorem 16.4, and it needs no hypothesis on `f` or `g`. -/
theorem conj_add_le_coe_add (h₁ : conj B f y₁ ≤ (c₁ : EReal)) (h₂ : conj B g y₂ ≤ (c₂ : EReal)) :
    conj B (f + g) (y₁ + y₂) ≤ ((c₁ + c₂ : ℝ) : EReal) := by
  rw [conj_le_coe_iff] at h₁ h₂ ⊢
  intro x
  have hsplit : affineFn B (y₁ + y₂) (c₁ + c₂) x
      = affineFn B y₁ c₁ x + affineFn B y₂ c₂ x := by
    rw [affineFn_eq_coe, affineFn_eq_coe, affineFn_eq_coe, ← _root_.EReal.coe_add]
    congr 1
    rw [map_add]
    ring
  rw [hsplit, Pi.add_apply]
  exact add_le_add (h₁ x) (h₂ x)

/-- The epigraph of `f*` and the epigraph of `g*` add into the epigraph of `(f + g)*`. This is
`conj_add_le_coe_add` in the language `infConv` is defined in. -/
theorem epi_conj_add_epi_conj_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    epi (conj B f) + epi (conj B g) ⊆ epi (conj B (f + g)) := by
  rintro _ ⟨⟨y₁, c₁⟩, h₁, ⟨y₂, c₂⟩, h₂, rfl⟩
  rw [mk_mem_epi] at h₁ h₂
  simpa using conj_add_le_coe_add h₁ h₂

/-- **Half of Rockafellar's Theorem 16.4, unconditionally.** The conjugate of a sum is at most the
infimal convolution of the conjugates, for *arbitrary* `f` and `g`.

The reverse inequality is what `IsExactSum` asks for; it is the half that fails in general, and the
half every constraint qualification in the book exists to supply. -/
theorem conj_add_le_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    conj B (f + g) ≤ infConv (conj B f) (conj B g) := by
  rw [infConv_def]
  exact subset_epi_iff_le_ofEpi.1 (epi_conj_add_epi_conj_subset B f g)

/-- The pointwise form of `conj_add_le_infConv`. Unlike the two statements above it is *not*
unconditional: if `f ≡ +∞` and `g` takes `-∞` somewhere then `(f + g)* ≡ +∞` while
`f* y₁ + g* y₂ = ⊥ + ⊤ = ⊥`. Nonempty effective domains are exactly what rules that out. -/
theorem conj_add_le_add_conj (hf : (dom f).Nonempty) (hg : (dom g).Nonempty) (y₁ y₂ : F) :
    conj B (f + g) (y₁ + y₂) ≤ conj B f y₁ + conj B g y₂ := by
  rcases eq_or_ne (conj B f y₁) ⊤ with h₁ | h₁
  · rw [h₁, _root_.EReal.top_add_of_ne_bot (conj_ne_bot hg y₂)]
    exact le_top
  rcases eq_or_ne (conj B g y₂) ⊤ with h₂ | h₂
  · rw [h₂, _root_.EReal.add_top_of_ne_bot (conj_ne_bot hf y₁)]
    exact le_top
  obtain ⟨c₁, hc₁⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (conj_ne_bot hf y₁) (lt_top_iff_ne_top.2 h₁)
  obtain ⟨c₂, hc₂⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (conj_ne_bot hg y₂) (lt_top_iff_ne_top.2 h₂)
  rw [hc₁, hc₂, ← _root_.EReal.coe_add]
  exact conj_add_le_coe_add hc₁.le hc₂.le

end Sum

/-! ### Sums: the interface -/

section SumInterface

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- `f` and `g` **add exactly** with respect to the pairing `B`: both are proper, and the infimal
convolution `f* □ g*` is attained at every point — equivalently (`IsExactSum.conj_add`), the
conjugate of the sum *is* the infimal convolution of the conjugates.

This is the conclusion of Rockafellar's Theorem 16.4 and of its polyhedral refinement Theorem 20.1,
named so that the constraint qualifications become interchangeable sufficient conditions rather
than a hypothesis pattern repeated at every use site. -/
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  /-- The left summand is proper. -/
  proper_left : Proper f
  /-- The right summand is proper. -/
  proper_right : Proper g
  /-- At every `y` the infimal convolution defining `(f + g)*` is attained: some splitting
  `y = y₁ + y₂` already achieves the value. The reverse inequality is unconditional
  (`conj_add_le_infConv`), so this is the entire content. -/
  exact_le : ∀ y : F, ∃ y₁ y₂ : F, y₁ + y₂ = y ∧
    conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y

namespace IsExactSum

variable (h : IsExactSum B f g)
include h

theorem conj_left_ne_bot (y : F) : conj B f y ≠ ⊥ := conj_ne_bot h.proper_left.dom_nonempty y

theorem conj_right_ne_bot (y : F) : conj B g y ≠ ⊥ := conj_ne_bot h.proper_right.dom_nonempty y

/-- Exact addition is symmetric. -/
theorem symm : IsExactSum B g f where
  proper_left := h.proper_right
  proper_right := h.proper_left
  exact_le y := by
    obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
    refine ⟨y₂, y₁, by rw [add_comm]; exact hy, ?_⟩
    rw [add_comm g f, add_comm (conj B g y₂)]
    exact hle

/-- **The interface rules out disjoint effective domains.** If `dom f ∩ dom g = ∅` then
`f + g ≡ +∞` and `(f + g)* ≡ -∞`, which no sum of conjugates of proper functions can bound from
above. So the sum of two exactly-adding functions is itself proper. -/
theorem proper_add : Proper (f + g) := by
  have hb : conj B (f + g) 0 ≠ ⊥ := by
    obtain ⟨y₁, y₂, -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff, _root_.EReal.add_eq_bot_iff] at hle
    exact hle.elim (h.conj_left_ne_bot y₁) (h.conj_right_ne_bot y₂)
  refine ⟨?_, fun x hx => ?_⟩
  · by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))
  · rw [Pi.add_apply, _root_.EReal.add_eq_bot_iff] at hx
    exact hx.elim (h.proper_left.ne_bot x) (h.proper_right.ne_bot x)

theorem infConv_le_conj_add : infConv (conj B f) (conj B g) ≤ conj B (f + g) := by
  intro y
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  subst hy
  simpa using infConv_le_add h.conj_left_ne_bot h.conj_right_ne_bot (y₁ + y₂) y₂

/-- **Rockafellar's Theorem 16.4**, exact half: the conjugate of a sum is the infimal convolution
of the conjugates. -/
theorem conj_add : conj B (f + g) = infConv (conj B f) (conj B g) :=
  le_antisymm (conj_add_le_infConv B f g) h.infConv_le_conj_add

/-- Theorem 16.4 spelled out as an infimum. -/
theorem conj_add_apply (y : F) :
    conj B (f + g) y = ⨅ y' : F, conj B f (y - y') + conj B g y' := by
  rw [h.conj_add]
  exact infConv_apply h.conj_left_ne_bot h.conj_right_ne_bot y

/-- **The infimal convolution is attained**, which is the half of Theorem 16.4 that the constraint
qualifications are for. -/
theorem exists_conj_add_eq (y : F) :
    ∃ y₁ y₂ : F, y₁ + y₂ = y ∧ conj B f y₁ + conj B g y₂ = conj B (f + g) y := by
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine ⟨y₁, y₂, hy, le_antisymm hle ?_⟩
  subst hy
  exact conj_add_le_add_conj h.proper_left.dom_nonempty h.proper_right.dom_nonempty y₁ y₂

end IsExactSum

end SumInterface

/-! ### Images -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **Half of Rockafellar's Theorem 16.3, unconditionally.** The conjugate of the inverse image
`g A` is at most the image under the transpose of the conjugate of `g`.

Only the adjointness datum is used; `g` is arbitrary. The reverse inequality is what
`IsExactImage` asks for. -/
theorem conj_compLin_le_mapLin (hA : IsAdjointPair B B' A A') (g : G → EReal) :
    conj B (compLin g A) ≤ mapLin A' (conj B' g) := by
  intro y
  refine le_mapLin fun z hz => ?_
  rw [conj_apply]
  refine iSup_le fun x => ?_
  rw [compLin_apply, ← hz, ← hA x z]
  exact sub_le_conj B' g (A x) z

/-- `g` **pulls back exactly** along `A`: `g` is proper, and the infimum over the fibres of the
transpose `A'` that defines `A' (g*)` is attained — equivalently (`IsExactImage.conj_compLin`),
`(g A)* = A' (g*)`.

This is the conclusion of Rockafellar's Theorem 16.3. The transpose `A'` and the adjointness `hA`
are *data*: between arbitrarily paired spaces a linear map need not have an adjoint at all. -/
structure IsExactImage (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) (hA : IsAdjointPair B B' A A') (g : G → EReal) : Prop where
  /-- The function being pulled back is proper. -/
  proper : Proper g
  /-- Wherever `(g A)* y` is finite, the infimum defining `A' (g*) y` is attained on the fibre of
  `A'` over `y`. The reverse inequality is unconditional (`conj_compLin_le_mapLin`).

  The guard `(g A)* y < ⊤` is not a weakening of convenience: without it the field would demand a
  point of the fibre `A' ⁻¹' {y}` for *every* `y`, i.e. it would silently force `A'` to be
  surjective. See the design notes. -/
  exact_le : ∀ y : F, conj B (compLin g A) y < ⊤ →
    ∃ z : H, A' z = y ∧ conj B' g z ≤ conj B (compLin g A) y

namespace IsExactImage

variable {hA : IsAdjointPair B B' A A'} (h : IsExactImage B B' A A' hA g)
include h

/-- **The interface rules out a range that misses the effective domain.** If `A x ∉ dom g` for
every `x` then `g A ≡ +∞` and `(g A)* ≡ -∞`, which no conjugate of a proper function bounds from
above. -/
theorem proper_compLin : Proper (compLin g A) := by
  have hb : conj B (compLin g A) 0 ≠ ⊥ := by
    intro hc
    obtain ⟨z, -, hle⟩ := h.exact_le 0 (by rw [hc]; exact bot_lt_top)
    rw [hc, le_bot_iff] at hle
    exact conj_ne_bot h.proper.dom_nonempty z hle
  refine ⟨?_, fun x => h.proper.ne_bot (A x)⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

theorem mapLin_le_conj_compLin : mapLin A' (conj B' g) ≤ conj B (compLin g A) := fun y => by
  rcases eq_top_or_lt_top (conj B (compLin g A) y) with hy | hy
  · rw [hy]; exact le_top
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact (mapLin_le hz).trans hle

/-- **Rockafellar's Theorem 16.3**, exact half: the conjugate of an inverse image is the image of
the conjugate under the transpose. -/
theorem conj_compLin : conj B (compLin g A) = mapLin A' (conj B' g) :=
  le_antisymm (conj_compLin_le_mapLin hA g) h.mapLin_le_conj_compLin

/-- **The infimum over the fibre is attained**, which is the half of Theorem 16.3 that the
constraint qualifications are for. -/
theorem exists_conj_compLin_eq {y : F} (hy : conj B (compLin g A) y < ⊤) :
    ∃ z : H, A' z = y ∧ conj B' g z = conj B (compLin g A) y := by
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact ⟨z, hz, le_antisymm hle (h.conj_compLin ▸ mapLin_le hz)⟩

end IsExactImage

end Image

end Tdaf.ConvexAnalysis
