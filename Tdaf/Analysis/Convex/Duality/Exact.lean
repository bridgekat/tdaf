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
* `IsExactFinsetSum B s f` — the same for a finite family: `(fᵢ)_{i ∈ s}` are proper and the
  `m`-fold infimal convolution defining `(∑ fᵢ)*` is attained. This is the form Rockafellar states
  Theorems 16.4, 20.1 and 23.8 in.
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
* `conj_finsetSum_le_sum_toInfConvFn` — the unconditional half for `m` summands.
* `IsExactFinsetSum.conj_finsetSum`, `IsExactFinsetSum.exists_conj_finsetSum_eq` —
  **Theorem 16.4** in the book's `m`-ary form: `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*`, attained.
* `IsExactFinsetSum.singleton`, `IsExactFinsetSum.cons`, `IsExactFinsetSum.of_split` — the family
  interface built out of binary ones, which is how every `m`-ary constraint qualification is
  discharged.
* `IsExactSum.proper_add`, `IsExactFinsetSum.proper_finsetSum`, `IsExactImage.proper_compLin` —
  the interfaces are not vacuous, and they are unsatisfiable when the effective domains miss each
  other.

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

**The family interface is not an iterated binary one, and it is empty at `s = ∅`.** Its
consequences are proved once for the family rather than by re-entering the binary lemma: the
`m`-ary infimum bound `sum_toInfConvFn_le_sum` (`Operations/InfConv.lean`) puts its `≠ ⊥`
hypothesis on each `fᵢ` and never on a partial convolute, because `□` does not preserve `≠ ⊥`, so
the binary `infConv_le_add` cannot be iterated at all. What *does* iterate is the construction:
`IsExactFinsetSum.cons` reduces a family to a binary hypothesis about `fᵢ` and `∑_{j ∈ t} fⱼ`, and
that is where each constraint qualification does its work. Note that `exact_le` demands a splitting
`y = ∑_{i ∈ s} yᵢ` for *every* `y`, so `IsExactFinsetSum B ∅ f` forces every `y : F` to be `0`:
the empty family is not exact, in the same way and for the same reason that two functions with
disjoint effective domains are not.

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

/-! ### Sums over a `Finset`: the unconditional half -/

section FinsetSum

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

omit [AddCommGroup E] [Module ℝ E] in
/-- The effective domain of a finite sum is the intersection of the effective domains: `dom_add`
over a `Finset`, with the same `≠ ⊥` hypothesis and for the same reason. -/
theorem dom_finsetSum (hf : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) :
    dom (∑ i ∈ s, f i) = ⋂ i ∈ s, dom (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    ext x
    simp
  | cons i t hi ih =>
    have hbot : ∀ x, (∑ j ∈ t, f j) x ≠ ⊥ := fun x => by
      rw [Finset.sum_apply]
      exact Tdaf.EReal.sum_ne_bot fun j hj => hf j (by simp [hj]) x
    rw [Finset.sum_cons, dom_add (hf i (by simp)) hbot, ih fun j hj => hf j (by simp [hj])]
    ext x
    simp [Finset.mem_cons]

/-- Affine minorants of `f₁, …, fₘ` add to an affine minorant of `f₁ + ⋯ + fₘ`. This is
`conj_add_le_coe_add` over a `Finset`, and like it, it needs no hypothesis whatsoever. -/
theorem conj_finsetSum_le_coe_sum {y : ι → F} {c : ι → ℝ}
    (h : ∀ i ∈ s, conj B (f i) (y i) ≤ (c i : EReal)) :
    conj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ((∑ i ∈ s, c i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [conj_le_coe_iff]
    intro x
    rw [affineFn_eq_coe]
    simp
  | cons i t hi ih =>
    simp only [Finset.sum_cons]
    exact conj_add_le_coe_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- The pointwise `m`-ary form: `(f₁ + ⋯ + fₘ)* (y₁ + ⋯ + yₘ) ≤ f₁* y₁ + ⋯ + fₘ* yₘ`.

As in the binary case (`conj_add_le_add_conj`) this is *not* unconditional: non-empty effective
domains are what keep the right-hand side from collapsing to `⊥` through a `⊤ + ⊥`. -/
theorem conj_finsetSum_le_sum_conj (hf : ∀ i ∈ s, (dom (f i)).Nonempty) (y : ι → F) :
    conj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ∑ i ∈ s, conj B (f i) (y i) := by
  rcases eq_or_ne (∑ i ∈ s, conj B (f i) (y i)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hbot : ∀ i ∈ s, conj B (f i) (y i) ≠ ⊥ := fun i hi => conj_ne_bot (hf i hi) (y i)
  have hfin : ∀ i ∈ s, conj B (f i) (y i) ≠ ⊤ :=
    Tdaf.EReal.forall_ne_top_of_sum_ne_top s _ hbot htop
  have hci : ∀ i ∈ s, conj B (f i) (y i) = (((conj B (f i) (y i)).toReal : ℝ) : EReal) :=
    fun i hi => (_root_.EReal.coe_toReal (hfin i hi) (hbot i hi)).symm
  have hsum : ∑ i ∈ s, conj B (f i) (y i)
      = ((∑ i ∈ s, (conj B (f i) (y i)).toReal : ℝ) : EReal) := by
    rw [Tdaf.EReal.coe_sum]
    exact Finset.sum_congr rfl hci
  rw [hsum]
  exact conj_finsetSum_le_coe_sum fun i hi => (hci i hi).le

/-- **Half of Rockafellar's Theorem 16.4 in the book's `m`-ary form, unconditionally**:
`(f₁ + ⋯ + fₘ)* ≤ f₁* □ ⋯ □ fₘ*`, the `□`-product being the `AddCommMonoid` sum of
`InfConvFn F`.

No properness is needed anywhere, and none may be assumed at the intermediate stages: `□` does not
preserve properness, so the induction runs on `infConv_mono` and never re-enters the infimum
formula. -/
theorem conj_finsetSum_le_sum_toInfConvFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) :
    conj B (∑ i ∈ s, f i) ≤ ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty, ofInfConvFn_zero]
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [indicatorFn_of_mem (s := ({0} : Set F)) (Set.mem_singleton_iff.2 rfl), conj_apply]
      refine iSup_le fun x => ?_
      simp
    · rw [indicatorFn_of_notMem (s := ({0} : Set F)) (by simpa using hy)]
      exact le_top
  | cons i t hi ih =>
    simp only [Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact (conj_add_le_infConv B (f i) _).trans (infConv_mono le_rfl ih)

end FinsetSum

/-! ### Sums over a `Finset`: the interface -/

section FinsetSumInterface

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- A finite family `(fᵢ)_{i ∈ s}` **adds exactly** with respect to the pairing `B`: every member
is proper, and the `m`-fold infimal convolution `f₁* □ ⋯ □ fₘ*` is attained at every point —
equivalently (`IsExactFinsetSum.conj_finsetSum`), the conjugate of `f₁ + ⋯ + fₘ` *is*
`f₁* □ ⋯ □ fₘ*`.

This is the conclusion of Rockafellar's Theorem 16.4 and of its polyhedral refinement
Theorem 20.1, both of which the book states for `m` summands; `IsExactSum` is the case of two.
Nothing here is special to `m = 2` reached by iteration: `IsExactFinsetSum.cons` and
`IsExactFinsetSum.of_split` build a family interface out of binary ones, and every consequence
below is proved once, for the family. -/
structure IsExactFinsetSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → E → EReal) : Prop where
  /-- Every member of the family is proper. -/
  proper : ∀ i ∈ s, Proper (f i)
  /-- At every `y` the `m`-fold infimal convolution defining `(f₁ + ⋯ + fₘ)*` is attained: some
  splitting `y = y₁ + ⋯ + yₘ` already achieves the value. The reverse inequality is unconditional
  (`conj_finsetSum_le_sum_toInfConvFn`), so this is the entire content. -/
  exact_le : ∀ y : F, ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
    ∑ i ∈ s, conj B (f i) (y' i) ≤ conj B (∑ i ∈ s, f i) y

namespace IsExactFinsetSum

variable (h : IsExactFinsetSum B s f)
include h

/-- The sum of an exactly-adding family never takes the value `⊥`. -/
theorem finsetSum_ne_bot (x : E) : (∑ i ∈ s, f i) x ≠ ⊥ := by
  rw [Finset.sum_apply]
  exact Tdaf.EReal.sum_ne_bot fun i hi => (h.proper i hi).ne_bot x

/-- **The interface rules out effective domains with empty intersection**, exactly as in the
binary case (`IsExactSum.proper_add`): if `⋂ dom fᵢ = ∅` then `f₁ + ⋯ + fₘ ≡ +∞` and its
conjugate is `≡ -∞`, which no sum of conjugates of proper functions bounds from above. -/
theorem proper_finsetSum : Proper (∑ i ∈ s, f i) := by
  have hb : conj B (∑ i ∈ s, f i) 0 ≠ ⊥ := by
    obtain ⟨y', -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff] at hle
    exact Tdaf.EReal.sum_ne_bot
      (fun i hi => conj_ne_bot (h.proper i hi).dom_nonempty (y' i)) hle
  refine ⟨?_, h.finsetSum_ne_bot⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

theorem sum_toInfConvFn_le_conj_finsetSum :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) ≤ conj B (∑ i ∈ s, f i) := by
  intro y
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  rw [← hy]
  exact sum_toInfConvFn_le_sum (fun i hi x => conj_ne_bot (h.proper i hi).dom_nonempty x) y'

/-- **Rockafellar's Theorem 16.4** in the book's `m`-ary form, exact half: the conjugate of a
finite sum is the infimal convolution of the conjugates. -/
theorem conj_finsetSum :
    conj B (∑ i ∈ s, f i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) :=
  le_antisymm (conj_finsetSum_le_sum_toInfConvFn B s f) h.sum_toInfConvFn_le_conj_finsetSum

/-- **The `m`-fold infimal convolution is attained**, which is the half of Theorem 16.4 that the
constraint qualifications are for:
`(f₁ + ⋯ + fₘ)* y = inf {f₁* y₁ + ⋯ + fₘ* yₘ | y₁ + ⋯ + yₘ = y}`, with the infimum attained. -/
theorem exists_conj_finsetSum_eq (y : F) :
    ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, conj B (f i) (y' i) = conj B (∑ i ∈ s, f i) y := by
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine ⟨y', hy, le_antisymm hle ?_⟩
  rw [← hy]
  exact conj_finsetSum_le_sum_conj (fun i hi => (h.proper i hi).dom_nonempty) y'

end IsExactFinsetSum

/-- A one-element family adds exactly as soon as its member is proper: there is nothing to
split. This is the base case of every `m`-ary constraint qualification. -/
theorem IsExactFinsetSum.singleton {i : ι} (hf : Proper (f i)) :
    IsExactFinsetSum B ({i} : Finset ι) f where
  proper j hj := by rw [Finset.mem_singleton.1 hj]; exact hf
  exact_le y := ⟨fun _ => y, by simp, by simp⟩

/-- **Adjoining one summand.** A family adds exactly as soon as its tail does and the new summand
adds exactly to the sum of the tail.

This is the induction step every `m`-ary constraint qualification runs on; what each of them has
to supply is the *binary* hypothesis `hbin`, and that is where the convexity, properness and
relative-interior facts about `f₁ + ⋯ + fₘ₋₁` are consumed. -/
theorem IsExactFinsetSum.cons {i : ι} {t : Finset ι} (hi : i ∉ t)
    (hbin : IsExactSum B (f i) (∑ j ∈ t, f j)) (ht : IsExactFinsetSum B t f) :
    IsExactFinsetSum B (Finset.cons i t hi) f := by
  classical
  refine ⟨fun j hj => ?_, fun y => ?_⟩
  · rcases Finset.mem_cons.1 hj with rfl | hj'
    · exact hbin.proper_left
    · exact ht.proper j hj'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨y', hy', hle'⟩ := ht.exact_le y₂
    obtain ⟨w, hwi, hwt⟩ : ∃ w : ι → F, w i = y₁ ∧ ∀ j ∈ t, w j = y' j :=
      ⟨Function.update y' i y₁, Function.update_self _ _ _,
        fun j hj => Function.update_of_ne (by rintro rfl; exact hi hj) _ _⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_cons, hwi, Finset.sum_congr rfl hwt, hy', hy]
    · rw [Finset.sum_cons, Finset.sum_cons, hwi]
      have hcongr : ∑ j ∈ t, conj B (f j) (w j) = ∑ j ∈ t, conj B (f j) (y' j) :=
        Finset.sum_congr rfl fun j hj => by rw [hwt j hj]
      rw [hcongr]
      exact le_trans (add_le_add le_rfl hle') hle

/-- **Gluing two exactly-adding subfamilies.** If `s` splits into disjoint `t` and `u`, both of
which add exactly, and the two partial sums add exactly to each other, then `s` adds exactly.

The splitting is spelled as `∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u` rather than `s = t ∪ u` so that the
statement needs no `DecidableEq` instance, which a caller supplying `Classical.propDecidable` could
not match. This is the form Rockafellar's proof of Theorem 20.1 uses: `t` the polyhedral indices,
`u` the rest. -/
theorem IsExactFinsetSum.of_split {t u : Finset ι} (hdisj : Disjoint t u)
    (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (ht : IsExactFinsetSum B t f) (hu : IsExactFinsetSum B u f)
    (hbin : IsExactSum B (∑ i ∈ t, f i) (∑ i ∈ u, f i)) :
    IsExactFinsetSum B s f := by
  classical
  have hsu : s = t ∪ u := Finset.ext fun i => by rw [hmem i, Finset.mem_union]
  subst hsu
  refine ⟨fun i hi => ?_, fun y => ?_⟩
  · rcases Finset.mem_union.1 hi with hi' | hi'
    · exact ht.proper i hi'
    · exact hu.proper i hi'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨a, ha, hlea⟩ := ht.exact_le y₁
    obtain ⟨b, hb, hleb⟩ := hu.exact_le y₂
    obtain ⟨w, hwt, hwu⟩ : ∃ w : ι → F, (∀ i ∈ t, w i = a i) ∧ ∀ i ∈ u, w i = b i :=
      ⟨fun i => if i ∈ t then a i else b i, fun i hi => by simp [hi],
        fun i hi => by simp [Finset.disjoint_right.1 hdisj hi]⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_union hdisj, Finset.sum_congr rfl hwt, Finset.sum_congr rfl hwu, ha, hb, hy]
    · rw [Finset.sum_union hdisj, Finset.sum_union hdisj]
      have h₁ : ∑ i ∈ t, conj B (f i) (w i) = ∑ i ∈ t, conj B (f i) (a i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwt i hi]
      have h₂ : ∑ i ∈ u, conj B (f i) (w i) = ∑ i ∈ u, conj B (f i) (b i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwu i hi]
      rw [h₁, h₂]
      exact le_trans (add_le_add hlea hleb) hle

end FinsetSumInterface

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
