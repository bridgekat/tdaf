/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Tdaf.Analysis.Convex.Indicator
import Tdaf.Analysis.Convex.Operations.Epi

/-!
# The convex hull of a family of functions

Rockafellar §5: the convex hull `conv {f i | i ∈ I}` of a family of functions is the function
obtained from Theorem 5.3 from the convex hull of the union of the epigraphs. It is the **greatest
convex function below every `f i`** — the pointwise infimum is generally not convex, and the convex
hull is what replaces it.

## Main definitions

* `Tdaf.convFn f` — the convex hull of a family `f : ι → E → EReal`.
* `Tdaf.convHullFn g` — the convex hull of a single function, `conv g`, i.e. the greatest convex
  function majorised by `g`.
* `Tdaf.convFn₂ f g` — the binary case, which is the meet of two convex functions.

## Main results

* `Tdaf.convexFn_convFn` — the convex hull is convex (an instance of Theorem 5.3).
* `Tdaf.convFn_le`, `Tdaf.le_convFn`, `Tdaf.isGreatest_convFn` — **the universal property**: the
  convex hull is the greatest convex function below all of the `f i`. This is the definition
  Rockafellar states in words, and everything else in this file is a consequence of it.
* `Tdaf.convFn_le_iInf` — the convex hull is below the pointwise infimum, generally *strictly*;
  `Tdaf.convFn₂_indicatorFn_lt_inf` is a machine-checked witness of the strictness.
* `Tdaf.gci_val_convHullFn` — `conv` is a **coreflection**: it is right adjoint to the inclusion of
  the convex functions into all functions, as a `GaloisCoinsertion`. This is the structural fact
  that makes the convex functions a complete lattice with `⨅ = convFn` and `⨆ = sSup` (§5, after
  Theorem 5.6); `Lattice.lean` gets that from `GaloisCoinsertion.liftCompleteLattice`.
* `Tdaf.convFn_apply` — **Rockafellar's Theorem 5.6**: the explicit formula
  `(conv {f i}) x = inf {∑ λ i * f i (x i) | ∑ λ i • x i = x}`.
* `Tdaf.convFn₂_apply` — Theorem 5.6 for two functions, in the shape one actually uses:
  `(conv {f, g}) x = inf {a * f u + b * g v | a • u + b • v = x}`.

## Design notes

**Why both `convFn` and `convHullFn`.** They determine each other —
`Tdaf.convFn_eq_convHullFn_iInf` says `conv {f i} = conv (⨅ i, f i)`, and `Tdaf.convFn_unit` says
`conv g = conv {g}` — but they play different roles: `convFn` is the *infimum* in the lattice of
convex functions, while `convHullFn` is the *coreflector* onto that lattice. Only the latter is an
adjoint, and only the former takes a family.

**Why a `GaloisCoinsertion` and not a `ClosureOperator`.** `conv` is contracting (`conv g ≤ g`),
monotone and idempotent, so it is a closure operator on `(E → EReal)ᵒᵈ`. Recording it that way costs
an `OrderDual` transport that Mathlib does not simplify away (compare `Tdaf.epiClosure`, where the
dual is unavoidable because `ofEpi` is *antitone*). Here the adjunction is honestly monotone —
the inclusion of convex functions into all functions is left adjoint to `conv` — so the
`GaloisCoinsertion` between `{g // ConvexFn g}` and `E → EReal` is available directly, and it is
strictly more useful: `GaloisCoinsertion.liftCompleteLattice` is what `Lattice.lean` needs. The
three closure-operator facts are recorded separately as `Tdaf.convHullFn_le`,
`Tdaf.convHullFn_mono` and `Tdaf.convHullFn_idem`.

**The two forms of Theorem 5.6.** `Tdaf.convFn_apply` is the book's statement, over an arbitrary
index set, and its infimum ranges over `Finset`-indexed convex combinations. `Tdaf.convFn₂_apply`
is the two-function case written without `Finset`s, which is the form later sections use. They are
proved independently — the binary case through Mathlib's `convexJoin` (Rockafellar's Theorem 3.3
for two sets), the general case through `convexHull_eq` — and their hypotheses differ accordingly:
the general case needs only `f i ≠ ⊥`, while the binary case, routed through
`Convex.convexHull_union`, additionally wants both epigraphs non-empty, i.e. full `Tdaf.Proper`.
The mathematical content of the difference is nil (`dom f = ∅` means `f ≡ ⊤`, and both sides are
then computed by the other function alone); it is an artefact of the shortest available route.

**Where the merging happens.** Theorem 3.3 presents a point of `conv (⋃ i, C i)` as a convex
combination of finitely many points each drawn from *some* `C i`, with repetitions allowed, whereas
Theorem 5.6's infimum ranges over combinations with *one* point per index. The proof of
`Tdaf.convFn_apply` bridges the two by replacing the points drawn from a single `C i = epi (f i)`
by their center of mass, which is legitimate exactly because `epi (f i)` is convex — and that is
the only use made of the convexity hypothesis.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (the discussion after
  Theorem 5.5, and Theorem 5.6).
-/

open Set

namespace Tdaf


section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The convex hull of a family -/

section Family

variable {ι : Sort*} {f : ι → E → EReal} {g : E → EReal}

/-- The **convex hull of a family of functions**: the function determined, in the sense of
Rockafellar's Theorem 5.3, by the convex hull of the union of the epigraphs (Rockafellar §5, the
discussion preceding Theorem 5.6).

`Tdaf.isGreatest_convFn` is the characterisation Rockafellar gives in words: this is the greatest
convex function `h`, proper or not, with `h ≤ f i` for every `i`. -/
noncomputable def convFn (f : ι → E → EReal) : E → EReal :=
  ofEpi (convexHull ℝ (⋃ i, epi (f i)))

/-- The convex hull of a family is convex — an instance of Theorem 5.3, since a convex hull is
convex. -/
theorem convexFn_convFn (f : ι → E → EReal) : ConvexFn (convFn f) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull lies below every member of the family. -/
theorem convFn_le (f : ι → E → EReal) (i : ι) : convFn f ≤ f i := by
  have h : epi (f i) ⊆ convexHull ℝ (⋃ j, epi (f j)) :=
    (subset_iUnion (fun j => epi (f j)) i).trans (subset_convexHull ℝ _)
  have h' := ofEpi_mono h
  rwa [ofEpi_epi] at h'

/-- **The universal property.** Any convex function below every `f i` is below the convex hull; with
`Tdaf.convFn_le` and `Tdaf.convexFn_convFn` this says the convex hull is the *greatest* convex
minorant of the family. -/
theorem le_convFn (hg : ConvexFn g) (h : ∀ i, g ≤ f i) : g ≤ convFn f :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (iUnion_subset fun i => epi_mono (h i)) hg.convex_epi)

/-- The universal property, packaged as `IsGreatest`. -/
theorem isGreatest_convFn (f : ι → E → EReal) :
    IsGreatest {g : E → EReal | ConvexFn g ∧ ∀ i, g ≤ f i} (convFn f) :=
  ⟨⟨convexFn_convFn f, convFn_le f⟩, fun _ hg => le_convFn hg.1 hg.2⟩

/-- The convex hull is monotone in the family. -/
theorem convFn_mono {f₁ f₂ : ι → E → EReal} (h : ∀ i, f₁ i ≤ f₂ i) : convFn f₁ ≤ convFn f₂ :=
  le_convFn (convexFn_convFn f₁) fun i => (convFn_le f₁ i).trans (h i)

/-- The epigraph of the convex hull is the convex hull of the union of epigraphs — under the
hypothesis that the latter is an epigraph at all. It need not be: even for two functions the
infimum in Theorem 5.6 need not be attained. Compare `Tdaf.epi_ofEpi`. -/
theorem epi_convFn (h : IsEpiLike (convexHull ℝ (⋃ i, epi (f i)))) :
    epi (convFn f) = convexHull ℝ (⋃ i, epi (f i)) :=
  epi_ofEpi h

/-- The convex hull is below the pointwise infimum. The inequality is strict in general — see
`Tdaf.convFn₂_indicatorFn_lt_inf` — and that is the entire reason the convex hull exists: the
pointwise infimum of convex functions is not convex. -/
theorem convFn_le_iInf (f : ι → E → EReal) (x : E) : convFn f x ≤ ⨅ i, f i x :=
  le_iInf fun i => convFn_le f i x

/-- When the pointwise infimum happens to be convex, it *is* the convex hull. -/
theorem convFn_eq_iInf (hc : ConvexFn fun x => ⨅ i, f i x) : convFn f = fun x => ⨅ i, f i x :=
  le_antisymm (fun x => convFn_le_iInf f x)
    (le_convFn hc fun i x => iInf_le (fun j => f j x) i)

end Family

/-! ### The convex hull of a single function -/

section Single

variable {g h : E → EReal}

/-- The **convex hull of a function**, `conv g`: the greatest convex function majorised by `g`
(Rockafellar §5, "the convex hull of a non-convex function `g`"). -/
noncomputable def convHullFn (g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi g))

/-- The convex hull of a function is convex (Theorem 5.3). -/
theorem convexFn_convHullFn (g : E → EReal) : ConvexFn (convHullFn g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull of a function lies below it. -/
theorem convHullFn_le (g : E → EReal) : convHullFn g ≤ g := by
  have h' := ofEpi_mono (subset_convexHull ℝ (epi g))
  rwa [ofEpi_epi] at h'

/-- **The universal property of `conv g`.** -/
theorem le_convHullFn (hh : ConvexFn h) (hg : h ≤ g) : h ≤ convHullFn g :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (epi_mono hg) hh.convex_epi)

/-- `conv g` is the greatest convex minorant of `g`. -/
theorem isGreatest_convHullFn (g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ g} (convHullFn g) :=
  ⟨⟨convexFn_convHullFn g, convHullFn_le g⟩, fun _ hh => le_convHullFn hh.1 hh.2⟩

/-- `conv` is monotone. -/
theorem convHullFn_mono (hgh : g ≤ h) : convHullFn g ≤ convHullFn h :=
  le_convHullFn (convexFn_convHullFn g) ((convHullFn_le g).trans hgh)

/-- A convex function is its own convex hull. -/
theorem convHullFn_eq_self (hg : ConvexFn g) : convHullFn g = g :=
  le_antisymm (convHullFn_le g) (le_convHullFn hg le_rfl)

/-- Convexity is exactly closedness under `conv`. -/
theorem convexFn_iff_convHullFn_eq : ConvexFn g ↔ convHullFn g = g :=
  ⟨convHullFn_eq_self, fun h => h ▸ convexFn_convHullFn g⟩

/-- `conv` is idempotent. -/
theorem convHullFn_idem (g : E → EReal) : convHullFn (convHullFn g) = convHullFn g :=
  convHullFn_eq_self (convexFn_convHullFn g)

end Single

/-! ### The coreflection onto the convex functions

The inclusion of the convex functions into all functions has a right adjoint, namely `conv`. Since
`conv` fixes the convex functions, the adjunction is a `GaloisCoinsertion`, from which
`Lattice.lean` obtains the complete lattice structure of §5 by
`GaloisCoinsertion.liftCompleteLattice`. -/

section Coreflection

/-- **`conv` is right adjoint to the inclusion of the convex functions.** For convex `h` and
arbitrary `g`, `h ≤ g` and `h ≤ conv g` say the same thing — which is the universal property
`Tdaf.le_convHullFn` read as an adjunction. -/
theorem gc_val_convHullFn :
    GaloisConnection (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  fun h g => ⟨fun hle => le_convHullFn h.2 hle,
    fun hle => (show (h : E → EReal) ≤ convHullFn g from hle).trans (convHullFn_le g)⟩

/-- The adjunction is a coinsertion, because `conv` fixes the convex functions. The convex
functions are therefore a *coreflective* subobject of all `EReal`-valued functions, and inherit a
complete lattice structure in which the infimum is `Tdaf.convFn`. -/
noncomputable def gci_val_convHullFn :
    GaloisCoinsertion (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  gc_val_convHullFn.toGaloisCoinsertion fun h => convHullFn_le (h : E → EReal)

end Coreflection

/-! ### The two hulls determine each other -/

section Compare

variable {ι : Sort*} {f : ι → E → EReal}

/-- Rockafellar: the convex hull of a collection "is the convex hull of the pointwise infimum of
the collection". Both sides are the greatest convex function below every `f i`. -/
theorem convFn_eq_convHullFn_iInf (f : ι → E → EReal) :
    convFn f = convHullFn fun x => ⨅ i, f i x :=
  le_antisymm (le_convHullFn (convexFn_convFn f) fun x => convFn_le_iInf f x)
    (le_convFn (convexFn_convHullFn _) fun i =>
      (convHullFn_le _).trans fun x => iInf_le (fun j => f j x) i)

/-- The convex hull of a single function is the convex hull of the one-element family, so
`Tdaf.convHullFn` really is a special case of `Tdaf.convFn`. -/
theorem convFn_unit (g : E → EReal) : convFn (fun _ : Unit => g) = convHullFn g := by
  rw [convFn_eq_convHullFn_iInf]
  simp

end Compare

/-! ### The binary case -/

section Binary

variable {f g h : E → EReal}

/-- The convex hull of two functions: the greatest convex function below both. This is the meet in
the lattice of convex functions. -/
noncomputable def convFn₂ (f g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi f ∪ epi g))

/-- The convex hull of two functions is convex. -/
theorem convexFn_convFn₂ (f g : E → EReal) : ConvexFn (convFn₂ f g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull of two functions lies below the first. -/
theorem convFn₂_le_left (f g : E → EReal) : convFn₂ f g ≤ f := by
  have h' := ofEpi_mono (subset_union_left.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

/-- The convex hull of two functions lies below the second. -/
theorem convFn₂_le_right (f g : E → EReal) : convFn₂ f g ≤ g := by
  have h' := ofEpi_mono (subset_union_right.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

/-- **The universal property**, binary case. -/
theorem le_convFn₂ (hh : ConvexFn h) (h₁ : h ≤ f) (h₂ : h ≤ g) : h ≤ convFn₂ f g :=
  subset_epi_iff_le_ofEpi.1
    (convexHull_min (union_subset (epi_mono h₁) (epi_mono h₂)) hh.convex_epi)

/-- The binary convex hull is the greatest convex function below both arguments. -/
theorem isGreatest_convFn₂ (f g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ f ∧ h ≤ g} (convFn₂ f g) :=
  ⟨⟨convexFn_convFn₂ f g, convFn₂_le_left f g, convFn₂_le_right f g⟩,
    fun _ hh => le_convFn₂ hh.1 hh.2.1 hh.2.2⟩

/-- The binary convex hull is below the pointwise minimum, generally strictly. -/
theorem convFn₂_le_inf (f g : E → EReal) : convFn₂ f g ≤ f ⊓ g :=
  le_inf (convFn₂_le_left f g) (convFn₂_le_right f g)

/-- The binary case is the two-element instance of `Tdaf.convFn`: both are the greatest convex
function below `f` and below `g`. -/
theorem convFn₂_eq_convFn (f g : E → EReal) :
    convFn₂ f g = convFn (fun b : Bool => cond b f g) := by
  refine le_antisymm (le_convFn (convexFn_convFn₂ f g) fun b => ?_)
    (le_convFn₂ (convexFn_convFn _) (convFn_le _ true) (convFn_le _ false))
  cases b
  · exact convFn₂_le_right f g
  · exact convFn₂_le_left f g

/-- **The inequality `Tdaf.convFn₂_le_inf` is strict in general.** The indicator functions of `{0}`
and `{1}` in `ℝ` are both convex; their pointwise minimum is `⊤` at `1 / 2`, while their convex
hull — the indicator function of the segment `[0, 1]` — is `0` there.

This is what makes the convex hull a genuinely new construction rather than a pointwise infimum,
and it is the reason `Tdaf.convFn` is defined through epigraphs. -/
theorem convFn₂_indicatorFn_lt_inf :
    convFn₂ (indicatorFn ({0} : Set ℝ)) (indicatorFn ({1} : Set ℝ)) (1 / 2) <
      indicatorFn ({0} : Set ℝ) (1 / 2) ⊓ indicatorFn ({1} : Set ℝ) (1 / 2) := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({0} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({1} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have hconv := convex_convexHull ℝ
    (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ)))
  have hmid := hconv (subset_convexHull ℝ _ (Or.inl h0)) (subset_convexHull ℝ _ (Or.inr h1))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpt : ((1 / 2 : ℝ), (0 : ℝ)) ∈
      convexHull ℝ (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ))) := by
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmid
  refine lt_of_le_of_lt (ofEpi_apply_le hpt) ?_
  rw [indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({0} : Set ℝ)),
    indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({1} : Set ℝ))]
  simp

/-! #### Theorem 5.6 for two functions -/

/-- Every convex combination `a • u + b • v = x` bounds the convex hull at `x`: this is the easy
half of Theorem 5.6.

Only `f, g ≠ ⊥` is needed, not full properness — with `⊥` allowed the right-hand side can be `⊥`
(as `⊥ + ⊤ = ⊥` in `EReal`) while the left-hand side is `⊤`. -/
theorem convFn₂_le_combo (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) {u v x : E} (hx : a • u + b • v = x) :
    convFn₂ f g x ≤ (a : EReal) * f u + (b : EReal) * g v := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    have hxv : v = x := by rw [← hx, hb1]; simp
    subst hb1
    subst hxv
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, zero_add]
    exact convFn₂_le_right f g v
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    have hxu : u = x := by rw [← hx, ha1]; simp
    subst ha1
    subst hxu
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, add_zero]
    exact convFn₂_le_left f g u
  by_cases hS : (a : EReal) * f u + (b : EReal) * g v = ⊤
  · rw [hS]; exact le_top
  have hfu : f u ≠ ⊤ := by
    intro hfu
    exact hS (by rw [hfu, EReal.coe_mul_top_of_pos ha',
      EReal.top_add_of_ne_bot (Tdaf.EReal.coe_mul_ne_bot hb'.le (hg v))])
  have hgv : g v ≠ ⊤ := by
    intro hgv
    exact hS (by rw [hgv, EReal.coe_mul_top_of_pos hb',
      EReal.add_top_of_ne_bot (Tdaf.EReal.coe_mul_ne_bot ha'.le (hf u))])
  obtain ⟨μ, hμ⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf u) (lt_top_iff_ne_top.2 hfu)
  obtain ⟨ν, hν⟩ :=
    Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg v) (lt_top_iff_ne_top.2 hgv)
  have hpt : (x, a * μ + b * ν) ∈ convexHull ℝ (epi f ∪ epi g) := by
    have hmem := convex_convexHull ℝ (epi f ∪ epi g)
      (subset_convexHull ℝ _ (Or.inl (mk_mem_epi.2 hμ.le)))
      (subset_convexHull ℝ _ (Or.inr (mk_mem_epi.2 hν.le))) ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hx] using hmem
  refine (ofEpi_apply_le hpt).trans (le_of_eq ?_)
  rw [hμ, hν, Tdaf.EReal.coe_mul_coe, Tdaf.EReal.coe_mul_coe, ← EReal.coe_add]

/-- **Rockafellar, Theorem 5.6, for two functions.** The convex hull of two proper convex functions
is given by the explicit formula

`(conv {f, g}) x = inf {a f u + b g v | a u + b v = x, a, b ≥ 0, a + b = 1}`.

Properness is Rockafellar's hypothesis and both halves of it are used: `f, g ≠ ⊥` keeps the sum
unambiguous (see `Tdaf.convFn₂_le_combo`), and `dom f, dom g ≠ ∅` makes the epigraphs non-empty,
which is what turns the convex hull of their union into the convex join (Rockafellar's Theorem 3.3,
Mathlib's `Convex.convexHull_union`).

Note that the infimum is over *all* representations, and it is genuinely an infimum: it need not be
attained, so the proof of `≥` goes through `Tdaf.le_ofEpi` rather than through a chosen witness.

`Tdaf.convFn_apply` proves the same theorem for an arbitrary family and needs only the `≠ ⊥` half
of properness; the extra hypothesis here buys the shorter proof through `convexJoin`. -/
theorem convFn₂_apply (hf : ConvexFn f) (hg : ConvexFn g) (hf' : Proper f) (hg' : Proper g)
    (x : E) :
    convFn₂ f g x = sInf {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} := by
  have hfe : (epi f).Nonempty := ((dom_eq_fst_image_epi f) ▸ hf'.dom_nonempty).of_image
  have hge : (epi g).Nonempty := ((dom_eq_fst_image_epi g) ▸ hg'.dom_nonempty).of_image
  refine le_antisymm (le_sInf ?_) ?_
  · rintro z ⟨a, b, u, v, ha, hb, hab, hx, rfl⟩
    exact convFn₂_le_combo hf'.ne_bot hg'.ne_bot ha hb hab hx
  · refine le_ofEpi fun μ hμ => ?_
    rw [hf.convex_epi.convexHull_union hg.convex_epi hfe hge] at hμ
    obtain ⟨p, hp, q, hq, a, b, ha, hb, hab, hcombo⟩ := mem_convexJoin.1 hμ
    have hx : a • p.1 + b • q.1 = x := congrArg Prod.fst hcombo
    have hμ2 : a * p.2 + b * q.2 = μ := congrArg Prod.snd hcombo
    have h₁ : (a : EReal) * f p.1 ≤ (a : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hp) (by exact_mod_cast ha)
    have h₂ : (b : EReal) * g q.1 ≤ (b : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hq) (by exact_mod_cast hb)
    have hmem : (a : EReal) * f p.1 + (b : EReal) * g q.1 ∈
        {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
          a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} :=
      ⟨a, b, p.1, q.1, ha, hb, hab, hx, rfl⟩
    refine (sInf_le hmem).trans ?_
    refine (add_le_add h₁ h₂).trans (le_of_eq ?_)
    rw [Tdaf.EReal.coe_mul_coe, Tdaf.EReal.coe_mul_coe, ← EReal.coe_add, hμ2]

/-- `conv (f ⊓ g) = conv {f, g}`: the convex hull of the pointwise minimum of two functions is the
convex hull of the pair. Both sides are the greatest convex function below both arguments. -/
theorem convHullFn_inf (f g : E → EReal) : convHullFn (f ⊓ g) = convFn₂ f g :=
  le_antisymm
    (le_convFn₂ (convexFn_convHullFn _) ((convHullFn_le _).trans inf_le_left)
      ((convHullFn_le _).trans inf_le_right))
    (le_convHullFn (convexFn_convFn₂ f g) (convFn₂_le_inf f g))

end Binary

end Module

/-! ### Theorem 5.6 in general -/

section Formula

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- **Rockafellar, Theorem 5.6.** The convex hull of a family of convex functions, none of which
takes the value `⊥`, is given by the explicit formula

`(conv {f i}) x = inf {∑ λ i * f i (x i) | ∑ λ i • x i = x}`,

the infimum being over all representations of `x` as a convex combination of points `x i`, with only
finitely many non-zero coefficients.

Rockafellar assumes the `f i` proper. Only the `≠ ⊥` half of properness is used, and it is used
twice: it keeps `λ i * f i (x i)` from being `−∞` where `λ i = 0` (Rockafellar's parenthetical "so
that the summation is unambiguous"), and it is what turns a finite bound on the sum into a finite
bound on each term. `dom (f i) ≠ ∅` does no work — with every `f i` identically `⊤` both sides are
`⊤` — exactly as in Theorem 5.2.

The proof of `≤` puts a representation into `Finset.centerMass` form. The proof of `≥` runs
Rockafellar's argument through Theorem 3.3 (`convexHull_eq`), which presents a point of the convex
hull as a combination of points drawn from the `epi (f i)` *with repetitions*, and then merges the
points drawn from one and the same `epi (f i)` into their center of mass — which is where convexity
of the `f i` enters, and the only place it does. -/
theorem convFn_apply {f : ι → E → EReal} (hf : ∀ i, ConvexFn (f i)) (hf' : ∀ i x, f i x ≠ ⊥)
    (x : E) :
    convFn f x = sInf {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
      (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
        z = ∑ i ∈ t, (w i : EReal) * f i (p i)} := by
  classical
  refine le_antisymm (le_sInf ?_) ?_
  -- **`≤`**: the convex hull is below the value of every representation of `x`.
  · rintro z ⟨t, w, p, hw₀, hw₁, hwx, rfl⟩
    by_cases htop : ∑ i ∈ t, (w i : EReal) * f i (p i) = ⊤
    · rw [htop]; exact le_top
    have hbot : ∀ i ∈ t, (w i : EReal) * f i (p i) ≠ ⊥ := fun i hi =>
      Tdaf.EReal.coe_mul_ne_bot (hw₀ i hi) (hf' i (p i))
    have hnetop := Tdaf.EReal.forall_ne_top_of_sum_ne_top t _ hbot htop
    -- discard the indices carrying zero weight, whose points need not lie in `dom (f i)`
    set t' : Finset ι := t.filter (fun i => 0 < w i) with ht'def
    have hsub : t' ⊆ t := Finset.filter_subset _ _
    have hzero : ∀ i ∈ t, i ∉ t' → w i = 0 := by
      intro i hi hi'
      rcases eq_or_lt_of_le (hw₀ i hi) with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.2 ⟨hi, h⟩) hi'
    have hw₁' : ∑ i ∈ t', w i = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
    have hwx' : ∑ i ∈ t', w i • p i = x := by
      rw [Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]]; exact hwx
    obtain ⟨μ, hμ⟩ : ∃ μ : ι → ℝ, ∀ i ∈ t', f i (p i) = (μ i : EReal) := by
      refine ⟨fun i => (f i (p i)).toReal, fun i hi => ?_⟩
      have hpos : 0 < w i := (Finset.mem_filter.1 hi).2
      have hne : f i (p i) ≠ ⊤ := fun hcon =>
        hnetop i (hsub hi) (by rw [hcon, _root_.EReal.coe_mul_top_of_pos hpos])
      exact (_root_.EReal.coe_toReal hne (hf' i (p i))).symm
    have hcm := Finset.centerMass_mem_convexHull t'
      (fun i hi => ((Finset.mem_filter.1 hi).2).le) (by rw [hw₁']; exact zero_lt_one)
      (z := fun i => ((p i, μ i) : E × ℝ))
      (fun i hi => mem_iUnion.2 ⟨i, mk_mem_epi.2 (le_of_eq (hμ i hi))⟩)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁'] at hcm
    have hsplit : ∑ i ∈ t', w i • ((p i, μ i) : E × ℝ) = (x, ∑ i ∈ t', w i * μ i) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]; simpa using hwx'
      · rw [Prod.snd_sum]; simp [smul_eq_mul]
    rw [hsplit] at hcm
    refine (ofEpi_apply_le hcm).trans (le_of_eq ?_)
    rw [Tdaf.EReal.coe_sum,
      ← Finset.sum_subset hsub (fun i hi hi' => by rw [hzero i hi hi']; simp)]
    exact Finset.sum_congr rfl fun i hi => by rw [hμ i hi, Tdaf.EReal.coe_mul_coe]
  -- **`≥`**: every point of the convex hull of the union comes from a representation.
  · refine le_ofEpi fun ν hν => ?_
    rw [convexHull_eq] at hν
    obtain ⟨κ, s, w, z, hw₀, hw₁, hz, hcm⟩ := hν
    set s' : Finset κ := s.filter (fun j => 0 < w j) with hs'def
    have hsub : s' ⊆ s := Finset.filter_subset _ _
    have hwpos : ∀ j ∈ s', 0 < w j := fun j hj => (Finset.mem_filter.1 hj).2
    have hzero : ∀ j ∈ s, j ∉ s' → w j = 0 := by
      intro j hj hj'
      rcases eq_or_lt_of_le (hw₀ j hj) with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.2 ⟨hj, h⟩) hj'
    have hw₁' : ∑ j ∈ s', w j = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
    have hcm' : ∑ j ∈ s', w j • z j = (x, ν) := by
      rw [Finset.sum_subset hsub fun j hj hj' => by rw [hzero j hj hj', zero_smul],
        ← Finset.centerMass_eq_of_sum_1 _ _ hw₁]
      exact hcm
    -- choose, for each point of the combination, an index whose epigraph it belongs to
    obtain ⟨j₀, hj₀⟩ : s'.Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [hw₁']; exact one_ne_zero)
    obtain ⟨i₀, -⟩ := mem_iUnion.1 (hz j₀ (hsub hj₀))
    have hchoice : ∀ j : κ, ∃ i : ι, j ∈ s' → z j ∈ epi (f i) := by
      intro j
      by_cases hj : j ∈ s'
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (hz j (hsub hj))
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun hcon => absurd hcon hj⟩
    choose σ hσ using hchoice
    -- merge the points drawn from one and the same epigraph into their center of mass
    obtain ⟨W, hW⟩ : ∃ W : ι → ℝ, ∀ i, W i = ∑ j ∈ s' with σ j = i, w j := ⟨_, fun _ => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ι → E × ℝ,
        ∀ i, Q i = (s'.filter fun j => σ j = i).centerMass w z := ⟨_, fun _ => rfl⟩
    have hmaps : ∀ j ∈ s', σ j ∈ s'.image σ := fun j hj => Finset.mem_image_of_mem σ hj
    have hWpos : ∀ i ∈ s'.image σ, 0 < W i := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [hW]
      exact Finset.sum_pos (fun k hk => hwpos k (Finset.mem_filter.1 hk).1)
        ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩
    have hQmem : ∀ i ∈ s'.image σ, Q i ∈ epi (f i) := by
      intro i hi
      rw [hQ]
      refine (hf i).convex_epi.centerMass_mem
        (fun j hj => (hwpos j (Finset.mem_filter.1 hj).1).le) ?_ (fun j hj => ?_)
      · have := hWpos i hi; rwa [hW] at this
      · obtain ⟨hj₁, hj₂⟩ := Finset.mem_filter.1 hj
        exact hj₂ ▸ hσ j hj₁
    have hWsum : ∑ i ∈ s'.image σ, W i = 1 := by
      simp only [hW]
      rw [Finset.sum_fiberwise_of_maps_to hmaps w]
      exact hw₁'
    have hQsum : ∑ i ∈ s'.image σ, W i • Q i = (x, ν) := by
      have hstep : ∀ i ∈ s'.image σ, W i • Q i = ∑ j ∈ s' with σ j = i, w j • z j := by
        intro i hi
        have hWi : (∑ j ∈ s' with σ j = i, w j) ≠ 0 := by
          have hpos := hWpos i hi
          rw [hW] at hpos
          exact hpos.ne'
        rw [hQ, Finset.centerMass, hW, smul_inv_smul₀ hWi]
      rw [Finset.sum_congr rfl hstep,
        Finset.sum_fiberwise_of_maps_to hmaps (fun j => w j • z j)]
      exact hcm'
    have hx' : ∑ i ∈ s'.image σ, W i • (Q i).1 = x := by
      have hfst := congrArg Prod.fst hQsum
      rw [Prod.fst_sum] at hfst
      simpa using hfst
    have hν' : ∑ i ∈ s'.image σ, W i * (Q i).2 = ν := by
      have hsnd := congrArg Prod.snd hQsum
      rw [Prod.snd_sum] at hsnd
      simpa [smul_eq_mul] using hsnd
    have hval : ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1) ≤ (ν : EReal) := by
      calc ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)
          ≤ ∑ i ∈ s'.image σ, (W i : EReal) * (((Q i).2 : ℝ) : EReal) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (mem_epi.1 (hQmem i hi))
              (by exact_mod_cast (hWpos i hi).le)
        _ = ((∑ i ∈ s'.image σ, W i * (Q i).2 : ℝ) : EReal) := by
            rw [Tdaf.EReal.coe_sum]
            exact Finset.sum_congr rfl fun i _ => (Tdaf.EReal.coe_mul_coe _ _).symm
        _ = (ν : EReal) := by rw [hν']
    have hmemS : (∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)) ∈
        {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
          (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
            z = ∑ i ∈ t, (w i : EReal) * f i (p i)} :=
      ⟨s'.image σ, W, fun i => (Q i).1, fun i hi => (hWpos i hi).le, hWsum, hx', rfl⟩
    exact (sInf_le hmemS).trans hval

end Formula

end Tdaf
