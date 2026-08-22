/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Tdaf.Analysis.Convex.Epigraph

/-!
# The function determined by a set in `E × ℝ`

Rockafellar's Theorem 5.3 records a device: to build a convex function on `E`, build a convex set
`F` in `E × ℝ` and take the function whose graph is the *lower boundary* of `F`,

`ofEpi F x = inf {μ : ℝ | (x, μ) ∈ F}`.

This is the single generator of §5. Infimal convolution, right scalar multiplication, the convex
hull of a family of functions, the image of a function under a linear map, and the
lower-semicontinuous hull are all `ofEpi` applied to a set built from epigraphs, so this file is
written to be used by all of them.

## Main definitions

* `ofEpi F` — the function determined by `F ⊆ E × ℝ`.
* `IsEpiLike F` — `F` *is* an epigraph, i.e. `F = epi f` for some `f`.

## Main results

* `subset_epi_iff_le_ofEpi` — the defining adjunction `F ⊆ epi g ↔ g ≤ ofEpi F`. `ofEpi` and
  `epi` form an antitone Galois connection, and every order fact below is a formal consequence.
* `convexFn_ofEpi` — **Rockafellar's Theorem 5.3**: `ofEpi F` is convex when `F` is.
* `ofEpi_epi` — `ofEpi (epi f) = f`, with no hypothesis.
* `epi_ofEpi` — `epi (ofEpi F) = F`, under `IsEpiLike F`.
* `IsEpiLike.iInter`, `IsEpiLike.inter`, `IsEpiLike.union`,
  `IsEpiLike.of_isClosed`, `IsEpiLike.closure` — the stability properties that the §5
  operations consume.

## Design notes

`epi (ofEpi F) = F` is **false in general**, and the failure is the whole content of this file.
Only `F ⊆ epi (ofEpi F)` holds unconditionally; equality says exactly that every vertical section
`{μ : ℝ | (x, μ) ∈ F}` is one of `∅`, `ℝ`, `Set.Ici c` — upward closed *and* attaining its
infimum. Both halves are needed: `Set.Ioi c` is upward closed but does not attain, and `{0}`
attains but is not upward closed. Since a set of that shape is precisely a vertical section of an
epigraph, `IsEpiLike F` is *defined* as `∃ f, F = epi f`; `isEpiLike_iff_forall` is the
pointwise criterion one actually checks, and `isEpiLike_iff` says the witness is always
`ofEpi F`.

The definition of `ofEpi` needs no structure on `E` whatsoever, so `IsEpiLike` and the whole order
API live in a structure-free section; only Theorem 5.3 itself needs a real vector space.

Note that `IsEpiLike` is *not* preserved by the operations that §5 cares about most: the sum of two
epigraphs need not be an epigraph (an infimal convolution need not attain its infimum), and neither
need the convex hull of a union. Those modules must carry `IsEpiLike` as a hypothesis, which is why
it is a named predicate here rather than an inline side condition.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (Theorem 5.3 and the
  paragraph preceding it).
-/

open Set

namespace Tdaf.ConvexAnalysis

section Basic

variable {E : Type*}

/-! ### The function determined by a set -/

/-- The function whose graph is the *lower boundary* of a set `F ⊆ E × ℝ`:
`ofEpi F x = inf {μ | (x, μ) ∈ F}` (Rockafellar §5, the construction of Theorem 5.3).

The infimum is taken in `EReal`, so it is `⊤` when the vertical section over `x` is empty and `⊥`
when that section is unbounded below. Rockafellar draws attention to the first convention in the
proof of Theorem 5.3. -/
noncomputable def ofEpi (F : Set (E × ℝ)) : E → EReal :=
  fun x => ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)

variable {F G : Set (E × ℝ)} {f g : E → EReal} {x : E} {μ ν : ℝ} {z : EReal}

/-- Every point of `F` bounds `ofEpi F` from above. -/
theorem ofEpi_apply_le (h : (x, μ) ∈ F) : ofEpi F x ≤ (μ : EReal) :=
  iInf₂_le (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) μ h

/-- The dual half of the definition: `ofEpi F x` is the *greatest* lower bound. -/
theorem le_ofEpi (h : ∀ μ : ℝ, (x, μ) ∈ F → z ≤ (μ : EReal)) : z ≤ ofEpi F x :=
  le_iInf₂ (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) h

/-- An infimum is strictly below `z` exactly when some member of the section is. This is the
workhorse of the file: the infimum defining `ofEpi F x` need not be attained, so every argument
about `ofEpi` proceeds through a strict inequality. -/
theorem ofEpi_lt_iff : ofEpi F x < z ↔ ∃ μ : ℝ, (x, μ) ∈ F ∧ (μ : EReal) < z := by
  simp only [ofEpi, iInf_lt_iff, exists_prop]
  exact Iff.rfl

/-- **The universal property.** `ofEpi F` is the greatest `EReal`-valued function whose epigraph
contains `F`; equivalently, `epi` and `ofEpi` form an antitone Galois connection between
`Set (E × ℝ)` and `E → EReal`. -/
theorem subset_epi_iff_le_ofEpi : F ⊆ epi g ↔ g ≤ ofEpi F := by
  constructor
  · exact fun h y => le_ofEpi fun _ hμ => h hμ
  · rintro h ⟨y, ρ⟩ hp
    exact (h y).trans (ofEpi_apply_le hp)

/-- `F` always lies in the epigraph of the function it determines. The reverse inclusion is
`epi_ofEpi` and needs `IsEpiLike`. -/
theorem subset_epi_ofEpi (F : Set (E × ℝ)) : F ⊆ epi (ofEpi F) :=
  subset_epi_iff_le_ofEpi.2 le_rfl

/-- `ofEpi` is antitone: a larger set has more points to take an infimum over. (Compare
`epi_anti`, which is antitone in the same sense.) -/
theorem ofEpi_mono (h : F ⊆ G) : ofEpi G ≤ ofEpi F :=
  subset_epi_iff_le_ofEpi.1 (h.trans (subset_epi_ofEpi G))

/-- `ofEpi F x = ⊤` exactly when the vertical section over `x` is empty: the infimum of the empty
set of reals is `+∞`, the convention Rockafellar highlights in the proof of Theorem 5.3. -/
theorem ofEpi_eq_top_iff : ofEpi F x = ⊤ ↔ ∀ μ : ℝ, (x, μ) ∉ F := by
  rw [← not_iff_not, ← Ne, ← lt_top_iff_ne_top, ofEpi_lt_iff]
  simp

@[simp] theorem ofEpi_empty : ofEpi (∅ : Set (E × ℝ)) = ⊤ :=
  funext fun _ => ofEpi_eq_top_iff.2 fun _ => notMem_empty _

@[simp] theorem ofEpi_univ : ofEpi (univ : Set (E × ℝ)) = ⊥ :=
  funext fun _ => Tdaf.EReal.eq_bot_of_forall_le_coe fun r => ofEpi_apply_le (mem_univ (_, r))

/-- The epigraph of `f` determines `f` back: this holds with no hypothesis at all, because a
vertical section of an epigraph is `∅`, `ℝ` or a closed half-line, and in each case the infimum is
the value of `f`. -/
@[simp] theorem ofEpi_epi (f : E → EReal) : ofEpi (epi f) = f := by
  refine le_antisymm (fun x => ?_) (subset_epi_iff_le_ofEpi.1 subset_rfl)
  rcases eq_top_or_lt_top (f x) with h | h
  · rw [h]; exact le_top
  by_cases hb : f x = ⊥
  · rw [hb, le_bot_iff]
    exact Tdaf.EReal.eq_bot_of_forall_le_coe fun r =>
      ofEpi_apply_le (mk_mem_epi.2 (hb.le.trans bot_le))
  · obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb h
    exact hr ▸ ofEpi_apply_le (mk_mem_epi.2 hr.le)

/-- A function is recovered from its epigraph, in the form used to identify the §5 operations with
their `ofEpi` descriptions. -/
theorem eq_ofEpi_of_epi_eq (h : epi f = F) : f = ofEpi F := by rw [← h, ofEpi_epi]

/-- `ofEpi F x` depends only on the vertical section of `F` over `x`. -/
theorem ofEpi_apply_congr (h : ∀ μ : ℝ, (x, μ) ∈ F ↔ (x, μ) ∈ G) : ofEpi F x = ofEpi G x := by
  have hs : {μ : ℝ | (x, μ) ∈ F} = {μ : ℝ | (x, μ) ∈ G} := Set.ext h
  simp only [ofEpi, hs]

/-- The effective domain of `ofEpi F` is the projection of `F` on `E`, for any `F`. This is
`dom_eq_fst_image_epi` transported across the Galois connection; it holds with no hypothesis
because `ofEpi F x < ⊤` says exactly that the vertical section over `x` is nonempty. -/
theorem dom_ofEpi (F : Set (E × ℝ)) : dom (ofEpi F) = Prod.fst '' F := by
  ext x
  constructor
  · intro hx
    by_contra hx'
    exact absurd (ofEpi_eq_top_iff.2 fun μ hμ => hx' ⟨(x, μ), hμ, rfl⟩) hx.ne
  · rintro ⟨⟨w, μ⟩, hw, rfl⟩
    exact lt_of_le_of_lt (ofEpi_apply_le hw) (_root_.EReal.coe_lt_top μ)

/-! ### The Galois connection between sets and functions

`subset_epi_iff_le_ofEpi` says exactly that `ofEpi` and `epi` are adjoint, antitonely. Recording
that as Mathlib's `GaloisConnection` — and, since `ofEpi (epi f) = f`, as a `GaloisInsertion` —
makes the whole `ClosureOperator` API available, and identifies `IsEpiLike` with the closed elements
of that operator. The `OrderDual` on the function side is what makes the antitone adjunction fit
Mathlib's monotone `GaloisConnection`. -/

open OrderDual in
/-- `ofEpi` is left adjoint to `epi`, antitonely: `F ⊆ epi g ↔ g ≤ ofEpi F`. -/
theorem gc_ofEpi_epi :
    GaloisConnection (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  fun _ _ => subset_epi_iff_le_ofEpi.symm

open OrderDual in
/-- The adjunction is an insertion, because `ofEpi (epi f) = f` on the nose. -/
noncomputable def gi_ofEpi_epi :
    GaloisInsertion (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  gc_ofEpi_epi.toGaloisInsertion fun g => le_of_eq (by simp [ofEpi_epi])

/-- The closure operator `F ↦ epi (ofEpi F)` induced by the adjunction. Its closed elements are
exactly the epi-like sets, so `Mathlib`'s `ClosureOperator` API — monotonicity, extensivity,
idempotence, and the complete lattice of closed elements — applies to them. -/
noncomputable def epiClosure : ClosureOperator (Set (E × ℝ)) := gc_ofEpi_epi.closureOperator

@[simp] theorem epiClosure_apply (F : Set (E × ℝ)) : epiClosure F = epi (ofEpi F) := rfl

/-- `epi` is injective: a function is determined by its epigraph. -/
theorem epi_injective : Function.Injective (epi : (E → EReal) → Set (E × ℝ)) :=
  fun _ _ h => by simpa using congrArg ofEpi h

/-! ### Sets that are epigraphs -/

/-- `F ⊆ E × ℝ` is *epi-like* when it is the epigraph of some function `E → EReal`.

Equivalently (`isEpiLike_iff_forall`), every vertical section `{μ | (x, μ) ∈ F}` is upward
closed and attains its infimum — that is, it is `∅`, `ℝ`, or a closed half-line `Set.Ici c`.

This is the condition under which `epi (ofEpi F) = F`, and it is a genuine hypothesis: it fails for
`{p | 0 < p.2}` (upward closed but not attaining) and for `{(0, 0)}` (attaining but not upward
closed). Stating it as an existential makes it a *concept* — "`F` is an epigraph" — rather than a
pair of side conditions, and makes `isEpiLike_epi` and the stability lemmas below one-liners;
`isEpiLike_iff` recovers the canonical witness, which is always `ofEpi F`. -/
def IsEpiLike (F : Set (E × ℝ)) : Prop := ∃ f : E → EReal, F = epi f

@[simp] theorem isEpiLike_epi (f : E → EReal) : IsEpiLike (epi f) := ⟨f, rfl⟩

/-- **The point of `IsEpiLike`.** For an epi-like set the two constructions are inverse. -/
@[simp] theorem epi_ofEpi (h : IsEpiLike F) : epi (ofEpi F) = F := by
  obtain ⟨f, rfl⟩ := h
  rw [ofEpi_epi]

/-- `ofEpi F` is the only possible witness, so `IsEpiLike` is decided by a single equation. -/
theorem isEpiLike_iff : IsEpiLike F ↔ epi (ofEpi F) = F :=
  ⟨epi_ofEpi, fun h => ⟨ofEpi F, h.symm⟩⟩

/-- `IsEpiLike` is `epiClosure`-closedness. -/
theorem isEpiLike_iff_isClosed {F : Set (E × ℝ)} : IsEpiLike F ↔ epiClosure.IsClosed F :=
  isEpiLike_iff

/-- Vertical sections of an epi-like set are upward closed. -/
theorem IsEpiLike.mem_of_le (h : IsEpiLike F) (hμ : (x, μ) ∈ F) (hμν : μ ≤ ν) : (x, ν) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  exact mk_mem_epi.2 ((mk_mem_epi.1 hμ).trans (by exact_mod_cast hμν))

/-- Vertical sections of an epi-like set attain their infima: they are closed from below. -/
theorem IsEpiLike.mem_of_forall_lt (h : IsEpiLike F) (hμ : ∀ ν : ℝ, μ < ν → (x, ν) ∈ F) :
    (x, μ) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  refine mk_mem_epi.2 (Tdaf.EReal.le_coe_of_forall_lt fun q hq => ?_)
  obtain ⟨ρ, hμρ, hρq⟩ := exists_between hq
  exact lt_of_le_of_lt (mk_mem_epi.1 (hμ ρ hμρ)) (by exact_mod_cast hρq)

/-- The criterion one checks in practice: a set whose vertical sections are upward closed and
closed from below is an epigraph. -/
theorem isEpiLike_of_forall
    (hmono : ∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F)
    (hbelow : ∀ (x : E) (μ : ℝ), (∀ ν : ℝ, μ < ν → (x, ν) ∈ F) → (x, μ) ∈ F) :
    IsEpiLike F := by
  refine isEpiLike_iff.2 (subset_antisymm ?_ (subset_epi_ofEpi F))
  rintro ⟨y, ρ⟩ hp
  refine hbelow y ρ fun σ hσ => ?_
  have hlt : ofEpi F y < (σ : EReal) :=
    lt_of_le_of_lt (mk_mem_epi.1 hp) (by exact_mod_cast hσ)
  obtain ⟨τ, hτF, hτσ⟩ := ofEpi_lt_iff.1 hlt
  exact hmono y τ σ hτF (by exact_mod_cast hτσ.le)

/-- The two halves of `IsEpiLike`, as a characterisation. -/
theorem isEpiLike_iff_forall :
    IsEpiLike F ↔ (∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F) ∧
      ∀ (x : E) (μ : ℝ), (∀ ν : ℝ, μ < ν → (x, ν) ∈ F) → (x, μ) ∈ F :=
  ⟨fun h => ⟨fun _ _ _ hμ hμν => h.mem_of_le hμ hμν, fun _ _ hμ => h.mem_of_forall_lt hμ⟩,
    fun h => isEpiLike_of_forall h.1 h.2⟩

/-- An arbitrary intersection of epigraphs is an epigraph — the epigraph of the pointwise supremum.
This is the epigraph half of Rockafellar's Theorem 5.5. -/
theorem IsEpiLike.iInter {ι : Sort*} {F : ι → Set (E × ℝ)} (h : ∀ i, IsEpiLike (F i)) :
    IsEpiLike (⋂ i, F i) := by
  choose f hf using h
  refine ⟨⨆ i, f i, ?_⟩
  ext p
  simp [hf, epi, iSup_apply, iSup_le_iff]

/-- The intersection of two epigraphs is the epigraph of the pointwise maximum. -/
theorem IsEpiLike.inter (hF : IsEpiLike F) (hG : IsEpiLike G) : IsEpiLike (F ∩ G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  refine ⟨f ⊔ g, ?_⟩
  ext p
  simp [epi, sup_le_iff]

/-- The union of two epigraphs is the epigraph of the pointwise minimum. Note that this uses
linearity of `EReal` and fails for infinite unions: the union of the epigraphs of the constants
`1 / (n + 1)` is not an epigraph. -/
theorem IsEpiLike.union (hF : IsEpiLike F) (hG : IsEpiLike G) : IsEpiLike (F ∪ G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  refine ⟨f ⊓ g, ?_⟩
  ext p
  simp [epi, inf_le_iff]

end Basic

/-! ### Theorem 5.3 -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Rockafellar, Theorem 5.3.** The function whose graph is the lower boundary of a convex set
`F ⊆ E × ℝ` is convex.

Rockafellar's proof is "evident from Theorem 4.2", and that really is the route: the infimum
defining `ofEpi F x` need not be attained, so no witness can be chosen from a non-strict
inequality. Theorem 4.2 (`convexFn_iff_forall_lt`) asks only for *strict* upper bounds
`ofEpi F x < α`, and a strict inequality against an infimum does produce a witness
(`ofEpi_lt_iff`). -/
theorem convexFn_ofEpi {F : Set (E × ℝ)} (hF : Convex ℝ F) : ConvexFn (ofEpi F) := by
  rw [convexFn_iff_forall_lt]
  intro x y a b ha hb hab α β hx hy
  obtain ⟨μ, hμF, hμα⟩ := ofEpi_lt_iff.1 hx
  obtain ⟨ν, hνF, hνβ⟩ := ofEpi_lt_iff.1 hy
  have hcombo : (a • x + b • y, a * μ + b * ν) ∈ F := by
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hF hμF hνF ha.le hb.le hab
  refine lt_of_le_of_lt (ofEpi_apply_le hcombo) ?_
  have h1 : a * μ < a * α := mul_lt_mul_of_pos_left (by exact_mod_cast hμα) ha
  have h2 : b * ν < b * β := mul_lt_mul_of_pos_left (by exact_mod_cast hνβ) hb
  exact_mod_cast add_lt_add h1 h2

end Module

/-! ### Epi-likeness and topology -/

section Topology

variable {E : Type*} [TopologicalSpace E] {F : Set (E × ℝ)}

/-- A **closed** set whose vertical sections are upward closed is an epigraph.

Closedness alone does not suffice — `{(0, 0)}` is closed but is not an epigraph — so the
upward-closure hypothesis is not removable. What closedness buys is the other half: a closed
vertical section contains the infimum of its points. -/
theorem IsEpiLike.of_isClosed
    (hmono : ∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F) (hF : IsClosed F) :
    IsEpiLike F := by
  refine isEpiLike_of_forall hmono fun x μ hμ => ?_
  have hcont : Continuous fun ν : ℝ => (x, ν) := continuous_const.prodMk continuous_id
  have hclosed : IsClosed ((fun ν : ℝ => (x, ν)) ⁻¹' F) := hF.preimage hcont
  have hsub : Ioi μ ⊆ (fun ν : ℝ => (x, ν)) ⁻¹' F := fun ν hν => hμ ν hν
  have hmem : μ ∈ closure (Ioi μ) := by rw [closure_Ioi]; exact le_refl μ
  have hmem' := closure_mono hsub hmem
  rwa [hclosed.closure_eq] at hmem'

variable [AddZeroClass E] [ContinuousAdd E]

/-- The closure of an epigraph is an epigraph. This is what `lscHull f := ofEpi (closure (epi f))`
needs in order to satisfy `epi (lscHull f) = closure (epi f)`. -/
theorem IsEpiLike.closure (h : IsEpiLike F) : IsEpiLike (_root_.closure F) := by
  refine IsEpiLike.of_isClosed (fun x μ ν hμ hμν => ?_) isClosed_closure
  have hcont : Continuous fun p : E × ℝ => p + ((0 : E), ν - μ) :=
    continuous_id.add continuous_const
  have himg : (fun p : E × ℝ => p + ((0 : E), ν - μ)) '' F ⊆ F := by
    rintro _ ⟨⟨z, ρ⟩, hz, rfl⟩
    simpa using h.mem_of_le hz (by linarith : ρ ≤ ρ + (ν - μ))
  have hmem := image_closure_subset_closure_image hcont (mem_image_of_mem _ hμ)
  have hmem' := closure_mono himg hmem
  simpa using hmem'

end Topology

end Tdaf.ConvexAnalysis
