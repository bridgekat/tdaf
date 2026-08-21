/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Indicator
import Tdaf.Analysis.Convex.Operations.Epi

/-!
# Infimal convolution

Rockafellar's `f □ g`, the functional operation corresponding to addition of epigraphs
(*Convex Analysis*, §5, Theorem 5.4). It is the first application of the device of Theorem 5.3,
and it is dual to pointwise addition of convex functions under the conjugacy of §16.

## Main definitions

* `Tdaf.infConv f g` — the infimal convolute `f □ g`, **defined** as `ofEpi (epi f + epi g)`.
* `Tdaf.InfConvFn E` — the type synonym `E → EReal` carrying `□` as its addition, so that
  Rockafellar's m-ary `f₁ □ ⋯ □ fₘ` is a `Finset.sum`.

## Main results

* `Tdaf.convexFn_infConv` — **Theorem 5.4**: `f □ g` is convex when `f` and `g` are.
* `Tdaf.infConv_apply` — the classical formula `(f □ g) x = ⨅ y, f (x - y) + g y`, valid when
  neither function takes the value `⊥`.
* `Tdaf.dom_infConv` — `dom (f □ g) = dom f + dom g`, with no hypothesis at all.
* `Tdaf.infConv_comm`, `Tdaf.infConv_assoc`, `Tdaf.infConv_indicatorFn_zero` — `□` is commutative
  and associative with identity `δ(· | 0)`, exactly as Rockafellar states in the paragraph after
  Theorem 5.4. `Tdaf.InfConvFn.instAddCommMonoid` records this as a Mathlib `AddCommMonoid`.
* `Tdaf.infConv_indicatorFn_singleton` — `f □ δ(· | a)` translates the graph of `f` by `a`.
* `Tdaf.convexFn_sum_toInfConvFn` — Theorem 5.4 for `m` functions, as a `Finset.sum` in
  `Tdaf.InfConvFn E`.

## Design notes

**Why the definition is not the infimum formula.** Rockafellar states Theorem 5.4 for *proper*
convex functions and then remarks that "infimal convolution of improper functions [is not] defined
by this formula, because of the rule of avoiding `∞ - ∞`", giving instead the epigraph definition
`(f₁ □ f₂) x = inf {μ | (x, μ) ∈ epi f₁ + epi f₂}`. That is the definition used here. The infimum
formula is recovered as `Tdaf.infConv_apply` under `∀ x, f x ≠ ⊥` and `∀ x, g x ≠ ⊥`; the
hypotheses are not decoration. Take `f ≡ ⊤` and `g` with `g 0 = ⊥`: then `epi f = ∅`, so
`epi f + epi g = ∅` and `(f □ g) x = ⊤`, while `⨅ y, f (x - y) + g y = ⊤ + ⊥ = ⊥`. One `≠ ⊥`
hypothesis does not suffice either — that example uses only `f x = ⊤` and `g y = ⊥` — so both are
carried, inline, following the treatment of Theorem 5.2 in `Operations/Basic.lean`.

**`epi (f □ g) = epi f + epi g` is false.** Only `epi f + epi g ⊆ epi (f □ g)` holds
(`Tdaf.subset_epi_infConv`): the infimum defining `f □ g` need not be attained, and a sum of
epigraphs need not be an epigraph. On `ℝ`, take `f x = 1/x` for `x > 0` and `⊤` otherwise, and
`g ≡ 0`. Both are convex, `epi g = ℝ ×ˢ Ici 0`, and every vertical section of `epi f + epi g` is
`Ioi 0`: the sum is `ℝ ×ˢ Ioi 0`, which is not an epigraph. Indeed `f □ g ≡ 0`, whose epigraph is
`ℝ ×ˢ Ici 0`. `Tdaf.epi_infConv` therefore carries `Tdaf.IsEpiLike (epi f + epi g)` as a
hypothesis.

**Associativity is not `add_assoc`.** Because `epi (f □ g)` is strictly larger than
`epi f + epi g` in general, `epi ((f □ g) □ h)` is *not* `(epi f + epi g) + epi h`, and
associativity does not follow from associativity of set addition alone. What makes it work is
`Tdaf.epi_ofEpi_add_subset`: enlarging a summand to the epigraph it determines does not move the
lower boundary of the sum, so `Tdaf.infConv_ofEpi_left` lets the `ofEpi` be peeled off. The same
lemma is what a future `smulRight` / `convFn` / `mapLin` file will need.

**The monoid instance.** Rockafellar: "infimal convolution is commutative, associative and
convexity-preserving. The function `δ(· | 0)` acts as the identity element". That is an
`AddCommMonoid`, and it is instantiated on the type synonym `Tdaf.InfConvFn E` — a synonym is
forced, since `E → EReal` already carries `Pi.addCommMonoid` (pointwise `+`, the operation `□` is
*dual* to) and `Pi.commMonoid` (pointwise `*`). Additive notation is the right one: `□` is
epigraph addition, and its unit `δ(· | 0)` is an indicator of `{0}`. The payoff is Theorem 5.4 in
the book's own m-ary form, `Tdaf.convexFn_sum_toInfConvFn`, via `Finset.sum` and
`Finset.cons_induction`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5 (Theorem 5.4 and the
  discussion following it).
-/

open Pointwise Set

namespace Tdaf

/-! ### The definition and its epigraph -/

section Basic

variable {E : Type*} [AddCommGroup E] {f g f₁ f₂ g₁ g₂ : E → EReal} {y z : E} {ν ρ : ℝ}

/-- **Infimal convolution**, Rockafellar §5: `f □ g`.

*Defined* by addition of epigraphs, not by the infimum formula
`(f □ g) x = ⨅ y, f (x - y) + g y`: the latter is ill-formed when `f` or `g` takes the value `⊥`,
because it then produces the forbidden `∞ - ∞`. Rockafellar makes exactly this point after Theorem
5.4 and gives this definition instead. See `Tdaf.infConv_apply` for the infimum formula as a
theorem. -/
noncomputable def infConv (f g : E → EReal) : E → EReal := ofEpi (epi f + epi g)

/-- The definition of `Tdaf.infConv`, as a rewrite rule. -/
theorem infConv_def (f g : E → EReal) : infConv f g = ofEpi (epi f + epi g) := rfl

/-- The sum of the epigraphs is always contained in the epigraph of the infimal convolute. The
reverse inclusion is `Tdaf.epi_infConv` and is genuinely conditional. -/
theorem subset_epi_infConv (f g : E → EReal) : epi f + epi g ⊆ epi (infConv f g) :=
  subset_epi_ofEpi _

/-- Rockafellar's description of `epi (f □ g)`, under the hypothesis that makes it true.

The hypothesis is not removable: the infimum defining `f □ g` need not be attained, so a sum of
epigraphs need not be an epigraph. See the module docstring. -/
theorem epi_infConv (h : IsEpiLike (epi f + epi g)) : epi (infConv f g) = epi f + epi g :=
  epi_ofEpi h

/-- The basic upper bound, phrased entirely inside the epigraphs so that no `∞ - ∞` can arise:
a point of `epi f` over `y` and a point of `epi g` over `z` bound `f □ g` at `y + z`. This is
`Tdaf.ofEpi_apply_le` specialised to a sum of epigraphs. -/
theorem infConv_apply_le (hy : f y ≤ (ν : EReal)) (hz : g z ≤ (ρ : EReal)) :
    infConv f g (y + z) ≤ ((ν + ρ : ℝ) : EReal) := by
  refine ofEpi_apply_le ?_
  have hmem : ((y, ν) : E × ℝ) + (z, ρ) ∈ epi f + epi g :=
    Set.add_mem_add (mk_mem_epi.2 hy) (mk_mem_epi.2 hz)
  rwa [Prod.mk_add_mk] at hmem

/-! ### The effective domain -/

/-- "The effective domain of `f □ g` is the sum of `dom f` and `dom g`" (Rockafellar, §5, after
Theorem 5.4).

No hypothesis is needed, in contrast with `Tdaf.dom_add` for pointwise addition: `dom` is the
projection of the epigraph (`Tdaf.dom_eq_fst_image_epi`) with no properness assumption, and
projection is an additive hom, so it commutes with the pointwise sum of sets. -/
theorem dom_infConv (f g : E → EReal) : dom (infConv f g) = dom f + dom g := by
  rw [infConv_def, dom_ofEpi, dom_eq_fst_image_epi f, dom_eq_fst_image_epi g]
  exact Set.image_add (AddMonoidHom.fst E ℝ)

/-! ### The infimum formula -/

/-- The infimum formula as an inequality: `(f □ g) x ≤ f (x - y) + g y`.

Both `≠ ⊥` hypotheses are needed. Without them the right-hand side can be `⊤ + ⊥ = ⊥` while the
left-hand side is `⊤`; see the module docstring. -/
theorem infConv_le_add (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x y : E) :
    infConv f g x ≤ f (x - y) + g y := by
  rcases eq_top_or_lt_top (f (x - y)) with h1 | h1
  · rw [h1, _root_.EReal.top_add_of_ne_bot (hg y)]
    exact le_top
  rcases eq_top_or_lt_top (g y) with h2 | h2
  · rw [h2, _root_.EReal.add_top_of_ne_bot (hf (x - y))]
    exact le_top
  obtain ⟨p, hp⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hf (x - y)) h1
  obtain ⟨q, hq⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hg y) h2
  rw [hp, hq, ← _root_.EReal.coe_add]
  simpa using infConv_apply_le (f := f) (g := g) hp.le hq.le

/-- **Rockafellar's formula for `□`**: `(f □ g) x = ⨅ y, f (x - y) + g y`, "analogous to the
classical formula for integral convolution".

The hypotheses `∀ x, f x ≠ ⊥` and `∀ x, g x ≠ ⊥` are exactly what makes the right-hand side
meaningful: `f (x - y) + g y` is the forbidden `∞ - ∞` as soon as one function reaches `⊤` where
the other reaches `⊥`, and `EReal` resolves it as `⊥`, which is the wrong value. Concretely, for
`f ≡ ⊤` and `g` with `g 0 = ⊥` the left side is `⊤` and the right side is `⊥`. This is why
`Tdaf.infConv` is defined through epigraphs and this identity is a theorem rather than the
definition. -/
theorem infConv_apply (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x : E) :
    infConv f g x = ⨅ y, f (x - y) + g y := by
  refine le_antisymm (le_iInf fun y => infConv_le_add hf hg x y) (le_ofEpi fun μ hμ => ?_)
  obtain ⟨⟨a, ν⟩, ha, ⟨b, ρ⟩, hb, hab⟩ := Set.mem_add.1 hμ
  rw [Prod.mk_add_mk, Prod.mk.injEq] at hab
  refine le_trans (iInf_le (fun y => f (x - y) + g y) b) ?_
  rw [← hab.1, add_sub_cancel_right, ← hab.2, _root_.EReal.coe_add]
  exact add_le_add (mk_mem_epi.1 ha) (mk_mem_epi.1 hb)

/-! ### Commutativity, associativity, monotonicity -/

/-- `□` is commutative, because addition of sets is (Rockafellar, §5). -/
theorem infConv_comm (f g : E → EReal) : infConv f g = infConv g f := by
  rw [infConv_def, infConv_def, add_comm]

/-- Enlarging a summand from `F` to the epigraph `epi (ofEpi F)` it determines does not move the
lower boundary of the sum.

This is the lemma that makes `□` associative. The inclusion `F ⊆ epi (ofEpi F)` is always strict
in the relevant cases — `epi (ofEpi F)` fills in the unattained infima of the vertical sections of
`F` — but every filled-in point is a limit from above of points of `F`, and `ofEpi` only sees
infima, so the sum's lower boundary is unchanged. -/
theorem epi_ofEpi_add_subset (F G : Set (E × ℝ)) :
    epi (ofEpi F) + G ⊆ epi (ofEpi (F + G)) := by
  rintro p hp
  obtain ⟨⟨w, μ⟩, hwμ, ⟨u, σ⟩, huσ, rfl⟩ := Set.mem_add.1 hp
  rw [Prod.mk_add_mk]
  refine mk_mem_epi.2 (Tdaf.EReal.le_coe_of_forall_lt fun q hq => ?_)
  have hlt : ofEpi F w < ((μ + (q - (μ + σ)) : ℝ) : EReal) :=
    lt_of_le_of_lt (mk_mem_epi.1 hwμ)
      (by exact_mod_cast (by linarith : μ < μ + (q - (μ + σ))))
  obtain ⟨τ, hτF, hτ⟩ := ofEpi_lt_iff.1 hlt
  have hmem : ((w, τ) : E × ℝ) + (u, σ) ∈ F + G := Set.add_mem_add hτF huσ
  rw [Prod.mk_add_mk] at hmem
  refine lt_of_le_of_lt (ofEpi_apply_le hmem) ?_
  have hτ' : τ < μ + (q - (μ + σ)) := by exact_mod_cast hτ
  exact_mod_cast (by linarith : τ + σ < q)

/-- The `ofEpi` of a set may be convolved by adding the set itself: the `epi (ofEpi ·)` in the
definition of `Tdaf.infConv` can be peeled off on the left. -/
theorem infConv_ofEpi_left (F : Set (E × ℝ)) (g : E → EReal) :
    infConv (ofEpi F) g = ofEpi (F + epi g) := by
  refine le_antisymm (ofEpi_mono (Set.add_subset_add_right (subset_epi_ofEpi F))) ?_
  exact subset_epi_iff_le_ofEpi.1 (epi_ofEpi_add_subset F (epi g))

/-- `Tdaf.infConv_ofEpi_left` on the right. -/
theorem infConv_ofEpi_right (f : E → EReal) (G : Set (E × ℝ)) :
    infConv f (ofEpi G) = ofEpi (epi f + G) := by
  rw [infConv_comm, infConv_ofEpi_left, add_comm]

/-- `□` is associative (Rockafellar, §5).

Note that this is *not* a direct consequence of associativity of set addition: `epi (f □ g)` is
larger than `epi f + epi g` in general. `Tdaf.epi_ofEpi_add_subset`, through
`Tdaf.infConv_ofEpi_left`, is what closes the gap. -/
theorem infConv_assoc (f g h : E → EReal) :
    infConv (infConv f g) h = infConv f (infConv g h) := by
  rw [infConv_def f g, infConv_def g h, infConv_ofEpi_left, infConv_ofEpi_right, add_assoc]

/-- `□` is monotone in both arguments, since `Tdaf.epi` and `Tdaf.ofEpi` are both antitone. -/
theorem infConv_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : infConv f₁ g₁ ≤ infConv f₂ g₂ :=
  ofEpi_mono (Set.add_subset_add (epi_mono hf) (epi_mono hg))

/-! ### Indicator functions: the identity element and translation -/

/-- Adding the epigraph of `δ(· | a)` — the half-cylinder `{a} ×ˢ Ici 0` — translates an epigraph
horizontally by `a`. Unlike a general sum of epigraphs, this one *is* an epigraph. -/
theorem epi_add_epi_indicatorFn_singleton (f : E → EReal) (a : E) :
    epi f + epi (indicatorFn ({a} : Set E)) = epi fun x => f (x - a) := by
  rw [epi_indicatorFn]
  ext p
  constructor
  · intro hp
    obtain ⟨⟨w, ν'⟩, hw, ⟨u, σ⟩, hu, rfl⟩ := Set.mem_add.1 hp
    have hu1 : u = a := hu.1
    have hu2 : (0 : ℝ) ≤ σ := hu.2
    subst hu1
    rw [Prod.mk_add_mk]
    refine mk_mem_epi.2 ?_
    rw [add_sub_cancel_right]
    exact (mk_mem_epi.1 hw).trans (by exact_mod_cast (by linarith : ν' ≤ ν' + σ))
  · intro hp
    obtain ⟨w, μ⟩ := p
    have hmem : ((w - a, μ) : E × ℝ) + (a, 0) ∈ epi f + ({a} ×ˢ Ici (0 : ℝ)) :=
      Set.add_mem_add (mk_mem_epi.2 (mk_mem_epi.1 hp)) ⟨rfl, le_refl (0 : ℝ)⟩
    simpa using hmem

/-- "`f □ δ(· | a)` is the function whose graph is obtained by translating the graph of `f`
horizontally by `a`" (Rockafellar, §5). -/
theorem infConv_indicatorFn_singleton (f : E → EReal) (a : E) :
    infConv f (indicatorFn ({a} : Set E)) = fun x => f (x - a) := by
  rw [infConv_def, epi_add_epi_indicatorFn_singleton, ofEpi_epi]

/-- **`δ(· | 0)` is the identity element for `□`** (Rockafellar, §5). -/
@[simp] theorem infConv_indicatorFn_zero (f : E → EReal) :
    infConv f (indicatorFn ({0} : Set E)) = f := by
  simpa using infConv_indicatorFn_singleton f 0

/-- `δ(· | 0)` is the identity on the left as well. -/
@[simp] theorem indicatorFn_zero_infConv (f : E → EReal) :
    infConv (indicatorFn ({0} : Set E)) f = f := by
  rw [infConv_comm, infConv_indicatorFn_zero]

/-- If `g` is nonpositive at the origin then `f □ g ≤ f`: the identity `δ(· | 0)` dominates such a
`g`, and `□` is monotone. -/
theorem infConv_le_left (f : E → EReal) (hg : g 0 ≤ 0) : infConv f g ≤ f := by
  refine le_of_le_of_eq (infConv_mono (le_refl f) ?_) (infConv_indicatorFn_zero f)
  intro w
  by_cases hw : w = 0
  · subst hw
    simpa using hg
  · have hw' : w ∉ ({0} : Set E) := fun hmem => hw hmem
    simp [hw']

/-- If `f` is nonpositive at the origin then `f □ g ≤ g`. -/
theorem infConv_le_right (hf : f 0 ≤ 0) (g : E → EReal) : infConv f g ≤ g := by
  rw [infConv_comm]
  exact infConv_le_left g hf

end Basic

/-! ### Theorem 5.4 -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → EReal}

/-- **Rockafellar, Theorem 5.4.** The infimal convolute of two convex functions is convex.

The proof is the one in the book: `epi f + epi g` is a convex set because a sum of convex sets is
convex, and `f □ g` is the function it determines by Theorem 5.3. Note that no properness is
needed — that hypothesis in the book is there only to make the infimum formula meaningful, and the
epigraph definition does not use it. -/
theorem convexFn_infConv (hf : ConvexFn f) (hg : ConvexFn g) : ConvexFn (infConv f g) :=
  convexFn_ofEpi (hf.convex_epi.add hg.convex_epi)

end Module

/-! ### `□` as a commutative monoid

Rockafellar: "As an operation on the collection of all functions from `Rⁿ` to `[-∞, +∞]`, infimal
convolution is commutative, associative and convexity-preserving. The function `δ(· | 0)` acts as
the identity element for this operation." That is precisely an `AddCommMonoid`, recorded here on a
type synonym because `E → EReal` already carries the pointwise `AddCommMonoid` and `CommMonoid`
structures. -/

/-- `E → EReal`, carrying infimal convolution as its addition and `δ(· | 0)` as its zero.

A type synonym is unavoidable: the pointwise `+` on `E → EReal` is `Pi.addCommMonoid`, and it is
the operation *dual* to `□`, not `□` itself. Additive notation is chosen because `□` is addition
of epigraphs and its unit is the indicator of `{0}`; in particular `∑ i ∈ s, toInfConvFn (f i)` is
Rockafellar's `f₁ □ ⋯ □ fₘ`. -/
def InfConvFn (E : Type*) : Type _ := E → EReal

/-- A function `E → EReal`, regarded as an element of the infimal-convolution monoid. -/
def toInfConvFn {E : Type*} (f : E → EReal) : InfConvFn E := f

/-- An element of the infimal-convolution monoid, regarded as a function `E → EReal`. -/
def ofInfConvFn {E : Type*} (F : InfConvFn E) : E → EReal := F

/-- `Tdaf.toInfConvFn` and `Tdaf.ofInfConvFn` are mutually inverse. -/
@[simp] theorem ofInfConvFn_toInfConvFn {E : Type*} (f : E → EReal) :
    ofInfConvFn (toInfConvFn f) = f := rfl

/-- `Tdaf.ofInfConvFn` and `Tdaf.toInfConvFn` are mutually inverse. -/
@[simp] theorem toInfConvFn_ofInfConvFn {E : Type*} (F : InfConvFn E) :
    toInfConvFn (ofInfConvFn F) = F := rfl

section Monoid

variable {E : Type*} [AddCommGroup E]

/-- Infimal convolution is the addition of `Tdaf.InfConvFn E`. -/
noncomputable instance InfConvFn.instAdd : Add (InfConvFn E) := ⟨infConv⟩

/-- `δ(· | 0)` is the zero of `Tdaf.InfConvFn E`. -/
noncomputable instance InfConvFn.instZero : Zero (InfConvFn E) := ⟨indicatorFn {0}⟩

/-- Addition in `Tdaf.InfConvFn E` is infimal convolution. -/
@[simp] theorem toInfConvFn_add (f g : E → EReal) :
    toInfConvFn f + toInfConvFn g = toInfConvFn (infConv f g) := rfl

/-- The zero of `Tdaf.InfConvFn E` is `δ(· | 0)`. -/
@[simp] theorem toInfConvFn_indicatorFn_zero :
    toInfConvFn (indicatorFn ({0} : Set E)) = 0 := rfl

/-- `Tdaf.ofInfConvFn` turns the monoid addition back into `Tdaf.infConv`. -/
@[simp] theorem ofInfConvFn_add (F G : InfConvFn E) :
    ofInfConvFn (F + G) = infConv (ofInfConvFn F) (ofInfConvFn G) := rfl

/-- `Tdaf.ofInfConvFn` turns the monoid zero back into `δ(· | 0)`. -/
@[simp] theorem ofInfConvFn_zero :
    ofInfConvFn (0 : InfConvFn E) = indicatorFn ({0} : Set E) := rfl

/-- **Rockafellar, §5**: the functions `E → EReal` form a commutative monoid under infimal
convolution, with `δ(· | 0)` as identity.

The `add` and `zero` fields are taken from `Tdaf.InfConvFn.instAdd` and `Tdaf.InfConvFn.instZero`
rather than being spelled out again: `nsmul := nsmulRec` needs `Add` and `Zero` *instances*, not
structure fields, and the class default `nsmulRecAuto` needs an `AddSemigroup` instance that does
not exist until this declaration is complete. -/
noncomputable instance InfConvFn.instAddCommMonoid : AddCommMonoid (InfConvFn E) where
  add := (· + ·)
  zero := 0
  add_assoc := infConv_assoc
  zero_add := indicatorFn_zero_infConv
  add_zero := infConv_indicatorFn_zero
  add_comm := infConv_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

end Monoid

section MonoidConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Rockafellar, Theorem 5.4** in the book's own m-ary form: `f₁ □ ⋯ □ fₘ` is convex whenever
`f₁, …, fₘ` are. The `□`-product is the `AddCommMonoid` sum in `Tdaf.InfConvFn E`, so the
induction is `Finset.cons_induction`; the empty case is `δ(· | 0)`, which is convex because `{0}`
is. -/
theorem convexFn_sum_toInfConvFn {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) :
    ConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  induction s using Finset.cons_induction with
  | empty => simpa using convexFn_indicatorFn.2 (convex_singleton (0 : E))
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    simp only [ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact convexFn_infConv (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))

end MonoidConvex

end Tdaf
