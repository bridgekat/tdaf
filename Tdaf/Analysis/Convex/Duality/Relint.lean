/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Duality.Exact
import Tdaf.Analysis.Convex.Duality.Ops
import Tdaf.Analysis.Convex.Recession.Closedness
import Tdaf.Analysis.Convex.Recession.Conjugate
import Tdaf.Analysis.Convex.RelativeInterior

/-!
# The relative-interior constraint qualification

`Duality/Exact.lean` names the *conclusions* `IsExactImage` and `IsExactSum`; this file supplies
the first sufficient condition for each, Rockafellar's own hypothesis in **Theorems 16.3 and
16.4**:

```
A ⁻¹' ri (dom g) ≠ ∅        and        ri (dom f) ∩ ri (dom g) ≠ ∅.
```

Until now both were unpopulated interfaces — Theorems 16.3, 16.4, 23.8 and 23.9 were proved
against them, but nothing produced one. `IsExactImage.of_relint` and `IsExactSum.of_relint` are
what discharge them.

## Main results

* `IsExactImage.of_relint` — **Rockafellar, Theorem 16.3**: if `g` is closed proper convex and the
  range of `A` meets `ri (dom g)`, then `g` pulls back exactly along `A`.
* `IsExactSum.of_relint` — **Rockafellar, Theorem 16.4**: two *proper convex* functions whose
  effective domains share a relative interior point add exactly. `IsExactSum.of_relint_closed` is
  the closed case, which carries the actual argument.
* `TendstoClFnAlongSegment` — "`cl f` is the limit of `f` along segments issuing from `x₀`", the
  single hypothesis shared by **Theorem 7.5** (`x₀ ∈ ri (dom f)`) and **Corollary 7.5.1** (`f`
  closed proper, `x₀ ∈ dom f`).
* `conj_add_eq_conj_clFn_add_clFn` — **Theorem 9.3** in conjugate form,
  `(f + g)* = (cl f + cl g)*`. The book's own form `cl (f + g) = cl f + cl g` is `clFn_add` in
  `Recession/Closedness.lean`; it is *not* what §20 can use, see the design notes.
* `IsExactSum.of_clFn` — exactness transfers from the closures.
* `proper_conj_of_proper` — **Theorem 12.2** in the form §13 uses it: in finite dimensions
  `f` proper convex already gives `f*` proper, with no closedness hypothesis.

## Design notes

**Closedness is not needed for Theorem 16.4, and the book does not ask for it.** The closed case
`IsExactSum.of_relint_closed` is where the work is; the general case is Theorem 9.3. Replacing `f`
and `g` by their closures moves `conj_add_eq_clFn_infConv` the wrong way *only* if one compares
`(f + g)*` with `(cl f + cl g)*` naively: `cl f + cl g ≤ f + g` gives `(f + g)* ≤ (cl f + cl g)*`,
which is the same direction as the unconditional `conj_add_le_infConv`, so nothing follows. What
closes the gap is that the two conjugates are in fact *equal*
(`conj_add_eq_conj_clFn_add_clFn`), and one passage to the limit along a segment issuing from the
common relative interior point proves it. The conjugate form is deliberately weaker than the book's
`cl (f + g) = cl f + cl g` (`clFn_add`, `Recession/Closedness.lean`): proving that identity needs
Theorem 7.5 for `f + g` too, hence a relative interior point of *both* domains, whereas §20 has
only a point of `dom f`.

**Neither closed proof is an argument; both are assemblies.** Every ingredient is already proved
elsewhere, and the two constructors differ only in which §9 theorem they invoke — Theorem 9.2 for
images, Corollary 9.1.1 for sums.

For the image rule:

1. `conj_compLin_eq_clFn_mapLin` (§16) gives `(g A)* = cl (A' g*)` for closed convex `g`,
   unconditionally.
2. `closedProperConvexFn_mapLin` — **Theorem 9.2** — says the closure is redundant, and the
   infimum defining `A' g*` is attained, provided `g*` is *constant* along every direction of
   recession that `A'` kills.
3. `constancySpace_conj` — **Theorem 13.3** — rewrites that hypothesis about `g*` as a hypothesis
   about `dom g`: "`g*` recedes in the direction `z`" is "`⟨·, z⟩ ≤ 0` on `dom g`", and "`g*` is
   constant along `z`" is "`⟨·, z⟩ = 0` on `dom g`".
4. `eq_zero_of_nonpos_of_mem_relint` (§6) closes the gap between those two: a linear function that
   is `≤ 0` on a convex set and vanishes at a *relative interior* point vanishes identically on it.

Adjointness supplies the one link between (3) and (4): `A' z = 0` forces `⟨A x₀, z⟩ = ⟨x₀, A' z⟩`
to vanish, and `A x₀ ∈ ri (dom g)` is exactly the relative interior point step (4) asks for.

For the sum rule the same four steps appear with `conj_add_eq_clFn_infConv` in place of (1) and
`Convex.isClosed_add` — **Corollary 9.1.1** applied to `epi f*` and `epi g*` — in place of (2).
Step (3) is again Theorem 13.3 and step (4) is `eq_of_isMaxOn_of_mem_relint`, the *maximum* form
rather than the vanishing form: two cancelling recession directions `(z, ν)` and `(-z, -ν)` force
`⟨x₀, z⟩ ≤ ν` and `-⟨x₀, z⟩ ≤ -ν`, so both bounds are attained at `x₀` and both linear functions
are constant on the respective domains. Closedness of `epi f* + epi g*` then makes it an epigraph
(`IsEpiLike.of_isClosed`), namely that of `f* □ g*`, and the splitting read off a point of that sum
*is* the attainment `IsExactSum.exact_le` asks for.

**Where the layers land.** The image rule puts Theorem 9.2 on `H`, so `H` must be
finite-dimensional, and `ri (dom g)` puts `G` there too; `F` only receives an image, so a normed
space suffices, and `E` is never topologised at all — it enters only through `A`, `B` and the
adjointness datum. The sum rule is the reverse: `ri (dom f)` needs only a normed `E`, while
Corollary 9.1.1 runs in `F × ℝ` and so `F` must be finite-dimensional.

**The `< ⊤` guard is what makes the image rule true without surjectivity.** Theorem 9.2 attains
the infimum only where the image function is bounded above by a real; off the range of `A'` both
sides of Theorem 16.3 are `+∞` and there is nothing to attain. That is precisely the shape of
`IsExactImage.exact_le`; see its design notes.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16 (Theorem 16.3,
  Theorem 16.4).
-/

open Pointwise

namespace Tdaf.ConvexAnalysis

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- Theorem 9.2's hypothesis for `g*` and the transpose `A'`, discharged from Rockafellar's
relative-interior condition.

Read through Theorem 13.3 (`constancySpace_conj`), "`g*` recedes in the direction `z`, and `A'`
kills `z`" says that `⟨·, z⟩` is `≤ 0` on `dom g` and vanishes at the point `A x₀`, which the
hypothesis places in `ri (dom g)`. Theorem 6.4 then forces `⟨·, z⟩ ≡ 0` on `dom g`, which is
constancy of `g*` along `z`. -/
theorem mem_constancySpace_conj_of_relint [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (dom g)) {z : H}
    (hrec : recessionFn (conj B' g) z ≤ 0) (hz0 : A' z = 0) :
    z ∈ constancySpace (conj B' g) := by
  have hconjp : Proper (conj B' g) := proper_conj hg
  rw [constancySpace_conj hg.proper hconjp]
  have hzero : ((0 : ℝ) : EReal) = 0 := by norm_num
  have hnonpos : ∀ x ∈ dom g, (B'.flip z) x ≤ 0 := by
    intro x hx
    rw [recessionFn_conj hg.proper hconjp, ← hzero, supportFn_le_coe_iff] at hrec
    exact hrec x hx
  have hvanish : (B'.flip z) (A x₀) = 0 := by
    rw [LinearMap.flip_apply, hA x₀ z, hz0, map_zero]
  exact eq_zero_of_nonpos_of_mem_relint hx₀ hnonpos hvanish

omit [FiniteDimensional ℝ G] in
/-- **Rockafellar, Theorem 16.3**: a closed proper convex function pulls back exactly along a
linear map whose range meets the relative interior of its effective domain.

This is the first constructor for `IsExactImage`, and with it Theorem 16.3
(`IsExactImage.conj_compLin`) and Theorem 23.9 (`IsExactImage.subgradient_compLin`) acquire their
first supplied instances. -/
theorem IsExactImage.of_relint [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    [IsCompatiblePairing B.flip] (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (dom g)) :
    IsExactImage B B' A A' hA g := by
  have hconjp : Proper (conj B' g) := proper_conj hg
  have hconjcpc : ClosedProperConvexFn (conj B' g) :=
    ⟨convexFn_conj B' g, closedFn_conj, hconjp⟩
  have hkey : ∀ z : H, recessionFn (conj B' g) z ≤ 0 → A' z = 0 → z ∈ constancySpace (conj B' g) :=
    fun z hrec hz0 => mem_constancySpace_conj_of_relint hA hg hx₀ hrec hz0
  obtain ⟨-, hcpc⟩ :=
    closedProperConvexFn_mapLin (convexFn_conj B' g) hconjp hconjcpc.isClosed_epi A' hkey
  -- Theorem 9.2 says the closure in the §16 identity is redundant
  have heq : conj B (compLin g A) = mapLin A' (conj B' g) := by
    rw [conj_compLin_eq_clFn_mapLin hA hg.convex hg.closed]
    exact hcpc.closed
  refine ⟨hg.proper, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hcpc.proper.ne_bot y) hy
  obtain ⟨z, hzy, hz⟩ :=
    exists_mapLin_eq (convexFn_conj B' g) hconjp hconjcpc.isClosed_epi A' hkey hμ.le
  exact ⟨z, hzy, hμ ▸ hz⟩

end Image

/-! ### Theorem 16.4: sums -/

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- A direction of recession of `epi f*` bounds the pairing on `dom f`: this is Theorem 13.3 read
one point at a time. -/
theorem le_of_mk_mem_recessionCone_epi_conj [IsCompatiblePairing B] (hf : ClosedProperConvexFn f)
    {z : F} {ν : ℝ} (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (conj B f)))
    {x : E} (hx : x ∈ dom f) : B x z ≤ ν := by
  have hle := recessionFn_le_coe_iff.2 hp
  rw [recessionFn_conj hf.proper (proper_conj hf), supportFn_le_coe_iff] at hle
  exact hle x hx

omit [FiniteDimensional ℝ F] in
/-- **The relative-interior step for sums.** If `(z, ν)` is a direction of recession of `epi f*`
whose bound `ν` is *already attained* at a relative interior point of `dom f`, then `(z, ν)` lies
in the lineality space.

Theorem 13.3 turns `(z, ν) ∈ 0⁺(epi f*)` into "`⟨·, z⟩ ≤ ν` on `dom f`". The extra hypothesis says
the linear function `⟨·, z⟩` attains that bound at `x₀ ∈ ri (dom f)`, so Theorem 6.4 makes it
*constant* on `dom f`, which is exactly `(-z, -ν) ∈ 0⁺(epi f*)`. -/
theorem mk_mem_linealitySpace_epi_conj_of_relint [IsCompatiblePairing B]
    (hf : ClosedProperConvexFn f) {x₀ : E} (hx₀ : x₀ ∈ ri (dom f)) {z : F} {ν : ℝ}
    (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (conj B f))) (hν : ν ≤ B x₀ z) :
    ((z, ν) : F × ℝ) ∈ linealitySpace (epi (conj B f)) := by
  have hx₀f : x₀ ∈ dom f := intrinsicInterior_subset hx₀
  have hmax : B x₀ z = ν :=
    le_antisymm (le_of_mk_mem_recessionCone_epi_conj hf hp hx₀f) hν
  have hconst : ∀ x ∈ dom f, (B.flip z) x = (B.flip z) x₀ :=
    eq_of_isMaxOn_of_mem_relint hx₀ fun x hx =>
      le_trans (le_of_mk_mem_recessionCone_epi_conj hf hp hx) hν
  refine mem_linealitySpace.2 ⟨hp, ?_⟩
  rw [Prod.neg_mk, ← recessionFn_le_coe_iff, recessionFn_conj hf.proper (proper_conj hf),
    supportFn_le_coe_iff]
  intro x hx
  have hx' : B x z = ν := by
    have hc := hconst x hx
    rw [LinearMap.flip_apply, LinearMap.flip_apply, hmax] at hc
    exact hc
  rw [map_neg, hx']

/-- **Rockafellar, Theorem 16.4**: two closed proper convex functions add exactly as soon as their
effective domains have a common relative interior point.

The proof is Corollary 9.1.1 applied to the two epigraphs `epi f*` and `epi g*`. Their sum is the
epigraph of `f* □ g*` as soon as it is closed, Theorem 16.4's closure form
(`conj_add_eq_clFn_infConv`) then loses its closure, and the splitting that Corollary 9.1.1 hands
back at each point is exactly the attainment `IsExactSum.exact_le` asks for.

Corollary 9.1.1's hypothesis — two cancelling recession directions must be lineality directions —
is Theorem 13.3 plus Theorem 6.4: `(z, ν) ∈ 0⁺(epi f*)` and `(-z, -ν) ∈ 0⁺(epi g*)` force
`⟨x₀, z⟩ ≤ ν` and `-⟨x₀, z⟩ ≤ -ν` at the common point `x₀`, so both bounds are attained at a
relative interior point and both linear functions are constant. -/
theorem IsExactSum.of_relint_closed [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ ri (dom g)) :
    IsExactSum B f g := by
  have hx₀f : x₀ ∈ dom f := intrinsicInterior_subset hxf
  have hx₀g : x₀ ∈ dom g := intrinsicInterior_subset hxg
  have hup : Proper (conj B f) := proper_conj hf
  have hvp : Proper (conj B g) := proper_conj hg
  have hucpc : ClosedProperConvexFn (conj B f) := ⟨convexFn_conj B f, closedFn_conj, hup⟩
  have hvcpc : ClosedProperConvexFn (conj B g) := ⟨convexFn_conj B g, closedFn_conj, hvp⟩
  have hune : (epi (conj B f)).Nonempty := (epi_nonempty_iff _).2 hup.dom_nonempty
  have hvne : (epi (conj B g)).Nonempty := (epi_nonempty_iff _).2 hvp.dom_nonempty
  -- Corollary 9.1.1's hypothesis, discharged by Theorem 13.3 and Theorem 6.4
  have hrec : ∀ p ∈ recessionCone (epi (conj B f)), ∀ q ∈ recessionCone (epi (conj B g)),
      p + q = 0 →
        p ∈ linealitySpace (epi (conj B f)) ∧ q ∈ linealitySpace (epi (conj B g)) := by
    rintro ⟨z, ν⟩ hp ⟨w, ρ⟩ hq hzero
    have hz : z + w = 0 := congrArg Prod.fst hzero
    have hνρ : ν + ρ = 0 := congrArg Prod.snd hzero
    have h₁ : B x₀ z ≤ ν := le_of_mk_mem_recessionCone_epi_conj hf hp hx₀f
    have h₂ : B x₀ w ≤ ρ := le_of_mk_mem_recessionCone_epi_conj hg hq hx₀g
    have hBzw : B x₀ z + B x₀ w = 0 := by rw [← map_add, hz, map_zero]
    exact ⟨mk_mem_linealitySpace_epi_conj_of_relint hf hxf hp (by linarith),
      mk_mem_linealitySpace_epi_conj_of_relint hg hxg hq (by linarith)⟩
  have hclosed : IsClosed (epi (conj B f) + epi (conj B g)) :=
    Convex.isClosed_add (convexFn_conj B f).convex_epi hucpc.isClosed_epi hune
      (convexFn_conj B g).convex_epi hvcpc.isClosed_epi hvne hrec
  -- a closed sum of epigraphs is an epigraph, namely that of the infimal convolution
  have hmono : ∀ (y : F) (μ ν : ℝ), (y, μ) ∈ epi (conj B f) + epi (conj B g) → μ ≤ ν →
      (y, ν) ∈ epi (conj B f) + epi (conj B g) := by
    rintro y μ ν ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ hμν
    have hy : y₁ + y₂ = y := congrArg Prod.fst heq
    have hab : a + b = μ := congrArg Prod.snd heq
    refine ⟨(y₁, a), h₁, (y₂, b + (ν - μ)), mk_mem_epi.2 ?_, ?_⟩
    · exact (mk_mem_epi.1 h₂).trans (by exact_mod_cast (by linarith : b ≤ b + (ν - μ)))
    · change ((y₁, a) : F × ℝ) + (y₂, b + (ν - μ)) = (y, ν)
      rw [Prod.mk_add_mk, hy, show a + (b + (ν - μ)) = ν by linarith]
  have hepiEq : epi (infConv (conj B f) (conj B g)) = epi (conj B f) + epi (conj B g) :=
    epi_infConv (IsEpiLike.of_isClosed hmono hclosed)
  -- properness of the infimal convolution, from properness of `(f + g)*`
  have hdomne : (dom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_dom, Pi.add_apply]
      exact _root_.EReal.add_lt_top (mem_dom.1 hx₀f).ne (mem_dom.1 hx₀g).ne⟩
  have hproper : Proper (infConv (conj B f) (conj B g)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := hup.dom_nonempty
      obtain ⟨q, hq⟩ := hvp.dom_nonempty
      exact ⟨p + q, by rw [dom_infConv]; exact Set.add_mem_add hp hq⟩
    · have hle := conj_add_le_infConv B f g y
      rw [hy, le_bot_iff] at hle
      exact conj_ne_bot hdomne y hle
  have hclosedFn : ClosedFn (infConv (conj B f) (conj B g)) :=
    (ClosedProperConvexFn.of_isClosed_epi
      (convexFn_infConv (convexFn_conj B f) (convexFn_conj B g))
      (by rw [hepiEq]; exact hclosed) hproper).closed
  have hconjadd : conj B (f + g) = infConv (conj B f) (conj B g) := by
    rw [conj_add_eq_clFn_infConv hf.convex hf.closed hg.convex hg.closed]
    exact hclosedFn
  refine ⟨hf.proper, hg.proper, fun y => ?_⟩
  rw [hconjadd]
  rcases eq_top_or_lt_top (infConv (conj B f) (conj B g) y) with htop | htop
  · exact ⟨y, 0, add_zero y, by rw [htop]; exact le_top⟩
  obtain ⟨μ, hμ⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top (hproper.ne_bot y) htop
  have hmem : ((y, μ) : F × ℝ) ∈ epi (conj B f) + epi (conj B g) := by
    rw [← hepiEq]; exact mk_mem_epi.2 hμ.le
  obtain ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ := hmem
  refine ⟨y₁, y₂, congrArg Prod.fst heq, ?_⟩
  have hab : a + b = μ := congrArg Prod.snd heq
  rw [hμ]
  calc conj B f y₁ + conj B g y₂ ≤ ((a : ℝ) : EReal) + ((b : ℝ) : EReal) :=
        add_le_add (mk_mem_epi.1 h₁) (mk_mem_epi.1 h₂)
    _ = ((μ : ℝ) : EReal) := by rw [← _root_.EReal.coe_add, hab]

end Sum

/-! ### Theorem 9.3: dropping closedness from the constraint qualifications -/

section Closure

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- `f` is **recovered along segments issuing from `x₀`**: at every `y` the value `(cl f) y` is the
limit of `f` along the half-open segment running from `x₀` to `y`.

This is the conclusion of **Theorem 7.5** when `x₀ ∈ ri (dom f)`, and of **Corollary 7.5.1** when
`f` is closed proper convex and `x₀ ∈ dom f`. It is the only property of `x₀` that the closure
formula of **Theorem 9.3** uses, and naming it is what lets §16's relative-interior qualification
and §20's polyhedral one run through one and the same lemma. -/
def TendstoClFnAlongSegment (f : E → EReal) (x₀ : E) : Prop :=
  ∀ y, Tendsto (fun a : ℝ => f ((1 - a) • x₀ + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (clFn f y))

omit [FiniteDimensional ℝ F] in
/-- **In finite dimensions the conjugate of a proper convex function is proper.**

Rockafellar states Theorems 13.3 and 13.4 for a proper convex `f`, where `proper_conj` asks for
`ClosedProperConvexFn f`. The gap closes here rather than in `Duality/Conjugate.lean` because it
runs through **Theorem 7.4** (`ConvexFn.proper_clFn`, `RelativeInterior.lean`), which is where
finite-dimensionality enters: `f* = (cl f)*`, and `cl f` is closed proper convex. -/
theorem proper_conj_of_proper [IsCompatiblePairing B] (hf : ConvexFn f) (hp : Proper f) :
    Proper (conj B f) := by
  rw [← conj_clFn]
  exact proper_conj ⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp⟩

/-- **Rockafellar, Theorem 7.5**: a proper convex function is recovered along segments issuing from
any relative interior point of its effective domain. -/
theorem ConvexFn.tendstoClFnAlongSegment (hf : ConvexFn f) (hp : Proper f) {x₀ : E}
    (hx₀ : x₀ ∈ ri (dom f)) : TendstoClFnAlongSegment f x₀ := by
  intro y
  rw [hf.clFn_eq_lscHull hp]
  exact hf.tendsto_lscHull_along_segment_relint hx₀ y

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Rockafellar, Corollary 7.5.1**: a closed proper convex function is recovered along segments
issuing from any point of its effective domain — no relative interior is needed. This is the extra
freedom that makes Theorem 20.1 stronger than Theorem 16.4. -/
theorem ClosedProperConvexFn.tendstoClFnAlongSegment (hf : ClosedProperConvexFn f) {x₀ : E}
    (hx₀ : x₀ ∈ dom f) : TendstoClFnAlongSegment f x₀ := by
  intro y
  rw [show clFn f = f from hf.closed]
  exact tendsto_along_segment_of_closed_proper hf hx₀ y

omit [FiniteDimensional ℝ F] in
/-- **Rockafellar, Theorem 9.3**, in the form the constraint qualifications consume it: if two
proper convex functions are both recovered along segments issuing from one common point, then
`f + g` and `cl f + cl g` have the same conjugate.

Rockafellar's own statement is `cl (f + g) = cl f + cl g`, and proving *that* needs Theorem 7.5 for
`f + g` as well, hence `x₀ ∈ ri (dom f) ∩ ri (dom g)`. The conjugate form needs no such thing:
`f* = (cl f)*` holds outright (**Theorem 12.2**), so only the *sum* has to be compared, and one
passage to the limit along the segment does that. That is what lets Theorem 20.1 drop closedness
too, where `x₀` is a point of `dom f` and of `ri (dom g)` only.

The hard half is the inequality `(cl f + cl g)* ≤ (f + g)*`, i.e. that every affine minorant of
`f + g` already minorises `cl f + cl g`; the reverse is `cl ≤ id` and antitonicity. -/
theorem conj_add_eq_conj_clFn_add_clFn (hf : ConvexFn f) (hpf : Proper f) (hg : ConvexFn g)
    (hpg : Proper g) {x₀ : E} (hsf : TendstoClFnAlongSegment f x₀)
    (hsg : TendstoClFnAlongSegment g x₀) :
    conj B (f + g) = conj B (clFn f + clFn g) := by
  have hclf : Proper (clFn f) := hf.proper_clFn hpf
  have hclg : Proper (clFn g) := hg.proper_clFn hpg
  have hmono : clFn f + clFn g ≤ f + g := fun x => add_le_add (clFn_le f x) (clFn_le g x)
  refine funext fun y => le_antisymm (conj_antitone B hmono y) ?_
  have key : ∀ c : ℝ, conj B (f + g) y ≤ (c : EReal) →
      conj B (clFn f + clFn g) y ≤ (c : EReal) := by
    intro c hc
    rw [conj_le_coe_iff] at hc ⊢
    intro x
    have hlin : ∀ a : ℝ, B ((1 - a) • x₀ + a • x) y = (1 - a) * B x₀ y + a * B x y := by
      intro a
      rw [map_add, map_smul, map_smul]
      simp
    have hL : Tendsto (fun a : ℝ => affineFn B y c ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 (affineFn B y c x)) := by
      simp only [affineFn_eq_coe, hlin]
      exact EReal.tendsto_coe.2
        ((tendsto_affine_nhdsLT_one (B x₀ y) (B x y)).sub tendsto_const_nhds)
    have hR : Tendsto (fun a : ℝ => (f + g) ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 ((clFn f + clFn g) x)) := by
      have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (clFn f x, clFn g x) :=
        EReal.continuousAt_add (Or.inr (hclg.ne_bot x)) (Or.inl (hclf.ne_bot x))
      exact hcont.tendsto.comp ((hsf x).prodMk_nhds (hsg x))
    exact le_of_tendsto_of_tendsto' hL hR fun a => hc _
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, h1, h2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd (key c h1.le) (not_le.2 h2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Exactness passes from the closures to the functions themselves, as soon as the sum has not
changed its conjugate. `conj_add_eq_conj_clFn_add_clFn` is what supplies the second hypothesis. -/
theorem IsExactSum.of_clFn [IsContinuousPairing B] (hpf : Proper f) (hpg : Proper g)
    (h : IsExactSum B (clFn f) (clFn g))
    (hconj : conj B (f + g) = conj B (clFn f + clFn g)) : IsExactSum B f g := by
  refine ⟨hpf, hpg, fun y => ?_⟩
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  rw [conj_clFn, conj_clFn] at hle
  exact ⟨y₁, y₂, hy, by rw [hconj]; exact hle⟩

/-- **Rockafellar, Theorem 16.4**, with the book's hypotheses: two *proper convex* functions add
exactly as soon as their effective domains have a relative interior point in common. Closedness is
not needed, and Rockafellar does not assume it.

The reduction is Theorem 9.3: `cl f` and `cl g` are closed proper convex with the same relative
interiors of effective domains (**Corollary 7.4.1**), so `IsExactSum.of_relint_closed` applies to
them; `conj_add_eq_conj_clFn_add_clFn` says the passage back to `f` and `g` costs nothing. -/
theorem IsExactSum.of_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (hpf : Proper f) (hg : ConvexFn g) (hpg : Proper g)
    {x₀ : E} (hxf : x₀ ∈ ri (dom f)) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g :=
  IsExactSum.of_clFn hpf hpg
    (IsExactSum.of_relint_closed ⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hpf⟩
      ⟨convexFn_clFn hg, closedFn_clFn g, hg.proper_clFn hpg⟩
      (by rw [hf.relint_dom_clFn hpf]; exact hxf) (by rw [hg.relint_dom_clFn hpg]; exact hxg))
    (conj_add_eq_conj_clFn_add_clFn hf hpf hg hpg
      (hf.tendstoClFnAlongSegment hpf hxf) (hg.tendstoClFnAlongSegment hpg hxg))

end Closure

end Tdaf.ConvexAnalysis
