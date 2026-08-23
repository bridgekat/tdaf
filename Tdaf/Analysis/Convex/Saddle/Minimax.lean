/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Optimization.Lagrangian
import Tdaf.Analysis.Convex.Optimization.Minimum
import Tdaf.Analysis.Convex.Optimization.Normal
import Tdaf.Analysis.Convex.Saddle.Kernel

/-!
# Minimax problems

Rockafellar's §36. A function `K` of two variables has two iterated extrema,

`maximin K = ⨆ u, ⨅ x, K (u, x)`  and  `minimax K = ⨅ x, ⨆ u, K (u, x)`,

the first is never above the second (Lemma 36.1), and when they agree their common value is the
**saddle-value** of `K`. A **saddle-point** is a point `p` at which `K (·, p.2)` is maximised and
`K (p.1, ·)` is minimised; Lemma 36.2 says that a saddle-point is exactly a pair of optimal
strategies together with the existence of the saddle-value.

## Main definitions

* `IsSaddlePoint K p` — `K (u, p.2) ≤ K p ≤ K (p.1, x)` for all `u`, `x`.
* `IsSaddlePointOn K C D p` — the same, with `u` ranging over `C` and `x` over `D`.
* `maximin K`, `minimax K` — Rockafellar's "sup inf" and "inf sup".
* `HasSaddleValue K` — `maximin K = minimax K`.
* `saddleLagrangian Bu F` — the Lagrangian of `(P)` read as a function on `V × X`, i.e. as a
  saddle-function.
* `flipBifun F` — the bifunction with its two arguments exchanged.

## Main results

* `maximin_le_minimax` — **Lemma 36.1**, with no hypothesis of any kind, not even nonemptiness.
* `isSaddlePoint_iff_iSup_eq_iInf` — the one-equation form of the saddle-point condition. It is
  the workhorse: everything downstream is a computation of `⨆ u, K (u, x)` and `⨅ x, K (u, x)`.
* `isSaddlePoint_iff_attained` — **Lemma 36.2**.
* `maximin_eq_biSup_dom₁`, `minimax_eq_biInf_dom₂` — the outer extrema may always be restricted
  to the effective domains, with no hypothesis at all.
* `maximin_eq_biSup_biInf`, `minimax_eq_biInf_biSup`, `isSaddlePoint_iff_isSaddlePointOn_dom` —
  **Theorem 36.3**: for a closed proper concave-convex function the minimax problem on the whole
  space and the one on `C × D = dom K` have the same value and the same saddle-points.
* `IsSaddlePoint.mem_domSaddle`, `IsSaddlePoint.exists_maximin_eq_coe` — **Corollary 36.3.1**.
* `SaddleEquiv.maximin_eq`, `.minimax_eq`, `.hasSaddleValue_iff`, `.isSaddlePoint_iff` —
  **Theorem 36.4**.
* `isSaddlePoint_lagrangian_iff` — **Theorem 29.3**, which `Optimization/Lagrangian.lean` had to
  leave out for want of `IsSaddlePoint`.
* `mem_argmin_iff_exists_isSaddlePoint_lagrangian`,
  `isSaddlePoint_lagrangian_iff_mem_kuhnTucker` — **Theorem 36.6** (= **Corollary 29.3.1**), the
  general Kuhn–Tucker theorem.
* `isSaddlePoint_lagrangian_iff_normal_and_optimal`,
  `isSaddlePoint_lagrangian_iff_le_adjointBifun` — **Corollary 30.5.1**, which
  `Optimization/Normal.lean` had to leave out for the same reason.
* `upperClosedFn_saddleLagrangian`, `exists_unique_closedBifun_saddleLagrangian_eq` —
  **Theorem 36.5**: the Lagrangians of closed convex programs are exactly the upper closed
  concave-convex functions.
* `ConvexFn.exists_mem_relint_dom_lt`, `ConvexFn.biInf_eq_iInf_of_relint_dom_subset` —
  **Corollary 7.3.1**, the tool Theorem 36.3 runs on; a relocation candidate for
  `RelativeInterior.lean`.
* `iSup_clConcave_eq_iSup` — the concave mirror of `iInf_clFn_eq_iInf`; a relocation candidate for
  `Duality/ConcaveConj.lean`.

## Design notes

**`HasSaddleValue` is the *existence* of the saddle-value, not its finiteness.** Rockafellar
(§36, first page) calls the common value of the two iterated extrema the saddle-value *when they
are equal*, and then states finiteness separately wherever he needs it (Corollary 36.3.1,
Corollary 37.1.3, Theorem 37.3). So `HasSaddleValue K` is the bare equation
`maximin K = minimax K`, and finiteness is a second conclusion. Building finiteness into the
definition would make Corollary 36.3.1 vacuous and would match none of the book's statements.

**`maximin` and `minimax` are taken over the whole space.** Rockafellar's §36 opens by showing
that a minimax problem on `C × D` is the same as one on `R^m × R^n` once `K` is extended by
`+∞`/`−∞`; the extended form is the one every later theorem uses, and it is the one taken here.
`IsSaddlePointOn` records the translation.

**Lemma 36.1 and Lemma 36.2 need no structure at all** — no topology, no module structure, and
not even nonemptiness of the two spaces (the book assumes `C × D ≠ ∅`, which the `±∞` extension
makes unnecessary). They are stated over bare types. So is Corollary 36.3.1, which needs only
`ProperSaddleFn`; and Theorem 36.4 needs only a topology on each factor — neither closedness nor
properness nor concave-convexity nor finite dimension enter.

**Theorem 36.5 goes through the *negated* pairing, not through the inverse bifunction.**
Rockafellar reads the Lagrangian as `L (v, x) = ⟨v, F_* x⟩`, a bracket of the *concave* inverse
`F_*`, and appeals to a concave mirror of Theorem 33.3 that the backbone does not have. The same
identity read after `saddleSwap` — which negates and exchanges the variables — is
`saddleSwap L = ⟨(flip F) x, v⟩` for the pairing `-Bu` (`saddleSwap_saddleLagrangian`), so the
*convex* Theorem 33.3 applies verbatim. The price is two instances,
`isCompatiblePairing_neg` and `flip_neg`, both three lines: negating a pairing preserves
continuity, and `g = ⟨·, y⟩` for `-B` exactly when `-g = ⟨·, y⟩` for `B`.

## What is not here

**The subgradient form of the Kuhn–Tucker condition** `(0, 0) ∈ ∂L (v̄, x̄)` needs §35's
`∂L = ∂₁L × ∂₂L`, which is not formalized. `isSaddlePoint_lagrangian_iff` gives the equivalent
"optimal solution plus Kuhn–Tucker vector" form, which is what Rockafellar's Theorem 36.6 is a
restatement of.

**§37.** `conjugateSaddle`, Theorem 37.1 and the minimax existence theorems belong in a file of
their own and are not written.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §36.
-/

namespace Tdaf.ConvexAnalysis

/-! ### Saddle-points and the two iterated extrema -/

section Basic

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- `p` is a **saddle-point** of `K`: the concave variable is maximised and the convex variable is
minimised there (Rockafellar, §36). -/
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop :=
  (∀ u, K (u, p.2) ≤ K p) ∧ ∀ x, K p ≤ K (p.1, x)

/-- `p` is a **saddle-point of `K` relative to `C × D`**: Rockafellar's saddle-point with respect
to maximising over `C` and minimising over `D`. -/
def IsSaddlePointOn (K : U × X → EReal) (C : Set U) (D : Set X) (p : U × X) : Prop :=
  p.1 ∈ C ∧ p.2 ∈ D ∧ (∀ u ∈ C, K (u, p.2) ≤ K p) ∧ ∀ x ∈ D, K p ≤ K (p.1, x)

/-- Rockafellar's `sup inf`. -/
noncomputable def maximin (K : U × X → EReal) : EReal := ⨆ u, ⨅ x, K (u, x)

/-- Rockafellar's `inf sup`. -/
noncomputable def minimax (K : U × X → EReal) : EReal := ⨅ x, ⨆ u, K (u, x)

theorem maximin_apply (K : U × X → EReal) : maximin K = ⨆ u, ⨅ x, K (u, x) := rfl

theorem minimax_apply (K : U × X → EReal) : minimax K = ⨅ x, ⨆ u, K (u, x) := rfl

/-- The **saddle-value of `K` exists** when the two iterated extrema agree. Following Rockafellar,
this says nothing about the common value being finite. -/
def HasSaddleValue (K : U × X → EReal) : Prop := maximin K = minimax K

theorem hasSaddleValue_iff : HasSaddleValue K ↔ maximin K = minimax K := Iff.rfl

/-- **Rockafellar, Lemma 36.1**: `sup inf ≤ inf sup`. No hypothesis at all is needed — in
particular neither `U` nor `X` need be nonempty, the book's nonemptiness assumption serving only
to make his `C × D` formulation match this one. -/
theorem maximin_le_minimax (K : U × X → EReal) : maximin K ≤ minimax K :=
  iSup_le fun u => le_iInf fun x => (iInf_le (fun x => K (u, x)) x).trans
    (le_iSup (fun u => K (u, x)) u)

theorem iInf_slice_le_maximin (K : U × X → EReal) (u : U) : (⨅ x, K (u, x)) ≤ maximin K :=
  le_iSup (fun u => ⨅ x, K (u, x)) u

theorem minimax_le_iSup_slice (K : U × X → EReal) (x : X) : minimax K ≤ ⨆ u, K (u, x) :=
  iInf_le (fun x => ⨆ u, K (u, x)) x

theorem iInf_slice_le_self (K : U × X → EReal) (p : U × X) : (⨅ x, K (p.1, x)) ≤ K p :=
  iInf_le (fun x => K (p.1, x)) p.2

theorem le_iSup_slice (K : U × X → EReal) (p : U × X) : K p ≤ ⨆ u, K (u, p.2) :=
  le_iSup (fun u => K (u, p.2)) p.1

/-- **The saddle-point condition in one equation.** `p` is a saddle-point exactly when the maximum
of `K (·, p.2)` and the minimum of `K (p.1, ·)` agree; the common value is then `K p`. Rockafellar
uses this reformulation throughout §29 and §36. -/
theorem isSaddlePoint_iff_iSup_eq_iInf :
    IsSaddlePoint K p ↔ (⨆ u, K (u, p.2)) = ⨅ x, K (p.1, x) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (le_iInf fun x => (iSup_le h1).trans (h2 x))
      ((iInf_slice_le_self K p).trans (le_iSup_slice K p))
  · intro h
    refine ⟨fun u => ?_, fun x => ?_⟩
    · exact ((le_iSup (fun u => K (u, p.2)) u).trans h.le).trans (iInf_slice_le_self K p)
    · exact ((le_iSup_slice K p).trans h.le).trans (iInf_le (fun x => K (p.1, x)) x)

theorem IsSaddlePoint.iSup_eq (h : IsSaddlePoint K p) : (⨆ u, K (u, p.2)) = K p :=
  le_antisymm (iSup_le h.1) (le_iSup_slice K p)

theorem IsSaddlePoint.iInf_eq (h : IsSaddlePoint K p) : (⨅ x, K (p.1, x)) = K p :=
  le_antisymm (iInf_slice_le_self K p) (le_iInf h.2)

/-- **Rockafellar, Lemma 36.2**: `p` is a saddle-point exactly when the outer supremum in
`sup inf` is attained at `p.1`, the outer infimum in `inf sup` is attained at `p.2`, and the two
extrema are equal. -/
theorem isSaddlePoint_iff_attained :
    IsSaddlePoint K p ↔
      (⨅ x, K (p.1, x)) = maximin K ∧ (⨆ u, K (u, p.2)) = minimax K ∧ HasSaddleValue K := by
  constructor
  · intro h
    have h₁ : K p ≤ maximin K := h.iInf_eq ▸ iInf_slice_le_maximin K p.1
    have h₂ : minimax K ≤ K p := h.iSup_eq ▸ minimax_le_iSup_slice K p.2
    have hmm : maximin K = K p := le_antisymm ((maximin_le_minimax K).trans h₂) h₁
    have hMM : minimax K = K p := le_antisymm h₂ (h₁.trans (maximin_le_minimax K))
    exact ⟨by rw [h.iInf_eq, hmm], by rw [h.iSup_eq, hMM], by rw [hasSaddleValue_iff, hmm, hMM]⟩
  · rintro ⟨h1, h2, h3⟩
    exact isSaddlePoint_iff_iSup_eq_iInf.2 (by rw [h1, h2, hasSaddleValue_iff.1 h3])

/-- **Rockafellar, Lemma 36.2**, last sentence: at a saddle-point the saddle-value is `K p`. -/
theorem IsSaddlePoint.maximin_eq (h : IsSaddlePoint K p) : maximin K = K p :=
  (isSaddlePoint_iff_attained.1 h).1.symm.trans h.iInf_eq

theorem IsSaddlePoint.minimax_eq (h : IsSaddlePoint K p) : minimax K = K p :=
  (isSaddlePoint_iff_attained.1 h).2.1.symm.trans h.iSup_eq

theorem IsSaddlePoint.hasSaddleValue (h : IsSaddlePoint K p) : HasSaddleValue K :=
  (isSaddlePoint_iff_attained.1 h).2.2

/-- A saddle-point relative to `C × D` is characterised by the same one equation, now with the
two extrema restricted. -/
theorem isSaddlePointOn_iff_biSup_eq_biInf {C : Set U} {D : Set X} (h₁ : p.1 ∈ C)
    (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔ (⨆ u ∈ C, K (u, p.2)) = ⨅ x ∈ D, K (p.1, x) := by
  have hle : K p ≤ ⨆ u ∈ C, K (u, p.2) := le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) p.1 h₁
  have hge : (⨅ x ∈ D, K (p.1, x)) ≤ K p := iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) p.2 h₂
  constructor
  · rintro ⟨-, -, hu, hx⟩
    exact le_antisymm (le_iInf₂ fun x hx' => (iSup₂_le hu).trans (hx x hx')) (hge.trans hle)
  · intro h
    refine ⟨h₁, h₂, fun u hu => ?_, fun x hx => ?_⟩
    · exact ((le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) u hu).trans h.le).trans hge
    · exact (hle.trans h.le).trans (iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) x hx)

@[simp] theorem isSaddlePointOn_univ_univ :
    IsSaddlePointOn K Set.univ Set.univ p ↔ IsSaddlePoint K p := by
  simp only [IsSaddlePointOn, IsSaddlePoint, Set.mem_univ, true_and, forall_const]

/-! ### Restricting the outer extrema to the effective domains -/

theorem iInf_slice_eq_bot_of_notMem_dom₁ {u : U} (hu : u ∉ dom₁ K) : (⨅ x, K (u, x)) = ⊥ := by
  rw [mem_dom₁] at hu
  push Not at hu
  obtain ⟨x, hx⟩ := hu
  exact le_bot_iff.1 ((iInf_le (fun x => K (u, x)) x).trans hx)

theorem iSup_slice_eq_top_of_notMem_dom₂ {x : X} (hx : x ∉ dom₂ K) : (⨆ u, K (u, x)) = ⊤ := by
  rw [mem_dom₂] at hx
  push Not at hx
  obtain ⟨u, hu⟩ := hx
  exact top_le_iff.1 (hu.trans (le_iSup (fun u => K (u, x)) u))

/-- The outer supremum in `sup inf` may always be restricted to `dom₁ K`: off it the inner
infimum is `−∞`. -/
theorem maximin_eq_biSup_dom₁ (K : U × X → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ x, K (u, x) := by
  refine le_antisymm (iSup_le fun u => ?_)
    (iSup₂_le fun u _ => le_iSup (fun u => ⨅ x, K (u, x)) u)
  by_cases hu : u ∈ dom₁ K
  · exact le_iSup₂ (f := fun u (_ : u ∈ dom₁ K) => ⨅ x, K (u, x)) u hu
  · rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact bot_le

/-- The outer infimum in `inf sup` may always be restricted to `dom₂ K`: off it the inner
supremum is `+∞`. -/
theorem minimax_eq_biInf_dom₂ (K : U × X → EReal) :
    minimax K = ⨅ x ∈ dom₂ K, ⨆ u, K (u, x) := by
  refine le_antisymm (le_iInf₂ fun x _ => iInf_le (fun x => ⨆ u, K (u, x)) x)
    (le_iInf fun x => ?_)
  by_cases hx : x ∈ dom₂ K
  · exact iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => ⨆ u, K (u, x)) x hx
  · rw [iSup_slice_eq_top_of_notMem_dom₂ hx]
    exact le_top

end Basic

/-! ### Theorem 36.4: the two extrema see only the equivalence class -/

section ClosureExtrema

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] {g : E → EReal}

/-- The concave mirror of `iInf_clFn_eq_iInf`: a concave function and its concave closure have the
same supremum. Like its convex original it needs no convexity.

This belongs next to `clConcave` in `Duality/ConcaveConj.lean`; it lives here until something else
needs it. -/
theorem iSup_clConcave_eq_iSup (g : E → EReal) : (⨆ x, clConcave g x) = ⨆ x, g x := by
  have h : (⨆ x, clConcave g x) = -⨅ x, clFn (fun z => -(g z)) x := by
    rw [Tdaf.EReal.neg_iInf]
    exact iSup_congr fun x => rfl
  rw [h, iInf_clFn_eq_iInf, Tdaf.EReal.neg_iInf]
  exact iSup_congr fun x => neg_neg _

end ClosureExtrema

section Thm364

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [TopologicalSpace X]
  [AddCommGroup X] {K L : U × X → EReal} {p : U × X}

omit [TopologicalSpace U] [AddCommGroup U] in
/-- Closing in the convex variable does not change the inner infimum. -/
theorem iInf_partialCl₂_slice (K : U × X → EReal) (u : U) :
    (⨅ x, partialCl₂ K (u, x)) = ⨅ x, K (u, x) :=
  iInf_clFn_eq_iInf fun x => K (u, x)

omit [TopologicalSpace X] [AddCommGroup X] in
/-- Closing in the concave variable does not change the inner supremum. -/
theorem iSup_partialCl₁_slice (K : U × X → EReal) (x : X) :
    (⨆ u, partialCl₁ K (u, x)) = ⨆ u, K (u, x) :=
  iSup_clConcave_eq_iSup fun u => K (u, x)

omit [AddCommGroup U] in
/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same inner infima —
"two convex functions with the same closure have the same infimum". -/
theorem SaddleEquiv.iInf_slice_eq (h : SaddleEquiv K L) (u : U) :
    (⨅ x, K (u, x)) = ⨅ x, L (u, x) := by
  rw [← iInf_partialCl₂_slice K u, ← iInf_partialCl₂_slice L u, h.2]

omit [AddCommGroup X] in
/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same inner suprema. -/
theorem SaddleEquiv.iSup_slice_eq (h : SaddleEquiv K L) (x : X) :
    (⨆ u, K (u, x)) = ⨆ u, L (u, x) := by
  rw [← iSup_partialCl₁_slice K x, ← iSup_partialCl₁_slice L x, h.1]

omit [AddCommGroup U] in
/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same `sup inf`. -/
theorem SaddleEquiv.maximin_eq (h : SaddleEquiv K L) : maximin K = maximin L :=
  iSup_congr fun u => h.iInf_slice_eq u

omit [AddCommGroup X] in
/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same `inf sup`. -/
theorem SaddleEquiv.minimax_eq (h : SaddleEquiv K L) : minimax K = minimax L :=
  iInf_congr fun x => h.iSup_slice_eq x

/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same saddle-value. -/
theorem SaddleEquiv.hasSaddleValue_iff (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L := by
  change maximin K = minimax K ↔ maximin L = minimax L
  rw [h.maximin_eq, h.minimax_eq]

/-- **Rockafellar, Theorem 36.4**: equivalent saddle-functions have the same saddle-points.
The saddle-point condition is an equation between an inner supremum and an inner infimum
(`isSaddlePoint_iff_iSup_eq_iInf`), and equivalence preserves both. -/
theorem SaddleEquiv.isSaddlePoint_iff (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p := by
  rw [isSaddlePoint_iff_iSup_eq_iInf, isSaddlePoint_iff_iSup_eq_iInf, h.iSup_slice_eq,
    h.iInf_slice_eq]

end Thm364

/-! ### Corollary 36.3.1 -/

section Cor3631

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- **Rockafellar, Corollary 36.3.1**, first half: a saddle-point of a proper saddle-function
lies in its effective domain. Only properness is used: neither closedness, nor concave-convexity,
nor finite dimension. -/
theorem IsSaddlePoint.mem_domSaddle (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K := by
  obtain ⟨u₀, hu₀⟩ := hp.dom₁_nonempty
  obtain ⟨x₀, hx₀⟩ := hp.dom₂_nonempty
  have hbot : ⊥ < K p := by
    by_contra hc
    have hKp : K p = ⊥ := le_bot_iff.1 (not_lt.1 hc)
    exact absurd (le_bot_iff.1 (hKp ▸ h.1 u₀)) (ne_of_gt (hu₀ p.2))
  have htop : K p < ⊤ := by
    by_contra hc
    have hKp : K p = ⊤ := top_le_iff.1 (not_lt.1 hc)
    exact absurd (top_le_iff.1 (hKp ▸ h.2 x₀)) (ne_of_lt (hx₀ p.1))
  exact ⟨fun x => lt_of_lt_of_le hbot (h.2 x), fun u => lt_of_le_of_lt (h.1 u) htop⟩

/-- **Rockafellar, Corollary 36.3.1**, second half: the saddle-value at a saddle-point of a proper
saddle-function is finite. -/
theorem IsSaddlePoint.exists_maximin_eq_coe (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top
    (ne_of_gt (bot_lt_of_mem_domSaddle (h.mem_domSaddle hp)))
    (lt_top_of_mem_domSaddle (h.mem_domSaddle hp))
  exact ⟨r, by rw [h.maximin_eq, hr]⟩

end Cor3631

/-! ### Corollary 7.3.1, the tool Theorem 36.3 runs on -/

section Cor731

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **Rockafellar, Corollary 7.3.1**: a convex function that is somewhere below a real level `α`
is already below `α` at some relative interior point of its effective domain. The proof is the
book's: the open half-space `{(x, μ) | μ < α}` meets `epi f`, hence meets `ri (epi f)`
(Corollary 6.3.2), and `ri (epi f)` sits over `ri (dom f)` (Lemma 7.3).

This belongs in `RelativeInterior.lean` next to `ConvexFn.relint_epi`; it lives here until
something else needs it. -/
theorem ConvexFn.exists_mem_relint_dom_lt (hf : ConvexFn f) {α : ℝ} {x : E}
    (hx : f x < (α : EReal)) : ∃ z ∈ ri (dom f), f z < (α : EReal) := by
  obtain ⟨μ, hμ₁, hμ₂⟩ : ∃ μ : ℝ, f x ≤ (μ : EReal) ∧ μ < α := by
    rcases eq_or_ne (f x) ⊥ with hb | hb
    · exact ⟨α - 1, by rw [hb]; exact bot_le, by linarith⟩
    · obtain ⟨r, hr⟩ := Tdaf.EReal.exists_coe_of_ne_bot_of_lt_top hb (hx.trans_le le_top)
      refine ⟨r, le_of_eq hr, ?_⟩
      rw [hr] at hx
      exact_mod_cast hx
  have hU : IsOpen {q : E × ℝ | q.2 < α} := isOpen_lt continuous_snd continuous_const
  obtain ⟨q, hqU, hq⟩ := Convex.relint_inter_nonempty_of_isOpen hf.convex_epi hU
    ⟨(x, μ), hμ₂, subset_closure (show (x, μ) ∈ epi f from hμ₁)⟩
  rw [hf.relint_epi] at hq
  have hcast : ((q.2 : ℝ) : EReal) < (α : EReal) := by exact_mod_cast hqU
  exact ⟨q.1, hq.1, hq.2.trans hcast⟩

/-- **Rockafellar, Corollary 7.3.1**, in the form Theorem 36.3 uses it: minimising a convex
function over any set containing `ri (dom f)` gives the global infimum. -/
theorem ConvexFn.biInf_eq_iInf_of_relint_dom_subset (hf : ConvexFn f) {S : Set E}
    (hS : ri (dom f) ⊆ S) : (⨅ x ∈ S, f x) = ⨅ x, f x := by
  refine le_antisymm ?_ (le_iInf₂ fun x _ => iInf_le f x)
  refine Tdaf.EReal.le_of_forall_coe_le fun s hs => ?_
  refine Tdaf.EReal.le_coe_of_forall_lt fun q hq => ?_
  have hqc : ((s : ℝ) : EReal) < (q : EReal) := by exact_mod_cast hq
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 (lt_of_le_of_lt hs hqc)
  obtain ⟨z, hz, hzq⟩ := hf.exists_mem_relint_dom_lt hx
  exact lt_of_le_of_lt (iInf₂_le (f := fun x (_ : x ∈ S) => f x) z (hS hz)) hzq

end Cor731

/-! ### Theorem 36.3 -/

section Thm363

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}
  {p : U × X}

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Theorem 36.3**, the inner infimum: for a closed proper concave-convex `K` the
infimum of a slice over all of `X` is already reached over `D = dom₂ K`.

`SaddleStructure K` is Theorem 34.3's structural description; `ClosedSaddleFn.saddleStructure`
supplies it from closedness. -/
theorem biInf_dom₂_eq_iInf_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (u : U) : (⨅ x ∈ dom₂ K, K (u, x)) = ⨅ x, K (u, x) := by
  by_cases hu : u ∈ dom₁ K
  · refine ConvexFn.biInf_eq_iInf_of_relint_dom_subset (hK.convex_snd u) ?_
    have hrw : ri (dom fun x => K (u, x)) = ri (dom₂ K) :=
      Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₂ (hK.convex_snd u).convex_dom
        (dom₂_subset_dom_slice K u) (hs.1.dom_slice_subset_closure u hu)
    rw [hrw]
    exact intrinsicInterior_subset
  · obtain ⟨x₀, hx₀⟩ := ProperSaddleFn.relint_dom₂_nonempty hK hp
    have hbot : K (u, x₀) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu x₀ hx₀
    rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact le_bot_iff.1 ((iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => K (u, x)) x₀
      (intrinsicInterior_subset hx₀)).trans hbot.le)

omit [FiniteDimensional ℝ X] in
/-- **Rockafellar, Theorem 36.3**, the inner supremum: the mirror of `biInf_dom₂_eq_iInf_slice`,
obtained from it at the swapped saddle-function. -/
theorem biSup_dom₁_eq_iSup_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (x : X) : (⨆ u ∈ dom₁ K, K (u, x)) = ⨆ u, K (u, x) := by
  have h := biInf_dom₂_eq_iInf_slice (concaveConvexFn_saddleSwap hK) hs.saddleSwap hp.saddleSwap x
  rw [dom₂_saddleSwap] at h
  have hneg := congrArg (fun z : EReal => -z) h
  simpa only [Tdaf.EReal.neg_iInf, saddleSwap_apply, neg_neg] using hneg

omit [FiniteDimensional ℝ U] in
/-- **Rockafellar, Theorem 36.3**, first displayed equation: `sup inf` over the whole space is
`sup inf` over `C × D`. -/
theorem maximin_eq_biSup_biInf (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : maximin K = ⨆ u ∈ dom₁ K, ⨅ x ∈ dom₂ K, K (u, x) := by
  rw [maximin_eq_biSup_dom₁]
  exact iSup_congr fun u => iSup_congr fun _ => (biInf_dom₂_eq_iInf_slice hK hs hp u).symm

omit [FiniteDimensional ℝ X] in
/-- **Rockafellar, Theorem 36.3**, second displayed equation: `inf sup` over the whole space is
`inf sup` over `C × D`. -/
theorem minimax_eq_biInf_biSup (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : minimax K = ⨅ x ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, x) := by
  rw [minimax_eq_biInf_dom₂]
  exact iInf_congr fun x => iInf_congr fun _ => (biSup_dom₁_eq_iSup_slice hK hs hp x).symm

/-- **Rockafellar, Theorem 36.3**, last sentence: the saddle-points of `K` with respect to the
whole space are exactly its saddle-points with respect to `C × D = dom K`. -/
theorem isSaddlePoint_iff_isSaddlePointOn_dom (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := h.mem_domSaddle hp
    refine (isSaddlePointOn_iff_biSup_eq_biInf h₁ h₂).2 ?_
    rw [biSup_dom₁_eq_iSup_slice hK hs hp, biInf_dom₂_eq_iInf_slice hK hs hp]
    exact isSaddlePoint_iff_iSup_eq_iInf.1 h
  · intro h
    refine isSaddlePoint_iff_iSup_eq_iInf.2 ?_
    rw [← biSup_dom₁_eq_iSup_slice hK hs hp, ← biInf_dom₂_eq_iInf_slice hK hs hp]
    exact (isSaddlePointOn_iff_biSup_eq_biInf h.1 h.2.1).1 h

end Thm363

/-! ### Slices of a bifunction in its *first* variable -/

section SliceFlip

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- Each *first*-variable slice `F (·) x` of a convex bifunction is convex — the mirror of
`ConvexBifun.convexFn_apply`, and, like it, not an instance of `convexFn_compLin`, because
`u ↦ (u, x)` is affine and not linear. -/
theorem ConvexBifun.convexFn_flip (hF : ConvexBifun F) (x : X) : ConvexFn fun u => F u x := by
  refine convexFn_of_epi_combo fun u w mu nu hu hw a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (w, x)) hu hw ha hb hab
  have hx : a • ((u, x) : U × X) + b • (w, x) = (a • u + b • w, x) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hx] at h

end SliceFlip

section ClosedSliceFlip

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- Each *first*-variable slice of a closed bifunction is closed — the mirror of
`ClosedBifun.imageClosedBifun`. -/
theorem ClosedBifun.closedFn_flip (hF : ClosedBifun F) (x : X) : ClosedFn fun u => F u x := by
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun u => congrFun h (u, x)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_id.prodMk continuous_const), fun u => hne (u, x)⟩)

end ClosedSliceFlip

/-! ### The Lagrangian as a saddle-function -/

section SaddleLagrangian

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The Lagrangian of `(P)` read as a function on the product `V × X`, i.e. as a saddle-function.
Rockafellar's §36 studies the minimax problem for exactly this function. -/
noncomputable def saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V × X → EReal :=
  fun q => lagrangian Bu F q.1 q.2

theorem saddleLagrangian_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (q : V × X) :
    saddleLagrangian Bu F q = lagrangian Bu F q.1 q.2 := rfl

end SaddleLagrangian

/-! ### Theorem 29.3: saddle-points of the Lagrangian -/

section Thm293

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X] in
/-- The companion of `iInf_lagrangian`: *maximising* the Lagrangian over the price variable gives
the closure of the objective slice at the origin. This is `clFn_zero_eq_iSup_iInf` read at
`f = F (·) x`, and it is the computation Rockafellar performs inside the proof of Theorem 29.3. -/
theorem iSup_lagrangian (hf : ConvexFn fun u => F u x) :
    (⨆ w, lagrangian Bu F w x) = clFn (fun u => F u x) 0 :=
  (clFn_zero_eq_iSup_iInf (B := Bu) hf).symm

/-- For a closed convex bifunction the supremum of the Lagrangian over the price variable is the
objective `(F 0)(x)` itself. -/
theorem iSup_lagrangian_eq (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    (⨆ w, lagrangian Bu F w x) = F 0 x := by
  rw [iSup_lagrangian (hF.convexFn_flip x), congrFun (hcl.closedFn_flip x) 0]

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] [TopologicalSpace X]
  [IsTopologicalAddGroup X] in
/-- Properness bounds the Lagrangian's infimum away from `+∞`. -/
theorem iInf_lagrangian_ne_top (hpr : Proper (graphFn F)) :
    (⨅ y, lagrangian Bu F v y) ≠ ⊤ := by
  obtain ⟨q, hq⟩ := hpr.dom_nonempty
  refine ne_of_lt (lt_of_le_of_lt (iInf_le (fun y => lagrangian Bu F v y) q.2) ?_)
  refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u q.2) q.1) ?_
  exact _root_.EReal.add_lt_top (_root_.EReal.coe_ne_top _) (ne_of_lt hq)

/-- **Rockafellar, Theorem 29.3**: `(v, x)` is a saddle-point of the Lagrangian of `(P)` exactly
when `v` is a Kuhn–Tucker vector for `(P)` and `x` is an optimal solution to `(P)`.

The proof is Rockafellar's: `⨅ y, L (v, y) ≤ inf F 0 ≤ (F 0) x = ⨆ w, L (w, x)`, the outer terms
are respectively `≠ ⊤` and `≠ ⊥` by properness, and the saddle-point condition
(`isSaddlePoint_iff_iSup_eq_iInf`) collapses the chain. -/
theorem isSaddlePoint_lagrangian_iff (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x)
      ↔ v ∈ KuhnTucker Bu F ∧ x ∈ argmin (F 0) := by
  have hA : (⨅ y, lagrangian Bu F v y) ≤ infBifun F 0 := iInf_lagrangian_le Bu F v
  have hB : infBifun F 0 ≤ F 0 x := iInf_le (fun z => F 0 z) x
  have hsup : (⨆ w, lagrangian Bu F w x) = F 0 x := iSup_lagrangian_eq hF hcl
  have hAtop : (⨅ y, lagrangian Bu F v y) ≠ ⊤ := iInf_lagrangian_ne_top hpr
  have hBbot : F 0 x ≠ ⊥ := hpr.ne_bot (0, x)
  rw [isSaddlePoint_iff_iSup_eq_iInf, mem_kuhnTucker_iff_iInf_lagrangian,
    mem_argmin_iff_le_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [hsup]
  constructor
  · intro h
    have h1 : (⨅ y, lagrangian Bu F v y) = infBifun F 0 :=
      le_antisymm hA (by rw [← h]; exact hB)
    have h2 : F 0 x = infBifun F 0 := by rw [h, h1]
    exact ⟨⟨by rw [← h1]; exact hAtop, by rw [← h2]; exact hBbot, h1⟩, le_of_eq h2⟩
  · rintro ⟨⟨-, -, h1⟩, h2⟩
    rw [h1]
    exact le_antisymm (le_trans h2 (le_of_eq rfl)) hB

end Thm293

/-! ### Theorem 36.6 and Corollary 30.5.1 -/

section Thm366

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [IsCompatiblePairing Bu] [TopologicalSpace X] [IsTopologicalAddGroup X] in
/-- Minimising the Lagrangian over the convex variable *is* evaluating the dual objective `F* 0`:
both are `⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem iInf_lagrangian_eq_adjointBifun_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (⨅ y, lagrangian Bu F v y) = adjointBifun Bu Bx F 0 v := by
  rw [iInf_lagrangian, adjointBifun_zero_apply]

/-- **Rockafellar, Corollary 30.5.1**, (b) ⟺ (c): `(v, x)` is a saddle-point of the Lagrangian
exactly when the primal objective at `x` is no larger than the dual objective at `v` — in which
case weak duality forces equality. -/
theorem isSaddlePoint_lagrangian_iff_le_adjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ F 0 x ≤ adjointBifun Bu Bx F 0 v := by
  have hge : adjointBifun Bu Bx F 0 v ≤ F 0 x :=
    (adjointBifun_zero_le Bu Bx F v).trans (iInf_le (fun z => F 0 z) x)
  rw [isSaddlePoint_iff_iSup_eq_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [iSup_lagrangian_eq hF hcl, iInf_lagrangian_eq_adjointBifun_zero (Bu := Bu) Bx]
  exact ⟨le_of_eq, fun h => le_antisymm h hge⟩

/-- **Rockafellar, Corollary 30.5.1**, (a) ⟺ (b) — the corollary `Optimization/Normal.lean` had
to leave out for want of `IsSaddlePoint`. `(v, x)` is a saddle-point of the Lagrangian exactly
when normality holds and `x`, `v` are optimal for `(P)` and `(P*)`. -/
theorem isSaddlePoint_lagrangian_iff_normal_and_optimal (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ Normal F ∧ x ∈ argmin (F 0) ∧
      adjointBifun Bu Bx F 0 v = ⨆ w, adjointBifun Bu Bx F 0 w := by
  constructor
  · intro h
    obtain ⟨hv, hx⟩ := (isSaddlePoint_lagrangian_iff hF hcl hpr).1 h
    have hn : Normal F := normal_of_kuhnTucker_nonempty Bx hF ⟨v, hv⟩
    obtain ⟨ht, hb, -⟩ := (mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)).1 hv
    exact ⟨hn, hx,
      (mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bu := Bu) Bx hF hn ht hb).1 hv⟩
  · rintro ⟨hn, hx, hv⟩
    refine (isSaddlePoint_lagrangian_iff_le_adjointBifun Bx hF hcl).2 ?_
    rw [hv, (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hn]
    exact mem_argmin_iff_le_iInf.1 hx

omit [AddCommGroup Y] [Module ℝ Y] in
/-- **Rockafellar, Theorem 36.6** (= **Corollary 29.3.1**), the general Kuhn–Tucker theorem: once
one Kuhn–Tucker vector is known to exist, `x` solves `(P)` exactly when some `v` makes `(v, x)` a
saddle-point of the Lagrangian, and the `v` that do are precisely the Kuhn–Tucker vectors. -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hkt : (KuhnTucker Bu F).Nonempty) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) := by
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := hkt
    exact ⟨w, (isSaddlePoint_lagrangian_iff hF hcl hpr).2 ⟨hw, hx⟩⟩
  · rintro ⟨w, hw⟩
    exact ((isSaddlePoint_lagrangian_iff hF hcl hpr).1 hw).2

omit [AddCommGroup Y] [Module ℝ Y] in
/-- **Rockafellar, Theorem 36.6**, the "which `v`" clause: for an optimal `x`, the prices `v`
completing it to a saddle-point of the Lagrangian are exactly the Kuhn–Tucker vectors. -/
theorem isSaddlePoint_lagrangian_iff_mem_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hx : x ∈ argmin (F 0)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ v ∈ KuhnTucker Bu F :=
  (isSaddlePoint_lagrangian_iff hF hcl hpr).trans ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

end Thm366

section Thm366Slater

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Bifun U X}
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {x : X}

/-- **Rockafellar, Theorem 36.6** under the strong-consistency qualification: for a strongly
consistent closed proper convex program, `x` is an optimal solution exactly when it is the convex
half of a saddle-point of the Lagrangian. -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian_of_stronglyConsistent
    (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hip : Proper (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) :=
  mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr
    (kuhnTucker_nonempty_of_stronglyConsistent hF hip hs ht)

end Thm366Slater

/-! ### Theorem 36.5: Lagrangians are exactly the upper closed concave-convex functions -/

section NegPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- A negated pairing is still continuous. -/
theorem isContinuousPairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (-B) :=
  ⟨fun y => (continuous_pairing B y).neg⟩

/-- A negated pairing is still compatible: `g = ⟨·, y⟩` for `-B` exactly when `-g = ⟨·, y⟩`
for `B`. -/
theorem isCompatiblePairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (-B) :=
  have : IsContinuousPairing (-B) := isContinuousPairing_neg B
  { surjective_eval := fun g => by
      obtain ⟨y, hy⟩ := exists_pairing_eq B (-g)
      refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
      have h : (-B) x y = -(B x y) := rfl
      rw [evalCLM_apply, h, ← hy]
      exact neg_neg _ }

omit [TopologicalSpace E] in
theorem flip_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (-B).flip = -B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

end NegPairing

section FlipBifun

variable {U X : Type*}

/-- The bifunction with its two arguments exchanged. Unlike Rockafellar's inverse operation `F_*`
this does not negate, so it stays convex; it is what lets Theorem 33.3 be applied to the swapped
saddle-function. -/
def flipBifun (F : Bifun U X) : Bifun X U := fun x u => F u x

@[simp] theorem flipBifun_apply (F : Bifun U X) (x : X) (u : U) : flipBifun F x u = F u x := rfl

@[simp] theorem flipBifun_flipBifun (F : Bifun U X) : flipBifun (flipBifun F) = F := rfl

theorem graphFn_flipBifun (F : Bifun U X) (q : X × U) :
    graphFn (flipBifun F) q = graphFn F (q.2, q.1) := rfl

end FlipBifun

section FlipBifunConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- Exchanging the two arguments preserves convexity. -/
theorem convexBifun_flipBifun (hF : ConvexBifun F) : ConvexBifun (flipBifun F) := by
  refine convexFn_of_epi_combo fun q r mu nu hq hr a b ha hb hab => ?_
  have h := hF.epi_combo (x := (q.2, q.1)) (y := (r.2, r.1)) hq hr ha hb hab
  have hsw : a • ((q.2, q.1) : U × X) + b • (r.2, r.1)
      = ((a • q + b • r).2, (a • q + b • r).1) := rfl
  rwa [hsw] at h

end FlipBifunConvex

section FlipBifunClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- Exchanging the two arguments preserves closedness. -/
theorem closedBifun_flipBifun (hF : ClosedBifun F) : ClosedBifun (flipBifun F) := by
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun q => congrFun h (q.2, q.1)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_snd.prodMk continuous_fst), fun q => hne (q.2, q.1)⟩)

end FlipBifunClosed

section Thm365

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {L : V × X → EReal}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- **The Lagrangian is a bracket, after swapping.** Rockafellar writes the Lagrangian as
`L (v, x) = ⟨v, F_* x⟩` through the *inverse* bifunction; the same identity, negated and with the
two variables exchanged, is the bracket of `flipBifun F` for the **negated** pairing. Stating it
this way lets Theorem 33.3 be used verbatim instead of remirrored. -/
theorem saddleSwap_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    saddleSwap (saddleLagrangian Bu F)
      = fun q : X × V => bracket (-Bu) (flipBifun F) q.1 q.2 := by
  funext q
  rw [saddleSwap_apply, saddleLagrangian_apply, lagrangian_apply, bracket_apply,
    Tdaf.EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  have hb : (((-Bu) u q.2 : ℝ) : EReal) = ((-(Bu u q.2) : ℝ) : EReal) := rfl
  rw [hb, _root_.EReal.coe_neg,
    _root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _)) (.inl (_root_.EReal.coe_ne_top _))]
  rfl

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] in
/-- **Rockafellar, §36**, the sentence before Theorem 36.5: the Lagrangian of a convex program is
a concave-convex function. This is Theorem 33.1, applied to the swapped bracket. -/
theorem concaveConvexFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian Bu F) := by
  have h : ConcaveConvexFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact concaveConvexFn_bracket (convexBifun_flipBifun hF) (-Bu)
  have h2 := concaveConvexFn_saddleSwap h
  rwa [saddleSwap_saddleSwap] at h2

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **Rockafellar, Theorem 36.5**, necessity: the Lagrangian of a closed convex bifunction is an
upper closed concave-convex function. -/
theorem upperClosedFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : ConvexBifun F) (hcl : ClosedBifun F) : UpperClosedFn (saddleLagrangian Bu F) := by
  have h1 : IsCompatiblePairing (-Bu) := isCompatiblePairing_neg Bu
  have h2 : IsCompatiblePairing (-Bu).flip := by
    rw [flip_neg]
    exact isCompatiblePairing_neg Bu.flip
  have h : LowerClosedFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact lowerClosedFn_bracket Bx (-Bu) (convexBifun_flipBifun hF) (closedBifun_flipBifun hcl)
  have h3 := lowerClosedFn_iff_upperClosedFn_saddleSwap.1 h
  rwa [saddleSwap_saddleSwap] at h3

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **Rockafellar, Theorem 36.5**, sufficiency: every upper closed concave-convex function on
`V × X` is the Lagrangian of one and only one closed convex bifunction from `U` to `X`. -/
theorem exists_unique_closedBifun_saddleLagrangian_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun U X, ConvexBifun G ∧ ClosedBifun G ∧ saddleLagrangian Bu G = L := by
  have h1 : IsCompatiblePairing (-Bu) := isCompatiblePairing_neg Bu
  have h2 : IsCompatiblePairing (-Bu).flip := by
    rw [flip_neg]
    exact isCompatiblePairing_neg Bu.flip
  have hsw : ConcaveConvexFn (saddleSwap L) := concaveConvexFn_saddleSwap hL
  have hlc : LowerClosedFn (saddleSwap L) := by
    refine lowerClosedFn_iff_upperClosedFn_saddleSwap.2 ?_
    rwa [saddleSwap_saddleSwap]
  obtain ⟨H, ⟨hHconv, hHcl, hHbr⟩, huniq⟩ :=
    exists_unique_convexBifun_bracket_eq Bx (-Bu) hsw hlc
  refine ⟨flipBifun H, ⟨convexBifun_flipBifun hHconv, closedBifun_flipBifun hHcl, ?_⟩, ?_⟩
  · refine saddleSwap_injective ?_
    rw [saddleSwap_saddleLagrangian, flipBifun_flipBifun]
    exact hHbr
  · rintro G ⟨hGconv, hGcl, hGL⟩
    have hbr : (fun q : X × V => bracket (-Bu) (flipBifun G) q.1 q.2) = saddleSwap L := by
      rw [← saddleSwap_saddleLagrangian, hGL]
    have hHG := huniq (flipBifun G)
      ⟨convexBifun_flipBifun hGconv, closedBifun_flipBifun hGcl, hbr⟩
    rw [← hHG, flipBifun_flipBifun]

end Thm365

end Tdaf.ConvexAnalysis
