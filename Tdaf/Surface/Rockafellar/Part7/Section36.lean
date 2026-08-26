/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Saddle.Subgradient
import Tdaf.Surface.Rockafellar.Part7.Section33

/-!
# Rockafellar, §36: Minimax Problems

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §36, pp. 379–387: the two iterated extrema
`sup inf` and `inf sup`, the **saddle-value** and the **saddle-point**, the reduction of a minimax
problem on `C × D` to one on all of `ℝᵐ × ℝⁿ`, the **inverse bifunction** `F_*`, and — the
structural pay-off of Part VII — the identification of the Lagrangians of closed convex programs
with the upper closed concave-convex functions.

All seven numbered results are here: Lemmas 36.1 and 36.2, Theorems 36.3, 36.4, 36.5, 36.6 and
Corollary 36.3.1.

## The orientation convention (15449), in force for the whole rest of the book

Rockafellar declares it in one sentence, immediately before Theorem 36.3, and never repeats it:

> *"It is to be understood always that the minimization takes place in the convex argument of the
> function, and that the maximization takes place in the concave argument."*

For a **concave-convex** `K (u, v)` — concave in the **first** argument, convex in the **second**,
which is §33's orientation and this Part's — that fixes both iterated extrema once and for all:

| book | this module | reads |
|---|---|---|
| `sup_u inf_v K (u, v)` | `maximin K` | **maximise** over the **concave/first** argument, having
  **minimised** over the **convex/second** one |
| `inf_v sup_u K (u, v)` | `minimax K` | **minimise** over the **convex/second** argument, having
  **maximised** over the **concave/first** one |

Everything downstream is oriented by that single choice:

* **Lemma 36.1** is `maximin K ≤ minimax K` — `sup inf ≤ inf sup`, never the reverse.
* A **saddle-point** is a `p` with `K (u, p.2) ≤ K p ≤ K (p.1, v)` for all `u`, `v`: the **first**
  argument is where `K` is *maximised*, the **second** where it is *minimised*.
* `∂K = ∂₁K × ∂₂K` (§35, 15155) therefore mixes a **concave** subdifferential in the **first**
  argument with a **convex** one in the **second**. That is why §37's Corollary 37.5.2 has to
  insert `u* ↦ −u*` before it can speak of a monotone operator, and why Corollary 37.5.1's
  homeomorphism is the asymmetric `(u − u*, v + v*)`.
* The lower conjugate `K̲*` is `sup_v inf_u`, the upper `K̄*` is `inf_u sup_v` (§37, 15763/15769),
  and `K̲* ≤ K̄*` is Lemma 36.1 again (`lowerConjSaddle_le_upperConjSaddle`).

**Theorems 36.3–36.6 and every result of §37 are false verbatim under the opposite convention.**
Track the sign explicitly; do not try to derive it from the shape of a statement.

For a *convex-concave* `K` the book exchanges the two words; the translation is plain **negation**,
`convexConcave_lowerClosed_iff` / `convexConcave_upperClosed_iff` in §33 — *not* `saddleSwap`,
which preserves the concave-convex class rather than flipping it.

## Contents

| label | declaration |
|---|---|
| §36 definitions, 15311–15349 | `isSaddlePoint_iff_forall`, `hasSaddleValue_iff_maximin_eq` |
| Lemma 36.1 | `lemma_36_1`, `lemma_36_1_on` |
| Lemma 36.2 | `lemma_36_2`, `lemma_36_2_saddleValue` |
| §36 extension device, 15379–15447 | `maximin_restricted`, `minimax_restricted` |
| Theorem 36.3 | `theorem_36_3_maximin`, `theorem_36_3_minimax`, `theorem_36_3_saddlePoint` |
| Corollary 36.3.1 | `corollary_36_3_1_mem_dom`, `corollary_36_3_1_finite` |
| Theorem 36.4 | `theorem_36_4_maximin`, `theorem_36_4_minimax`,
  `theorem_36_4_hasSaddleValue`, `theorem_36_4_saddlePoint` |
| §36 definitions, 15505–15561 | `concaveBifun_inverseBifun`, `inverseBifun_involutive`,
  `concaveAdjointBifun_inverseBifun`, `inverseBifunBracket`, `inverseBifunBracket_apply` |
| §36, 15565–15583 | `saddleLagrangian_eq_inverseBifunBracket`,
  `saddleLagrangian_concaveConvex` |
| Theorem 36.5 | `theorem_36_5`, `theorem_36_5_upperClosed`, `theorem_36_5_unique` |
| §36, 15665–15679 | `zero_mem_saddleSubgradient_iff_isSaddlePoint`, `kuhnTucker_condition_iff` |
| Theorem 36.6 | `theorem_36_6_stronglyConsistent`, `theorem_36_6_strictlyConsistent`,
  `theorem_36_6_polyhedral`, `theorem_36_6_kuhnTucker` |

## What §36 exports, by book name

Everything here is the backbone's, used verbatim, except `Rockafellar.inverseBifunBracket`.

* `sup_u inf_v K` and `inf_v sup_u K` — `maximin`, `minimax` (`Saddle/Minimax.lean`)
* the saddle-value exists — `HasSaddleValue`, the bare equation `maximin K = minimax K`
* saddle-point, saddle-point relative to `C × D` — `IsSaddlePoint`, `IsSaddlePointOn`
* effective domain `dom K = C × D` of a saddle-function — `domSaddle`, `dom₁`, `dom₂`
* closed / proper saddle-function — `ClosedSaddleFn` (`Saddle/Equiv.lean`), `ProperSaddleFn`
* equivalent saddle-functions — `SaddleEquiv` (`Saddle/Equiv.lean`)
* **the inverse bifunction `F_*`** — `inverseBifun` (`Optimization/Perturbation.lean`; note the
  module, it is *not* in `Saddle/`), with `inverseBifun_apply`, `inverseBifun_inverseBifun`,
  `graphFn_inverseBifun`
* `F_*^*`, i.e. `(F_*)^* = (F^*)_*` — `inverseBifun (dualProgram F)`, equal to
  `concaveAdjointBifun (pairing m) (pairing n) (inverseBifun F)` by
  `concaveAdjointBifun_inverseBifun`
* the Lagrangian `L (u*, x)` of `(P)` — `lagrangian (pairing m) F` (§29), and as a saddle-function
  on `ℝᵐ × ℝⁿ`, `saddleLagrangian (pairing m) F`
* **`⟨u*, F_* x⟩`** — `Rockafellar.inverseBifunBracket`, defined here; it *is* the Lagrangian
  (`saddleLagrangian_eq_inverseBifunBracket`), and §37 conjugates through it
* the **Kuhn–Tucker condition** `(0, 0) ∈ ∂L (ū*, x̄)` —
  `(0 : Rn m × Rn n) ∈ saddleSubgradient (pairing m) (pairing n) (saddleLagrangian (pairing m) F) p`
  (`saddleSubgradient` is `Saddle/Subgradient.lean`'s; §35 is where the surface names it)

## Where the book is defective

**Theorem 36.6 is printed with no proof, and the section ends immediately after its statement**
(15681). Rockafellar introduces it as a restatement of Corollary 29.3.1, and that is exactly how it
is closed here: `corollary_29_3_1_stronglyConsistent` and its two siblings in
`Part6/Section29.lean`, composed with `zero_mem_saddleSubgradient_iff_isSaddlePoint`.

**Corollary 36.3.1 needs only properness.** The book says "closed proper saddle-function"; neither
closedness nor concave-convexity nor finite dimension is used, and none is carried here. Theorem
36.3, whose proof the corollary invokes, does need them — but only to identify `dom K` as the set
over which the outer extrema may be restricted, and `IsSaddlePoint.mem_domSaddle` reaches the
membership directly from the two saddle-point inequalities.

**`HasSaddleValue` is only the equality of the two iterated extrema.** Rockafellar calls the common
value the saddle-value *when they are equal*, and states finiteness separately wherever he needs it.
Building finiteness into the definition would make Corollary 36.3.1 — whose whole content is that
finiteness is a *consequence* at a saddle-point of a proper function — vacuous.

## What is not here

**Nothing numbered is omitted.** All seven results have declarations.

Of the unnumbered material:

* **The ±∞ extension device (15379–15447)** — extend a finite `K` on `C × D` by `+∞` for
  `u ∈ C, v ∉ D` and `−∞` for `u ∉ C, v ∈ D`, and the two problems coincide — is *omitted with a
  reason*: `maximin_restricted` and `minimax_restricted` record the same content in the sharper
  hypothesis-free form the backbone proves it in (the outer extremum may always be restricted to
  the effective domain, whatever `K` is), and Theorem 36.3 is the version every later result uses.
  The device itself is a statement about a *choice* of extension, and the surface has no reason to
  quantify over such choices.
* **The two-player game (15361–15375)** is motivation, not mathematics; nothing is asserted.
* **`F_*` of an indicator bifunction is the indicator of `A⁻¹` (15517)** is *deferred by scope*: the
  backbone has `linearIndicatorBifun` (§29) but no concave indicator bifunction, so the statement
  would have to introduce one, and `A⁻¹` is only a bifunction-level inverse for a `LinearEquiv`.
* **`(F* x*)(u*) = inf_x {L (u*, x) − ⟨x*, x⟩}` (15645)** is *deferred by scope*: its `x* = 0`
  instance, which is the one the book uses (the dual objective is `inf_x L (·, x)`), is
  `dualProgram_zero_eq_iInf_lagrangian` in `Part6/Section30.lean`, and the general form needs a
  backbone `adjointBifun_eq_iInf_lagrangian_sub` that does not exist.
* **The four displays after Theorem 36.5 (15613–15661)** — the objective and optimal value of `(P)`
  are `sup_{u*} L (u*, ·)` and `inf_x sup_{u*} L`, those of `(P*)` are `inf_x L (·, x)` and
  `sup_{u*} inf_x L` — are already `objective_eq_iSup_lagrangian`, `infBifun_eq_minimax`,
  `dualProgram_zero_eq_iInf_lagrangian` and `supBifun_dualProgram_eq_maximin` in
  `Part6/Section30.lean`, which §36 imports. They are cited, not restated: the surface namespace is
  flat, and a second copy would be a name collision.
* **"The Kuhn–Tucker condition reduces to Theorem 28.3 / Theorem 31.3" (15679)** is *deferred by
  scope*: both are subgradient calculus (§23) applied to a particular `F`, and neither reduction is
  a numbered result.
* **Corollary 34.2.2** — "each equivalence class contains a unique upper closed `L`" — is quoted in
  the discussion after Theorem 36.5 (15663) and is §34's, written concurrently. What Theorem 36.5
  needs of it is the *uniqueness* half of `exists_unique_closedBifun_saddleLagrangian_eq`
  (`Saddle/Minimax.lean`), which is proved from `exists_unique_convexBifun_bracket_eq`
  (`Saddle/Kernel.lean`); no §34 surface declaration is used.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §36, pp. 379–387.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The saddle-value and the saddle-point

Lines 15305–15349. `maximin`, `minimax`, `HasSaddleValue`, `IsSaddlePoint` and `IsSaddlePointOn`
are the backbone's and are used verbatim; the two theorems here are the book's defining displays. -/

section Defs

variable {m n : ℕ}

/-- **Rockafellar, §36** (15311–15317): the two iterated extrema, and (15319) the **saddle-value**
of `K` — their common value, *when they are equal*. This is `HasSaddleValue`, unfolded.

Nothing is said about the common value being finite; finiteness is a separate conclusion, drawn
where the book draws it (Corollary 36.3.1). -/
theorem hasSaddleValue_iff_maximin_eq (K : Rn m × Rn n → EReal) :
    HasSaddleValue K ↔ (⨆ u : Rn m, ⨅ v : Rn n, K (u, v)) = ⨅ v : Rn n, ⨆ u : Rn m, K (u, v) :=
  Iff.rfl

/-- **Rockafellar, §36** (15347), the definition of a **saddle-point**: `(ū, v̄)` is a saddle-point
of `K` with respect to maximizing over the first argument and minimizing over the second when

`K (u, v̄) ≤ K (ū, v̄) ≤ K (ū, v)` for all `u` and all `v`.

The orientation is the section's: the **first** argument is the one `K` is *maximised* over. -/
theorem isSaddlePoint_iff_forall (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔ ∀ u : Rn m, ∀ v : Rn n, K (u, p.2) ≤ K p ∧ K p ≤ K (p.1, v) :=
  ⟨fun h u v => ⟨h.1 u, h.2 v⟩, fun h => ⟨fun u => (h u 0).1, fun v => (h 0 v).2⟩⟩

end Defs

/-! ### Lemma 36.1 -/

section Lemma361

variable {m n : ℕ}

/-- **Rockafellar, Lemma 36.1** (15321): `sup inf ≤ inf sup`.

Specialises `maximin_le_minimax`, which needs **no hypothesis at all** — not even nonemptiness of
the two spaces, the book's `C × D ≠ ∅` serving only to make his formulation match this one. -/
theorem lemma_36_1 (K : Rn m × Rn n → EReal) : maximin K ≤ minimax K :=
  maximin_le_minimax K

/-- **Rockafellar, Lemma 36.1** (15321) in the book's own `C × D` form, for arbitrary subsets
`C ⊆ ℝᵐ` and `D ⊆ ℝⁿ`:

`sup_{u ∈ C} inf_{v ∈ D} K (u, v) ≤ inf_{v ∈ D} sup_{u ∈ C} K (u, v)`.

The book assumes `C × D` nonempty; the `⨆ ∈ / ⨅ ∈` reading makes that unnecessary, and the proof is
Rockafellar's verbatim — `K (u, v) ≥ inf_{v ∈ D} K (u, ·)` for every `u ∈ C`, so the inner supremum
dominates `α` for every `v ∈ D`. -/
theorem lemma_36_1_on (C : Set (Rn m)) (D : Set (Rn n)) (K : Rn m × Rn n → EReal) :
    (⨆ u ∈ C, ⨅ v ∈ D, K (u, v)) ≤ ⨅ v ∈ D, ⨆ u ∈ C, K (u, v) :=
  iSup₂_le fun u hu => le_iInf₂ fun v hv =>
    (iInf₂_le (f := fun v (_ : v ∈ D) => K (u, v)) v hv).trans
      (le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, v)) u hu)

end Lemma361

/-! ### Lemma 36.2 -/

section Lemma362

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Rockafellar, Lemma 36.2** (15355): `(ū, v̄)` is a saddle-point of `K` if and only if the
supremum in `sup_u inf_v K (u, v)` is attained at `ū`, the infimum in `inf_v sup_u K (u, v)` is
attained at `v̄`, and these two extrema are equal.

Specialises `isSaddlePoint_iff_attained`. No hypothesis is needed.

Stated on all of `ℝᵐ × ℝⁿ`, not on the book's `C × D`: the section's own reduction (15379–15447,
and Theorem 36.3 for the case that matters) makes the two the same problem, and every later result
in §§36–37 uses the whole-space form. `IsSaddlePointOn` and
`isSaddlePointOn_iff_biSup_eq_biInf` carry the `C × D` reading where it is wanted. -/
theorem lemma_36_2 (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔
      (⨅ v : Rn n, K (p.1, v)) = maximin K ∧ (⨆ u : Rn m, K (u, p.2)) = minimax K ∧
        HasSaddleValue K :=
  isSaddlePoint_iff_attained

/-- **Rockafellar, Lemma 36.2**, last sentence (15361): at a saddle-point the saddle-value of `K`
is `K (ū, v̄)` — both iterated extrema equal it. -/
theorem lemma_36_2_saddleValue (h : IsSaddlePoint K p) :
    maximin K = K p ∧ minimax K = K p :=
  ⟨IsSaddlePoint.maximin_eq h, IsSaddlePoint.minimax_eq h⟩

end Lemma362

/-! ### The reduction to the whole space

Lines 15379–15447. The book extends a finite `K` on `C × D` to `ℝᵐ × ℝⁿ` by `+∞` and `−∞` and
observes that the two minimax problems coincide. The backbone proves the sharper statement that
carries the same content: whatever `K` is, the *outer* extremum in each iterated extremum may be
restricted to the corresponding effective domain, because off it the *inner* extremum is already
`−∞`, respectively `+∞`. -/

section Extension

variable {m n : ℕ}

/-- **Rockafellar, §36** (15393–15399), in hypothesis-free form: the outer supremum in `sup inf`
may always be restricted to `C = dom₁ K`, since `inf_v K (u, v) = −∞` for `u ∉ C`.

Specialises `maximin_eq_biSup_dom₁`. -/
theorem maximin_restricted (K : Rn m × Rn n → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v : Rn n, K (u, v) :=
  maximin_eq_biSup_dom₁ K

/-- **Rockafellar, §36** (15407–15413), in hypothesis-free form: the outer infimum in `inf sup` may
always be restricted to `D = dom₂ K`, since `sup_u K (u, v) = +∞` for `v ∉ D`.

Specialises `minimax_eq_biInf_dom₂`. -/
theorem minimax_restricted (K : Rn m × Rn n → EReal) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u : Rn m, K (u, v) :=
  minimax_eq_biInf_dom₂ K

end Extension

/-! ### Theorem 36.3 -/

section Thm363

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Rockafellar, Theorem 36.3** (15453), first displayed equation. For a closed proper
concave-convex `K` on `ℝᵐ × ℝⁿ`, with `C = dom₁ K` and `D = dom₂ K`,

`sup_{u ∈ ℝᵐ} inf_{v ∈ ℝⁿ} K (u, v) = sup_{u ∈ C} inf_{v ∈ D} K (u, v)`.

Specialises `maximin_eq_biSup_biInf`. Rockafellar's proof runs Corollary 7.3.1 — a convex function
is minimised over any set containing `ri (dom f)` — against the domain relations of Theorem 34.3,
which is what `ClosedSaddleFn.saddleStructure` supplies. -/
theorem theorem_36_3_maximin (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v ∈ dom₂ K, K (u, v) :=
  maximin_eq_biSup_biInf hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Rockafellar, Theorem 36.3** (15453), second displayed equation:

`inf_{v ∈ ℝⁿ} sup_{u ∈ ℝᵐ} K (u, v) = inf_{v ∈ D} sup_{u ∈ C} K (u, v)`.

Specialises `minimax_eq_biInf_biSup`. Together with `theorem_36_3_maximin` this is the theorem's
assertion that the saddle-value with respect to `ℝᵐ × ℝⁿ` is the saddle-value with respect to
`C × D`: the two problems have the same pair of iterated extrema, hence the same
`HasSaddleValue`. -/
theorem theorem_36_3_minimax (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, v) :=
  minimax_eq_biInf_biSup hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Rockafellar, Theorem 36.3** (15473), last sentence: the saddle-points of `K` with respect to
`ℝᵐ × ℝⁿ` are the same as its saddle-points with respect to `C × D = dom K`.

Specialises `isSaddlePoint_iff_isSaddlePointOn_dom`. -/
theorem theorem_36_3_saddlePoint (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p :=
  isSaddlePoint_iff_isSaddlePointOn_dom hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

end Thm363

/-! ### Corollary 36.3.1 -/

section Cor3631

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Rockafellar, Corollary 36.3.1** (15483), first assertion: a saddle-point of a proper
saddle-function lies in `dom K = dom₁ K × dom₂ K`.

Specialises `IsSaddlePoint.mem_domSaddle`. The book deduces it from Theorem 36.3 and so states it
for a *closed* proper saddle-function; closedness is not used. The two saddle-point inequalities
already forbid `K p = ±∞` once `K` is finite somewhere in each variable. -/
theorem corollary_36_3_1_mem_dom (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp h

/-- **Rockafellar, Corollary 36.3.1** (15483), second assertion: the saddle-value of a proper
saddle-function that has a saddle-point is **finite**.

Specialises `IsSaddlePoint.exists_maximin_eq_coe`. This is the corollary that `HasSaddleValue`
deliberately does not absorb: `HasSaddleValue` is the bare equality of the two iterated extrema, so
finiteness stays a conclusion with content. -/
theorem corollary_36_3_1_finite (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) :=
  IsSaddlePoint.exists_maximin_eq_coe hp h

end Cor3631

/-! ### Theorem 36.4 -/

section Thm364

variable {m n : ℕ} {K L : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Rockafellar, Theorem 36.4** (15491): equivalent saddle-functions on `ℝᵐ × ℝⁿ` have the same
`sup inf`.

Specialises `SaddleEquiv.maximin_eq`. Rockafellar's proof: equivalence is `cl₁ K = cl₁ K'` and
`cl₂ K = cl₂ K'`, two concave functions with the same closure have the same supremum and two convex
functions with the same closure have the same infimum, and the two iterated extrema see only those
inner extrema. Neither closedness nor properness nor finite dimension enters. -/
theorem theorem_36_4_maximin (h : SaddleEquiv K L) : maximin K = maximin L :=
  SaddleEquiv.maximin_eq h

/-- **Rockafellar, Theorem 36.4** (15491): equivalent saddle-functions have the same `inf sup`.

Specialises `SaddleEquiv.minimax_eq`. -/
theorem theorem_36_4_minimax (h : SaddleEquiv K L) : minimax K = minimax L :=
  SaddleEquiv.minimax_eq h

/-- **Rockafellar, Theorem 36.4** (15491): equivalent saddle-functions have the same saddle-value —
one has it exactly when the other does, and then they agree.

Specialises `SaddleEquiv.hasSaddleValue_iff`. -/
theorem theorem_36_4_hasSaddleValue (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L :=
  SaddleEquiv.hasSaddleValue_iff h

/-- **Rockafellar, Theorem 36.4** (15491): equivalent saddle-functions have the same saddle-points
(if any).

Specialises `SaddleEquiv.isSaddlePoint_iff`. This is what makes minimax theory a theory of
*equivalence classes*, and hence — by Theorem 36.5 — of closed convex programs. -/
theorem theorem_36_4_saddlePoint (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p :=
  SaddleEquiv.isSaddlePoint_iff h

end Thm364

/-! ### The inverse bifunction `F_*`

Lines 15505–15561. `F_*` is the backbone's `inverseBifun`, in `Optimization/Perturbation.lean`
beside `Bifun` and `graphFn` — *not* in a `Saddle/` module. It is used verbatim; the declarations
here are the properties the book records and §37 uses. -/

section Inverse

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Rockafellar, §36** (15515): `F_*` is **concave** if `F` is convex.

The backbone has the other half, `convexBifun_inverseBifun` (`Saddle/Minimax.lean`); this is its
mirror, and both are the observation that `inverseBifun` is `flipBifun` composed with a change of
sign (`inverseBifun_eq_flipBifun_neg`). -/
theorem concaveBifun_inverseBifun (hF : ConvexBifun F) : ConcaveBifun (inverseBifun F) := by
  have he : (fun q : Rn n × Rn m => -(graphFn (inverseBifun F) q)) = graphFn (flipBifun F) :=
    funext fun _ => neg_neg _
  have h : ConcaveFn (graphFn (inverseBifun F)) := by
    rw [concaveFn_iff_convexFn_neg, he]
    exact convexBifun_flipBifun hF
  exact h

/-- **Rockafellar, §36** (15525): the inverse operation is **involutory**, `(F_*)_* = F`.

Specialises `inverseBifun_inverseBifun`. -/
theorem inverseBifun_involutive (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun F) = F :=
  inverseBifun_inverseBifun F

/-- **Rockafellar, §36** (15531): the inverse operation **commutes with the adjoint**,

`(F_*)^* = (F^*)_*`,

so that one may write `F_*^*` for either. The left side is the *concave* adjoint of the concave
bifunction `F_*`; the right is the inverse of `F*`. Rockafellar reads this as the generalisation of
`(A⁻¹)^* = (A^*)⁻¹` for a non-singular linear transformation.

Specialises `lowerAdjointBifun_eq_concaveAdjointBifun`, after `flip_pairing` collapses the two
flipped pairings the backbone states it against: `lowerAdjointBifun` *is* `(F^*)_*`, by `rfl`. -/
theorem concaveAdjointBifun_inverseBifun (F : Bifun (Rn m) (Rn n)) :
    concaveAdjointBifun (pairing m) (pairing n) (inverseBifun F)
      = inverseBifun (dualProgram F) := by
  have hlow : lowerAdjointBifun (pairing m) (pairing n) F = inverseBifun (dualProgram F) := rfl
  have h := lowerAdjointBifun_eq_concaveAdjointBifun (pairing m) (pairing n) F
  rw [hlow] at h
  simpa only [flip_pairing] using h.symm

/-- **Rockafellar's `⟨u*, F_* x⟩`** (15577), the concave bracket of the inverse bifunction, read as
a function of the pair `(u*, x)`.

By `saddleLagrangian_eq_inverseBifunBracket` this *is* the Lagrangian of `(P)`, and by Theorem 37.1
it is the **upper conjugate** `K̄*` of every member of the class `Ω (F)`. A reducible `abbrev` for
§33's `concaveBifunBracket` at `inverseBifun F`, so every §33 theorem about the concave bracket
applies to it verbatim. -/
noncomputable abbrev inverseBifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (inverseBifun F)

/-- The book's defining formula for `⟨u*, F_* x⟩` (15571): `inf_u {⟨u*, u⟩ − (F_* x)(u)}`, which is
`inf_u {⟨u*, u⟩ + (Fu)(x)}`. -/
theorem inverseBifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    inverseBifunBracket F p = ⨅ u : Rn m, ((pairing m p.1 u : ℝ) : EReal) - inverseBifun F p.2 u :=
  rfl

end Inverse

/-! ### Theorem 36.5

The structural pay-off of Part VII. The Lagrangians of closed convex programs are *exactly* the
upper closed concave-convex functions, so a "regularized minimax problem" and a "dual pair of
convex programs" are the same object. Combined with Corollary 34.2.2 — each equivalence class of
closed proper concave-convex functions contains a **unique** upper closed member — this fixes the
canonical representative of a class, and it is why §37 can present the whole existence theory of
saddle-values as corollaries of §29 and §30. -/

section Thm365

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {L : Rn m × Rn n → EReal}

/-- **Rockafellar, §36** (15565–15581): the Lagrangian of the convex program `(P)` associated with
`F`,

`L (u*, x) = inf_u {⟨u*, u⟩ + (Fu)(x)}`,

**is** the bracket `⟨u*, F_* x⟩` of the inverse bifunction.

The book obtains it by substituting `(F_* x)(u) = −(Fu)(x)` into the definition. The only step that
is not `rfl` here is the symmetry of the Euclidean pairing: `lagrangian` writes the perturbation
variable first, `concaveBracket` the price variable. -/
theorem saddleLagrangian_eq_inverseBifunBracket (F : Bifun (Rn m) (Rn n)) :
    saddleLagrangian (pairing m) F = inverseBifunBracket F := by
  funext p
  rw [saddleLagrangian_apply, lagrangian_apply, inverseBifunBracket_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, pairing_comm, sub_eq_add_neg, neg_neg]

/-- **Rockafellar, §36**, the sentence before Theorem 36.5 (15583): the Lagrangian of a convex
program is a **concave-convex** function on `ℝᵐ × ℝⁿ` — concave in the price variable `u*`, convex
in the primal variable `x`, which is the orientation this Part runs on.

Specialises `concaveConvexFn_saddleLagrangian`; the book gets it from Theorem 33.1 applied to
`⟨u*, F_* x⟩`. -/
theorem saddleLagrangian_concaveConvex (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian (pairing m) F) :=
  concaveConvexFn_saddleLagrangian (pairing m) hF

/-- **Rockafellar, Theorem 36.5** (15585). *In order that `L` be the Lagrangian of a convex program
`(P)` associated with a closed convex bifunction `F` from `ℝᵐ` to `ℝⁿ`, it is necessary and
sufficient that `L` be an upper closed concave-convex function on `ℝᵐ × ℝⁿ`.*

This is the structural pay-off of Part VII: the regularized minimax problems of §36 and the closed
proper convex programs of §§29–30 are the **same objects**, read through the Lagrangian. Combined
with Corollary 34.2.2 — a unique upper closed member per equivalence class — it names the canonical
representative of a class, and it is why §37 can derive the whole existence theory of saddle-values
from Theorems 29.x and 30.x rather than proving it again.

Necessity is `upperClosedFn_saddleLagrangian` together with `concaveConvexFn_saddleLagrangian`,
sufficiency the existence half of `exists_unique_closedBifun_saddleLagrangian_eq`. Rockafellar's
own proof is one line — "immediate from Theorem 33.3" — read through `L (u*, x) = ⟨u*, F_* x⟩`; the
backbone runs the same argument after `saddleSwap`, so that the *convex* Theorem 33.3 applies
verbatim instead of a concave mirror of it. -/
theorem theorem_36_5 (L : Rn m × Rn n → EReal) :
    (∃ F : Bifun (Rn m) (Rn n),
        ConvexBifun F ∧ ClosedBifun F ∧ saddleLagrangian (pairing m) F = L)
      ↔ ConcaveConvexFn L ∧ UpperClosedFn L := by
  constructor
  · rintro ⟨F, hF, hcl, rfl⟩
    exact ⟨concaveConvexFn_saddleLagrangian (pairing m) hF,
      upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl⟩
  · rintro ⟨hL, huc⟩
    obtain ⟨G, hG, -⟩ :=
      exists_unique_closedBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc
    exact ⟨G, hG⟩

/-- **Rockafellar, Theorem 36.5** (15585), necessity in isolation: the Lagrangian of a **closed
convex** bifunction is an upper closed concave-convex function.

Specialises `upperClosedFn_saddleLagrangian`, which is Theorem 33.3 read after `saddleSwap`. -/
theorem theorem_36_5_upperClosed (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    UpperClosedFn (saddleLagrangian (pairing m) F) :=
  upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl

/-- **Rockafellar, §36** (15601), the sentence after Theorem 36.5: an upper closed concave-convex
`L` is the Lagrangian of **one and only one** closed convex bifunction — "the unique *closed*
convex program `(P)` having `L` as its Lagrangian".

Specialises `exists_unique_closedBifun_saddleLagrangian_eq`. The book determines `F` explicitly,
by `F_* x = ` the concave conjugate of `L (·, x)`, i.e.
`(Fu)(x) = sup_{u*} {L (u*, x) − ⟨u*, u⟩}`; the backbone's `∃!` does not name its witness, which is
the one piece of friction in this section (see the report). -/
theorem theorem_36_5_unique (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun (Rn m) (Rn n),
      ConvexBifun G ∧ ClosedBifun G ∧ saddleLagrangian (pairing m) G = L :=
  exists_unique_closedBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc

end Thm365

/-! ### The Kuhn–Tucker condition, and Theorem 36.6

Lines 15665–15687. Because the Lagrangian is concave-convex, its saddle-points are exactly the
points where the concave slice is maximised and the convex slice minimised, i.e. where the saddle
subdifferential `∂L = ∂₁L × ∂₂L` of §35 contains the origin. Rockafellar calls
`(0, 0) ∈ ∂L (ū*, x̄)` the **Kuhn–Tucker condition** for `(P)`. -/

section Thm366

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- **Rockafellar, §36** (15665–15679): `(0, 0) ∈ ∂K (u, v)` if and only if `(u, v)` is a
saddle-point of `K` — the concave slice `K (·, v)` attains its maximum at `u` (that is
`0 ∈ ∂₁K`) and the convex slice `K (u, ·)` attains its minimum at `v` (that is `0 ∈ ∂₂K`).

**No hypothesis of any kind is needed.** It is Theorem 37.4 at the zero tilt
(`mem_saddleSubgradient_iff_isSaddlePoint` composed with `saddleTilt_zero`), which the backbone
does not package; see the report. -/
theorem zero_mem_saddleSubgradient_iff_isSaddlePoint (K : Rn m × Rn n → EReal)
    (p : Rn m × Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubgradient (pairing m) (pairing n) K p ↔ IsSaddlePoint K p := by
  rw [mem_saddleSubgradient_iff_isSaddlePoint, saddleTilt_zero]

/-- **Rockafellar, §36** (15679), the **Kuhn–Tucker condition for `(P)`**: for a closed proper
convex bifunction `F`, `(0, 0) ∈ ∂L (ū*, x̄)` holds exactly when `ū*` is a Kuhn–Tucker vector for
`(P)` and `x̄` is an optimal solution to `(P)`.

`zero_mem_saddleSubgradient_iff_isSaddlePoint` turns the left side into a saddle-point of `L`, and
Theorem 29.3 (`theorem_29_3_isSaddlePoint`) reads that off. -/
theorem kuhnTucker_condition_iff (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubgradient (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [zero_mem_saddleSubgradient_iff_isSaddlePoint]
  exact theorem_29_3_isSaddlePoint hF hcl hpr

/-- **Rockafellar, Theorem 36.6** (15681), the **strongly consistent** case. Let `(P)` be the
convex program associated with a closed proper convex bifunction `F` from `ℝᵐ` to `ℝⁿ`, and assume
`(P)` is strongly consistent. In order that `x̄ ∈ ℝⁿ` be an optimal solution to `(P)`, it is
necessary and sufficient that there exist `ū* ∈ ℝᵐ` with `(0, 0) ∈ ∂L (ū*, x̄)`, where `L` is the
Lagrangian of `(P)`.

**The book prints no proof, and §36 ends immediately after the statement.** Rockafellar introduces
it as a restatement of the general Kuhn–Tucker Theorem, Corollary 29.3.1, and that is how it is
closed here: `corollary_29_3_1_stronglyConsistent` composed with
`zero_mem_saddleSubgradient_iff_isSaddlePoint`. -/
theorem theorem_36_6_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubgradient (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_stronglyConsistent hF hcl hpr hs]
  exact exists_congr fun v =>
    (zero_mem_saddleSubgradient_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Rockafellar, Theorem 36.6** (15681), the **strictly consistent** case. A strictly consistent
program is strongly consistent, so this is the previous theorem verbatim. -/
theorem theorem_36_6_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubgradient (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) :=
  theorem_36_6_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Rockafellar, Theorem 36.6** (15681), the **polyhedral** case: for a polyhedral closed proper
convex program no more than plain consistency is needed, Theorem 29.2 supplying a Kuhn–Tucker
vector with no interiority hypothesis. -/
theorem theorem_36_6_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubgradient (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_polyhedral hF hcl hpr hc]
  exact exists_congr fun v =>
    (zero_mem_saddleSubgradient_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Rockafellar, Theorem 36.6** (15687), last sentence: the vectors `ū*` satisfying the
Kuhn–Tucker condition for a given optimal `x̄` are **precisely the Kuhn–Tucker vectors** for `(P)`.

Neither of the three constraint qualifications is needed for this clause — it is
`kuhnTucker_condition_iff` with the optimality of `x̄` supplied. -/
theorem theorem_36_6_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hx : IsOptimalSolution F x) (v : Rn m) :
    (0 : Rn m × Rn n) ∈ saddleSubgradient (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F := by
  rw [kuhnTucker_condition_iff hF hcl hpr]
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

end Thm366

end Rockafellar
