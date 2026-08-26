/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Common.Euclidean
import Tdaf.Surface.Rockafellar.Part7.Section33

/-!
# Rockafellar, §34: Closures and Equivalence Classes

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §34, pp. 359–369: the **lower** and
**upper closures** `cl₂ cl₁ K` and `cl₁ cl₂ K`, the effective domain `dom K`, **equivalence** of
saddle-functions, **closed** saddle-functions, the class `Ω (F)`, the **kernel**, and **simple**
saddle-functions.

All ten numbered results are here: Theorems 34.1–34.5 (34.3 in its six clauses (a)–(f)) and
Corollaries 34.2.1, 34.2.2, 34.2.3, 34.2.4, 34.5.1.

## Theorem 34.2 comes first, and that is the design of the section

The natural primitive of Part VII is **not** a saddle-function. It is the pair
`(K̲, K̄) = (⟨Fu, x*⟩, ⟨u, F*x*⟩)` of a closed convex bifunction `F` — equivalently `F` itself.
Theorem 34.2 is what licenses that reading: the order interval `Ω (F) = {K | K̲ ≤ K ≤ K̄}` is
*exactly* one equivalence class of closed concave-convex functions, every equivalence class of
closed concave-convex functions arises this way, and the bifunction is unique. So `Ω` is stated
before anything else here, and Theorem 34.1 — which chronologically comes first in the book — is
stated after it, as the fact that the two closure operations land in such a pair.

Everything downstream (§§35–37) should therefore quantify over a closed convex bifunction, or over
a class, and never over a bare saddle-function.

## Orientation

Inherited verbatim from `Part7/Section33.lean`, whose docstring states it in full:

| book | this file | closes | in which argument |
|---|---|---|---|
| `cl₁ K = cl_u K` | `cl₁` (`partialCl₁`) | **concavely** | the **first**, the concave one |
| `cl₂ K = cl_v K` | `cl₂` (`partialCl₂`) | **convexly** | the **second**, the convex one |

`lowerCl K = cl₂ (cl₁ K)`, `upperCl K = cl₁ (cl₂ K)`; `LowerClosedFn` and `UpperClosedFn` are
their fixed points. For a *convex-concave* `K` the book exchanges the two words, and the
translation is **plain negation** — `convexConcave_lowerClosed_iff` in §33 — never `saddleSwap`,
which preserves the concave-convex class rather than flipping it.

The `+∞`/`−∞` pattern of Corollary 34.2.4 (14826) is the orientation-sensitive one: `+∞` where
`u ∈ C` and `v ∉ D`, `−∞` where `u ∉ C` and `v ∈ D`. It is the *opposite* of the pattern a
convex-concave convention would give, and it is read off the backbone
(`mem_saddleClass_simpleExt_iff`), not re-derived.

## Contents

| label | declaration |
|---|---|
| §34 definitions, 14601–14650 | `dom₁_eq`, `dom₂_eq`, `domSaddle_eq`, `properSaddleFn_iff`,
  `domSaddle_lowerSimpleExt`, `domSaddle_upperSimpleExt`, `saddleEquiv_iff`, `closedSaddleFn_iff` |
| Theorem 34.2 | `Ω`, `mem_Ω`, `mem_bifunSaddleClass_of_mem_Ω`, `theorem_34_2_lower_mem`,
  `theorem_34_2_upper_mem`, `theorem_34_2_closed`, `theorem_34_2_equiv`, `theorem_34_2_maximal`,
  `theorem_34_2_converse`, `theorem_34_2_mem_self`, `theorem_34_2_cl₁`, `theorem_34_2_cl₂`,
  `theorem_34_2_dom₁`, `theorem_34_2_dom₂`, `theorem_34_2_dom`,
  `theorem_34_2_bifunOfSaddleFn`, `theorem_34_2_bifun_apply`, `theorem_34_2_adjoint`,
  `theorem_34_2_eq_of_mem_relint_dom₁`, `theorem_34_2_eq_of_mem_relint_dom₂` |
| Theorem 34.1 | `theorem_34_1_lower`, `theorem_34_1_upper`, `theorem_34_1_lower_eq`,
  `theorem_34_1_upper_eq` |
| Corollary 34.2.1 | `corollary_34_2_1_dom`, `corollary_34_2_1_dom_of_not_closed`,
  `corollary_34_2_1_eq_of_mem_relint_dom₁`, `corollary_34_2_1_eq_of_mem_relint_dom₂` |
| Corollary 34.2.2 | `corollary_34_2_2_of_lowerClosed`, `corollary_34_2_2_of_upperClosed`,
  `corollary_34_2_2_of_fullyClosed`, `corollary_34_2_2_lower_exists`,
  `corollary_34_2_2_upper_exists`, `corollary_34_2_2_lower_unique`,
  `corollary_34_2_2_upper_unique`, `corollary_34_2_2_least`, `corollary_34_2_2_greatest` |
| Corollary 34.2.3 | `corollary_34_2_3`, `corollary_34_2_3_not_equiv` |
| Corollary 34.2.4 | `corollary_34_2_4_mem_iff`, `corollary_34_2_4_closed`,
  `corollary_34_2_4_proper`, `corollary_34_2_4_equiv`, `corollary_34_2_4_least`,
  `corollary_34_2_4_greatest` |
| Theorem 34.3 | `theorem_34_3_a`, `theorem_34_3_b`, `theorem_34_3_c`, `theorem_34_3_d`,
  `theorem_34_3_e`, `theorem_34_3_f`, `theorem_34_3` |
| §34 definitions, 14905–14915 | `relint_domSaddle_eq_prod`, `kernel_eq_restrict`,
  `kernel_eq_iff'`, `simpleSaddleFn_iff`, `simpleSaddleFn_of_closed`,
  `simpleSaddleFn_lowerSimpleExt'`, `simpleSaddleFn_bifunBracket` |
| Theorem 34.4 | `theorem_34_4` |
| Theorem 34.5 | `theorem_34_5_le`, `theorem_34_5_equiv`, `theorem_34_5_closed`,
  `theorem_34_5_proper`, `theorem_34_5_kernel`, `theorem_34_5_mem_of_kernel_eq`, `theorem_34_5` |
| Corollary 34.5.1 | `corollary_34_5_1` |

## What §34 exports for §§35–37

Everything is the backbone's, used verbatim, except the two entries marked `Rockafellar.`.

| book name | Lean name | home |
|---|---|---|
| `dom₁ K`, `dom₂ K` | `dom₁`, `dom₂` | `Saddle/Defs.lean` |
| `dom K = dom₁ K × dom₂ K` | `domSaddle` | `Saddle/Kernel.lean` |
| proper saddle-function | `ProperSaddleFn` | `Saddle/Kernel.lean` |
| lower closure `cl₂ cl₁ K`, upper closure `cl₁ cl₂ K` | `lowerCl`, `upperCl` |
  `Saddle/Closure.lean` |
| `K` equivalent to `L` | `SaddleEquiv` | `Saddle/Equiv.lean` |
| closed saddle-function | `ClosedSaddleFn` | `Saddle/Equiv.lean` |
| the order interval between a closure pair | `saddleClass` | `Saddle/Equiv.lean` |
| **`Ω (F)`** | **`Rockafellar.Ω`** | this module |
| the interval without the concave-convexity | `bifunSaddleClass` | `Saddle/Minimax.lean` |
| kernel of `K` | `kernel`, `kernelSet` | `Saddle/Kernel.lean` |
| simple saddle-function | `SimpleSaddleFn` | `Saddle/Kernel.lean` |
| clauses (a)–(f) of Theorem 34.3, bundled | `SaddleStructure`, `ConvexSliceStructure` |
  `Saddle/Kernel.lean` |

`Ω F` is `{K | ConcaveConvexFn K} ∩ saddleClass (bifunBracket F) (adjointBracket F)`; the
concave-convexity is part of Rockafellar's definition (14659, "the collection of all
concave-convex functions `K` such that `K̲ ≤ K ≤ K̄`") and is *not* part of the backbone's
`bifunSaddleClass`. `mem_bifunSaddleClass_of_mem_Ω` is the bridge, and it is what §37's
`dom₁_eq_domBifun_of_mem_bifunSaddleClass`, `partialCl₁_lowerConjSaddle` and friends consume.

## Where the book is defective

**Corollaries 34.2.1 and 34.2.3 are printed with no proof at all** (14761, 14819). Both are
derived here from Theorem 34.2. Recorded again in their docstrings.

**Theorem 34.2's proof begins 34 lines after its statement** (14657 vs 14691); the intervening
text is the `Ω (F*) = Ω (F)` discussion, which is not part of the proof.

**Theorem 34.2's `dom K = dom F × dom F*` is a product identity, and only that.** The book's proof
argues the two factors separately — "`u ∉ dom₁ K` if and only if `Fu` is the constant `+∞`" — and
that factorwise claim is *false* when `F` is improper. If the graph function of `F` is identically
`+∞` then `K̲ = K̄ ≡ −∞`, so `dom₁ K = ∅ = dom F` but `dom₂ K = ℝⁿ` while `dom F* = ∅`. The
product identity survives (both sides are empty), the factor identity does not.
`theorem_34_2_dom₁` and `theorem_34_2_dom₂` therefore carry the nonemptiness hypothesis the book
suppresses, and `theorem_34_2_dom` is stated from them.

**Corollary 34.2.4's hypothesis is weakened.** The book asks for `K` "finite continuous" on
`C × D`, i.e. jointly continuous; the argument uses only separate continuity of each slice on its
own set (`hcontD`, `hcontC`), and that is what is asked for here. This is the same weakening §33
recorded for Corollary 33.3.3. The proof route also differs from the book's: the backbone closes
Corollary 34.2.4 directly from the closedness of the slices of the two simple extensions, not
through Corollary 33.3.3.

**Corollary 34.2.1's `dom L = dom K` clause needs no closedness**, only properness of both. The
book states the whole corollary under "let `K` be a closed saddle-function";
`corollary_34_2_1_dom_of_not_closed` records that the first clause holds without it.

**Theorem 34.1 needs no hypothesis whatsoever.** The book proves it through Theorems 33.1, 33.2,
33.3 and 30.1, for a saddle-function; the backbone reproves it (`lowerCl_idem`, `upperCl_idem`)
from monotonicity and idempotence of the two closure operations alone, so the surface statements
quantify over *every* `K : ℝᵐ × ℝⁿ → EReal`. That is strictly stronger than the book's.

## What is not here

* **The three examples of the discrepancy `cl₂ cl₁ K ≠ cl₁ cl₂ K`** (`uᵛ` on the unit square,
  `u/v` on the positive quadrant, and the "freakish" `uv`-sign function), 14535–14595. *Deferred
  by scope*: each is a page of explicit `EReal`-valued computation on `ℝ × ℝ` with no numbered
  content, and the `uᵛ` one turns on the impossibility of defining `0⁰`, which is a real-analysis
  argument about `u ↦ uᵛ` rather than a convex-analysis one.
* **"The lower and upper simple extensions of a finite saddle-function on a convex `C × D ≠ ∅`
  are equivalent"** (14640), asserted with no proof and with no closedness or continuity
  hypothesis. *Omitted*: the backbone proves the equivalence only under the hypotheses of
  Corollary 34.2.4 (`saddleEquiv_of_mem_saddleClass_simpleExt`). The declaration wanted is
  `saddleEquiv_lowerSimpleExt_upperSimpleExt` in `Saddle/Kernel.lean`, with no hypotheses beyond
  `C`, `D` nonempty convex.
* **`Ω (F*) = Ω (F)`** (14790). *Omitted with a reason*: the book's `Ω (G)` for a **concave**
  bifunction `G` is defined as an equivalence class rather than as an order interval, so the
  identity is a statement about two differently-shaped objects. Its content — that the class is
  determined by either bracket — is `theorem_34_2_maximal` together with `theorem_34_2_upper_mem`.
* **"Every saddle-function whose effective domain has nonempty interior is simple"** (14915),
  asserted with no proof. *Omitted*: nothing in the backbone approaches it. It would need a
  lemma of the shape "for `u ∈ int (dom₁ K)` and `x ∉ cl (dom₂ K)`, `K (u, x) = ⊤`", proved by
  running a line segment from an interior point of `dom₂ K` through `x` and using finiteness of
  `K (u, ·)` on `dom₂ K` — an argument of §7/§10 type that has no counterpart in
  `Saddle/Kernel.lean`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §34, pp. 359–369.
-/

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

/-! ### The vocabulary of §34 (14601–14650)

`dom₁`, `dom₂`, `dom K`, proper, equivalent, closed. Every one of these is the backbone's under
the same reading; the lemmas here are the alignment with the book's displayed formulas. -/

section Vocabulary

variable {m n : ℕ}

/-- **Rockafellar's `dom₁ K = {u | K (u, v) > −∞, ∀ v}`** (14603). -/
theorem dom₁_eq (K : Rn m × Rn n → EReal) : dom₁ K = {u | ∀ v, ⊥ < K (u, v)} := rfl

/-- **Rockafellar's `dom₂ K = {v | K (u, v) < +∞, ∀ u}`** (14605). -/
theorem dom₂_eq (K : Rn m × Rn n → EReal) : dom₂ K = {v | ∀ u, K (u, v) < ⊤} := rfl

/-- **Rockafellar's `dom K = dom₁ K × dom₂ K`** (14615), the effective domain of a
saddle-function. -/
theorem domSaddle_eq (K : Rn m × Rn n → EReal) : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl

/-- **`K` is proper when `dom K ≠ ∅`** (14621). Specialises
`properSaddleFn_iff_domSaddle_nonempty`. -/
theorem properSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ProperSaddleFn K ↔ (domSaddle K).Nonempty :=
  properSaddleFn_iff_domSaddle_nonempty

/-- **On `dom K` a saddle-function is finite** (14617). -/
theorem lt_top_of_mem_domSaddle' {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}
    (hp : p ∈ domSaddle K) : ⊥ < K p ∧ K p < ⊤ :=
  ⟨bot_lt_of_mem_domSaddle hp, lt_top_of_mem_domSaddle hp⟩

variable {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **The lower simple extension of a finite saddle-function on a nonempty `C × D` has
`dom K = C × D`, and is proper** (14634). -/
theorem domSaddle_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (lowerSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (lowerSimpleExt C D K)
      = dom₁ (lowerSimpleExt C D K) ×ˢ dom₂ (lowerSimpleExt C D K) := rfl
  rw [h, dom₁_lowerSimpleExt hDne, dom₂_lowerSimpleExt hCne]

/-- **The upper simple extension likewise** (14638). -/
theorem domSaddle_upperSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (upperSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (upperSimpleExt C D K)
      = dom₁ (upperSimpleExt C D K) ×ˢ dom₂ (upperSimpleExt C D K) := rfl
  rw [h, dom₁_upperSimpleExt hDne, dom₂_upperSimpleExt hCne]

/-- **Rockafellar's *equivalent*** (14640): `cl₁ K = cl₁ L` and `cl₂ K = cl₂ L`. -/
theorem saddleEquiv_iff (K L : Rn m × Rn n → EReal) :
    SaddleEquiv K L ↔ cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L := Iff.rfl

/-- **Rockafellar's *closed*** (14646): `cl₁ cl₂ K = cl₁ K` and `cl₂ cl₁ K = cl₂ K`. The book
defines closedness as "`cl₁ K` and `cl₂ K` are both equivalent to `K`" and then observes that
idempotence of the two closures reduces it to these two equations (14648). -/
theorem closedSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ClosedSaddleFn K ↔ cl₁ (cl₂ K) = cl₁ K ∧ cl₂ (cl₁ K) = cl₂ K := Iff.rfl

end Vocabulary

/-! ### Theorem 34.2

The class `Ω (F)`, stated first because it is the primitive the rest of Part VII quantifies
over. -/

section Thm342

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar's `Ω (F)`** (14659): for a closed convex bifunction `F` from `ℝᵐ` to `ℝⁿ`, the
collection of all **concave-convex** functions `K` on `ℝᵐ × ℝⁿ` with
`⟨Fu, x*⟩ ≤ K (u, x*) ≤ ⟨u, F*x*⟩`.

The backbone's `bifunSaddleClass` is the same order interval *without* the concave-convexity, and
`mem_bifunSaddleClass_of_mem_Ω` is the bridge to it. -/
noncomputable def Ω (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n → EReal) :=
  {K | ConcaveConvexFn K} ∩ saddleClass (bifunBracket F) (adjointBracket F)

theorem mem_Ω : K ∈ Ω F ↔ ConcaveConvexFn K ∧ bifunBracket F ≤ K ∧ K ≤ adjointBracket F :=
  Iff.rfl

/-- The bridge from the book's `Ω (F)` to the backbone's order interval, which is what every §37
statement about a class is phrased against. -/
theorem mem_bifunSaddleClass_of_mem_Ω (hK : K ∈ Ω F) :
    K ∈ bifunSaddleClass (pairing m) (pairing n) F := hK.2

/-- **Rockafellar, Theorem 34.2**: `K̲ (u, x*) = ⟨Fu, x*⟩` belongs to `Ω (F)`. -/
theorem theorem_34_2_lower_mem (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    bifunBracket F ∈ Ω F :=
  ⟨theorem_33_1_concaveConvex hF,
    mem_saddleClass_left (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Rockafellar, Theorem 34.2**: `K̄ (u, x*) = ⟨u, F*x*⟩` belongs to `Ω (F)`. -/
theorem theorem_34_2_upper_mem (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    adjointBracket F ∈ Ω F :=
  ⟨adjointBracket_concaveConvex F,
    mem_saddleClass_right (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Rockafellar, Theorem 34.2**, second equation: `cl₂ K = K̲` for every `K ∈ Ω (F)`.
Specialises `partialCl₂_eq_bracket_of_mem_saddleClass`. -/
theorem theorem_34_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₂ K = bifunBracket F :=
  partialCl₂_eq_bracket_of_mem_saddleClass (pairing m) (pairing n) hF hcl hK.2

/-- **Rockafellar, Theorem 34.2**, first equation: `cl₁ K = K̄` for every `K ∈ Ω (F)`.
Specialises `partialCl₁_eq_concaveBracket_of_mem_saddleClass`; no closedness of `F` is needed. -/
theorem theorem_34_2_cl₁ (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    cl₁ K = adjointBracket F :=
  partialCl₁_eq_concaveBracket_of_mem_saddleClass (pairing m) (pairing n) hF hK.2

/-- **Rockafellar, Theorem 34.2**: every member of `Ω (F)` is a closed saddle-function.
Specialises `closedSaddleFn_of_mem_saddleClass_bracket`. -/
theorem theorem_34_2_closed (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn K :=
  closedSaddleFn_of_mem_saddleClass_bracket (pairing m) (pairing n) hF hcl hK.2

/-- **Rockafellar, Theorem 34.2**: any two members of `Ω (F)` are equivalent. -/
theorem theorem_34_2_equiv (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : SaddleEquiv K L :=
  saddleEquiv_of_mem_saddleClass (corollary_33_3_1_necessity_first hF)
    (corollary_33_3_1_necessity_second hF hcl) hK.2 hL.2

/-- **Rockafellar, Theorem 34.2**: `Ω (F)` is a *whole* equivalence class — a concave-convex
function equivalent to a member is itself a member. Together with `theorem_34_2_equiv` this is
"`Ω (F)` is an equivalence class". -/
theorem theorem_34_2_maximal (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : L ∈ Ω F := by
  refine ⟨hL, ?_⟩
  have e2 : partialCl₂ L = bifunBracket F := by
    have hK2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
    rw [← h.2]; exact hK2
  have e1 : partialCl₁ L = adjointBracket F := by
    have hK1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
    rw [← h.1]; exact hK1
  have hmem := mem_saddleClass_self L
  rw [e1, e2] at hmem
  exact hmem

/-- **Rockafellar, Theorem 34.2**, converse: a closed concave-convex function determines one and
only one closed convex bifunction whose two brackets are `cl₂ K` and `cl₁ K`. Specialises
`exists_unique_bifun_of_closedSaddleFn`. -/
theorem theorem_34_2_converse (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧
      bifunBracket F = cl₂ K ∧ adjointBracket F = cl₁ K :=
  exists_unique_bifun_of_closedSaddleFn (pairing m) (pairing n) hK hcl

/-- **Rockafellar, Theorem 34.2**, converse: and `K` does lie in the class of that bifunction, so
every equivalence class of closed concave-convex functions is an `Ω (F)`. -/
theorem theorem_34_2_mem_self (hK : ConcaveConvexFn K) (hlow : bifunBracket F = cl₂ K)
    (hup : adjointBracket F = cl₁ K) : K ∈ Ω F := by
  refine ⟨hK, ?_⟩
  have e2 : partialCl₂ K = bifunBracket F := hlow.symm
  have e1 : partialCl₁ K = adjointBracket F := hup.symm
  have hmem := mem_saddleClass_self K
  rw [e1, e2] at hmem
  exact hmem

/-- **Rockafellar, Theorem 34.2**, `dom` clause, first factor: `dom₁ K = dom F` for `K ∈ Ω (F)`.
Specialises `dom₁_eq_domBifun_of_mem_bifunSaddleClass`.

The nonemptiness hypothesis is not in the book and cannot be dropped; see the module docstring. -/
theorem theorem_34_2_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hne : (dom₂ K).Nonempty) : dom₁ K = domBifun F :=
  dom₁_eq_domBifun_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl hK.2 hK.1 hne

/-- **The second effective domain of `⟨u, Gx*⟩` is `dom G`**, the mirror of `dom₁_bracket`, which
the backbone does not carry. §33 needed the same lemma and proves it `private` as well; see the
section report's backbone-gap list. -/
private theorem dom₂_adjointBracket (F : Bifun (Rn m) (Rn n)) :
    dom₂ (adjointBracket F) = domConcaveBifun (dualProgram F) := by
  ext y
  constructor
  · intro hy
    have h : y ∈ dom fun w => concaveBracket (pairing m) (dualProgram F) (0 : Rn m) w := hy 0
    rwa [dom_concaveBracket] at h
  · intro hy u
    have h : y ∈ dom fun w => concaveBracket (pairing m) (dualProgram F) u w := by
      rw [dom_concaveBracket]; exact hy
    exact h

/-- **Rockafellar, Theorem 34.2**, `dom` clause, second factor: `dom₂ K = dom F*` for
`K ∈ Ω (F)`. -/
theorem theorem_34_2_dom₂ (hF : ConvexBifun F) (hK : K ∈ Ω F) (hne : (dom₁ K).Nonempty) :
    dom₂ K = domConcaveBifun (dualProgram F) := by
  have e1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  rw [← dom₂_partialCl₁ hK.1 hne, e1, dom₂_adjointBracket]

/-- **Rockafellar, Theorem 34.2**: `dom K = dom F × dom F*`. -/
theorem theorem_34_2_dom (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) :
    domSaddle K = domBifun F ×ˢ domConcaveBifun (dualProgram F) := by
  have h : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl
  rw [h, theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty,
    theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]

/-- **Rockafellar, Theorem 34.2**: `F` is recovered from any `K ∈ Ω (F)` as `Fu = K (u, ·)*`.
Two image-closed convex bifunctions with the same bracket are equal (`eq_of_bracket_eq`), and the
bracket of `bifunOfSaddleFn K` is `cl₂ K = K̲`. -/
theorem theorem_34_2_bifunOfSaddleFn (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    bifunOfSaddleFn K = F := by
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  refine eq_of_bracket_eq (Bx := pairing n) (theorem_33_1_convexBifun hK.1) hF
    (theorem_33_1_imageClosed K) (imageClosedBifun_of_closedBifun hcl) ?_
  funext u x
  calc bracket (pairing n) (bifunOfSaddleFn K) u x
      = partialCl₂ K (u, x) := bracket_bifunOfSaddle hK.1 (u, x)
    _ = bracket (pairing n) F u x := congrFun h2 (u, x)

/-- **Rockafellar, Theorem 34.2**, third equation:
`(Fu)(x) = sup_{x*} {⟨x, x*⟩ − K (u, x*)}`. -/
theorem theorem_34_2_bifun_apply (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (u : Rn m) (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := by
  rw [← theorem_34_2_bifunOfSaddleFn hF hcl hK]
  exact bifunOfSaddleFn_apply K u x

/-- **The concave conjugate sees only the concave closure**, the mirror of `conj_clFn`
(Theorem 12.2, first half). The backbone does not carry it; see the section report. -/
private theorem concaveConj_clConcave (g : Rn m → EReal) :
    concaveConj (pairing m) (clConcave g) = concaveConj (pairing m) g := by
  funext y
  rw [concaveConj_eq_neg_conj_neg, concaveConj_eq_neg_conj_neg]
  have h : (fun x => -(clConcave g x)) = clFn fun z => -(g z) := funext (neg_clConcave g)
  rw [h, conj_clFn]

/-- **Rockafellar, Theorem 34.2**, fourth equation:
`(F*x*)(u*) = inf_u {⟨u, u*⟩ − K (u, x*)}`.

The book writes this off the third one by symmetry. It is not symmetric here: `F* x*` is the
*concave* conjugate of `u ↦ ⟨Fu, x*⟩ = (cl₂ K) (u, x*)`, and replacing `cl₂ K` by `K` under a
concave conjugate is exactly what closedness of `K` buys. -/
theorem theorem_34_2_adjoint (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (x : Rn n) (v : Rn m) :
    dualProgram F x v = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have hfun : (fun u => bracket (pairing n) F u x) = fun u => partialCl₂ K (u, x) := by
    funext u
    exact (congrFun h2 (u, x)).symm
  have hclc : clConcave (fun u => partialCl₂ K (u, x)) = clConcave fun u => K (u, x) := by
    rw [← partialCl₁_slice (partialCl₂ K) x, ← partialCl₁_slice K x, hcls.1]
  have hgoal : adjointBifun (pairing m) (pairing n) F x v
      = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
    rw [adjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) F x v, hfun,
      ← concaveConj_clConcave (fun u => partialCl₂ K (u, x)), hclc, concaveConj_clConcave,
      concaveConj_apply]
  exact hgoal

/-- **Rockafellar, Theorem 34.2**, last clause: `K (u, x*) = ⟨Fu, x*⟩ = ⟨u, F*x*⟩` when
`u ∈ ri (dom F)`. The hypothesis is the book's, on `dom F`; `theorem_34_2_dom₁` turns it into the
`ri (dom₁ K)` the backbone asks for. -/
theorem theorem_34_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (domBifun F)) (x : Rn n) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hu' : u ∈ ri (dom₁ K) := by
    rw [theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty]; exact hu
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x]
  exact congrFun h1 (u, x)

/-- **Rockafellar, Theorem 34.2**, last clause, second half: the same when
`x* ∈ ri (dom F*)`. -/
theorem theorem_34_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {x : Rn n}
    (hx : x ∈ ri (domConcaveBifun (dualProgram F))) (u : Rn m) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hx' : x ∈ ri (dom₂ K) := by
    rw [theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]; exact hx
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u]
  exact congrFun h1 (u, x)

end Thm342

/-! ### Theorem 34.1

Stated after Theorem 34.2 because it is that theorem's input: the two closure operations always
land on a closure pair, hence on an `Ω (F)`. -/

section Thm341

variable {m n : ℕ}

/-- **Rockafellar, Theorem 34.1**: the lower closure `cl₂ cl₁ K` of a saddle-function is lower
closed.

Specialises `lowerCl_idem`, the backbone's duality-free proof (monotonicity and idempotence of the
two closure operations). It needs **no hypothesis at all** — not concavity-convexity, not
properness — which is strictly stronger than the book's statement. -/
theorem theorem_34_1_lower (K : Rn m × Rn n → EReal) : LowerClosedFn (lowerCl K) :=
  lowerCl_idem K

/-- **Rockafellar, Theorem 34.1**: the upper closure `cl₁ cl₂ K` is upper closed. -/
theorem theorem_34_1_upper (K : Rn m × Rn n → EReal) : UpperClosedFn (upperCl K) :=
  upperCl_idem K

/-- **Rockafellar, Theorem 34.1**, first displayed equation (14503):
`cl₂ cl₁ cl₂ cl₁ K = cl₂ cl₁ K`. -/
theorem theorem_34_1_lower_eq (K : Rn m × Rn n → EReal) :
    cl₂ (cl₁ (cl₂ (cl₁ K))) = cl₂ (cl₁ K) := by
  have h : partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K))) = partialCl₂ (partialCl₁ K) :=
    lowerCl_idem K
  exact h

/-- **Rockafellar, Theorem 34.1**, second displayed equation (14505):
`cl₁ cl₂ cl₁ cl₂ K = cl₁ cl₂ K`. -/
theorem theorem_34_1_upper_eq (K : Rn m × Rn n → EReal) :
    cl₁ (cl₂ (cl₁ (cl₂ K))) = cl₁ (cl₂ K) := by
  have h : partialCl₁ (partialCl₂ (partialCl₁ (partialCl₂ K))) = partialCl₁ (partialCl₂ K) :=
    upperCl_idem K
  exact h

end Thm341

/-! ### Corollary 34.2.1

**Printed with no proof at all** (14761). -/

section Cor3421

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 34.2.1**, first clause: equivalent saddle-functions have the same
effective domain, `dom L = dom K`. Specialises `SaddleEquiv.domSaddle_eq`. -/
theorem corollary_34_2_1_dom (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    domSaddle L = domSaddle K :=
  (h.domSaddle_eq hK hpK hL hpL).symm

/-- **Rockafellar, Corollary 34.2.1**: the `dom L = dom K` clause **needs no closedness**, which
the book's hypothesis "`K` closed" suggests it does. `dom₁` is already `dom₁ (cl₂ ·)` and `dom₂`
already `dom₂ (cl₁ ·)`, so equivalence alone settles both factors. -/
theorem corollary_34_2_1_dom_of_not_closed (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    dom₁ L = dom₁ K ∧ dom₂ L = dom₂ K :=
  ⟨(h.dom₁_eq hK hpK hL hpL).symm, (h.dom₂_eq hK hpK hL hpL).symm⟩

/-- **Rockafellar, Corollary 34.2.1**, second clause: `L (u, v) = K (u, v)` whenever
`u ∈ ri (dom₁ K)`. Specialises `SaddleEquiv.eq_of_mem_relint_dom₁`. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₁ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {u : Rn m} (hu : u ∈ ri (dom₁ K))
    (v : Rn n) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₁ hclK hK hpK hclL hL hpL hu v).symm

/-- **Rockafellar, Corollary 34.2.1**, second clause: `L (u, v) = K (u, v)` whenever
`v ∈ ri (dom₂ K)`. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₂ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {v : Rn n} (hv : v ∈ ri (dom₂ K))
    (u : Rn m) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₂ hclK hK hpK hclL hL hpL hv u).symm

end Cor3421

/-! ### Corollary 34.2.2 -/

section Cor3422

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 34.2.2**: a lower closed saddle-function is closed. -/
theorem corollary_34_2_2_of_lowerClosed (h : LowerClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Rockafellar, Corollary 34.2.2**: an upper closed saddle-function is closed. -/
theorem corollary_34_2_2_of_upperClosed (h : UpperClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Rockafellar, Corollary 34.2.2**: a fully closed saddle-function is closed. -/
theorem corollary_34_2_2_of_fullyClosed (h : FullyClosedFn K) : ClosedSaddleFn K :=
  (fullyClosedFn_iff.1 h).1.closedSaddleFn

/-- **Rockafellar, Corollary 34.2.2**, existence: the class of a closed saddle-function contains a
lower closed member, namely `cl₂ K`. -/
theorem corollary_34_2_2_lower_exists (hcl : ClosedSaddleFn K) : LowerClosedFn (cl₂ K) :=
  hcl.lowerClosedFn_partialCl₂

/-- **Rockafellar, Corollary 34.2.2**, existence: and an upper closed member, `cl₁ K`. -/
theorem corollary_34_2_2_upper_exists (hcl : ClosedSaddleFn K) : UpperClosedFn (cl₁ K) :=
  hcl.upperClosedFn_partialCl₁

/-- **Rockafellar, Corollary 34.2.2**, uniqueness: a lower closed member of the class of `K` is
`cl₂ K`. -/
theorem corollary_34_2_2_lower_unique (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L = cl₂ K :=
  h.eq_partialCl₂_of_lowerClosedFn hL

/-- **Rockafellar, Corollary 34.2.2**, uniqueness: an upper closed member of the class of `K` is
`cl₁ K`. -/
theorem corollary_34_2_2_upper_unique (h : SaddleEquiv K L) (hL : UpperClosedFn L) : L = cl₁ K :=
  h.eq_partialCl₁_of_upperClosedFn hL

/-- **Rockafellar, Corollary 34.2.2**: the lower closed member is the **least** member of the
class. -/
theorem corollary_34_2_2_least (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L ≤ K := by
  have e : L = partialCl₂ K := h.eq_partialCl₂_of_lowerClosedFn hL
  rw [e]
  exact partialCl₂_le K

/-- **Rockafellar, Corollary 34.2.2**: the upper closed member is the **greatest** member. -/
theorem corollary_34_2_2_greatest (h : SaddleEquiv K L) (hL : UpperClosedFn L) : K ≤ L := by
  have e : L = partialCl₁ K := h.eq_partialCl₁_of_upperClosedFn hL
  rw [e]
  exact le_partialCl₁ K

end Cor3422

/-! ### Corollary 34.2.3

**Printed with no proof at all** (14819); the book's justification is the paragraph at 14799
about improper closed convex bifunctions. This is one of the results the alignment checklist
specifically warns about: it is *about* improper functions, so no properness hypothesis may be
added. -/

section Cor3423

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 34.2.3**: the only improper closed saddle-functions on `ℝᵐ × ℝⁿ` are
the two constants `−∞` and `+∞`. Specialises `ClosedSaddleFn.eq_const_of_not_properSaddleFn`. -/
theorem corollary_34_2_3 (hcl : ClosedSaddleFn K) (hp : ¬ ProperSaddleFn K) :
    K = (fun _ => (⊥ : EReal)) ∨ K = fun _ => (⊤ : EReal) :=
  hcl.eq_const_of_not_properSaddleFn hp

/-- **Rockafellar, Corollary 34.2.3**: and the two constants are **not equivalent**. -/
theorem corollary_34_2_3_not_equiv :
    ¬ SaddleEquiv (fun _ : Rn m × Rn n => (⊥ : EReal)) (fun _ => (⊤ : EReal)) :=
  not_saddleEquiv_const_bot_const_top

end Cor3423

/-! ### Corollary 34.2.4

The `+∞`/`−∞` pattern at 14826 is orientation-sensitive: `+∞` where `u ∈ C` and `v ∉ D`, `−∞`
where `u ∉ C` and `v ∈ D`. It is read off `mem_saddleClass_simpleExt_iff`.

**Two divergences from the book**, both recorded in the module docstring: the continuity
hypothesis is separate rather than joint, and the backbone proves this corollary directly rather
than through Corollary 33.3.3. Nothing here needs relative interiors. -/

section Cor3424

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
  {L : Rn m × Rn n → EReal}

/-- **Rockafellar, Corollary 34.2.4**: the class `Ω` of the corollary — the extensions of `K` with
`+∞` on `C × Dᶜ` and `−∞` on `Cᶜ × D` — is exactly the order interval between the lower and the
upper simple extension. The values on `Cᶜ × Dᶜ` are unconstrained, as in the book's `uᵛ` example.

Specialises `mem_saddleClass_simpleExt_iff`. Rockafellar's `Ω` additionally asks that its members
be concave-convex; every conclusion below holds without that. -/
theorem corollary_34_2_4_mem_iff :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      (∀ u ∈ C, ∀ v ∈ D, L (u, v) = (K (u, v) : EReal)) ∧
        (∀ u ∈ C, ∀ v ∉ D, L (u, v) = ⊤) ∧ ∀ u ∉ C, ∀ v ∈ D, L (u, v) = ⊥ :=
  mem_saddleClass_simpleExt_iff

/-- **Rockafellar, Corollary 34.2.4**: every member of `Ω` is a closed saddle-function. -/
theorem corollary_34_2_4_closed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC hL

/-- **Rockafellar, Corollary 34.2.4**: every member of `Ω` is proper. -/
theorem corollary_34_2_4_proper (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_simpleExt hCne hDne hL

/-- **Rockafellar, Corollary 34.2.4**: `Ω` is precisely one equivalence class. -/
theorem corollary_34_2_4_equiv (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C) :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      SaddleEquiv (lowerSimpleExt C D K) L :=
  mem_saddleClass_simpleExt_iff_saddleEquiv hCcl hDcl hCne hDne hcontD hcontC

/-- **Rockafellar, Corollary 34.2.4**, parenthetical clause: the lower simple extension is the
**least** member of `Ω`. -/
theorem corollary_34_2_4_least (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    lowerSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)

/-- **Rockafellar, Corollary 34.2.4**, parenthetical clause: the upper simple extension is the
**greatest** member of `Ω`. -/
theorem corollary_34_2_4_greatest (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    upperSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_right (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end Cor3424

/-! ### Theorem 34.3

Six clauses, one declaration each, in the necessity direction; the sufficiency direction needs all
six at once and is `theorem_34_3`, whose right-hand side is the backbone's `SaddleStructure` —
clauses (a)–(c) for `K` together with clauses (a)–(c) for `saddleSwap K`, which is what (d)–(f)
are. -/

section Thm343

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 34.3 (a).** For `u ∈ ri C`, where `C = dom₁ K`, the convex function
`K (u, ·)` is closed proper with effective domain `D = dom₂ K`. -/
theorem theorem_34_3_a (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ ClosedFn (fun v => K (u, v)) ∧
      Proper (fun v => K (u, v)) ∧ dom (fun v => K (u, v)) = dom₂ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.closedFn_slice u hu,
    hs.1.proper_slice u (intrinsicInterior_subset hu), hs.1.dom_slice u hu⟩

/-- **Rockafellar, Theorem 34.3 (b).** For `u ∈ C ∖ ri C`, the convex function `K (u, ·)` is
proper and its effective domain lies between `D` and `cl D`.

The lower inclusion `D ⊆ dom (K (u, ·))` is `dom₂_subset_dom_slice` and holds for every `u`
whatsoever; only the upper one uses the structure. -/
theorem theorem_34_3_b (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ dom₁ K \ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ Proper (fun v => K (u, v)) ∧
      dom₂ K ⊆ dom (fun v => K (u, v)) ∧
      dom (fun v => K (u, v)) ⊆ closure (dom₂ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.proper_slice u hu.1, dom₂_subset_dom_slice K u,
    hs.1.dom_slice_subset_closure u hu.1⟩

/-- **Rockafellar, Theorem 34.3 (c).** For `u ∉ C`, the convex function `K (u, ·)` is improper,
with the value `−∞` throughout `ri D` — throughout `D` itself if `u ∉ cl C`. -/
theorem theorem_34_3_c (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∉ dom₁ K) :
    ¬ Proper (fun v => K (u, v)) ∧ (∀ v ∈ ri (dom₂ K), K (u, v) = ⊥) ∧
      (u ∉ closure (dom₁ K) → ∀ v ∈ dom₂ K, K (u, v) = ⊥) := by
  have hs := hcl.saddleStructure hK hp
  have hbot : ∀ v ∈ ri (dom₂ K), K (u, v) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu
  refine ⟨?_, hbot, fun hu' => hs.1.eq_bot_of_notMem_closure_dom₁ u hu'⟩
  obtain ⟨v₀, hv₀⟩ := hp.relint_dom₂_nonempty hK
  exact fun hpr => hpr.ne_bot v₀ (hbot v₀ hv₀)

/-- **Rockafellar, Theorem 34.3 (d).** For `v ∈ ri D`, the concave function `K (·, v)` is closed
proper with effective domain `C`. -/
theorem theorem_34_3_d (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ClosedConcaveFn (fun u => K (u, v)) ∧
      ProperConcave (fun u => K (u, v)) ∧ domConcave (fun u => K (u, v)) = dom₁ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.closedConcaveFn_slice hv,
    hs.properConcave_slice (intrinsicInterior_subset hv), hs.domConcave_slice hv⟩

/-- **Rockafellar, Theorem 34.3 (e).** For `v ∈ D ∖ ri D`, the concave function `K (·, v)` is
proper and its effective domain lies between `C` and `cl C`. -/
theorem theorem_34_3_e (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ dom₂ K \ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ProperConcave (fun u => K (u, v)) ∧
      dom₁ K ⊆ domConcave (fun u => K (u, v)) ∧
      domConcave (fun u => K (u, v)) ⊆ closure (dom₁ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.properConcave_slice hv.1, dom₁_subset_domConcave_slice K v,
    hs.domConcave_slice_subset_closure hv.1⟩

/-- **Rockafellar, Theorem 34.3 (f).** For `v ∉ D`, the concave function `K (·, v)` is improper,
with the value `+∞` throughout `ri C` — throughout `C` itself if `v ∉ cl D`. -/
theorem theorem_34_3_f (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∉ dom₂ K) :
    ¬ ProperConcave (fun u => K (u, v)) ∧ (∀ u ∈ ri (dom₁ K), K (u, v) = ⊤) ∧
      (v ∉ closure (dom₂ K) → ∀ u ∈ dom₁ K, K (u, v) = ⊤) := by
  have hs := hcl.saddleStructure hK hp
  have htop : ∀ u ∈ ri (dom₁ K), K (u, v) = ⊤ := fun _u hu => hs.eq_top_of_notMem_dom₂ hv hu
  refine ⟨?_, htop, fun hv' _u hu => hs.eq_top_of_notMem_closure_dom₂ hv' hu⟩
  obtain ⟨u₀, hu₀⟩ := hp.relint_dom₁_nonempty hK
  exact fun hpr => hpr.ne_top u₀ (htop u₀ hu₀)

/-- **Rockafellar, Theorem 34.3.** A proper concave-convex function is closed **if and only if**
it has the six properties (a)–(f). Specialises `closedSaddleFn_iff_saddleStructure`, whose
`SaddleStructure` is (a)–(c) for `K` together with (a)–(c) for `saddleSwap K`; the latter three
are (d)–(f), as `theorem_34_3_d`–`theorem_34_3_f` read off. -/
theorem theorem_34_3 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ClosedSaddleFn K ↔ SaddleStructure K :=
  closedSaddleFn_iff_saddleStructure hK hp

end Thm343

/-! ### The kernel and simple saddle-functions (14905–14915) -/

section Kernel

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar's `ri (dom K) = ri (dom₁ K) × ri (dom₂ K)`** (14884), the rectangle the kernel
lives on. -/
theorem relint_domSaddle_eq_prod (K : Rn m × Rn n → EReal) :
    ri (domSaddle K) = ri (dom₁ K) ×ˢ ri (dom₂ K) :=
  relint_domSaddle K

/-- **The kernel of `K`** (14886): the restriction of `K` to `ri (dom K)`.

Rockafellar's kernel is a partial function on a rectangle that moves with `K`; the backbone
extends it by `+∞` off the rectangle so that `kernel K = kernel L` is a single equation rather
than a rectangle equality plus a transport. Nothing is lost: `K` is finite on `ri (dom K)`. -/
theorem kernel_eq_restrict (K : Rn m × Rn n → EReal) :
    kernel K = Tdaf.ConvexAnalysis.restrict (ri (domSaddle K)) K := by
  have h : kernel K = Tdaf.ConvexAnalysis.restrict (kernelSet K) K := rfl
  rw [h, kernelSet_eq_relint_domSaddle]

/-- Equality of kernels unpacked into the book's two facts: the same rectangle, and the same
values on it. -/
theorem kernel_eq_iff' :
    kernel K = kernel L ↔ kernelSet K = kernelSet L ∧ Set.EqOn K L (kernelSet K) :=
  kernel_eq_iff

/-- **Rockafellar's *simple*** (14907): over `ri (dom₁ K)` the convex slices stay inside
`cl (dom₂ K)`, and over `ri (dom₂ K)` the concave slices stay inside `cl (dom₁ K)`. -/
theorem simpleSaddleFn_iff (K : Rn m × Rn n → EReal) :
    SimpleSaddleFn K ↔
      ((∀ u ∈ ri (dom₁ K), dom (fun v => K (u, v)) ⊆ closure (dom₂ K)) ∧
        ∀ v ∈ ri (dom₂ K), domConcave (fun u => K (u, v)) ⊆ closure (dom₁ K)) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Every closed proper saddle-function is simple** (14909, "by Theorem 34.3"): clauses (b) and
(e) say exactly that. -/
theorem simpleSaddleFn_of_closed (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : SimpleSaddleFn K :=
  hcl.simpleSaddleFn hK hp

/-- **The lower and upper simple extensions of a finite saddle-function on a nonempty `C × D` are
simple** (14909, "the most important examples"). -/
theorem simpleSaddleFn_lowerSimpleExt' {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    SimpleSaddleFn (lowerSimpleExt C D K) ∧ SimpleSaddleFn (upperSimpleExt C D K) := by
  refine ⟨simpleSaddleFn_lowerSimpleExt hCne hDne, ?_⟩
  rw [upperSimpleExt_eq_saddleSwap]
  exact simpleSaddleFn_saddleSwap_iff.2 (simpleSaddleFn_lowerSimpleExt hDne hCne)

/-- **Every saddle-function of the form `K (u, x*) = ⟨Fu, x*⟩` is simple** — Rockafellar's
exercise at 14909.

The book asks for nothing but "`F` a convex or concave bifunction". What is proved here needs
`F` **closed** — so that `K` is lower closed (Theorem 33.3) hence closed — and `K` **proper**, so
that Theorem 34.3 applies. Under those hypotheses simplicity is clauses (b) and (e). Whether the
unrestricted claim is true is not settled here: with `F u ≡ −∞` for some `u`, `dom₂ K` is empty
while `dom₁ K` need not be, and the first clause of simplicity then asks for
`dom (K (u, ·)) = ∅` at relative interior points of `dom₁ K`. -/
theorem simpleSaddleFn_bifunBracket {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hp : ProperSaddleFn (bifunBracket F)) :
    SimpleSaddleFn (bifunBracket F) :=
  (theorem_34_2_closed hF hcl (theorem_34_2_lower_mem hF hcl)).simpleSaddleFn
    (theorem_33_1_concaveConvex hF) hp

end Kernel

/-! ### Theorem 34.4 -/

section Thm344

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 34.4.** Two closed proper concave-convex functions on `ℝᵐ × ℝⁿ` are
equivalent **if and only if** they have the same kernel.

Specialises `saddleEquiv_iff_kernel_eq`. Because the backbone's `kernel` is a total function —
`K` on `ri (dom K)` and `+∞` off it — this is *one* equation, not a rectangle equality plus an
agreement on it; `kernel_eq_iff'` recovers the pair when it is wanted. -/
theorem theorem_34_4 (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    SaddleEquiv K L ↔ kernel K = kernel L :=
  saddleEquiv_iff_kernel_eq hclK hK hpK hclL hL hpL

end Thm344

/-! ### Theorem 34.5 and Corollary 34.5.1 -/

section Thm345

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Rockafellar, Theorem 34.5**: `cl₂ cl₁ K ≤ cl₁ cl₂ K` for a simple proper concave-convex
`K`. -/
theorem theorem_34_5_le (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : lowerCl K ≤ upperCl K :=
  lowerCl_le_upperCl hK hp hs

/-- **Rockafellar, Theorem 34.5**: the lower and upper closures of a simple proper concave-convex
function are **equivalent**. -/
theorem theorem_34_5_equiv (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SaddleEquiv (lowerCl K) (upperCl K) :=
  saddleEquiv_lowerCl_upperCl hK hp hs

/-- **Rockafellar, Theorem 34.5**: every saddle-function between the two closures is closed. -/
theorem theorem_34_5_closed (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_lowerCl hK hp hs hL

/-- **Rockafellar, Theorem 34.5**: every saddle-function between the two closures is proper. -/
theorem theorem_34_5_proper (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_lowerCl hK hp hL

/-- **Rockafellar, Theorem 34.5**: every concave-convex saddle-function between the two closures
has the same kernel as `K`. -/
theorem theorem_34_5_kernel (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : ConcaveConvexFn L)
    (hmem : L ∈ saddleClass (lowerCl K) (upperCl K)) : kernel L = kernel K :=
  kernel_of_mem_saddleClass_lowerCl hK hp hs hL hmem

/-- **Rockafellar, Theorem 34.5**, converse half: a closed proper concave-convex function with the
same kernel as `K` lies between the two closures — so the interval is the *whole* class. -/
theorem theorem_34_5_mem_of_kernel_eq (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (hker : kernel L = kernel K) :
    L ∈ saddleClass (lowerCl K) (upperCl K) :=
  mem_saddleClass_lowerCl_of_kernel_eq hK hp hs hclL hL hpL hker

/-- **Rockafellar, Theorem 34.5**, summary: the kernel of a simple proper concave-convex function
is the kernel of exactly one equivalence class of closed proper concave-convex functions, and
`cl₂ cl₁ K` represents it. Specialises `exists_unique_saddleEquiv_class_of_kernel`. -/
theorem theorem_34_5 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = kernel K) ∧ ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L →
      ProperSaddleFn L → (kernel L = kernel K ↔ SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_kernel hK hp hs

end Thm345

/-! ### Corollary 34.5.1 -/

section Cor3451

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Rockafellar, Corollary 34.5.1.** For nonempty convex `C ⊆ ℝᵐ`, `D ⊆ ℝⁿ` and a finite
concave-convex `K` on `C × D`, there is **one and only one** equivalence class of closed proper
concave-convex functions on `ℝᵐ × ℝⁿ` whose kernel is the restriction of `K` to `ri (C × D)`.

Specialises `exists_unique_saddleEquiv_class_of_finite`; the representative is the class of the
lower simple extension, exactly as the book's proof says. -/
theorem corollary_34_5_1 (hC : Convex ℝ C) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v)) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = Tdaf.ConvexAnalysis.restrict (ri (C ×ˢ D)) fun p => (K p : EReal)) ∧
      ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L → ProperSaddleFn L →
        (kernel L = Tdaf.ConvexAnalysis.restrict (ri (C ×ˢ D)) (fun p => (K p : EReal)) ↔
          SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_finite hC hCne hDne hconv hconc

end Cor3451

end Rockafellar
