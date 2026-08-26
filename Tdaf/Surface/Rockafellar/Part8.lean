/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part8.Section38
import Tdaf.Surface.Rockafellar.Part8.Section39

/-!
# Rockafellar, Part VIII: Convex Algebra

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §§38–39. This module imports the two
section modules and adds nothing of its own.

| § | module | subject | declarations |
|---|---|---|---|
| 38 | `Part8.Section38` | The Algebra of Bifunctions | 59 |
| 39 | `Part8.Section39` | Convex Processes | 101 |

**All 21 of Part VIII's numbered results have declarations.** Nothing is deferred by scope and
nothing was blocked. This is the only Part of the book that is entirely `G` — all 21 results
survive generalisation beyond `ℝⁿ`, so both modules are thin specialisations and every result
closes in one to five lines. Two results are partial and say so in their docstrings: Lemma 38.6's
second assertion, `⟨cl f, cl g⟩ = ⟨f, g⟩`, which wants the concave mirror of
`proper_conj_of_proper`; and Theorem 38.7's middle member `−⟨f*, F⁎g⟩`, which the book itself
breaks off mid-sentence at 16631.

Lines 17199–17268 — an algebra of oriented processes and a proposed duality for multivalued maps,
sketched without proof — are the end of the book rather than a section of results. Nothing there
is numbered and nothing there became a declaration.

## The three gates, and why two of them were not gates

* **§2.2, de-leak `reflect`'s mirror statements** — a real gate, and closed before the section was
  written. Eight statements in `Bifunction/Process.lean` mentioned the involution in their own
  hypotheses; a surface theorem named `theorem_39_2` must read like the book's Theorem 39.2 and
  not like a transport lemma. `coadjointProcess_add` and `coadjointProcess_comp` now carry
  Theorems 39.5's and 39.8's own hypotheses verbatim, and both were usable *unchanged* in the
  surface, with no transport step at either use site.
* **§4.1, "bundle the adjoint"** — not a gate, and the claim behind it was a confusion of two
  different stars. §38's `F*` and §39's `A*` are `adjointBifun` and `adjointProcess`: *defined
  operations* of a pair of pairings, taking no linear map and carrying no adjoint datum.
  `IsAdjointPair` occurs nowhere in `Bifunction/{Algebra, Cofinite, Process, ProcessDuality}.lean`,
  so there was nothing here for a `HasTranspose` class to supply.
* **§4.4, the `m`-ary `infConv`** — not a gate either. No numbered result of either section is
  `m`-ary; the `m`-ary `□` belongs to the associativity discussion, which
  `infConvBifun_assoc`/`infConvBifun_comm` already settle unconditionally.

## What this Part settles about the backbone

**Orientation is data, and the backbone is right not to bundle it.** The plan for this Part said
the backbone "carries [orientation] as a field". It deliberately does not — `Process.lean`'s design
note is explicit that orientation is a second adjoint rather than a flag — so the surface builds
the formal pair Rockafellar defines at 16945–16965: `Orientation`, `OrientedProcess`, and the
dispatch `Orientation.adjointProcess`. This is the one place in the book where that apparatus is
unavoidable rather than merely convenient. Theorems 39.5 and 39.8 require *the same* orientation
and Theorem 39.2 *flips* it, so a global convention of the kind §36 imposes for saddle-functions
cannot even state Theorem 39.5. The pair pays for itself immediately: `theorem_39_5` and
`theorem_39_8` take `hor : A₁.orientation = A₂.orientation` and `subst` it,
`theorem_39_2_orientation` is `rfl`, and Theorem 39.3 comes out with positive homogeneity
orientation-free and convexity/concavity as four visibly mirrored declarations.

**One notation must not carry two `∞ − ∞` rules, and the surface can prove it.** Theorem 38.1's
convention is `−∞` for convex bifunctions and `+∞` for concave — the fourth overloading of `⟨·,·⟩`
in the book and the fourth distinct `∞ − ∞` rule. The two are named apart as `convexAdd` and
`concaveAdd`, with `convexAdd_ne_concaveAdd` and `concaveAdd_eq_convexAdd` for the agreement off
the two collisions. `theorem_38_1_bracket_concave` is **false** with `convexAdd` in its place, so
the separation is not fastidiousness.

**`⟨f, g⟩` is kept partial, as the book's prose admits it is** (16527). `HasInnerProduct` is an
explicit hypothesis wherever an inner product is claimed to exist, so the place where the book's
fluency hides a side condition stays visible.

**Co-finiteness needed Corollary 13.3.1, not Theorem 34.2.** The book cites Theorem 34.2 for
`dom F = ℝᵐ ∧ dom F* = ℝⁿ ⇒ co-finite` (16701), and the backbone's own gap note predicted the proof
would need `IsExactSum` over four spaces. Neither is so: `cofiniteBifun_iff_domBifun_eq_univ` is
Corollary 13.3.1 applied slice by slice, with no saddle-function machinery at all.

## Where the book is defective

* **Theorem 38.1's domain formula is misprinted** at 16214 as `dom (F₁ ∩ F₂) = dom F₁ ∩ dom F₂`;
  the operation meant is `□`. `theorem_38_1_dom` states the intended identity.
* **Corollary 38.7.2's proof is incomplete** — the `ri (dom (GF))` formula is left "to the reader as
  a pithy exercise" (16691) — so `corollary_38_7_2_first` carries the `IsExactSum` its proof
  actually consumes.
* **Theorem 39.1's boundedness hypothesis is stronger than its proof.** The first line converts
  "`A0` bounded" into `A0 = {0}` and nothing afterwards uses boundedness, so `theorem_39_1` takes
  `A.eval 0 = {0}` and `theorem_39_1_isBounded` recovers the book's literal form. Same divergence,
  same reason, as Corollary 32.3.3 in Part VI.
* **Theorem 39.3's last assertion needs no closedness on the `u` side**, though the book prefixes
  both halves with "if `A` is closed": that half is Corollary 33.2.1.
  `theorem_39_3_relint_dom` is stated without it and `theorem_39_3_relint_dom_adjoint` keeps it.
* **`□` is unconditionally commutative and associative here**, where the book hedges "to the extent
  that it is defined" (16239) — `infConv` is a total operation on `EReal`, so improper bifunctions
  are included. This is *stronger* than the book. The caveat that is real is the one about
  bifunction multiplication (16507), and that one is not discharged.

## Where the backbone is defective

**Theorems 39.5's and 39.8's hypotheses exclude §39's own running example**, and the surface
records this rather than working around it. `ConvexProcess.adjointProcess_add` asks for
`∀ y, IsExactSum …` on the summands `u ↦ -⟨Aᵢ u, x*⟩`. `IsExactSum` carries properness of both
summands as *fields*, so that hypothesis silently asserts `dom Aᵢ* = ℝⁿ`. For Rockafellar's own
example `Au = {x | x ≤ Bu}` it fails at every `x*` with a negative coordinate. `Process.lean`'s
design note says the reduction to Rockafellar's `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅` "is available and
simply has not been done" via `IsExactSum.of_relint`; it is not available, because `of_relint`
takes the properness as an argument. `adjointProcess_comp`, both `coadjoint*` mirrors, the four
closed halves, and `Algebra.lean`'s `adjointBifun_infConvBifun_eq_supConvBifun` all inherit it.
The surface transcribes the backbone hypothesis verbatim and flags the divergence in every
affected docstring; no weaker statement is numbered as the book's.
-/
