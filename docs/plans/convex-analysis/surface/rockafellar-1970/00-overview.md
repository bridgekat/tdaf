# Surface: R. T. Rockafellar, *Convex Analysis* (Princeton, 1970)

This surface states all **471** numbered results of *Convex Analysis* in `ℝⁿ`, in the book's own
numbering and notation, and proves each by specialising the backbone.

Per the repository README, the surface is the integration test: it is what tells us whether the
backbone's generality was chosen correctly. **If a surface proof is longer than a few lines, that
is a signal to change the backbone, not to write a longer surface proof.** Record every such
signal in [`../../backbone/08-remediation.md`](../../backbone/08-remediation.md) rather than
working around it.

The complete per-section result inventory — every label, its line in the source text, a one-line
statement, and a G/C/E/X classification — is [`inventory.md`](inventory.md). The per-part plans
are [`part1.md`](part1.md) … [`part8.md`](part8.md).

---

## 1. Layout

Chapter modules containing section modules, mirroring the book's own division into 8 parts:

```
Tdaf/Surface/Rockafellar/
  Notation.lean          -- δ(·|C), δ*(·|C), γ(·|C), f0⁺, fλ, □, #, K°, C°, ⟨f,g⟩
  Part1.lean             -- aggregator: imports Part1/Section01 … Section05
  Part1/Section01.lean … Section05.lean      -- Basic Concepts
  Part2.lean ; Part2/Section06.lean … Section10.lean   -- Topological Properties
  Part3.lean ; Part3/Section11.lean … Section16.lean   -- Duality Correspondences
  Part4.lean ; Part4/Section17.lean … Section22.lean   -- Representation and Inequalities
  Part5.lean ; Part5/Section23.lean … Section26.lean   -- Differential Theory
  Part6.lean ; Part6/Section27.lean … Section32.lean   -- Constrained Extremum Problems
  Part7.lean ; Part7/Section33.lean … Section37.lean   -- Saddle-functions and Minimax Theory
  Part8.lean ; Part8/Section38.lean … Section39.lean   -- Convex Algebra
```

`PartN.lean` imports its sections and nothing else; `Tdaf.lean` registers every module
alphabetically, as it does for the backbone.

### Naming

Namespace `Rockafellar`, **flat**. Declaration names are the book's numbering:

```
theorem_4_2      corollary_16_4_1      lemma_22_4      theorem_30_4_g
```

Flat beats nesting because the book's numbering is already globally unique, and because a reader
looking for Theorem 30.4 types `theorem_30_4` and finds it with no knowledge of which part it is
in. Multi-clause theorems get one declaration per clause with a letter suffix — there are **51**
such clauses, and their clauses genuinely differ in hypotheses and in backbone layer (Theorem 27.1
has 9, Theorem 30.4 has 10).

Every declaration carries a docstring quoting the book's statement, so that semantic alignment can
be checked by reading the surface file alone.

**This is the one place in the repository where bibliographic names are correct.**
[D10](../../00-overview.md#d10-the-backbone-is-not-tied-to-rockafellar) forbids them in the
backbone precisely so that they can be unambiguous here.

---

## 2. The ambient setting

```lean
namespace Tdaf.Surface
open Tdaf.ConvexAnalysis
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable abbrev pairing (n : ℕ) : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := innerₗ (Rn n)
```

This is `Tdaf/Surface/Common/Euclidean.lean`, written and building.

Everything is then `conj (pairing n)`, `subgradient (pairing n)`, and so on. Because `Rn n` is a
finite-dimensional real inner-product space, all four [D9](../../00-overview.md#d9-generality-boundaries)
layers are available at once — which is exactly why the book can state everything without
qualification.

Rockafellar identifies `ℝⁿ` with its dual, writing `x*` for a vector in the same space. The surface
honours this by taking `F = E` and `B = ⟨·,·⟩`, so the `*` decoration becomes a naming convention
rather than a type distinction. That is faithful, and it is also why the backbone must keep the two
spaces distinct: so that the general theory cannot silently depend on self-duality.

**The ambient setting is not Rockafellar-specific**, and is not in this directory.
Boyd–Vandenberghe wants the same `ℝⁿ` instantiation and Bauschke–Combettes the same Hilbert one, so
it lives in `Tdaf/Surface/Common/Euclidean.lean` and each surface imports it. The gaps below were
therefore fixed once.

### 2.1 Instantiation checklist

Ambient typeclasses on `Rn n` — all from Mathlib, all expected automatic:
`NormedAddCommGroup`, `InnerProductSpace ℝ`, `NormedSpace ℝ`, `FiniteDimensional ℝ`,
`CompleteSpace`, `T2Space`, `ProperSpace`, `LocallyConvexSpace ℝ`, `IsTopologicalAddGroup`,
`ContinuousSMul ℝ`, `SeparableSpace`.

Pairing classes — **all discharged**, and asserted as a regression test in
`Tdaf/Surface/Common/Euclidean.lean`:

| hypothesis | how |
|---|---|
| `IsInnerPairing`, `IsContinuousInnerPairing`, `IsContinuousPairing`, `IsCompatiblePairing` of `innerₗ E` | instances |
| the same at `.flip` and `.flip.flip` | instances — a symmetric pairing is its own flip |
| `IsContinuousPairing`/`IsCompatiblePairing (-B)` and `(-B).flip` | instances, `Duality/Pairing.lean` (remediation §1.3) |
| the four classes for `prodPairing Bu Bx` and its flip | instances |
| the four classes for `negFst (prodPairing Bu Bx)` and its flip | instances, `Duality/Pairing.lean` (remediation §4.2) |
| `SeparatingDual ℝ (Rn n)` | instance — was never missing |

The review predicted four gaps here and all four are closed. Two of them were not gaps at all: the
`(innerₗ E).flip` instances were already general in `Duality/InnerPairing.lean`, and
`SeparatingDual` needed nothing. The two that were real — the negated pairings and `negFst` — are
now instances, and `negFst` in particular needed the `LinearMap` equation
`negFst (prodPairing Bu Bx) = prodPairing (-Bu) Bx`, not the pointwise identity that already
existed: the classes are stated about the bilinear map, so a pointwise fact cannot reach them.

**`pairing n` must be an `abbrev`.** As a plain `def` instance search does not unfold it, and not
one of the classes above is found — `IsInnerPairing (pairing n)` already fails. This is the first
thing a new `Setup.lean` gets wrong; see gotcha PAIR2.

No `local instance` shims are needed. The three backbone sites that work around instance-search
failure with `rw [flip_innerₗ]; infer_instance` are `maxSynthPendingDepth` artefacts (gotcha PAIR5)
and do not recur here.


---

## 3. Alignment checklist

For each section, confirm before marking it done:

1. Every numbered result has a declaration, or falls into one of three explicit categories:
   **omitted with a reason**, **deferred by scope**, or **stated and refuted**. The third exists
   because Corollaries 17.1.4 and 17.1.6 are *false as Rockafellar states them*; the surface
   transcribes the counterexample rather than silently dropping them.
2. The statement quantifies over the same objects as the book. Rockafellar's "convex function"
   always means extended-real-valued and defined on all of `ℝⁿ`; a surface statement about
   `f : ℝⁿ → ℝ` is a mistranslation unless the book says *finite*.
3. Improperness is not silently excluded. Several theorems (7.2, 12.2, 34.2.3) are specifically
   about improper functions.
4. No `axiom`, no `sorry`, no definitional cheat — in particular the surface must not *define* a
   notion so as to make a theorem true by unfolding. Where a surface definition is introduced for
   alignment, it comes with an equivalence proof to the backbone notion.
5. `#print axioms` on each section's main results shows only the standard three.
6. **Where the book's proof is wrong or absent, say so in the docstring.** Fourteen results are
   printed with no proof at all, and three printed arguments are defective; see §5.

---

## 4. Modelling decisions forced by the text

These are not stylistic. Each one is a place where a naive transcription produces a statement that
cannot be proved, or that is false.

* **Mixed sets of points *and* directions.** `conv S`, `aff S`, `dim S` and "generalized simplex"
  in §§8, 17, 18, 19 are applied to an `S` that is a *pair* (points, directions), not a subset of
  `ℝⁿ`. Model `S` as a subset of the homogenisation cone `{(λ,x) | λ ∈ {0,1}}`; the backbone's
  `convexHullPD` and `HullDirections.lean` already take this route.
* **The `λ = 0⁺` scalar convention.** In Theorems 9.6, 9.7, 9.8, 19.5.1, 19.6, 19.7 the expression
  `λC` *means* `0⁺C` when `λ = 0`, not `{0}`. Needs an explicit extended-scalar type or a two-case
  rewrite of each statement.
* **Orientation is data, in three separate places.** (i) `cl₁` closes the *concave* argument and
  `cl₂` the convex — reverse it and every result in §§34–37 silently swaps. (ii) Minimise in the
  convex argument, maximise in the concave (§36, in force through §37) — this is *why* `∂K` mixes a
  concave subdifferential in the first argument with a convex one in the second, hence why
  Cor 37.5.2 inserts `u* ↦ −u*` and Cor 37.5.1's homeomorphism is the asymmetric `(u−u*, v+v*)`.
  **Track the sign explicitly; do not try to derive it.** (iii) Supremum vs infimum orientation of
  convex processes (§39): Rockafellar makes an oriented set formally a *pair*. Theorems 39.5 and
  39.8 quantify over two processes of the **same** orientation and Theorem 39.2 **flips** it, so
  both orientations must be simultaneously expressible — a global convention cannot state 39.5.
* **`⟨f,g⟩` is a partial operation**, undefined when the two extrema differ (§38). Model it as a
  predicate plus a value, or `Option`/`Part` — never a total function. Fenchel duality is what
  guarantees existence.
* **The `∞−∞` convention of Theorem 38.1 is orientation-dependent**: `−∞` for convex bifunctions,
  `+∞` for concave ones. `EReal` makes a different choice; handle it explicitly rather than
  inheriting it.
* **`Σ ζ*ᵢ Iᵢ > 0` in Theorem 22.6 is a set containment**, not a numeric inequality: the sum of
  intervals is an interval and `> 0` means `⊆ (0,∞)`. The book states this once, in a parenthesis,
  120 lines before the theorem.
* **`cl f` is defined by cases** (lsc hull if `f` never takes `−∞`, else the constant `−∞`), and
  `epi (cl f) = cl (epi f)` is asserted "by definition" but holds only for *proper* `f`.
* **`cone S` is defined to contain the origin** while the cone of Cors 2.6.2/2.6.3 need not. This
  off-by-one propagates through §§8, 9, 14, 19.
* **`dim f := dim (dom f)`**, not `dim (epi f)`; later text implicitly uses
  `dim (epi f) = dim f + 1`.

---

## 5. Where the book is defective

Carry these in the surface docstrings; a reader checking alignment must not conclude the
formalization is wrong.

**False as stated.** Corollaries 17.1.4 and 17.1.6 (counterexample recorded in
`api.md`'s `Caratheodory.lean` record). **Corollary 29.4.1** drops the properness hypothesis its
own Theorem 29.4 carries, and its clause about the perturbation functions agreeing near `0` is
false without it — found independently from the Lean side and from the text, and *stated and
refuted* in `Part6/Section29.lean`.

**One entry has been withdrawn from this section**, and it is worth leaving the scar. This file used
to record Theorem 29.4's printed proof as defective, on the ground that `cl f` is `+∞` outside
`cl (dom f)`. That is the lower semicontinuous hull `f̄`; Rockafellar defines `cl f` by cases at line
2177, and for an improper convex `f` it is the constant `−∞` **everywhere** — line 2231 draws the
contrast explicitly. The printed step is correct. A record that accuses the book is a claim like any
other, and LIB17 applies to it: the entry stood for three rounds and was checked by the first agent
that had to use it.

**Stated with no proof at all.** Theorem 12.4 (the monotone-conjugacy involution — the surface must
supply the entire argument), and Corollaries 23.5.1, 25.5.1, 27.2.1, 28.2.2, 28.3.1, 28.4.1,
31.5.1, 33.1.2, 34.2.1, 34.2.3, 37.1.3, and Theorem 36.6. Corollary 31.2.1's polyhedral
strengthening is asserted with the proof explicitly omitted.

**Cross-reference bug.** The book's own Comments cite "Corollary 21.3.3", which does not exist; the
text has 21.3.2.

**Asserted, not constructed.** The triangulation of a polyhedron near a point (Theorem 20.5), on
which Theorem 10.2 depends; and the eight "natural" partial additions underlying Theorem 5.8,
described only informally in §§3 and 5.

**Extraction hazard.** **23 labels are printed in mixed case** and are missed by a case-sensitive
scan — including **Theorem 5.4**, the definition site of the infimal-convolution notation, and
**Theorem 38.1**. Full list in [`inventory.md`](inventory.md).

---

## 6. Order of work

Follow the backbone's shape, not the book's order. Each group is gated on the remediation items it
needs.

| # | sections | gated on |
|---|---|---|
| 0 | `Setup.lean`, `Notation.lean` | remediation §1.2, §1.3, §4.2 — **hard gate** |
| 1 | §4, §5 | — the first alignment check, and the one most likely to expose a wrong definition |
| 2 | §11, §12, §13 | — conjugacy is where the pairing decision is tested |
| 3 | §2, §3, §1 | mostly Mathlib re-exports; cheap, and they make the earlier files readable |
| 4 | §6–§10 | — |
| 5 | §14, §15, §16 | §15 needs remediation §4.7 (`IsNorm` → `Seminorm`); §16 needs §4.1 (adjoint) and §4.4 (`m`-ary) |
| 6 | §23–§26 | §23 needs §4.4 |
| 7 | §17–§22 | §22 **deferred by scope** |
| 8 | §27–§32 | §27 needs §4.6; §28 is the thickest file and comes last in this group |
| 9 | §33–§39 | §29–§30 need §4.2 and §4.8 |

**Groups 0 through 7 are done** — §§1–26, in that order, with §22's elementary-vector development
the one scope deferral. Group 8 (§§27–32) is next; its gate, remediation §4.6, is still open, and
group 9's gates §4.2 and §4.8 are both closed.

§38 and §39 are the two sections that are **entirely** general (12/0 and 9/0 on the G/C split), so
they are also the natural first target if a general non-`ℝⁿ` second surface is ever wanted.

---

## 7. Status

The hard gate is closed: remediation §1.2, §1.3 and §4.2 are done, and
`Tdaf/Surface/Common/Euclidean.lean` is the ambient setting, asserting all 31 instances of §2.1 as
a regression test. There is no `Setup.lean`/`Notation.lean` pair — `Euclidean.lean` is that file,
and it lives under `Surface/Common/` because a second surface over `ℝⁿ` would want the same one.

**Counts are declarations and labels.** A *declaration* is any `theorem`, `lemma`, `def`, `abbrev`,
`structure` or `instance` in the module; a *label* is a numbered result of the book claimed by a
declaration's own doc comment, so a label mentioned only in prose — in a `## What is not here`
paragraph, say — does not count. Earlier versions of this table used a narrower declaration count;
the tables below are all on the one method, and the label columns are unchanged in meaning.

**Part I — all five sections written**, 185 declarations for all 49 of the Part's numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 1 | `Part1/Section01.lean` | 49 | 8 |
| 2 | `Part1/Section02.lean` | 23 | 13 |
| 3 | `Part1/Section03.lean` | 46 | 9 |
| 4 | `Part1/Section04.lean` | 21 | 11 |
| 5 | `Part1/Section05.lean` | 46 | 8 |

The declaration count runs to nearly four times the label count because the book states existence
and uniqueness in one sentence (§1), splits a theorem across unlettered clauses (§3, §5, §2's
Theorem 2.7), and defines as much as it proves — every surface definition carries its bridge lemma.

The order of §6 was not followed for Part I: §1–§5 were written together, because the five files are
independent and the point of the first round was to test the *backbone*, not to sequence the book.
What that round found is in [`../../backbone/08-remediation.md`](../../backbone/08-remediation.md)
§8 — seventeen backbone gaps, two scheduled items demoted, and five places where the book is wrong.
Ten are closed, one of which — extending a linear isomorphism between subspaces — turned out never
to have been a gap at all.

**Part II — all five sections written**, 222 declarations for all 84 of the Part's numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 6 | `Part2/Section06.lean` | 52 | 18 |
| 7 | `Part2/Section07.lean` | 24 | 17 |
| 8 | `Part2/Section08.lean` | 59 | 18 |
| 9 | `Part2/Section09.lean` | 60 | 18 |
| 10 | `Part2/Section10.lean` | 27 | 13 |

**Parts I and II are complete.** Corollaries 9.2.1 and 9.8.3 were the last two absent labels and the
gap round closed both (remediation §9.19, §9.20). Like the rest of §9 they are stated for two
functions; the `m`-ary forms stay in `Section09`'s `## What is not here`, and their obstacle is
recorded as remediation §9.18 — Rockafellar's own route runs Theorem 9.2 on `Eᵐ` against the sum
map, which needs an `m`-ary `infConv` and the recession function of a separable sum.

Two findings of the Part II round are worth promoting out of the remediation list:

* **The §10/§20 dependency does not exist.** `Analysis/Convex/Simplicial.lean` proves upper
  semicontinuity relative to a simplex at *every* point of it, not only at a vertex, so
  Rockafellar's triangulation step — the "intuitively obvious" barycentric fact he never proves, and
  which Theorem 20.5 supplies by assertion — is never invoked. Theorem 10.2 is unconditional here,
  and §20's author inherits no obligation from §10. §20 later confirmed this from its own side.
* **Rockafellar's `λ ≥ 0⁺` convention is modelled, not case-split.** §9 introduces `ExtCoeff`
  (`ofReal t | zeroPlus`) with actions on sets and on functions, so Theorems 9.6–9.8 are literally
  unions and infima over the book's index set. §19 inherited it unchanged.

**Part III — all six sections written**, 276 declarations for all 77 of the Part's numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 11 | `Part3/Section11.lean` | 30 | 16 |
| 12 | `Part3/Section12.lean` | 47 | 9 |
| 13 | `Part3/Section13.lean` | 47 | 15 |
| 14 | `Part3/Section14.lean` | 54 | 11 |
| 15 | `Part3/Section15.lean` | 56 | 11 |
| 16 | `Part3/Section16.lean` | 42 | 15 |

**Part III is complete.** Its last two absent labels were Theorem 14.4 and Corollary 16.2.2, and
both turned out to want a product transport rather than convex analysis — `ℝᵐ × ℝⁿ ≃ ℝᵐ⁺ⁿ` for the
first, `ι → E` for the second. Neither transport existed; both do now
(`Analysis/Convex/EuclideanProd.lean` and `Duality/FiniteProduct.lean`), and each closed something
outside its motivating label on the way: §22's interval reading and §9.18's sum map respectively.

**This is the Part that tests [D3](#d3-duality-is-developed-for-a-dual-pair-not-for-ℝⁿ-and-not-for-the-dual-space),
and D3 holds.** Not one §11–§16 statement needed the dual pair to be relaxed: `pairing n` discharges
every pairing class by instance search, and the only recurring friction is cosmetic — a backbone
statement hands back `B.flip` where the surface wants `B`, which eight `*_flip_pairing` rewrites in
the shared header absorb. The adjoint decision holds too, for a reason the plan did not predict:
remediation §4.1 proposed bundling the adjoint into a class because "~100 statements thread `(A')`
plus `IsAdjointPair`", but the *surface* pays none of that — `isAdjointPair_adjoint` already exists
in `Duality/Pairing.lean` for `innerₗ E`, so §16 writes every `A*` as `LinearMap.adjoint A` and
carries no adjoint hypothesis at all. What remains of §4.1 is backbone-internal.

**Part IV — all six sections written**, 206 declarations for 65 of the Part's 70 numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 17 | `Part4/Section17.lean` | 24 | 10 |
| 18 | `Part4/Section18.lean` | 49 | 16 |
| 19 | `Part4/Section19.lean` | 44 | 17 |
| 20 | `Part4/Section20.lean` | 26 | 8 |
| 21 | `Part4/Section21.lean` | 27 | 10 |
| 22 | `Part4/Section22.lean` | 36 | 4 of 9 |

The five absent labels are all in §22 and all one item: **Lemmas 22.4 and 22.5, Corollary 22.4.1,
and Theorems 22.6 and 22.7**, the elementary-vector development and Tucker's complementarity
theorem. They are *deferred by scope* — elementary vectors are the minimal-support vectors of a
subspace and their theory is combinatorial matroid theory, which the book itself presents as
independent of all convexity theory. **This is the only place in §§1–22 where a label is absent for
a reason other than a named backbone gap.** Theorems 22.1–22.3 and Farkas' Lemma are here.

Three of the round's findings are worth promoting out of the remediation list:

* **Corollaries 17.1.4 and 17.1.6 are false as Rockafellar states them, and §17 refutes them in
  Lean** rather than dropping them — `corollary_17_1_4_false`, `corollary_17_1_6_false`, both on
  `ℝ¹`. This is the *stated and refuted* category of the alignment checklist §3, and Part IV is what
  it was written for. Theorem 17.3 is false as printed too; the backbone already carried the missing
  hypothesis `0 ∉ S*`.
* **Theorem 20.5 supplies `LocallySimplicial` instances; it does not repair §10.** The Part II
  finding is confirmed from the §20 side, and by a stronger route: `Polyhedral.locallySimplicial`
  takes a coordinate cube for the neighbourhood and produces the simplices explicitly, so it never
  makes the appeal to Carathéodory's count that the book asserts without proof.
* **The book's own proof of Theorem 17.1's simplex clause needs `S₀ ≠ ∅` and does not say so.**
  Rockafellar extends to a basis of `span S′` and calls its dimension `d + 1`; if `S` has directions
  only then `C = ∅` and `dim C = −1` by his own p. 154 convention, so the arithmetic fails even
  though the clause is vacuous. `theorem_17_1_simplex` carries the hypothesis.

**Part V — all four sections written**, 249 declarations for all 49 of the Part's numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 23 | `Part5/Section23.lean` | 72 | 16 |
| 24 | `Part5/Section24.lean` | 48 | 11 |
| 25 | `Part5/Section25.lean` | 40 | 11 |
| 26 | `Part5/Section26.lean` | 89 | 11 |

**Part V is complete**, and it is the first Part written without a single deferral, refutation or
absent label. It is also the densest: five declarations per numbered result, against three for
Parts I–IV. Three findings are worth promoting out of the remediation list:

* **A complete non-decreasing curve is a maximal chain, and Mathlib already has that.** §24's
  `IsCompleteNonDecreasingCurve` is `IsMaxChain (· ≤ ·)` with the product order on `ℝ × ℝ`, per
  [D12](#d12-order-theoretic-duality-comes-from-mathlib). The book gives its *definition* at line
  9181 and this *characterisation* at 9195, in that order; taking the second means Theorem 24.3 is
  stated in order-theoretic vocabulary and needs no curve theory of its own. Only the implication
  back to the book's definition is missing, and Theorem 24.3 does not use it.
* **§25 is markedly less finite-dimensional than the plan supposed.** The plan classified all eleven
  results as concrete; three are general — Theorem 25.1's forward half (the gradient is the unique
  subgradient, on any normed space), both halves of Corollary 25.1.1, and Theorem 25.4's density
  clause. What is genuinely finite-dimensional is Theorem 25.1's *converse*, which runs through
  Corollary 11.6.1 and is false in infinite dimensions.
* **Line 8477's exercise is not discharged where the book says it is.** Rockafellar leaves
  `rec (∂f(x)) = N_{dom f}(x)` as an exercise in §23 and promises the verification "as part of the
  proof of Theorem 25.6". The backbone's proof of Theorem 25.6 uses only the inclusion `⊆`, so
  nothing discharges it on the way; §25 discharges it directly instead, in four lines and
  independently of Theorem 25.6, and §23 assumes it nowhere.

## 8. Where §§1–26 stand

**324 of the 329 numbered results have declarations, and the five that do not are deferred by
scope, not blocked.** They are §22's elementary-vector development — Lemmas 22.4 and 22.5, Corollary
22.4.1, and Theorems 22.6 and 22.7 — which is combinatorial matroid theory that the book itself
presents as independent of all convexity theory.

**Parts I, II, III and V are complete**, and Part IV is complete apart from that one deferral.
Nothing in §§1–26 is waiting on a backbone gap. That is 1138 declarations across 26 modules,
five Part aggregators and the shared header.

What is left in [`../../backbone/08-remediation.md`](../../backbone/08-remediation.md) is no longer
blocking anything: `recessionFn` of a separable sum (§9.18's last piece), two relative-interior
lemmas parked above their home (§11.21), three `api.md` records (§11.22), and the eight things the
Part V round proved on the surface that belong in the backbone (§12). The next round is §§27–39 —
Parts VI, VII and VIII, 142 numbered results.

### What the five rounds cost, and what they were worth

Twenty-two agents over five rounds: three surface rounds writing §§17–26, a gap round closing six of
the seven blocked labels, and a product round closing the seventh and eleven other items. The
recurring lesson is in `gotchas.md` LIB17 and it is about **this repository's own records rather
than about Lean**: fourteen times across the last three rounds, a plan or a remediation item named
a home, a prerequisite, a cost or a scope decision, and the claim was wrong — an isometry that
cannot exist, a theorem not on the route, a module that does not define the function it is about, a
cost estimate wrong twice in the same direction, a corollary recorded as out of scope that the
backbone had proved in full. Every one was found by an agent that checked the claim instead of
planning around it, and one of them (§11.4) had cost a full round of deferral. An item that names
something is making a claim, and it gets checked.

The Part V round added a second form of the same lesson, one level down: **a gate is not closed
because the interface it asked for exists.** §4.4 asked for an `m`-ary `IsExactSum`, the product
round built `IsExactFinsetSum` with both constructors, and the item was marked done — but
`Subgradient/Calculus.lean` still had only the binary *consequence*, which is what §23 actually
needed. Half a gate reads exactly like a whole one from the outside.

And a third, from the same round: **the `G/C` column of the Part plans is not a theorem/corollary
split**, and three agents in a row were handed it as one. Where a plan's table is terse, the brief
that quotes it should quote the header too.
