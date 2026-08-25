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
false without it — found independently from the Lean side and from the text.

**Defective printed argument.** Theorem 29.4's proof claims `((cl F)u)(y) = −∞` for *all* `y` in
the improper case, but `cl f` is `+∞` outside `cl (dom f)`. The theorem survives; the justification
does not.

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

§38 and §39 are the two sections that are **entirely** general (12/0 and 9/0 on the G/C split), so
they are also the natural first target if a general non-`ℝⁿ` second surface is ever wanted.

---

## 7. Status

The hard gate is closed: remediation §1.2, §1.3 and §4.2 are done, and
`Tdaf/Surface/Common/Euclidean.lean` is the ambient setting, asserting all 31 instances of §2.1 as
a regression test. There is no `Setup.lean`/`Notation.lean` pair — `Euclidean.lean` is that file,
and it lives under `Surface/Common/` because a second surface over `ℝⁿ` would want the same one.

**Part I — all five sections written**, 147 declarations for the Part's 49 numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 1 | `Part1/Section01.lean` | 50 | 8 |
| 2 | `Part1/Section02.lean` | 23 | 13 |
| 3 | `Part1/Section03.lean` | 36 | 9 |
| 4 | `Part1/Section04.lean` | 12 | 11 |
| 5 | `Part1/Section05.lean` | 26 | 8 |

The declaration count runs to three times the label count because the book states existence and
uniqueness in one sentence (§1), splits a theorem across unlettered clauses (§3, §5, §2's
Theorem 2.7), and defines as much as it proves — every surface definition carries its bridge
lemma.

The order of §6 was not followed for Part I: §1–§5 were written together, because the five files
are independent and the point of the first round was to test the *backbone*, not to sequence the
book. What the round found is in
[`../../backbone/08-remediation.md`](../../backbone/08-remediation.md) §8 — seventeen backbone gaps,
two scheduled items demoted, and five places where the book is wrong. Two of the seventeen are
already closed (`Analysis/Convex/Line.lean`, and Jensen moved to `Epigraph.lean`). Ten are
closed now: the two above plus the eight of the Batch A sweep, one of which — extending a linear
isomorphism between subspaces — turned out never to have been a gap at all.

**Part II — all five sections written**, 216 declarations for 82 of the Part's 84 numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 6 | `Part2/Section06.lean` | 52 | 18 |
| 7 | `Part2/Section07.lean` | 25 | 17 |
| 8 | `Part2/Section08.lean` | 59 | 18 |
| 9 | `Part2/Section09.lean` | 53 | 16 of 18 |
| 10 | `Part2/Section10.lean` | 27 | 13 |

The two absent labels are **Corollary 9.2.1** and **Corollary 9.8.3**, each waiting on a named
backbone lemma; both are recorded in `Section09`'s `## What is not here`.

Two findings of the Part II round are worth promoting out of the remediation list:

* **The §10/§20 dependency does not exist.** `Analysis/Convex/Simplicial.lean` proves upper
  semicontinuity relative to a simplex at *every* point of it, not only at a vertex, so
  Rockafellar's triangulation step — the "intuitively obvious" barycentric fact he never proves,
  and which Theorem 20.5 supplies by assertion — is never invoked. Theorem 10.2 is unconditional
  here, and §20's author inherits no obligation from §10.
* **Rockafellar's `λ ≥ 0⁺` convention is modelled, not case-split.** §9 introduces `ExtCoeff`
  (`ofReal t | zeroPlus`) with actions on sets and on functions, so Theorems 9.6–9.8 are literally
  unions and infima over the book's index set. §19 inherits it.

**Part III — all six sections written**, 259 declarations for 72 of the Part's 77 numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 11 | `Part3/Section11.lean` | 30 | 16 |
| 12 | `Part3/Section12.lean` | 47 | 9 |
| 13 | `Part3/Section13.lean` | 48 | 15 |
| 14 | `Part3/Section14.lean` | 45 | 9 of 11 |
| 15 | `Part3/Section15.lean` | 55 | 11 |
| 16 | `Part3/Section16.lean` | 34 | 12 of 15 |

The five absent labels are **Theorems 14.3 and 14.4** and **Lemma 16.2 with Corollaries 16.2.1 and
16.2.2**; each is one named backbone result away and each is recorded in its own module.

**This is the Part that tests [D3](#d3-duality-is-developed-for-a-dual-pair-not-for-ℝⁿ-and-not-for-the-dual-space),
and D3 holds.** Not one §11–§16 statement needed the dual pair to be relaxed: `pairing n` discharges
every pairing class by instance search, and the only recurring friction is cosmetic — a backbone
statement hands back `B.flip` where the surface wants `B`, which six `*_flip_pairing` rewrites in
the shared header absorb. The adjoint decision holds too, for a reason the plan did not predict:
remediation §4.1 proposed bundling the adjoint into a class because "~100 statements thread `(A')`
plus `IsAdjointPair`", but the *surface* pays none of that — `isAdjointPair_adjoint` already exists
in `Duality/Pairing.lean` for `innerₗ E`, so §16 writes every `A*` as `LinearMap.adjoint A` and
carries no adjoint hypothesis at all. What remains of §4.1 is backbone-internal.

The three sections whose gates were closed before the round — §14 (bundled bipolar), §15
(`IsNorm.toSeminorm`), §16 (the `m`-ary Theorem 16.4) — report that the gates worked: no §14
statement discharges the cone hypothesis triple by hand, and §16 did no induction over `□`.

**Part IV — all six sections written**, 177 declarations for 65 of the Part's 70 numbered results.

| § | module | declarations | labels |
|---|---|---|---|
| 17 | `Part4/Section17.lean` | 27 | 10 |
| 18 | `Part4/Section18.lean` | 43 | 16 |
| 19 | `Part4/Section19.lean` | 38 | 17 |
| 20 | `Part4/Section20.lean` | 19 | 8 |
| 21 | `Part4/Section21.lean` | 27 | 10 |
| 22 | `Part4/Section22.lean` | 23 | 4 of 9 |

The five absent labels are all in §22 and all one item: **Lemmas 22.4 and 22.5, Corollary 22.4.1,
and Theorems 22.6 and 22.7**, the elementary-vector development and Tucker's complementarity
theorem. They are *deferred by scope* — elementary vectors are the minimal-support vectors of a
subspace and their theory is combinatorial matroid theory, which the book itself presents as
independent of all convexity theory. **This is the only place in §§1–22 where a label is absent for
a reason other than a named backbone gap**, and it is the first time the scope rule has bitten.
Theorems 22.1–22.3 and Farkas' Lemma are here.

Two of the round's findings are worth promoting out of the remediation list:

* **Corollaries 17.1.4 and 17.1.6 are false as Rockafellar states them, and §17 refutes them in
  Lean** rather than dropping them — `corollary_17_1_4_false`, `corollary_17_1_6_false`, both on
  `ℝ¹`. This is the *stated and refuted* category of the alignment checklist §3, and Part IV is
  what it was written for.
* **Theorem 20.5 supplies `LocallySimplicial` instances; it does not repair §10.** The Part II
  finding is confirmed from the §20 side, and by a stronger route: `Polyhedral.locallySimplicial`
  takes a coordinate cube for the neighbourhood and produces the simplices explicitly, so it never
  makes the appeal to Carathéodory's count that the book asserts without proof.

Across §§1–22, **268 of the 280 numbered results have declarations**. Of the twelve that do not,
five are §22's scope deferral above and seven are blocked on a named backbone gap: Corollaries
9.2.1 and 9.8.3, Theorems 14.3 and 14.4, and Lemma 16.2 with Corollaries 16.2.1 and 16.2.2. What
the round found is in
[`../../backbone/08-remediation.md`](../../backbone/08-remediation.md) §11.
