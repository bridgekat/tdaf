# Sub-plan 8 — Remediation

Work created by the plan review of 2026-08, run as five independent adversarial reviewers over the
completed backbone (112 modules, 3 161 theorems). Ordered by **value / cost**, which is not the
order of importance: the cheapest items are first because they unblock the reading of everything
else.

Nothing here is new mathematics. Every item is either a defect the review found, or a piece of
scaffolding the surface library will otherwise pay for per-statement.

---

## Status

| item | state |
|---|---|
| §1.1 delete seven `flip.flip` workarounds | **done** |
| §1.2 the `(innerₗ E).flip` instances | **done, and the item was wrong** — see below |
| §1.3 promote `isCompatiblePairing_neg` | **done** — now four instances in `Duality/Pairing.lean` |
| §1.4 relocate `isMaximalMonotoneRel_subgradientRel` | **not done, and cannot be** — see below |
| §1.5 `Eponyms.lean` | **done** — nine aliases |
| §1.6 delete `partialConj₂` | **not done, deliberately** — D8 amended instead |
| §2.1 `saddleSwap` transport | **done** — 58 duplicated proof lines → 17; see the correction below |
| §3 `closedsOrderIso` | **done** — plus three instantiations; D12 amended |
| §4.2 `negFst` pairing instances | **done** — this was the `Setup.lean` blocker, and it is closed |
| §4.9 the reduction to lines | **done** — `Analysis/Convex/Line.lean`, with the converse too (§8.2) |
| §8.1 Jensen out of the subgradient tower | **done** — moved to `Epigraph.lean` |
| everything else | open |

Three items were **wrong as written**, and the corrections matter more than the items did.

**§1.2 was already general.** The claim was that a surface `Setup.lean` importing only `Duality/*`
could not see `IsContinuousPairing ((innerₗ E).flip)`, which is declared in
`Subgradient/StrictlyConvex.lean`. But `Duality/InnerPairing.lean` already carries
`isContinuousPairing_flip_of_isContinuousInnerPairing` and
`isCompatiblePairing_flip_of_isInnerPairing`, which cover it for *any* symmetric pairing — verified
by typechecking against that import alone. The two declarations in `StrictlyConvex.lean` were
duplicates of the general instances, not the only copies. Deleted.

**§1.4 is an import cycle.** `isMaximalMonotoneRel_subgradientRel` belongs by subject in
`Subgradient/Monotone.lean`, beside `IsMaximalMonotoneRel`. It cannot go there: its proof *is*
Moreau's theorem, and `Optimization/Prox.lean` imports `Subgradient/Monotone.lean`. The alias
`subgradient_maximalMonotone` plus a pointer in that file's "what is not here" is the whole
available remedy, and it is enough — the complaint was discoverability, not location.

**§1.6 would have removed the only precise statement of D8.** `partialConj₂` has no consumer outside
its own file, which is what the audit found and is true. But it is the *uncurried* reading of
`bracket`, and `partialConj₂_graphFn` — which is `rfl` — is what makes D8's claim that the bracket,
the Lagrangian, `cl₁`/`cl₂` and the adjoint are one operation into something checkable rather than
rhetoric. Deleting it would leave the claim and remove its proof. D8 is amended instead, to say the
operation is realised on bifunctions as `bracket`, which is what the development is written against.

**The instantiation checklist is closed.** All four gaps the review predicted for the surface's
ambient setting are gone, and `Tdaf/Surface/Common/Euclidean.lean` asserts all 31 classes as a
regression test. One of the four (`SeparatingDual ℝ (Rn n)`) was never missing.

---


## 1. Twenty-minute items

| # | item | where | note |
|---|---|---|---|
| 1.1 | Delete seven `flip.flip` workarounds | `Saddle/Conjugate.lean:241`, `Saddle/Minimax.lean:1311`, `Saddle/Subgradient.lean:647,648`, `Bifunction/Cofinite.lean:184`, `Polyhedral/Closedness.lean:137`, `Subgradient/Approx.lean:419` | `instIsCompatiblePairingFlipFlip` was added after the idiom took hold; bare `inferInstance` discharges all seven (verified) |
| 1.2 | Move `IsContinuousPairing ((innerₗ E).flip)` | from `Subgradient/StrictlyConvex.lean:312` to `Duality/InnerPairing.lean` | a surface `Setup.lean` importing only `Duality/*` cannot see it, and the failure reads as a missing instance rather than a missing import |
| 1.3 | Promote `isCompatiblePairing_neg` to an instance and relocate | from `Saddle/Minimax.lean:739` to `Duality/Pairing.lean` | consumers hand-roll it at `Saddle/Existence.lean:379–381`, `Saddle/Minimax.lean:855–856,873–874`; every surface §34/§37 statement would repeat those `have`s |
| 1.4 | Relocate `isMaximalMonotoneRel_subgradientRel` | from `Optimization/Prox.lean:435` to `Subgradient/Monotone.lean` | it is the theorem D10 itself advertises as `subgradient_maximalMonotone`, filed away from the predicate it is about |
| 1.5 | Add `Eponyms.lean` (or `alias` lines in place) | new | `fenchel_moreau := biconj_eq_clFn`, `fenchel_inequality := Proper.le_add_conj`, `minkowski_weyl := polyhedralCone_iff_finitelyGeneratedCone`, `krein_milman := convexHull_extremePoints`, `caratheodory := mem_convexHull_iff_exists_fin_finrank_succ`, `moreau_decomposition := moreau_add`, `subgradient_maximalMonotone := isMaximalMonotoneRel_subgradientRel`, `perspective := smulRight` |
| 1.6 | Delete `partialConj₂` | `Saddle/Defs.lean:206` | D8 calls it "the organizing operation" of Parts VI–VIII; it has **zero consumers outside its own file**. `bracket` (260 occurrences, 12 files) is the real operator. Either delete it or make it the definition of `bracket` — carrying a dead definition the plan advertises as load-bearing is worse than carrying none. **Amend D8 either way.** |

The naming test (§4.1 test 3) scored 53% on first guess before 1.5; the misses were all eponyms.

---

## 2. Symmetry work (D11)

### 2.1 The one large win: `saddleSwap` over `Kernel.lean`'s SimpleExt block

`Saddle/Kernel.lean` uses `saddleSwap` 106 times and states the policy in its own docstring at
`:454` — and then the entire upper-simple-extension block re-proves the lower one line for line,
with **zero** uses of it:

| lower | upper | duplicated |
|---|---|---|
| `Kernel.lean:1710–1881` | `Kernel.lean:1925–2065` | 141 lines |
| `partialCl₁_lowerSimpleExt :2096` | `partialCl₂_upperSimpleExt :2115` | 18 |
| `lowerClosedFn_lowerSimpleExt :2349` | `upperClosedFn_upperSimpleExt :2358` | 25 |

`lowerSimpleExt_slice₂_of_mem` (`:1732`) and `upperSimpleExt_slice₂_of_mem` (`:1947`) are
character-for-character identical bar the definition name.

Everything follows from **one** dictionary entry, verified compiling:

```lean
/-- The real-valued companion of `saddleSwap`. -/
def swapReal (K : U × X → ℝ) : X × U → ℝ := fun q => -K (q.2, q.1)

theorem upperSimpleExt_eq_saddleSwap (C : Set U) (D : Set X) (K : U × X → ℝ) :
    upperSimpleExt C D K = saddleSwap (lowerSimpleExt D C (swapReal K)) := by
  funext p
  obtain ⟨u, x⟩ := p
  by_cases hx : x ∈ D <;> by_cases hu : u ∈ C <;>
    simp [upperSimpleExt, lowerSimpleExt, saddleSwap, swapReal, hu, hx]
```

**Done.** And the headline number was wrong: 184 → 61 counted statements and docstrings as
duplication. What was actually duplicated was four proofs — `dom₁_upperSimpleExt` (13 lines),
`dom₂_upperSimpleExt` (13), `concaveConvexFn_upperSimpleExt` (14) and `partialCl₂_upperSimpleExt`
(18) — which come to **58 proof lines, now 17**. The four slice lemmas and
`mem_saddleClass_simpleExt_iff` are two-line `simp` calls either way and are left alone; the
`lowerClosedFn`/`upperClosedFn` pair was already two lines each. Net file size is unchanged, because
the 41 lines saved are spent on `swapReal`, the dictionary entry and their docstrings.

The line count was never the point, and the real result stands: **the transported hypotheses come
out identical to the re-proved ones**, so no caller changed, and Part VII now has *one*
orientation-flipping lemma to cite instead of two parallel developments to keep aligned. This is the
leak-free transport that §2.2 is about, and it is the template D11 asks for.

### 2.2 De-leak `reflect`'s mirror statements

`Bifunction/Process.lean`'s `reflect` is the best instance of D11 in the library: one involution,
intertwining lemmas for every operation, and then Thms 39.5/39.8 infimum-oriented as three-line
rewrites, and the whole `coBracket` section running off one sign lemma.

But **eight public theorems carry `.reflect` in their hypotheses** — `coadjointProcess_add`
(`:1766`), `coadjointProcess_comp` (`:1780`), `add_eq_coadjointProcess_add` (`:1811`),
`isClosed_graph_add` (`:1825`), `graph_adjointProcess_add_eq_closure` (`:1855`),
`comp_eq_coadjointProcess_comp` (`:1886`), `isClosed_graph_comp` (`:1901`) and
`graph_adjointProcess_comp_eq_closure` (`:1934`). The docstring of the first claims that
`eval_reflect` translates the hypothesis into a statement about `A₁` and `A₂` themselves; it does
not — three lines below, the hypothesis still reads `A₁.reflect.eval u` — and a caller of the
infimum-oriented Theorem 39.5 must reason about the reflection to discharge it. Push `eval_reflect` through
the hypotheses. Until this is done `reflect` is not a template anyone should copy.

### 2.3 Bundle the involutions

`reflect` and `saddleSwap` are bare `def`s. Bundle at the point of definition:

* `ConvexProcess.reflect` — additive, involutive, closedness-preserving ⇒ `AddAut`, or at minimum
  `Function.Involutive`, giving `.injective`/`.eq_iff`/`.toPerm` free.
* `saddleSwap` — involutive (`Closure.lean:135`) **and antitone** (`Existence.lean:119`) ⇒
  `OrderIso … ᵒᵈ`. Then `saddleSwap_injective` (`:138`, hand-proved) is `Equiv.injective`.

### 2.4 Sign symmetry (D2)

Small and cheap; do **not** expect a large payoff. Measured honestly: ~40 declarations collapse to
≤3-line forwards, **130–170 proof lines removed — 0.6% of the library**.

1. Add `neg_coe_add`, `neg_add_coe`, `neg_coe_sub` to `Order/EReal.lean`. These retire a five-token
   incantation at 17 sites and subsume the *private* copy someone already wrote at
   `Optimization/Normal.lean:766` instead of putting it where D2 asked.
2. Restate the sign dictionaries at object level: `concaveConj_eq`, `concaveSubgradient_eq_neg`,
   `ClosedConcaveFn` ↔ `ClosedFn (-·)`.
3. Fix the dozen proofs that re-derive a convex theorem sitting a few hundred lines above them —
   `ConcavePolyhedralBifun.concaveNormal` (`Normal.lean:1016`) does not call
   `PolyhedralBifun.normal` (`:1004`); `concaveNormal_of_concaveKuhnTucker_nonempty` (`:948`) does
   not call `normal_of_kuhnTucker_nonempty`; `continuousAt_comp_line_of_concaveOn`
   (`Saddle/Differential.lean:186`) is character-for-character its convex twin at `:176`.

**Order matters.** `Optimization/Fenchel.lean` and `Bifunction/Algebra.lean` hold the nine genuinely
conditional `neg_add` sites, and `@[simp]`-tagging `neg_coe_add`/`neg_coe_sub` changes the normal
form of every `⟨x,y⟩ - f x` in them. Migrate those two **last and separately**, or leave the new
lemmas un-tagged and cite them explicitly.

### 2.5 What the review says to leave alone

Recorded so it is not re-litigated: the **pairing transpose** (already exploited — not one theorem
is stated twice), **`partialInvertEquiv`** (already done right), **min/max** (§32 maximises a convex
function and is not §27's dual; `Maximum.lean` contains no `argmax`; the only real pair is four
declarations whose bridge already exists), and **`Left`/`Right` in `Bifunction/Algebra.lean`**
(misleading names — two different projections of one change of variables, no involution). And do
**not** build a Lean class abstracting "involution intertwining a family of operations": see D11.

---

## 3. Order-theoretic duality (D12)

Add `GaloisConnection.closedsOrderIso` — *a Galois connection restricts to an order isomorphism
between the closed elements* — which Mathlib lacks (`ClosureOperator.gi` is only the one-sided
`GaloisInsertion`). Twelve lines, verified compiling, upstreaming candidate:

```lean
def GaloisConnection.closedsOrderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    {a : α // u (l a) = a} ≃o {b : β // l (u b) = b} where
  toFun a := ⟨l a.1, gc.l_u_l_eq_l a.1⟩
  invFun b := ⟨u b.1, gc.u_l_u_eq_u b.1⟩
  left_inv a := Subtype.ext a.2
  right_inv b := Subtype.ext b.2
  map_rel_iff' {a a'} := by
    show l a.1 ≤ l a'.1 ↔ a.1 ≤ a'.1
    refine ⟨fun h => ?_, fun h => gc.monotone_l h⟩
    have := gc.monotone_u h
    rwa [a.2, a'.2] at this
```

Then: replace the hand proofs of `subset_polarCone_polarCone` (`Duality/Polar.lean:200`),
`polarCone_polarCone_polarCone` (`:253`) and `conj_biconj` (`Duality/Conjugate.lean:534`) by
`GaloisConnection.le_u_l` / `l_u_l_eq_l`, and re-express the six longhand bijections — `conjEquiv`,
`gaugeEquiv`, `polarFnEquiv`, `polarGaugeEquiv`, `supportEquiv`, `bifunSaddleEquiv` — as
`closedsOrderIso` instances. The line saving is small; the point is that the `gc_*` and
`ClosureOperator` objects are currently **inert** (each referenced only by its own `_apply` and
`isClosed_…_iff`), which makes the README's "reuse Mathlib vocabulary" satisfied on paper only.

Also fix `supportEquiv`'s docstring (`Duality/Support.lean:585`), which says it "is the restriction
of `conjEquiv` along the two embeddings" and then rebuilds the bijection from scratch. Either do it
or stop claiming it.

---

## 4. Scaffolding the surface will otherwise pay for per-statement

Ordered by how many surface statements each one taxes.

| # | item | tax if not done |
|---|---|---|
| 4.1 | **Bundle the adjoint.** A `class HasTranspose B B' A` / bundled `AdjointPair` with the finite-dimensional inner-product instance, so instance search supplies `A'` | ~100 statements across §16, §19, §30, §31, §38, §39 each thread `(A')` plus `IsAdjointPair` that the book writes as `A*`. **Largest single friction, and on both future surfaces' critical path** |
| 4.2 | **`negFst (prodPairing Bu Bx)` pairing-class instances.** Prove the `LinearMap` equation `negFst (prodPairing Bu Bx) = prodPairing (-Bu) Bx` — only the *pointwise* identity exists (`Duality/Pairing.lean:326`) — then derive the instances via `isCompatiblePairing_neg` | §30's adjoint bifunctions conjugate against `negFst`. **Most likely `Setup.lean` blocker** |
| 4.3 | **Bipolar theorem for `PointedCone`.** `polarCone_polarCone` takes three unbundled hypotheses (`Convex`, `∀ a > 0, a • K = K`, `Nonempty`); the pattern recurs 26 times | three hypothesis discharges per §14 surface statement, when a `PointedCone` argument would carry them |
| 4.4 | **`m`-ary `infConv` and `IsExactSum`** over a `Finset` | Thms 16.4, 20.1, 23.8, 31.x are stated for `f₁ □ ⋯ □ f_m`; the surface must induct and re-derive properness at each step |
| 4.5 | **Separable sums** over a finite product, with `conj (sepSum f) = sepSum (conj ∘ f)` | §16's separable rows and §38 |
| 4.6 | **Theorem 27.1(e)** restated under `[IsCompatiblePairing B] [IsCompatiblePairing B.flip]` | currently excluded as "needs a reflexive pairing"; `ℝⁿ` *is* reflexive, so the surface demands it and cannot get it |
| 4.7 | **`IsNorm k → ∃ p : Seminorm ℝ E, ∀ x, k x = p x`** at layer D | §15; the bridge is declined at `Duality/Gauge.lean:127` on layer-C grounds that do not apply on `ℝⁿ` |
| 4.8 | **`Rn m × Rn n ≃ₗᵢ Rn (m+n)`** with transport for `conj`, `subgradient`, `ri` | Rockafellar moves freely between `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ` in §29, §30, §37 |
| 4.9 | ~~**`convexOn_iff_convexOn_lines`**~~ **done** | Thms 4.4/4.5. The *concave* half existed, buried at `Saddle/Differential.lean:162`. Both now live in `Analysis/Convex/Line.lean`, together with the converse `convexOn_iff_lines` — which is the half that makes the reduction useful and which neither the review nor the plan had noticed was missing |
| 4.10 | Bundle layer D's typeclass triple | `[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` is spelled out in ~74 files; bundling makes a later relaxation one edit |

**Two obligations the old surface plan listed are struck**, not scheduled:

* *"Prove `clFn` agrees with the book's `cl f` on `ℝⁿ`"* — **already discharged in the backbone**,
  `ConvexFn.clFn_eq_lscHull` (`RelativeInterior.lean:1131`). Do not re-prove it on the surface.
* *"Supply a `(-∞,+∞]`-valued function interface via `WithTop ℝ`"* — **do not build it.**
  `Proper.ne_bot` already renders Rockafellar's phrase faithfully; a second carrier type buys
  cosmetic fidelity and costs an `Equiv` round-trip in every statement touching `conj`, `ofEpi` or
  `infConv` — which the old plan's own text explains cannot be defined on `WithTop ℝ` anyway.

---

## 5. D10 hygiene

| # | item | count | risk |
|---|---|---|---|
| 5.1 | Rename `section` names that are book numbers | **142** | none — sections are not namespaces here; no proof churn, no name resolution impact. `section Thm382` → `section AdjointComposition`, `section Corollary1461` → `section PolarDimension` |
| 5.2 | Rewrite module docstring first lines | **73 of 112** open with "Rockafellar's §N" | none — move the citation into the existing `## References` block. The compliant minority (`Duality/Barrier.lean`, `Concave.lean`) is the template |
| 5.3 | Rename 6 module titles carrying book numbering | 6 | low |
| 5.4 | Merge two single-corollary modules | `Optimization/ConeDuality.lean` (titled "Corollary 31.4.3") into `Optimization/Fenchel.lean`; `Polyhedral/Homogeneous.lean` (titled "Corollary 19.1.2 for functions") into `Polyhedral/Function.lean` | low |
| 5.5 | Add `## References` to the 10 modules lacking one | 10 | none — `Tdaf/Order/EReal.lean` legitimately has no book source; give it a one-line note so the absence is deliberate |
| 5.6 | Rename Rockafellar-only vocabulary | `obverse` (`Duality/Gauge.lean:1728`), `SimpleSaddleFn` (`Saddle/Kernel.lean:1355`), `bracket`/`concaveBracket` (`Saddle/Defs.lean:293,484`), `HasFenchelPairing` (`Bifunction/Algebra.lean:903`) | medium — these are used widely; do as one mechanical rename each, keeping the book's word in the docstring |

5.1 is the highest compliance-per-risk item in this document and was not previously on the plan's
radar: D10 checked module and declaration names, but a `section` name is what a file outline shows.

---

## 6. Move list — backbone → surface

Each of these fails test 2 or 3 of [§4.1](../00-overview.md#41-the-test).

| declaration | from | to |
|---|---|---|
| `polarCone_nonnegOrthant`, `section Orthant` | `Duality/Polar.lean:719–744` | Surface §14 — the only `EuclideanSpace`-typed statement in the backbone, zero uses |
| `programLagrangian`, `IsKuhnTuckerVector`, `feasibleSet`, `optimalValue` | `Optimization/Program.lean:71,83,93,107` | Surface §28 — they duplicate `lagrangian` and `KuhnTucker`, and their own docstrings say so. Keep the *theorem* `exists_isKuhnTuckerVector_of_slater` in the backbone, restated against `lagrangian` |
| `powHalfLine`, `monotoneConj_powHalfLine`, `PosHomogeneousDeg`, `degGauge`, `posHomogeneousDeg_iff_exists_isGauge`, `polarGauge_degGauge`, `pairing_le_rpow_mul_rpow` | `Duality/GaugeLike.lean:888–1322` | Surface §15 — this is Young's inequality read as conjugacy, i.e. Cors 15.3.1/15.3.2. Keep `MonotoneHalfLineFn`, `monotoneConj`, `monotoneComp`, `conj_monotoneComp`: half-line conjugacy is general and B&C will want it |
| `fenchelPairing` | `Bifunction/Algebra.lean:910` | Surface §38 notation — `:= fenchelInf B f g`, an alias for Rockafellar's `⟨f, g⟩` |

**Watch `Duality/GaugeLike.lean` as a whole**: 1 676 lines, and none of its nine public names is
used outside the file. Either name a downstream consumer or move more of it.

---

## 7. Sequencing

1. §1 (twenty-minute items) — unblocks reading; do first, one commit each.
2. §5.1 and §5.2 (mechanical D10 hygiene) — large surface area, zero risk, and they make everything
   below easier to review.
3. §3 (`closedsOrderIso`) — one lemma, then the substitutions.
4. §2.1–§2.3 (`saddleSwap` transport, `reflect` de-leak, bundling) — the real symmetry work.
5. §4.1 and §4.2 (adjoint bundling, `negFst` instances) — **must precede any surface work**; 4.2 is
   the likely `Setup.lean` blocker and 4.1 taxes ~100 surface statements.
6. §6 (move list) — do *with* the corresponding surface section, not before it exists.
7. §2.4 (sign symmetry), §4.3–§4.10 — as the surface sections that need them come up.
8. §5.6 (renames) — last, since they touch the most call sites.

Items 5 and 6 are the ones with a hard ordering constraint against the surface. Everything else can
be done in any order, or dropped, without blocking.

**§8 is the empirical version of this list** and supersedes it where the two disagree: it records
what the Part I surface agents actually hit, and it demoted §4.4 (the `m`-ary `infConv`) off §5's
critical path while promoting three `Homogenize.lean` gaps nobody had predicted. Schedule §8 items
the same way as §6 — with the surface section that wants them, not ahead of it.

---

## 8. Gaps reported by the Part I surface round

These are not from the review worktrees; they are what the four §1–§5 surface agents actually hit
while writing statements against the backbone. Each was worked around locally (a `private` lemma or
a `Rockafellar.*` helper in the surface file), so nothing here blocks; each is a place where the
backbone made a surface proof longer than the brief's "a few lines".

| # | item | reported by | status |
|---|---|---|---|
| 8.1 | **Jensen was in `Subgradient/Gradient.lean`.** Its proof is one `Convex.sum_mem` on `epi f`; a surface module wanting only Theorem 4.3 had to import the whole subgradient tower | §4 | **done** — moved to `Epigraph.lean` |
| 8.2 | **The reduction to lines** — `convexOn_iff_lines` and the step-set lemmas | §4 | **done** — `Analysis/Convex/Line.lean`, with the converse that §4.9 did not ask for |
| 8.3 | **`ConvexFn.sum_le'`, the `EReal`-valued Jensen.** The book's `∑ λᵢ f(xᵢ)` needs `0 · ∞ = 0` where `λᵢ = 0` and `f xᵢ = ⊤`; §4 filters to `{i | λᵢ ≠ 0}` by hand, 25 lines, its longest proof | §4 | open |
| 8.4 | **The second-derivative-along-a-line group.** Rockafellar's "a straightforward calculation" `g''(λ) = ⟨z, Q_x z⟩` is seven `private` lemmas in §4 (`hasDerivAt_line`, `hasFDerivAt_of_contDiffOn`, `hasFDerivAt_fderiv_of_contDiffOn`, `hasDerivAt_comp_line`, `deriv_comp_line_eventuallyEq`, `hasDerivAt_deriv_comp_line`) | §4 | open |
| 8.5 | **`convexFn_restrict_iff_le`.** `convexFn_iff_le` is the `C = ℝⁿ` case only; lifting to the book's "function from `C`" via `restrict` cost §4 eighteen lines of `⊤`-absorption | §4 | open |
| 8.6 | **The finite-family `∑ᵢ wᵢ • C = (∑ᵢ wᵢ) • C`** for convex nonempty `C`, which Theorem 3.3 needs — four private helpers, ~70 lines, the only long proof in §3 | §3 | open |
| 8.7 | **The set-level inverse sum `#` does not exist.** `Operations/InfConv.lean` is entirely function-level and its set-level shadow is ordinary `+`. `invSum` is a genuine surface definition | §3 | open — surface definition, may stay one |
| 8.8 | **`Homogenize.lean` has no properness lemmas.** `hom f q ≠ ⊥` for proper `f` written as `Rockafellar.hom_ne_bot`; needed by Theorem 5.8(g) | §5 | open |
| 8.9 | **`hom f (a, a • z) = a * f z` for `a ≥ 0`** — `Rockafellar.hom_apply_smul`; belongs beside `hom_apply_nonneg` | §5 | open |
| 8.10 | **No slice lemma** `ConvexFn G → ConvexFn (fun x => G (c, x))` for `G : ℝ × E → EReal`; used by three clauses of Theorem 5.8. Belongs beside `ConvexFn.comp_add_left` | §5 | open |
| 8.11 | **Convexity of an abstract linear functional as an `E → EReal`** exists only for pairing-presented functionals (`convexFn_affineFn`) | §5 | open |
| 8.12 | **`InfConvFn`'s `Finset.sum` is not connected to the `m`-ary infimum formula.** The bridge wanted is `ofInfConvFn (∑ toInfConvFn fᵢ) = mapLin sumLin (∑ᵢ fᵢ ∘ projᵢ)`. Note the obvious induction **cannot** work: properness is not preserved by `□`, so `infConv_apply` cannot be re-applied to a partial convolute | §5 | open — refines §4.4 |
| 8.13 | **No bridge from `Duality/Gauge.lean`'s gauge to `posHomGen (δ(·|C) + 1)`.** `Gauge.lean` takes the *computed* formula `inf {λ ≥ 0 \| x ∈ λC}` as the definition, so §5's identification of the gauge as a positively homogeneous generation is not statable | §5 | open |
| 8.14 | **`span ℝ K = K - K` for a convex cone containing `0`.** Theorem 2.7's `K - K = aff K` half; `Recession/Cone.lean:321` covers only the lineality half, and only for recession cones. §2 proved it in 18 lines by `Submodule.span_induction` | §2 | open |
| 8.15 | **`vectorSpan_eq_span_of_zero_mem` is buried in `Duality/Gauge.lean`**, which `Surface/Common/Euclidean.lean` does not reach. It is the backbone's Theorem 1.1 and belongs in a low-level module | §1 | open |
| 8.16 | **`Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` is not reachable from `Surface/Common/Euclidean.lean`** — `AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one` is an unknown constant. §1 imports it explicitly; §§17–19 will want it too | §1 | open — belongs in the shared surface header, not the backbone |
| 8.17 | **Nothing extends a linear isomorphism between two subspaces to an automorphism of the ambient space.** Written as `exists_linearEquiv_extend` / `exists_linearEquiv_apply_eq`, ~25 lines from `Submodule.prodEquivOfIsCompl`, `LinearEquiv.ofFinrankEq` and `Submodule.isCompl_orthogonal`. Theorem 1.6 and Corollary 1.6.1 both rest on it, and it is the most expensive thing in either §1 or §2 | §1 | open |

### Two things the round *un*-scheduled

* **§4.4's `m`-ary `infConv` is not on §5's critical path after all.** Theorem 5.4's literal m-ary
  form `inf {f₁x₁ + ⋯ + fₘxₘ | ∑ xᵢ = x}` *is* the image `mapLin sumLin (∑ᵢ fᵢ ∘ projᵢ)`, so
  Theorem 5.7 closes it in five lines — and the same route handles all four clauses of Theorem 5.8.
  §5 therefore has **no dependency on §3's partial addition**, contrary to the plan.
* **`Operations/*` is entirely function-level, so part1.md is wrong that §3 specialises it.** §3 is
  set algebra; all nine of its results specialise *Mathlib*.

### Book findings from the round

* **Theorem 3.8's second equation `K₁ # K₂ = K₁ ∩ K₂` does not need convexity** — closure under
  positive scaling plus `0 ∈ K` suffices.
* **The book's coefficient `(α₁⁻¹ + α₂⁻¹)⁻¹` for the inverse sum of vectors is wrong under Lean's
  `0⁻¹ = 0`** (it gives `α₂` at `α₁ = 0`); the book's own parenthetical caveat is load-bearing.
  `invSum_singleton_smul` uses `α₁α₂/(α₁+α₂)`, which is correct throughout.
* **Theorem 4.8's basis clause is false for `L = {0}` with an empty basis** — a positively
  homogeneous proper convex `f` may have `f 0 = +∞`. The backbone already carries the nonemptiness
  hypothesis; the surface states it.
* **Theorem 1.3's second sentence is false in `ℝ⁰`.** There `∅` has dimension `-1 = n - 1`, so it
  *is* a hyperplane, but no non-zero `b` exists to represent it. `theorem_1_3_exists` carries
  `0 < n`.
* **Theorem 2.4 needs `C.Nonempty`** — for `C = ∅` the set of simplex dimensions is empty and has
  no maximum.
