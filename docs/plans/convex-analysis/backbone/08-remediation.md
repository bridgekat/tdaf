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
| 4.3 | ~~**Bipolar theorem for `PointedCone`**~~ **done** | `polarCone_polarCone_pointedCone` already existed; the three companions did not. `Duality/Polar.lean` now has the whole Theorem 14.1 family in bundled form — `…_pointedCone`, `…_pointedCone_eq_closure`, `neg_polarCone_neg_polarCone_pointedCone`, `conj_indicatorFn_polarCone_pointedCone` — and the module docstring says to use them rather than discharge the triple by hand |
| 4.4 | **`m`-ary `infConv` and `IsExactSum`** over a `Finset` | Thms 16.4, 20.1, 23.8, 31.x are stated for `f₁ □ ⋯ □ f_m`; the surface must induct and re-derive properness at each step |
| 4.5 | **Separable sums** over a finite product, with `conj (sepSum f) = sepSum (conj ∘ f)` | §16's separable rows and §38 |
| 4.6 | **Theorem 27.1(e)** restated under `[IsCompatiblePairing B] [IsCompatiblePairing B.flip]` | currently excluded as "needs a reflexive pairing"; `ℝⁿ` *is* reflexive, so the surface demands it and cannot get it |
| 4.7 | ~~**`IsNorm k → ∃ p : Seminorm ℝ E, ∀ x, k x = p x`**~~ **done, and not at layer D** | `IsNorm.toSeminorm` in `Duality/Gauge.lean`, at layer **A**. Mathlib's `Seminorm` is purely algebraic — it asks nothing about a topology — so the old "not here" note declined it on grounds that belong to `NormedSpace` and to nothing else. `IsNorm.apply_smul` (absolute homogeneity, which positive homogeneity does not give) is the one step that needed proving |
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
| 8.8 | **`Homogenize.lean` has no properness lemmas.** `hom f q ≠ ⊥` for proper `f` written as `Rockafellar.hom_ne_bot`; needed by Theorem 5.8(g) | §5 | **closed** — `hom_ne_bot` in `Homogenize.lean`, hypothesis weakened to `∀ x, f x ≠ ⊥` |
| 8.9 | **`hom f (a, a • z) = a * f z` for `a ≥ 0`** — `Rockafellar.hom_apply_smul`; belongs beside `hom_apply_nonneg` | §5 | **closed** — `hom_apply_smul` in `Homogenize.lean` |
| 8.10 | **No slice lemma** `ConvexFn G → ConvexFn (fun x => G (c, x))` for `G : ℝ × E → EReal`; used by three clauses of Theorem 5.8. Belongs beside `ConvexFn.comp_add_left` | §5 | **closed** — `ConvexFn.comp_affine` and `ConvexFn.slice_left` / `.slice_right` in `Operations/Image.lean` |
| 8.11 | **Convexity of an abstract linear functional as an `E → EReal`** exists only for pairing-presented functionals (`convexFn_affineFn`) | §5 | **closed** — `convexFn_coe_linearMap` in `Operations/Basic.lean` |
| 8.12 | **`InfConvFn`'s `Finset.sum` is not connected to the `m`-ary infimum formula.** The bridge wanted is `ofInfConvFn (∑ toInfConvFn fᵢ) = mapLin sumLin (∑ᵢ fᵢ ∘ projᵢ)`. Note the obvious induction **cannot** work: properness is not preserved by `□`, so `infConv_apply` cannot be re-applied to a partial convolute | §5 | open — refines §4.4 |
| 8.13 | **No bridge from `Duality/Gauge.lean`'s gauge to `posHomGen (δ(·|C) + 1)`.** `Gauge.lean` takes the *computed* formula `inf {λ ≥ 0 \| x ∈ λC}` as the definition, so §5's identification of the gauge as a positively homogeneous generation is not statable | §5 | open |
| 8.14 | **`span ℝ K = K - K` for a convex cone containing `0`.** Theorem 2.7's `K - K = aff K` half; `Recession/Cone.lean:321` covers only the lineality half, and only for recession cones. §2 proved it in 18 lines by `Submodule.span_induction` | §2 | **closed** — `span_eq_sub_of_isCone` in `Homogeneous.lean`, at layer A |
| 8.15 | **`vectorSpan_eq_span_of_zero_mem` is buried in `Duality/Gauge.lean`**, which `Surface/Common/Euclidean.lean` does not reach. It is the backbone's Theorem 1.1 and belongs in a low-level module | §1 | **closed** — `Tdaf/LinearAlgebra/Subspace.lean`, generalised to an arbitrary field |
| 8.16 | **`Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` is not reachable from `Surface/Common/Euclidean.lean`** — `AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one` is an unknown constant. §1 imports it explicitly; §§17–19 will want it too | §1 | **closed** — added to `Surface/Common/Euclidean.lean` |
| 8.17 | **Nothing extends a linear isomorphism between two subspaces to an automorphism of the ambient space.** Written as `exists_linearEquiv_extend` / `exists_linearEquiv_apply_eq`, ~25 lines from `Submodule.prodEquivOfIsCompl`, `LinearEquiv.ofFinrankEq` and `Submodule.isCompl_orthogonal`. Theorem 1.6 and Corollary 1.6.1 both rest on it, and it is the most expensive thing in either §1 or §2 | §1 | **not a gap** — it is Mathlib’s `Submodule.exists_linearEquiv_restrict_eq`; §1 now calls it and the 25-line re-proof is deleted (`gotchas.md` DEP4) |

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

---

## 9. Gaps reported by the Part II surface round

The §6–§10 round, run the same way. Nothing here blocked a section: §6, §7, §8 and §10 are
complete, and §9 is 16 of 18 — Corollary 9.2.1 and Corollary 9.8.3 are the two entries below marked
**blocking**, and they are the only two labels in Parts I–II with no declaration.

| # | item | reported by | status |
|---|---|---|---|
| 9.1 | **Corollary 6.3.3 has no backbone declaration.** `Face.lean` has only the face-specific shadow (`IsFace.affineSpan_ne`, `IsFace.finrank_vectorSpan_lt`). §6 wrote `inter_relint_nonempty_of_affineSpan_eq` (12 lines) plus a 20-line corollary. Both belong in `RelativeInterior.lean`, with `Face.lean` routing through them | §6 | open |
| 9.2 | **Theorem 6.9 is two-set only** — `Convex.relint_convexHull_union`. The book states it for `m` sets | §6 | open |
| 9.3 | **No affine-map form of Theorems 6.6/6.7.** `Convex.relint_image` / `relint_preimage` take a `LinearMap`, so the book's "the same holds for affine transformations" is not statable | §6 | open |
| 9.4 | **`Convex.relint_cone_prodMk_one` is stated about `K ∪ {0}`**, but Rockafellar's cone in Corollary 6.8.1 excludes the origin; §6 re-derived `ri K = ri (K ∪ {0})` in 20 lines | §6 | open — friction |
| 9.5 | **Corollary 6.5.1 takes an `AffineSubspace ℝ E`, the book an affine set**; each clause needs an `IsAffineSet.toAffineSubspace` wrapper | §6 | open — friction |
| 9.6 | **No backbone `dim`.** `Rockafellar.dim` lives in surface §1, so a dimension clause has to be unrolled to `vectorSpan` / `direction_affineSpan` by hand. §6 did it twice, §7 wrote `dim_eq_of_affineSpan_eq` and `dim_eq_of_closure_eq` independently. A `finrank (vectorSpan …)` congruence for equal affine spans collapses all four | §6, §7 | open — the round's most duplicated item |
| 9.7 | **No `¬ Proper f → ¬ Proper (clFn f)`.** The converse of `ConvexFn.proper_clFn`; 11 lines in §7 as `not_proper_clFn`. Belongs in `Closure.lean` | §7 | open |
| 9.8 | **Corollary 7.3.2 has no backbone counterpart** — 17 lines from `ConvexFn.exists_mem_relint_dom_lt` plus `restrict` | §7 | open |
| 9.9 | **No slice-dimension count.** Theorem 7.6's "same dimension as `dom f`" needs `affineSpan ℝ {x ∈ ri (dom f) \| f x < α} = affineSpan ℝ (dom f)`; the book gets it from Theorem 6.8's dimension count, which the backbone lacks. §7's `affineSpan_relint_dom_lt` is 27 lines, the longest proof in that file. Belongs beside `Convex.mem_relint_prod_iff` | §7 | open |
| 9.10 | **`ConvexFn.le_of_mem_closure` carries `∀ z, f z ≠ ⊥`, which the book does not.** §7 avoided it by re-deriving Corollary 7.3.3 from 7.3.2 in 5 lines, as the book does — so the extra hypothesis is avoidable in finite dimensions and should come off | §7 | open |
| 9.11 | **Corollary 8.3.1's second assertion** (`y ∈ 0⁺(cl C) ↔ ∀ λ > 0, x + λy ∈ C` for `x ∈ ri C`) has no backbone lemma; 10 lines in §8. Belongs beside `Convex.recessionCone_relint` | §8 | open |
| 9.12 | **Corollary 8.6.1's second assertion** (a closed `f` bounded above on one line is constant in that direction) has no backbone lemma; ~15 lines in §8. Belongs in `Recession/Function.lean` | §8 | open |
| 9.13 | **`f0⁺ = δ(·\|0)` for proper `f` with bounded `dom f`** (book line 2807) — ~15 lines in §8. Belongs in `Recession/Function.lean` | §8 | open |
| 9.14 | **`recessionConeFn f ⊆ recessionCone (dom f)`** is not in the backbone. It is what makes the book's "not to be confused with" warning precise | §8 | open |
| 9.15 | **`closure_coe_hull_prodMk_one_eq_union` is missing**, mirroring `closure_coe_hull_eq_union`: the book's `cl K = K ∪ {0} × 0⁺C` cost §8 twelve lines of set juggling against `closedConeOver`'s slab form | §8 | open — friction |
| 9.16 | **The recession/closedness cluster takes `ConvexFn` + `IsClosed (epi f)` (+ `hbot`) unbundled** where the book says "closed proper convex" and `ClosedProperConvexFn` exists — `recessionCone_setOf_le`, `linealitySpace_setOf_le`, `isBounded_setOf_le`, `recessionFn_apply_eq_iSup_inv_mul`, `tendsto_coe_inv_mul_sub_atTop`, `recessionFn_le_coe_iff_of_isClosed`. Every call site is 2–3 projections | §8 | open — friction, cheap |
| 9.17 | **No `smul_mem_recessionConeFn`** to match `smul_mem_recessionCone`, so a bare real has to be routed through `Submodule.smul_mem` with a `{c : ℝ // 0 ≤ c}` scalar | §8 | open — friction |
| 9.18 | **`m`-ary sums are binary throughout `Recession/`.** `recessionCone_prod` / `linealitySpace_prod` exist for binary products but not for `Set.pi`, and the book's own proof of Corollary 9.1.1 runs Theorem 9.1 on `C₁ ⊕ ⋯ ⊕ Cₘ ⊆ ℝᵐⁿ`. §9 states Corollaries 9.1.1, 9.1.3, Theorem 9.3 and Theorem 9.8 for two sets | §9 | open |
| 9.19 | **Corollary 9.2.1 does not exist in the backbone** — `Recession/Closedness.lean` records the same | §9 | open — **blocking**, no §9 declaration |
| 9.20 | **Corollary 9.8.3 needs `IsEpiLike (conv (epi f₁ ∪ epi f₂))` and `Proper (convFn₂ f₁ f₂)` under a common recession function**; both belong beside `convFn₂` in `Operations/Hull.lean` | §9 | open — **blocking**, no §9 declaration |
| 9.21 | **Theorem 9.2's recession formula `(Ah)0⁺ = A(h0⁺)` is missing.** `closedProperConvexFn_mapLin` gives the epigraph identity, closedness, properness and attainment but not this; deriving it needs a second application of Theorem 9.1, to `recessionFn f` | §9 | open |
| 9.22 | **Corollary 9.7.1's `{x \| γ(x\|C) = 0} = 0⁺C` is not in `Duality/Gauge.lean`** — eight lines from `setOf_gaugeFn_le_pos` and `recessionCone_eq_iInter_smul`, but it is a gauge fact | §9 | open — friction |
| 9.23 | **There is no bare-set "convex cone" predicate**, so `corollary_9_1_3` is stated for `PointedCone`s where Rockafellar's cones need not contain the origin. `recessionCone_closure_coe_pointedCone` is only available bundled | §9 | open |
| 9.24 | **`exists_forall_abs_le_of_isCompact_relint` lost the convex-hull weakening.** `bddAbove_range_of_subset_convexHull_closure` proves the book's hypothesis (a) with `U ⊆ conv (cl C')` in the `interior` form, but the `ri` forms only take `ri C ⊆ closure C'` — and Theorem 10.6 is about a relatively open `C`, so only the `ri` form is usable. §10 had to state the stronger `C ⊆ closure C'`. Push the spreading through the chart in `Convergence.lean`'s `Relint` section | §10 | open |
| 9.25 | **Corollary 10.5.1's `liminf_{λ→∞} f(λy)/λ < ∞` has no `EReal` spelling.** `ConvexFn.exists_lipschitzWith_of_frequently_le` takes `∃ c, ∃ᶠ a in atTop, f (a • y) ≤ c * a`, faithful only up to Theorem 8.5's monotonicity | §10 | open — friction |
| 9.26 | **`ConvexFn.exists_lipschitzWith_of_le_lipschitz` does not use convexity of the dominating `g`**, which Corollary 10.5.2 hypothesises. The surface keeps `ConvexFn g` as `_hg` so the statement is the book's | §10 | open — friction, may stay |

### What the round closed or *un*-scheduled

* **The §10/§20 dependency does not exist.** `Analysis/Convex/Simplicial.lean` proves upper
  semicontinuity relative to a simplex at *every* point of it, not only at a vertex
  (`ConvexFn.upperSemicontinuousWithinAt_convexHull_range`), so Rockafellar's triangulation step is
  never invoked and Theorem 10.2 is unconditional. `Polyhedral/Simplicial.lean` independently
  proves Theorem 20.5 as `Polyhedral.locallySimplicial`. **§20 inherits no obligation from §10**,
  and the "locally simplicial" item comes off the Part IV gate list.
* **The shared surface header is closed** (was §8.16 in part). `Surface/Common/Euclidean.lean` now
  carries `Continuity`, `Convergence`, `Simplicial`, `Operations.Basic`, `Mathlib.Tactic.TFAE`,
  `Mathlib.Analysis.Convex.Join` and `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` — the
  seven imports five of the ten sections written so far had to add for themselves.
* **`Recession/Cone.lean`'s "what is deliberately absent" was stale**: it said Theorem 8.2's `cl K`
  formula is not proved. It is, as `closure_coe_hull_prodMk_one` in `Recession/ConeHull.lean`.
  Fixed.
* **Corollary 9.8.2 does not go through §9 at all.** `IsCompact.isCompact_convexHull`
  (`Caratheodory.lean`, Corollary 17.2.1) is shorter and needs neither convexity nor non-emptiness.

### Book findings from the round

* **Theorem 8.5's `∞ − ∞`.** Mathlib gives `⊤ - ⊤ = ⊥` and `⊥ - ⊥ = ⊥`, not `⊤`. Rockafellar's
  own properness hypothesis is exactly what keeps the junk value out; it was not weakened.
* **The barycentric fact Theorem 10.2 rests on is called "intuitively obvious" (book line 3417) and
  never proved**, and Theorem 20.5 supplies it by assertion. The backbone proves it outright — see
  above — so neither assertion is inherited.

---

## 10. Gaps reported by the Part III surface round

The §11–§16 round. Five labels have no declaration and are marked **blocking** below; everything
else is friction that a section absorbed.

| # | item | reported by | status |
|---|---|---|---|
| 10.1 | **Theorem 11.2 for a general affine `M` does not exist.** `Separation.lean` has the *open*-`C` form; `RelativeInterior.lean` has the relatively open form only for `M` a point. The missing step — thicken to `C + M.direction`, apply the point case, then `eq_of_le_on_affineSubspace` — cost §11 a 45-line proof, the one piece of real work in that file. Belongs beside `exists_lt_of_notMem_relint` | §11 | open |
| 10.2 | **Theorem 11.6 in the `ri` form does not exist.** The backbone has only `exists_isSupporting_iff_disjoint_interior`, with `interior` and an extra `(interior C).Nonempty`. The `ri` version is Theorem 11.3 plus `ri D ⊆ D`, ~25 lines in §11. Belongs in `RelativeInterior.lean` | §11 | open |
| 10.3 | **`Convex.isClosed_add_of_neg_notMem_recessionCone` is stated for `C + D`, not `C - D`**, so Corollary 11.4.1 has to introduce `-C₂` and rewrite through `recessionCone_neg` and `sub_eq_add_neg`. A `_sub_` mirror removes three lines per call site | §11 | open — friction |
| 10.4 | **Corollary 11.7.1's backbone form re-uses `K` on both sides of the equation**, so `rw [← isClosed_convex_isCone_eq_iInter_halfSpaceCone …]` rewrites the index condition too (`gotchas.md` EL4). A pointwise membership companion, the way `mem_iff_forall_le_halfSpace` accompanies Theorem 11.5, would be easier to consume | §11 | open — friction |
| 10.5 | **`proper_conj_iff` carries a `ClosedFn f` hypothesis the book does not have.** On `ℝⁿ` the closed form is strictly weaker | §12, §13 | **closed** — `proper_conj_of_proper` in `Duality/Relint.lean` |
| 10.6 | **Monotone conjugacy is duplicated.** `Duality/GaugeLike.lean` has `monotoneConj` / `MonotoneHalfLineFn` / `monotoneConj_monotoneConj` on `[0,∞) ⊂ ℝ`; that is exactly `n = 1` of Theorem 12.4, and `iSup_sub_monotoneConj` is exactly §12's `conj_posPart` in one variable. §12's `monotoneConjOrthant` should replace it in the backbone with the half-line version derived. **The largest gap the round hit** | §12 | open |
| 10.7 | **No orthant support in the backbone.** `convex_nonnegOrthant`, `isClosed_nonnegOrthant`, `inner_rn` and the positive-part / mask constructions were written from scratch in §12; `Duality/Polar.lean`'s `section Orthant` has only `polarCone_nonnegOrthant`. Remediation §6 plans to move that section to the surface — it should move *and grow* | §12 | open — refines §6 |
| 10.8 | **`ClosedFn.restrict` is in `Duality/GaugeLike.lean`**, whose own docstring says it belongs beside `ConvexFn.restrict` in `Operations/Basic.lean`. §12 imports a §15 module for one three-line lemma | §12 | open — a move, not a proof |
| 10.9 | **Corollary 7.3.4 exists only as a *surface* declaration**, in `Part2/Section07.lean`, with an inline proof; `corollary_12_2_2` therefore imports a sibling surface module rather than the backbone. It should be `clFn_restrict_relint_dom` in the backbone | §12 | open |
| 10.10 | **`Duality/Support.lean` has no `api.md` record.** Every other `Duality/*` module has one. Cost §13 a detour | §13 | open — documentation |
| 10.11 | **Corollary 13.3.3 is not in the backbone at all** — `dom f*` bounded ⟺ `f` globally Lipschitz. §13 assembles it in ~20 lines from `recessionFn_isLeast`, Theorem 13.3's dual form, `supportFn_closedBall` and Corollary 13.1.1. `corollary_13_3_3_least` should be hoisted into `Duality/Level.lean` | §13 | open |
| 10.12 | **`supportFn_closedBall` is in `Subgradient/Convergence.lean`**, so §13 imports the whole subgradient-convergence tower for one lemma. `api.md` already flags it as a relocation candidate for `Duality/Support.lean` | §13 | open — a move |
| 10.13 | **No `dim` or `rank` for convex functions.** Theorem 13.4's two dimensionality formulas were done by hand from `Submodule.finrank_add_finrank_orthogonal` and `finrank_euclideanSpace_fin`; §13 defines `rankFn` and §14 defines `rankSet`, both surface-side, because §8's surface deferred rank for want of §1's `dim` | §13, §14 | open — refines §9.6 |
| 10.14 | **Theorem 14.3 needs one lemma**: `{x \| (cl (posHomGen f)) x ≤ 0} = closure (PointedCone.hull ℝ {x \| f x ≤ 0})` for closed proper convex `f` with `f 0 > 0 > inf f`. Everything else it needs (`supportFn_setOf_conj_le_zero`, `polarCone_recessionConeFn`) is present. Belongs in `Recession/` or `Duality/Level.lean` | §14 | open — **blocking**, no §14 declaration |
| 10.15 | **Theorem 14.4** additionally needs the `ℝⁿ × ℝ × ℝ` ↔ `ℝⁿ⁺²` transport (§4.8), and the recession function of `posHomGen f` — an unstated part of Theorem 13.5 that `Duality/Polar.lean` already defers | §14 | open — **blocking**, no §14 declaration |
| 10.16 | **Corollary 14.5.1 has no backbone statement.** §14 assembles it in eight lines from `isBounded_iff_recessionCone_eq_zero`, `recessionCone_eq_polarCone_polarSet` and `zero_mem_interior_iff_polarCone_eq_zero`. `Duality/Polar.lean`'s docstring defers it to a gauge module, but the route used needs no gauge at all | §14 | open |
| 10.17 | **`recessionConeFn_conj_hull` takes `Proper f` *and* `Proper (conj B f)`** where the book says only "proper convex". Now dischargeable by `proper_conj_of_proper`, but the hypothesis should come off | §14 | open — friction, cheap |
| 10.18 | **`.flip` on a self-paired space.** Eight backbone statements hand back `polarCone B.flip …` / `polarSet B.flip …`, and three more hand back `polarGauge`/`polarFn` against `B.flip` | §14, §15 | **closed for `polarCone`/`polarSet`** — `Surface/Common/Euclidean.lean`; `polarGauge_flip_pairing` / `polarFn_flip_pairing` still open |
| 10.19 | **A norm's closedness is not in the backbone.** §15 wrote `isNorm_closedFn_rn` from `ConvexFn.continuous_of_dom_eq_univ` and three statements use it. A finite-dimensional section of `Duality/Gauge.lean` should carry `IsNorm.closedFn` | §15 | open |
| 10.20 | **Theorem 15.2's set-side translation is missing** — the other face of §4.7, which closed the function side. Wanted: `absorbsAll_iff_zero_mem_interior`, `rayFree_iff_isBounded` for closed convex sets, and pairing forms of both. Every `ℝⁿ` statement re-derives four translations by hand | §15 | open |
| 10.21 | **No `polarFn_indicatorFn` / `obverse_indicatorFn`**, for which two §15 remarks are deferred | §15 | open |
| 10.22 | **`IsExactImage.of_relint` still demands `ClosedProperConvexFn`** while `IsExactSum.of_relint` was relaxed to proper convex. §16 redoes the `clFn` reduction by hand twice, 5 lines apiece. Mirroring the sum-side relaxation makes both one-liners and matches the book | §16 | open — friction, cheap |
| 10.23 | **`IsExactSum` is binary** where the book states Theorem 16.4 and Corollary 16.4.1 for `f₁ + ⋯ + fₘ`. The `m`-ary *identities* are now present (`conj_sum_toInfConvFn`); the exact forms are not | §16 | open — refines §4.4 |
| 10.24 | **`Duality/Polar.lean` has no `polarCone_add`, `polarSet_convexHull`, `polarSet_iUnion`, `polarSet_smul`.** `polarCone_iUnion` exists; its `polarSet` twin does not. Three §16 proofs run 12–18 lines for this reason alone | §16 | open |
| 10.25 | **`Convex ℝ {x \| B x y ≤ 1}` is missing** — the backbone has only the `EReal` form `convex_setOf_pairing_le`, and the real form is what cuts out a polar set | §16 | open — one line |
| 10.26 | **`conj B 0 = δ(· \| 0)` is missing**, the converse of `conj_indicatorFn_zero` and the other half of Rockafellar's one-sentence proof of Theorem 16.1 at `λ = 0` | §16 | open — one line |
| 10.27 | **Lemma 16.2, Corollaries 16.2.1 and 16.2.2** — the recession-form dual of §9's constraint qualification. The backbone routes around the recession step entirely, so stating them means assembling Theorems 11.1, 11.3 and 13.3 into a new result | §16 | open — **blocking**, three §16 labels |
| 10.28 | **No `a • (s + t) = a • s + a • t` for `Set`**, in Mathlib or here; proved inline in §16 | §16 | open — one line, Mathlib-shaped |

### What the round closed

* **§4.3, the bundled bipolar** — `Duality/Polar.lean` now carries the whole Theorem 14.1 family in
  `PointedCone` form. §14 confirms no statement discharges the hypothesis triple by hand.
* **§4.7, `IsNorm` → `Seminorm`** — at layer A, not layer D, and the "not here" note that declined
  it was wrong about why.
* **The §16 half of §4.4** — `conj_sum_toInfConvFn`, Theorem 16.4 in the book's `m`-ary form.
* **§4.1, the adjoint, needs no work on the surface side.** The backbone already had
  `isAdjointPair_adjoint` for `innerₗ E`, and `pairing n` is an `abbrev` for it. §16 writes every
  `A*` as `LinearMap.adjoint A` and carries no adjoint hypothesis. What remains of §4.1 is the
  *backbone-internal* threading of `(A') (hA : IsAdjointPair …)` through ~100 statements, which the
  surface does not pay for.

### Documentation errors the round found

* **`Duality/Gauge.lean` said Theorem 15.3 and its corollaries were absent** because the
  one-dimensional monotone-conjugate theory does not exist. It does exist, in
  `Duality/GaugeLike.lean`, and §15's centrepiece was nearly deferred on the strength of the note.
  Fixed.
* **`isAdjointPair_adjoint` was written twice** — once in the backbone, once in the shared surface
  header by this session — making every use ambiguous. The surface copy is gone. `gotchas.md` LIB1
  again: grep before naming.

### Book findings from the round

* **Corollaries 11.5.2 and 11.7.3 need `C.Nonempty`** in addition to `C ≠ ℝⁿ`: in `ℝ⁰` the empty
  set is a proper convex subset and no non-zero `b` exists.
* **Theorem 12.4 is printed with no proof at all**, and the symmetrisation its surrounding prose
  suggests is not the shortest route. §12 proves it directly: `f*(y⁺) = f*(y)` for a function that
  is `+∞` off the orthant and non-decreasing on it, by zeroing the coordinates where `y < 0` in any
  competitor.
* **Theorem 14.7's closedness hypothesis is unnecessary**; `Duality/Gauge.lean` already recorded
  this and the surface states the weaker hypothesis.
* **Corollary 13.3.2's delegated step ("as an exercise in separation theory") needs no separation.**
  A non-empty convex `C` is affine iff every linear function bounded above on it is constant on it,
  and both directions follow from Theorem 13.1 plus Theorem 6.1's line-segment principle.
* **Corollary 9.8.2 is not a §9 result** — `IsCompact.isCompact_convexHull` (Corollary 17.2.1) is
  shorter and needs neither convexity nor non-emptiness. Recorded under §9 as well.
