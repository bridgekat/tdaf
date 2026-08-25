# Sub-plan 8 — Remediation

Work created by the plan review of 2026-08, run as five independent adversarial reviewers over the
completed backbone (112 modules, 3 161 theorems). Ordered by **value / cost**, which is not the
order of importance: the cheapest items are first because they unblock the reading of everything
else.

Nothing here is new mathematics. Every item is either a defect the review found, or a piece of
scaffolding the surface library will otherwise pay for per-statement.

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

184 lines → 61, over 14 declarations, and — the point — **the transported hypotheses come out
identical to the re-proved ones**, so no caller changes. This is the leak-free transport that §2.2
is about.

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
| 4.9 | **`convexOn_iff_convexOn_lines`** | Thms 4.4/4.5. The *concave* half already exists, buried at `Saddle/Differential.lean:162` — move both somewhere findable |
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
