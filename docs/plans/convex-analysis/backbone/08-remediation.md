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
| §2.2 de-leak `reflect`'s mirrors | **done, and the prescription was wrong** — see below |
| §2.3 bundle the involutions | **done** — `reflectAut`, `saddleSwapOrderIso` |
| §4.1 bundle the adjoint | **closed by measurement** — the count was 32, not ~100, and four of its six sections contribute zero; D3 unmodified |
| §4.4 `m`-ary `infConv` / `IsExactSum` | **done in full** — the constructors in the product round, the `m`-ary consequence in §12.1 |
| §4.6 Theorem 27.1(e) | **done, and the item was false twice over** — `∂f*(0)` is a subset of `E`, and no new hypothesis was needed. **Part VI now has no open gate** |
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

**Re-measured before the Part VII round.** Two of these six closed at some point without being
recorded, and two of the remaining four name places that no longer exist. The `where` column of a
twenty-minute item decays faster than the item does.

| # | item | where | note |
|---|---|---|---|
| 1.1 | Delete seven `flip.flip` workarounds | `Saddle/Conjugate.lean:241`, `Saddle/Minimax.lean:1311`, `Saddle/Subgradient.lean:647,648`, `Bifunction/Cofinite.lean:184`, `Polyhedral/Closedness.lean:137`, `Subgradient/Approx.lean:419` | `instIsCompatiblePairingFlipFlip` was added after the idiom took hold; bare `inferInstance` discharges all seven (verified). **Mostly closed, unrecorded**: of the six files named, four now contain no `flip_flip` at all, and `Saddle/Conjugate.lean` and `Saddle/Subgradient.lean` have one each — neither at the line given. Whether those two are workarounds or honest rewrites needs one look, not an item |
| 1.2 | Move `IsContinuousPairing ((innerₗ E).flip)` | **not** `Subgradient/StrictlyConvex.lean:312` (gone) — the two live `have`s are `Subgradient/Bounded.lean:201` and `Subgradient/Reconstruction.lean:553`; destination unchanged | a surface `Setup.lean` importing only `Duality/*` cannot see it, and the failure reads as a missing instance rather than a missing import |
| 1.3 | ~~Promote `isCompatiblePairing_neg` to an instance and relocate~~ **closed** | it is an `instance` at `Duality/Pairing.lean:511` | consumers hand-rolled it at `Saddle/Existence.lean:379–381`, `Saddle/Minimax.lean:855–856,873–874`; every surface §34/§37 statement would repeat those `have`s |
| 1.4 | Relocate `isMaximalMonotoneRel_subgradientRel` | from `Optimization/Prox.lean:435` to `Subgradient/Monotone.lean` | it is the theorem D10 itself advertises as `subgradient_maximalMonotone`, filed away from the predicate it is about |
| 1.5 | ~~Add `Eponyms.lean`~~ **closed** | `Tdaf/Analysis/Convex/Eponyms.lean`, 92 lines, nine aliases — the four the row asked for plus `jensen`, `caratheodory`, `moreau_decomposition`, `subgradient_maximalMonotone`, `perspective` | `fenchel_moreau := biconj_eq_clFn`, `fenchel_inequality := Proper.le_add_conj`, `minkowski_weyl := polyhedralCone_iff_finitelyGeneratedCone`, `krein_milman := convexHull_extremePoints`, `caratheodory := mem_convexHull_iff_exists_fin_finrank_succ`, `moreau_decomposition := moreau_add`, `subgradient_maximalMonotone := isMaximalMonotoneRel_subgradientRel`, `perspective := smulRight` |
| 1.6 | ~~Delete `partialConj₂`~~ **resolved the other way** | `Saddle/Defs.lean:205` now says in its own docstring that it is “kept for the statement of `partialConj₂_graphFn`”, which is the row's second option taken explicitly. Still zero consumers outside its file; **D8 still needs amending** | D8 calls it "the organizing operation" of Parts VI–VIII; it has **zero consumers outside its own file**. `bracket` (260 occurrences, 12 files) is the real operator. Either delete it or make it the definition of `bracket` — carrying a dead definition the plan advertises as load-bearing is worse than carrying none. **Amend D8 either way.** |

The naming test (§4.1 test 3) scored 53% on first guess before 1.5; the misses were all eponyms.

Note that 1.4 is **half** done: `Eponyms.lean` supplies the advertised name
`subgradient_maximalMonotone`, but the theorem itself is still in `Optimization/Prox.lean:435`,
filed away from the predicate it is about. An alias is not a relocation.

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
infimum-oriented Theorem 39.5 must reason about the reflection to discharge it.

**Done — and `eval_reflect` was the wrong tool.** All eight really did leak. But pushing
`eval_reflect` through gives `-(supportFn Bx (A₁.eval (-u)) (-y))`: it trades one involution for
two sign flips, and the caller is no better off. **The leak was in the proofs, not in the
statements.** Both mirrors reflected the *argument* —
`adjointProcess_reflect : adjointProcess Bu Bx A.reflect = coadjointProcess Bu Bx A` — which
forces the hypothesis to be read at `A.reflect`. The dictionary also carries the other
orientation, `coadjointProcess_eq_reflect_adjointProcess :
coadjointProcess Bu Bx A = (adjointProcess Bu Bx A).reflect`, which puts the involution on the
*conclusion*, where `reflect_add` and `reflect_comp` cancel it. With that,
`coadjointProcess_add` and `coadjointProcess_comp` carry Theorems 39.5 and 39.8's own hypotheses
**verbatim**, and the six closed halves each simply lose one `.reflect` per summand. No proof
grew: both mirrors are still four-line `rw` chains, and no call site outside the file changed
(there are none). The rule is now `gotchas.md` LIB4: *a mirror that leaks is a wrong proof, not a
wrong statement — look for the intertwining lemma that rewrites the conclusion.*

### 2.3 Bundle the involutions

`reflect` and `saddleSwap` are bare `def`s. Bundle at the point of definition:

* `ConvexProcess.reflect` — additive, involutive, closedness-preserving ⇒ `AddAut`, or at minimum
  `Function.Involutive`, giving `.injective`/`.eq_iff`/`.toPerm` free.
* `saddleSwap` — involutive (`Closure.lean:135`) **and antitone** (`Existence.lean:119`) ⇒
  `OrderIso … ᵒᵈ`. Then `saddleSwap_injective` (`:138`, hand-proved) is `Equiv.injective`.

**Done, and both claims held.** `ConvexProcess.reflectAut : AddAut (ConvexProcess U X)` — `AddAut`
needs only `[Add]`, which the processes have, so no group structure is required — built on
`reflect_involutive` and `reflect_add`; and
`saddleSwapOrderIso : (U × X → EReal) ≃o (X × U → EReal)ᵒᵈ`, after which `saddleSwap_injective` is
`Equiv.injective`. Note `saddleSwap` is *not* `Function.Involutive` — it is not an endomorphism,
the two factors being exchanged — so the two-sided inverse has to be recorded as an `Equiv`, which
is what the `OrderIso` does. Bundling cost nothing at the use sites: the bare `def` stays and the
bundle is built from it, so none of the 106 `saddleSwap` uses in `Kernel.lean` changed.
`saddleSwap_le_saddleSwap` moved from `Saddle/Existence.lean` up to `Saddle/Closure.lean`, so that
the bundle can sit beside the definition; it needed no hypotheses at all, so the move is free.

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
| 4.1 | **Bundle the adjoint.** A `class HasTranspose B B′ A` / bundled `AdjointPair` with the finite-dimensional inner-product instance, so instance search supplies `A′` | §16, §19, §30, §31, §38, §39 | **closed by measurement, not by building it — and the item was wrong three ways.** The library-wide count of statements threading `(A′)` plus `IsAdjointPair` is **32**, not ~100. Four of the six sections named contribute **zero**, because the book’s `A*` and `F*` in §§19, 30, 38 and 39 are *defined operations* (`adjointBifun`, `adjointProcess`) taking no linear map and carrying no adjoint datum — `IsAdjointPair` does not occur once in `Bifunction/{Algebra,Cofinite,Process,ProcessDuality}.lean`. And the *surface* pays none of the remaining friction: `isAdjointPair_adjoint` discharges the datum at **8** call sites in all of Parts I–IV. **D3 stands unmodified.** What Part VIII actually wanted was the one place a transpose of a linear map really occurs — a linear transformation read as a convex process has the adjoint linear transformation for its adjoint — and that is now `Bifunction/LinearProcess.lean` (`ConvexProcess.ofLinearMap`, `adjointProcess_ofLinearMap`, `coadjointProcess_ofLinearMap`) |
| 4.2 | **`negFst (prodPairing Bu Bx)` pairing-class instances.** Prove the `LinearMap` equation `negFst (prodPairing Bu Bx) = prodPairing (-Bu) Bx` — only the *pointwise* identity exists (`Duality/Pairing.lean:326`) — then derive the instances via `isCompatiblePairing_neg` | §30's adjoint bifunctions conjugate against `negFst`. **Most likely `Setup.lean` blocker** |
| 4.3 | ~~**Bipolar theorem for `PointedCone`**~~ **done** | `polarCone_polarCone_pointedCone` already existed; the three companions did not. `Duality/Polar.lean` now has the whole Theorem 14.1 family in bundled form — `…_pointedCone`, `…_pointedCone_eq_closure`, `neg_polarCone_neg_polarCone_pointedCone`, `conj_indicatorFn_polarCone_pointedCone` — and the module docstring says to use them rather than discharge the triple by hand |
| 4.4 | **`m`-ary `infConv` and `IsExactSum`** over a `Finset` | **constructors done, one consequence missing — see §12.1** — `IsExactFinsetSum` in `Duality/Exact.lean`, with `.singleton`, `.cons`, `.of_split`, `.of_relint` (Theorem 16.4) and the `Polyhedral/Duality.lean` constructors (Theorem 20.1). The consequences could **not** be inducted and the constructors could: iterating `infConv_le_add` over a partial convolute is not merely awkward but *false*, since `□` does not preserve `≠ ⊥` (take `g₁ x = -x`, `g₂ x = x`), so the epigraph-level `sum_toInfConvFn_apply_le` carries the induction hypothesis-free instead. The load-bearing missing piece was not properness but **Theorem 6.5 over a `Finset`**, which no surface agent could have supplied locally. **§23 then found the gate only half closed**: `Subgradient/Calculus.lean` still has only the binary *consequence* `IsExactSum.subgradient_add`, which is what Theorem 23.8 needs in `m`-ary form |
| 4.5 | **Separable sums** over a finite product, with `conj (sepSum f) = sepSum (conj ∘ f)` | §16's separable rows and §38 |
| 4.6 | **Theorem 27.1(e)** restated under `[IsCompatiblePairing B] [IsCompatiblePairing B.flip]` | §27 | **done, and the item was false twice over.** `∂f*(0)` does **not** live in `E**`: for `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, `conj B f : F → EReal` and `subgradient B.flip (conj B f) 0` is a subset of **`E`** — the exclusion note had silently substituted the canonical self-pairing of `F` for the given `B`. `argmin_eq_subgradient_conj_zero`, which *is* clause (b), had stated it without difficulty since the file was written. And the prescription was a no-op: both named classes were already on `section ConjugateAtZero`. What the clause needed was `Function.Injective B`, which is **free in a normed space** — `SeparatingDual ℝ E` is automatic and `separatingRight_flip_of_separatingDual` converts it. Closed as `section UniqueMinimiser` in `Optimization/Minimum.lean`. On the surface the clause is *two lines* through `theorem_25_1`, which has existed since the Part V round. **This item was open for five rounds on a sentence nobody tested** |
| 4.7 | ~~**`IsNorm k → ∃ p : Seminorm ℝ E, ∀ x, k x = p x`**~~ **done, and not at layer D** | `IsNorm.toSeminorm` in `Duality/Gauge.lean`, at layer **A**. Mathlib's `Seminorm` is purely algebraic — it asks nothing about a topology — so the old "not here" note declined it on grounds that belong to `NormedSpace` and to nothing else. `IsNorm.apply_smul` (absolute homogeneity, which positive homogeneity does not give) is the one step that needed proving |
| 4.8 | **`Rn m × Rn n ≃ₗᵢ Rn (m+n)`** with transport for `conj`, `subgradient`, `ri` | **done, and the item was false as written** — that isometry does not exist: Mathlib’s product norm is the supremum norm, and no linear map carries a square onto a disc. The right objects are `euclideanProdIsometry : WithLp 2 (Rn m × Rn n) ≃ₗᵢ Rn (m+n)` and, for the transport, `euclideanProdEquiv : (Rn m × Rn n) ≃L Rn (m+n)` on the plain product — `conj`, `subgradient` and `ri` need only the linear structure and the topology, and stating them on `WithLp` would force every consumer to move a `Convex`/`ConvexFn`/`IsClosed` across a type synonym. All in `Analysis/Convex/EuclideanProd.lean`. §§14 and 22 consume it; the item’s "where" column named only §§29, 30, 37 |
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
complete, and §9 is **now 18 of 18**: Corollary 9.2.1 (9.19) and Corollary 9.8.3 (9.20) were the
two entries marked **blocking**, and the gap round closed both. Every numbered result in Parts I
and II now has a surface declaration.

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
| 9.18 | **`m`-ary sums are binary throughout `Recession/`** | §9 | **all but one piece done** — `recessionCone_pi`, `linealitySpace_pi`, `pi_recessionCone_subset` in `Recession/Cone.lean`; the sum map `(xᵢ) ↦ ∑ xᵢ` and the `m`-ary Corollary 9.1.1 (`Convex.isClosed_sum`, `closure_sum_eq`, `recessionCone_sum`) in `Recession/PiSum.lean`; the `m`-ary `infConv` in `Operations/InfConv.lean` (§4.4). What is left is `recessionFn` of a separable sum. The §9 *surface* corollaries are still stated for two sets, which is now a choice rather than a constraint |
| 9.19 | **Corollary 9.2.1 does not exist in the backbone** — `Recession/Closedness.lean` records the same | §9 | **done** — `closedProperConvexFn_infConv_of_recessionFn_symm` and `exists_add_eq_of_infConv_le_of_recessionFn_symm` (`Recession/Closedness.lean`), surface `corollary_9_2_1`. **At `m = 2` this is not Corollary 9.2.2**: writing `φ z = (f0⁺) z + (g0⁺) (−z)`, 9.2.2 demands `{φ ≤ 0} = {0}` and 9.2.1 only that `{φ ≤ 0}` be *symmetric*, which `f = g = 0` satisfies and the other does not. 9.2.2 is now a two-line specialisation and its old 60-line proof is gone. The `m`-ary form folds into 9.18 |
| 9.20 | **Corollary 9.8.3 needs `IsEpiLike (conv (epi f₁ ∪ epi f₂))` and `Proper (convFn₂ f₁ f₂)` under a common recession function**; both belong beside `convFn₂` in `Operations/Hull.lean` | §9 | **done, and the item was half wrong** — only the `IsEpiLike` half is algebraic (`IsEpiLike.mem_convexHull_of_le`, `isEpiLike_convexHull_epi_union`, `epi_convFn₂`, all in `Operations/Hull.lean`, all unconditional). Properness is read off the recession cone and lands at layer D: `closedProperConvexFn_convFn₂` and `exists_combo_of_convFn₂_le` in `Recession/ConeHull.lean`. Surface `corollary_9_8_3` |
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

The §11–§16 round. Five labels had no declaration and **all five are now closed** — Theorem 14.3
(10.14), Lemma 16.2 and Corollary 16.2.1 (10.27) in the gap round; Corollary 16.2.2 (11.14) and
Theorem 14.4 (10.15) in the product round. **Part III is complete.** Everything else here is
friction that a section absorbed.

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
| 10.14 | **Theorem 14.3 needs one lemma**: `{x \| (cl (posHomGen f)) x ≤ 0} = closure (PointedCone.hull ℝ {x \| f x ≤ 0})` for closed proper convex `f` with `f 0 > 0 > inf f` | §14 | **done** — `setOf_clFn_posHomGen_le_zero` in `Duality/Level.lean`, surface `theorem_14_3`. **The item named the wrong prerequisites**: neither `polarCone_recessionConeFn` nor `supportFn_setOf_conj_le_zero` is used. Rockafellar routes through Theorem 14.2 and the recession cone of `cl k`, spending a paragraph on `(cl k)0⁺ = cl k`; none of it is needed, because `cl k` is a support function and a polar *is* the zero sublevel set of one (`polarCone_eq_setOf_supportFn_le_zero`, new). Two identities the book opens with and the backbone lacked — `conj_apply_zero` and `iInf_conj_eq_neg_apply_zero` — are what make `f 0 > 0 > inf f` self-dual |
| 10.15 | **Theorem 14.4** additionally needs the `ℝⁿ × ℝ × ℝ` ↔ `ℝⁿ⁺²` transport (§4.8), and the recession function of `posHomGen f` | §14 | **done, and the description was wrong twice over** — `closure_homCone_conj` in the new `Duality/HomConePolar.lean`, surface `theorem_14_4`. The recession function of `posHomGen f` is **not** a prerequisite and never was: that is the unnumbered paragraph *before* the theorem. The coordinate order is `(ℝ × E) × ℝ`, which is where `homCone` already lives and where `epiPairing` lives too, so no associativity shuffle is needed either. Sharper than the book: the proof needs neither `cl K` nor the bipolar theorem — the vertical ray forces `λ* ≥ 0` on `K°` and one affine minorant produces a point with `λ* = 1` — so it sits a layer *below* Theorem 14.1, needs no local convexity and no `IsCompatiblePairing`, and asks only for convex `f` with `dom f` and `dom f*` non-empty |
| 10.16 | **Corollary 14.5.1 has no backbone statement.** §14 assembles it in eight lines from `isBounded_iff_recessionCone_eq_zero`, `recessionCone_eq_polarCone_polarSet` and `zero_mem_interior_iff_polarCone_eq_zero` | §14 | **done** — new module `Duality/PolarBounded.lean`: `recessionCone_polarSet`, `isBounded_polarSet_iff_zero_mem_interior`, `isBounded_iff_zero_mem_interior_polarSet`, all over a dual pair. The surface is a one-line specialisation. `Duality/Polar.lean`’s deferral note claimed the corollary "quantifies over the gauge"; it does not — only Rockafellar’s *proof* does |
| 10.17 | **`recessionConeFn_conj_hull` takes `Proper f` *and* `Proper (conj B f)`** where the book says only "proper convex" | §14 | **cannot be closed where it stands** — the discharge is `proper_conj_of_proper`, which lives in `Duality/Relint.lean`, and `Duality/Relint.lean` imports `Recession/Conjugate.lean`. Taking the hypothesis off means first moving `proper_conj_of_proper` to a module both can see, or trading it for `ConvexFn f`, which is a different hypothesis rather than a weaker one. `recessionConeFn_conj` carries the identical redundancy and must move with it |
| 10.18 | **`.flip` on a self-paired space.** Eight backbone statements hand back `polarCone B.flip …` / `polarSet B.flip …`, and three more hand back `polarGauge`/`polarFn` against `B.flip` | §14, §15 | **done** — all four heads (`polarCone`, `polarSet`, `polarGauge`, `polarFn`) are `*_flip_pairing` simp lemmas in `Surface/Common/Euclidean.lean`, beside the original four |
| 10.19 | **A norm's closedness is not in the backbone.** §15 wrote `isNorm_closedFn_rn` from `ConvexFn.continuous_of_dom_eq_univ` and three statements use it. A finite-dimensional section of `Duality/Gauge.lean` should carry `IsNorm.closedFn` | §15 | open |
| 10.20 | **Theorem 15.2's set-side translation is missing** — the other face of §4.7, which closed the function side. Wanted: `absorbsAll_iff_zero_mem_interior`, `rayFree_iff_isBounded` for closed convex sets, and pairing forms of both. Every `ℝⁿ` statement re-derives four translations by hand | §15 | open |
| 10.21 | **No `polarFn_indicatorFn` / `obverse_indicatorFn`**, for which two §15 remarks are deferred | §15 | open |
| 10.22 | **`IsExactImage.of_relint` still demands `ClosedProperConvexFn`** while `IsExactSum.of_relint` was relaxed to proper convex. §16 redoes the `clFn` reduction by hand twice, 5 lines apiece. Mirroring the sum-side relaxation makes both one-liners and matches the book | §16 | open — friction, cheap |
| 10.23 | **`IsExactSum` is binary** where the book states Theorem 16.4 and Corollary 16.4.1 for `f₁ + ⋯ + fₘ` | §16 | **done** — `theorem_16_4_exact_finset`, `theorem_16_4_attained_finset`, `corollary_16_4_1_exact_finset`, `corollary_16_4_1_attained_finset`. Corollary 16.4.1’s printed "let `C₁, …, Cₘ` be non-empty convex sets" is redundant in the exact clause — a common point of the `ri Cᵢ` already gives it — and the `_exact_finset` form drops it |
| 10.24 | **`Duality/Polar.lean` has no `polarCone_add`, `polarSet_convexHull`, `polarSet_iUnion`, `polarSet_smul`.** `polarCone_iUnion` exists; its `polarSet` twin does not. Three §16 proofs run 12–18 lines for this reason alone | §16 | **done** — `polarSet_union`, `polarSet_iUnion`, `polarSet_convexHull`, `polarSet_smul` and `polarCone_add`, all in `Duality/Polar.lean` |
| 10.25 | **`Convex ℝ {x \| B x y ≤ 1}` is missing** — the backbone has only the `EReal` form `convex_setOf_pairing_le`, and the real form is what cuts out a polar set | §16 | **done** — `convex_setOf_pairing_le_coe`, `Duality/Polar.lean`; it is what `polarSet_convexHull` is proved from |
| 10.26 | **`conj B 0 = δ(· \| 0)` is missing**, the converse of `conj_indicatorFn_zero` and the other half of Rockafellar's one-sentence proof of Theorem 16.1 at `λ = 0` | §16 | **done** — `conj_zero_eq_indicatorFn` in `Duality/Level.lean`. It carries the same `SeparatingDual` hypothesis as `supportFn_univ_of_ne_zero`: the identity is false for a pairing that does not separate points |
| 10.27 | **Lemma 16.2, Corollaries 16.2.1 and 16.2.2** — the recession-form dual of §9’s constraint qualification. The backbone routes around the recession step entirely, so stating them means assembling Theorems 11.1, 11.3 and 13.3 into a new result | §16 | **two of three done** — new module `Duality/RelintSeparation.lean`, whose centrepiece `exists_pairing_le_iff_disjoint_relint` is Theorem 11.3 composed with Theorem 11.1 with the separating functional transported to `F`. Surface `lemma_16_2` and `corollary_16_2_1`. **Corollary 16.2.2 is open** and is not a §16 item — see 11.14 |
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

## 11. Gaps reported by the Part IV surface round

The §17–§22 round. **No label is blocked by a backbone gap.** Part IV's five absent labels are
§22's elementary-vector development (Lemmas 22.4 and 22.5, Corollary 22.4.1, Theorems 22.6
and 22.7), deferred by the standing scope rule — combinatorial matroid theory, not convex
analysis — and the one clause below marked **partial** is the *second sentence* of Theorem 17.1,
whose first sentence is `theorem_17_1`.

| # | item | reported by | status |
|---|---|---|---|
| 11.1 | **Corollary 17.2.1 is mislabelled and the real one is missing.** `Caratheodory.lean` puts the label on `IsCompact.isCompact_convexHull`, which is Theorem 17.2’s *second sentence*. The real Corollary 17.2.1 — for `S` non-empty closed bounded and `f` continuous real-valued on `S` and `+∞` off it, `conv f` is closed proper convex — had no backbone counterpart | §17 | **done** — `closedProperConvexFn_convHullFn_restrict` and `isClosed_convexHull_epi_restrict` in `Caratheodory.lean`, over an arbitrary finite-dimensional normed space; the label moved to Theorem 17.2, in `HullDirections.lean`’s docstring too. The surface is a two-line specialisation and shed four private helpers |
| 11.2 | **`exists_of_mem_convexHull_add_coneHull` discards the linear independence its own proof establishes.** `exists_linearIndepOn_of_mem_coneHull` produces it and the Carathéodory bound throws it away | §17 | **done** — `exists_linearIndepOn_of_mem_convexHull_add_coneHull` keeps it and the old statement is a two-line derivation, so no caller broke. The mixed-set vocabulary of pp. 154–155 went into `HullDirections.lean` (`affineSpanPD`, `finrankPD`, `AffineIndepPD`, `IsSimplexPD`), and the keystone is `finrank_span_liftPD` — homogenisation raises dimension by exactly one. Surface `theorem_17_1_simplex`; §17 now has no partial label |
| 11.3 | **"Every extreme direction of `C` is an extreme direction of `0⁺C`"** (p. 163), and its exposed analogue. The backbone has only `extremeDirections_subset_recessionCone` — an extreme direction *is a* direction of recession. The sharpening is the book's `C' ⊆ x + 0⁺C ⊆ C` argument | §18 | **done** — `isFace_recessionCone` and `extremeDirections_subset_extremeDirections_recessionCone` in `Representation.lean`, `isExposed_recessionCone` and `exposedDirections_subset_exposedDirections_recessionCone` in `Exposed.lean`. The general fact is that the recession cone of a face is a face of the recession cone whenever it is contained in it; it needs no closedness, no convexity of `C` and no topology, and simultaneously performs the book's restriction to `x + 0⁺C` and his translation by `-x` |
| 11.4 | **Theorem 19.1’s implications out of clause (b)** — finitely many faces ⇒ finitely generated | §19 | **done, and the item over-specified the route** — new module `Polyhedral/Faces.lean`. Only Theorem 18.5 and the lineality reduction are needed; **Theorem 18.8 is not on the route**, because (b) ⇒ (a) factors through (c), which is `polyhedral_iff_finitelyGenerated` and has been present all along. Naming 18.8 is what made this look hard enough to defer. The book’s unjustified "it suffices to treat the case where `C` is `n`-dimensional" is avoided rather than repaired, and the module says so. Two facts that lived only on the surface — a polyhedral set has finitely many faces, a face of one is polyhedral — came down into the backbone with it |
| 11.5 | **The `f = h + δ(· \| C)` normal form for a polyhedral convex function** (book 6771–6779): a maximum of finitely many affine functions plus the indicator of a polyhedral convex set | §19 | **done** — new module `Polyhedral/NormalForm.lean`: `maxAffineFn`, `polyhedralFn_maxAffineFn_add_indicatorFn` (unconditional), `PolyhedralFn.exists_maxAffineFn_add_indicatorFn_dom` and the iff `polyhedralFn_iff_maxAffineFn_add_indicatorFn` under `∀ x, f x ≠ ⊥`. Sharper than the book: the set can always be taken to be `dom f` |
| 11.6 | **Theorem 20.1 and Corollary 20.1.1 are binary** where the book states them for `f₁ + ⋯ + fₘ` with `f₁, …, f_k` polyhedral | §20 | **done** — `IsExactFinsetSum.of_polyhedral_pair` and `.of_polyhedral` in `Polyhedral/Duality.lean`, on `polyhedralFn_finsetSum` (Theorem 19.4 for `m` summands). Rockafellar’s own proof unchanged: the polyhedral block is one summand, the rest another, binary Theorem 20.1 joins them, `of_split` glues the exactness. His excluded cases `k = 0` and `k = m` are covered too |
| 11.7 | **Theorem 19.6 is two-set only** — `polyhedral_closure_convexHull_union` | §19 | **done, and "the evident induction" was wrong** — re-entering the binary lemma needs two facts the backbone lacks (that the closed convex hull absorbs an inner closure, and that `0⁺` of the inner hull is `∑ 0⁺Cᵢ`). What generalises is the binary *proof*: the same three-set sandwich run over a `Finset`, and no longer than the binary one. `finitelyGenerated_closure_convexHull_biUnion` and `polyhedral_closure_convexHull_biUnion` in `Polyhedral/Ops.lean`; surface `theorem_19_6_biUnion` |
| 11.8 | **The recession-hypothesis exercise of §21** (book **7593**; the row said 7601, which is a bare `\[` display delimiter). Assuming every finite subcollection is non-empty, the recession hypothesis of Helly's theorem holds iff some finite subcollection has bounded intersection | §21 | **closed — and the row's diagnosis was wrong twice over, as was mine.** The row said the forward direction "needs the recession cone of an *arbitrary* intersection … the backbone states that only for finitely many". Both halves false: `recessionCone_iInter` has always been `{ι : Sort*}`, and `0⁺(⋂ᵢ Cᵢ)` **never appears** — the hypothesis is `⋂ᵢ 0⁺Cᵢ = {0}`, an intersection *of* recession cones. My own sharper diagnosis (that `Nonempty` was the obstacle) was also wrong: the forward direction only calls the lemma on a *finite* subfamily, for which the exercise's standing hypothesis supplies a common point. **The item was closeable with the backbone exactly as it stood**, and had been for two rounds |
| 11.9 | **§22’s interval reading of `Ax ≤ a` and of `x ≥ 0, Ax = a`** needs the `ℝᵐ × ℝⁿ ≃ ℝᵐ⁺ⁿ` transport | §22 | **done** — `intervalVector`, `intervalSubspace`, `interval_reading_le`, `interval_reading_nonneg_eq` in `Part4/Section22.lean`. **The item had the ordering backwards**: p. 202 puts the `n` unknowns first and the `m` constraint values second, so the transport used is `ℝⁿ × ℝᵐ ≃ ℝⁿ⁺ᵐ`. The book writes `N = m + n` in the text while indexing `ζ_{n+i}`; the indices are what a formalization must follow |
| 11.10 | **`Module.finrank ℝ (Rn n) = n` is not a `simp` lemma.** `finrank_euclideanSpace_fin` is rewritten by hand at 22 sites across §1, §13, §14, §17 and §21, eleven of them in §21 alone | §13, §14, §17, §21 | **done** — the shared header gives it the `simp` attribute |
| 11.11 | **`pairing n` is symmetric and nothing says so.** Rockafellar writes every system as `⟨aᵢ, x⟩ ≤ αᵢ` and the backbone quantifies the other way round; §22 defined `pairing_comm`, `forall_pairing_le_comm` and `forall_pairing_lt_comm` locally | §22 | **done** — all three moved to `Surface/Common/Euclidean.lean` |
| 11.12 | **`(pairing n).SeparatingRight` is re-derived at every call site** from `separatingRight_flip_of_separatingDual` plus `flip_pairing`, four times across §13 and §21 | §13, §21 | **done** — `separatingRight_pairing` in the shared header |
| 11.13 | **`Analysis.Convex.HullDirections` is the module the mixed points-and-directions modelling decision runs on**, and only §17 imports it. §18 and §19 use `convexHullPD` forty times between them and reach it only by accident, through `Analysis.Convex.Representation` | §17, §18, §19 | **done** — a header import, and §17 drops its own |

| 11.14 | **Corollary 16.2.2 is a product-of-`ι` problem, not a §16 one.** It is Lemma 16.2 applied in `ι → E` to the diagonal subspace | §16 | **done** — new module `Duality/FiniteProduct.lean`: `piPairing` with **all four** pairing classes as instances (the item said two — `IsInnerPairing` and `IsContinuousInnerPairing` also had only `prodPairing` instances), `Convex.relint_univ_pi` (convexity only, no nonemptiness), and `supportFn_univ_pi`, unconditional. Surface `corollary_16_2_2`. **The item’s cost estimate was wrong for the second time**: the support-function piece is ~40 lines with no `⊤` case split and no ε — it is an induction on the index `Finset` using `Function.update`, closing on `Tdaf.EReal.biSup_add_biSup`, the same interchange `conj_infConv` runs on. And `Tdaf.EReal.coe_sum` exists (`Order/EReal.lean:204`); only *Mathlib* lacks it. The expensive piece was the pairing instances |
| 11.15 | **The duplicate `polarCone_hull` / `polarCone_coe_hull`.** `Duality/Polar.lean:**776**` (`@[simp]`; the row said 744, a blank line at `66f4626`) and `Recession/Conjugate.lean:184` are the same statement proved twice, and each has its own callers | §14 | **closed** — LIB1’s eighth instance. One survivor in `Duality/Polar.lean`, call sites repointed. Note which proof won: the copy the row implies should die had the **better** one — two lines against seven — so the survivor kept the loser's proof. A duplicate sweep that keeps the copy in the better *home* must still read both *bodies* |
| 11.16 | **`supportFn_le_zero_iff` and `zero_lt_supportFn_iff` are in the wrong file.** `supportFn_le_coe_iff` had no `c = 0` companion, so call sites open with `have hzero : ((0:ℝ):EReal) = 0 := by norm_num`. They now exist in `Duality/RelintSeparation.lean` and belong in `Duality/Support.lean` | §16 | **closed** — moved, and **the row undercounts the call sites: four, in three files, not two in two.** The third file is `Duality/Polar.lean:563`, which runs the same coercion in a different shape and so **does not match a grep for `hzero`** — the string the row's own phrasing tells you to search for. Its proof is now one line. The fourth site, `Duality/Relint.lean:146`, survived this round's own sweep and was closed post-merge |
| 11.17 | **`Caratheodory.lean` now splits a finite subset of `liftPD P D` twice** — inside `exists_linearIndepOn_of_mem_convexHull_add_coneHull` and standalone as `exists_finset_liftPD_eq`. Rebuilding the first on the second shortens the file by about 30 lines | §17 | **done, and the estimate was low by a factor of two** — `exists_finset_liftPD_eq` supplies the split, `Finset.coe_injective` turns `liftPD ↑p ↑d = ↑t` into a `Finset` identity, and `Finset.sum_union`/`Finset.sum_image` carry the weights. The proof went from 131 lines to 62 and the file is 68 lines shorter |
| 11.18 | **`recessionCone_polarSet` belongs at layer C**, beside `recessionCone_eq_polarCone_polarSet` in `Duality/Gauge.lean`; it sits in `Duality/PolarBounded.lean` under an `omit` only because the two theorems that consume it are finite-dimensional | §14 | **closed — and it was never the one-declaration move it reads as.** Landing it in `Gauge.lean`'s Theorem 14.6 section first required moving `convex_polarSet` and `polarSet_closure` out to `Duality/Polar.lean`, because `convex_polarSet` was declared **650 lines below the target section in the same file** — an intra-file ordering blocker, which no import-closure check detects and the grep finds while the elaborator does not. And **what blocked this row for two rounds was a false warning in our own `api.md`**: the `Duality/Gauge.lean` record listed both lemmas as "will name-clash if added there", but `Duality/Polar.lean` has `convex_polarCone` and `polarCone_closure` — not the `polarSet` spellings. Both moved cleanly, one call-site change. **A warning in our records earns the same grep a remediation row does** |

| 11.19 | **`posHomGen_mono` was declared twice, publicly, in the same namespace** — `HellyRefined.lean` and `Subgradient/Approx.lean`, the same statement proved twice. Neither module imported the other, so nothing was ambiguous *yet* | sweep | **done** — one copy, in `Recession/ConeHull.lean` immediately after `le_posHomGen`, which is where `posHomGen` is defined and where all five ingredients live. The item first named `Duality/Level.lean` as the home, which is wrong and which `Level.lean`’s own docstring contradicts; the agent that found it stopped and reported rather than editing outside its fence |
| 11.20 | **Four private near-duplicates across module boundaries**: `lift_mem_coneHull_liftPD` (private in `Caratheodory.lean`, public in `HullDirections.lean`, which imports it — legitimate, but worth a pointer), `iSup_sub_of_ne_bot` (`Bifunction/Algebra.lean`, `Optimization/Fenchel.lean`), `neg_coe_sub` (`Bifunction/Algebra.lean`, `Optimization/Adjoint.lean`, `Saddle/Existence.lean`, plus a primed variant in `Subgradient/Defs.lean`). Private, so harmless to the build; each is an `EReal` fact that should be a public lemma in `Tdaf/Order/EReal.lean` | sweep | **the two `EReal` facts are done**; `lift_mem_coneHull_liftPD` is not. `Tdaf.EReal.iSup_sub_of_ne_bot` is the `Optimization/Fenchel.lean` variant, which is strictly stronger — `Bifunction/Algebra.lean` asked for `[Nonempty ι]` and over an empty index set both sides are `⊥`. `Tdaf.EReal.neg_coe_sub` is `-(↑r - z) = z - ↑r`. The primed variant is in **`Saddle/Defs.lean`**, not `Subgradient/Defs.lean`, and the sweep found a fifth spelling, `neg_coe_sub_eq` in `Optimization/Normal.lean`; both fold an `add_comm` into the statement and their call sites depend on the orientation, so they are now one-line aliases rather than deletions. Still open: `HullDirections.lean` re-*proves* `lift_mem_coneHull_liftPD` instead of citing `Caratheodory.lean`’s private copy, and `Subgradient/Monotone.lean:564` declares `Tdaf.ConvexAnalysis.coe_sub_add_coe`, the same `EReal` fact as `Tdaf.EReal.coe_sub_add_coe` under the same bare name in a different namespace — LIB1’s shadowing note |

| 11.21 | **Two `Finset`-indexed relative-interior lemmas are parked above their home.** `Convex.relint_biInter_finset` (Theorem 6.5 over a `Finset`, in `Duality/Relint.lean`) and `Convex.relint_univ_pi` (in `Duality/FiniteProduct.lean`) both belong in `RelativeInterior.lean` beside `Convex.relint_iInter` and `intrinsicInterior_prod_eq`. They are where they are because that file has 19 direct importers and editing it costs a near-full rebuild. `RelativeInterior.lean` has Theorem 6.5 only for a `Type`-indexed family; the `Finset` form is what every `m`-ary statement wants | §16, §20 | open — two moves, to be done in one edit of that file |
| 11.22 | **New modules without an `api.md` record.** House style is one per backbone module (§10.10 treats a missing one as a defect) | sweep | **done** — all seven have records: `Duality/RelintSeparation.lean`, `Duality/PolarBounded.lean`, `Polyhedral/NormalForm.lean`, `EuclideanProd.lean`, `Duality/HomConePolar.lean`, and now `Duality/FiniteProduct.lean`, `Recession/PiSum.lean` and `Polyhedral/Faces.lean`. `Bifunction/LinearProcess.lean` was written with its record |

### What the product round closed

Five agents plus a stacked sixth, over remediation items 4.4, 4.8, 9.18, 10.23, 11.4, 11.6, 11.9,
11.14, 11.17, 11.19 and 11.20. **Every one of them closed**, and the two remaining absent labels of
§§1–22 came down to one: Corollary 16.2.2 landed, leaving Theorem 14.4.

The round's premise was that the last two blocked labels wanted the same thing, a product transport.
That was right, and it turned out to be *two* transports with nothing in common — `ℝᵐ × ℝⁿ ≃ ℝᵐ⁺ⁿ`,
which is about `Fin`, and `ι → E`, which is about pairings and `EReal` suprema. Both are now built,
and both immediately paid for themselves outside their motivating label: the first closed §22's
interval reading, the second closed §9.18's sum map.

**Theorem 14.4 closed on a stacked sixth worktree**, built on the transport an hour after it landed,
and it is the one place where scepticism about the handover was worth the most: two of the three
things the plan said the proof needs, it does not. **Parts I, II and III are complete**, and every
label in §§1–22 that is not deliberately deferred by scope now has a declaration.

**Five of the round's findings are corrections to this file.** 4.8 stated an isometry that cannot
exist; 10.15 named a prerequisite the proof does not use, with the coordinates in the wrong order;
11.4 named Theorem 18.8, which is not on the route, and that is what made the item look hard enough
to defer for a round; 11.14's cost estimate was wrong for the second time, and in the same
direction; 11.19 named a module that does not define the function it is about. The pattern is
consistent enough to be worth stating as a rule, and `gotchas.md` LIB17 now does: **an item that
names a home, a prerequisite or a cost is making a claim — check it before planning around it.**

### What the gap round closed

Six agents, one worktree each, over remediation items 9.18–9.20, 10.14, 10.16, 10.27, 11.1–11.3,
11.5 and 11.7. **Six of the seven labels that had no declaration are now closed**, and Parts I and
II are complete. What remains absent in §§1–22 is Theorem 14.4, Corollary 16.2.2, and §22’s five
elementary-vector results.

Three of the round’s findings are corrections to *this file*, and are recorded in the rows above:
10.14 named two prerequisites that the proof does not use, 9.20 put properness in the algebraic
layer where it does not belong, and 11.7 called an induction evident that is not. A fourth is a
correction to the brief rather than to the file — Corollary 17.2.1 has no family of functions and no
affine minorant; 11.1 now states it as the book does.

### What the round settled

* **The `λ ≥ 0⁺` convention is inherited, not re-invented.** §19's Theorems 19.5.1, 19.6 and 19.7
  reuse §9's `ExtCoeff` unchanged. This was the one Part II decision Part IV was going to test.
* **Theorem 20.5 supplies `LocallySimplicial` instances; it does not repair §10.** The Part II
  round's finding is confirmed from the §20 side, and by a stronger route than expected:
  `Polyhedral.locallySimplicial` does not follow the book's sketch at all — it takes a coordinate
  cube for the neighbourhood and produces the simplices explicitly as the convex hulls of the
  affinely independent subsets of a generating `Finset` (`convexHull_eq_union`), so it never
  appeals to Carathéodory's count, which is the step the book asserts without proof.
* **The `dom` / `ri dom` asymmetry of Theorem 20.1 is already factored correctly.**
  `IsExactSum.of_polyhedral_pair` and `IsExactSum.of_polyhedral` split it exactly where the book
  does, and the two segment lemmas they pay — Corollary 7.5.1 for the polyhedral side (a proper
  polyhedral function is already closed) and Theorem 7.5 for the other — are where the asymmetry
  lives. No §20 statement had to weaken a hypothesis.

### Book findings from the round

**False as stated.** **Corollaries 17.1.4 and 17.1.6.** Both are *stated and refuted* in
`Part4/Section17.lean` — `corollary_17_1_4_false` and `corollary_17_1_6_false`, on `ℝ¹`. The
failing step is Rockafellar's passage to "a minimal `α′` on the vertical line", which does not
exist when the generated function is improper; the affine elimination that rescues Corollary 17.1.3
has no conical analogue, because an affine dependency has coefficients summing to zero — so both
signs occur — while a conical one can have every coefficient of one sign. **Theorem 17.3** is also
false as printed, and the backbone already carries the missing hypothesis `0 ∉ S*`; conversely the
book's `x* ≠ 0` is not needed.

**Stated with no proof at all.** **Corollary 18.7.1** (supplied here by citing the argument the
book gives one layer up, for Corollary 18.5.2 — which is how the backbone's
`closure_coneHull_exposedDirections` is proved) and **Theorem 19.6** (the book derives it in
running text at 6949–6971, and that is what the backbone formalises).

**Defective printed argument.** **Theorem 19.1's (b) ⇒ (a)** opens "It suffices to treat the case
where `C` is `n`-dimensional in `Rⁿ`" and never says why. **Theorem 20.5's** proof is a two-line
sketch that asserts the Carathéodory triangulation of a polytope; see above.

**Hypotheses the book carries and the mathematics does not.** Theorem 18.3 does not need the face
to be non-empty. Corollaries 18.5.2 and 18.7.1 do not need the cone to be "more than just the
origin" — for `K = {0}` there are no extreme or exposed directions, the hypothesis is vacuous and
both sides are `{0}`. **Theorem 20.4 needs neither convexity nor non-emptiness of `C`**: the
backbone's `exists_polyhedral_between` is a finite subcover argument and never combines two points
of `C` convexly.

**An extension the book calls obvious and never states.** Theorem 18.5 "extends obviously to closed
convex sets of arbitrary lineality" (p. 166). It is cheap over the backbone and is here as
`theorem_18_5_lineality`, via `eq_add_inter_of_isCompl`.

**Two hypotheses that look like typos and are not.** Theorem 21.1 asks `dom fᵢ ⊇ ri C`, not
`⊇ C`, and that is exactly what its proof uses. Alternative (b) of Theorems 21.1–21.3 is read in
`EReal`, where `0 · (+∞) = 0`; the convention is load-bearing, because Corollary 21.6.2 extends a
short multiplier vector by zeros and would otherwise be false.

**A citation to a result that does not exist.** The Comments and References for Part IV (book line
17309) cite a "Corollary 21.3.3". §21 has Corollaries 21.3.1 and 21.3.2 and nothing further; the
intended reference is 21.3.2, Helly's theorem.

**A section-plan error, corrected.** `part4.md` records the definition of an elementary vector as
OCR-truncated in the source text. It is not truncated: the text reads "a non-zero `z ∈ L` whose
support is minimal with respect to `L`, i.e. does not properly include the support of any other
non-zero vector of `L`".

## 12. Gaps reported by the Part V surface round

The §§23–26 round, together with the two remediation agents that closed §2.2/§2.3 and §4.1.
**Part V is complete — all 49 numbered results have declarations, nothing was blocked, and nothing
is deferred by scope.** Everything below is either a proof that exists on the surface and belongs
in the backbone, or a fact the backbone does not have and no Part V label needed.

**How the fix round was partitioned, and what that cost.** Five agents on disjoint file sets, but
the disjointness was not free. Taking the transitive closure of "these two rows want the same
file" collapsed eight rows into one blob, because `Order/EReal.lean`, `Optimization/Minimum.lean`,
`Optimization/Normal.lean`, `Bifunction/Algebra.lean` and `Duality/FiniteProduct.lean` each appear
in two or three rows. Three rows were therefore closed **centrally, before any agent was spawned**,
purely to break that closure: §12.22 with the `EReal` halves of §12.23 and §12.29 (one hot file
wanted by three agents), §12.13 (a rename whose call sites straddle two fences), and §12.30 (one
keyword, but in a file two agents wanted). A fourth, §12.12, was *not* scheduled at all — its own
status line says to do it with `Section38.lean` rather than ahead of it, and its shape depends on
what §38 turns out to need.

The general lesson: **a ledger row's file list is what determines whether it can be delegated**,
and rows are written without reference to each other, so nothing in the ledger records the
contention. Building the file→rows index first is cheap and changes the partition.

| # | item | reported by | status |
|---|---|---|---|
| 12.1 | **`IsExactFinsetSum.subgradient_finsetSum`**, in `Subgradient/Calculus.lean`, with the unconditional `subgradient_finsetSum_subset` beside it. `Calculus.lean` has only the binary `IsExactSum.subgradient_add`, although §16’s `IsExactFinsetSum` interface and both its constructors are `m`-ary throughout. The `m`-ary form is what Rockafellar states and what Corollary 23.8.1 needs; going through the binary rule would re-derive properness and the relative-interior condition of every partial sum, which is exactly what `IsExactFinsetSum.cons` exists to avoid | §23 | **closed** — `subgradient_finsetSum_subset` (unconditional) and `IsExactFinsetSum.subgradient_finsetSum` in `Subgradient/Calculus.lean`, new `FinsetAdd` section at **layer A**, the same layer as the binary rule. §23’s three Theorem 23.8 declarations are now one-liners. **This closes §4.4 in full** |
| 12.2 | **`Tdaf.EReal.le_coe_of_sum_le_coe_sum`**, in `Order/EReal.lean`: from `∀ i ∈ s, (c i : EReal) ≤ u i` and `∑ i ∈ s, u i ≤ ↑(∑ i ∈ s, c i)`, conclude `u j ≤ ↑(c j)` for every `j ∈ s`. The binary `le_coe_of_add_le_coe_add` already names Theorem 23.8 as its consumer in its own docstring; the `m`-ary theorem needs the `m`-ary lemma, and the two-summand version does not iterate — there is no subtraction to peel a summand off with | §23 | **closed** — `Tdaf.EReal.le_coe_of_sum_le_coe_sum` in `Order/EReal.lean`, immediately after the binary form. It is a lemma and not a corollary: the proof splits `s` as `{j} ∪ s.erase j` and applies the two-summand version once to the two partial sums |
| 12.3 | **`IsExactImage.of_relint` without closedness**, in `Duality/Relint.lean`: `ConvexFn g → Proper g → A x₀ ∈ ri (dom g) → IsExactImage …`. The existing constructor asks for `ClosedProperConvexFn g`, so the closure reduction (`clFn_compLin` plus `ConvexFn.relint_dom_clFn`) is paid three times: inside `theorem_16_3_exact`, inside `theorem_16_3_attained`, and again in §23 to reach Theorem 23.9 with the book’s hypotheses. One constructor removes all three | §23 | **closed** — `IsExactImage.of_relint_proper` in `Duality/Relint.lean`, on a new `conj_compLin_eq_conj_compLin_clFn`, which is **Theorem 9.3 in conjugate form on the image side** and is strictly cheaper than its sum-side twin: one limit rather than two, so no properness is used, `EReal`’s discontinuous addition never enters, and `E` stays at **layer A** where the book’s own `clFn_compLin` would have forced `FiniteDimensional ℝ E`. **The row’s count was slightly wrong**: the reduction was written out twice, both times in §16, and §23 had a *wrapper* rebuilding an `IsExactImage` out of a surface theorem — itself a symptom. All three are gone |
| 12.4 | **`IsExactImage.of_polyhedral`**, in `Polyhedral/Duality.lean`: `PolyhedralFn g → Proper g → A x₀ ∈ dom g → IsExactImage …` — Theorem 20.1’s companion for the *image* rule. That file has the two sum constructors and no image one, so the last clause of **both** Theorem 16.3 and Theorem 23.9 was unreachable from the backbone. The proof is entirely §19’s: `g*` is polyhedral (Theorem 19.2), `A*g*` is polyhedral with its infimum attained (Corollary 19.3.1), and a polyhedral proper function is closed, so Theorem 16.3’s closure formula has nothing left to close | §23 | **closed** — `IsExactImage.of_polyhedral` in `Polyhedral/Duality.lean`, sharing no step with the sum constructors, plus `epi_mapLin_of_polyhedralFn` and `exists_mapLin_eq_of_polyhedralFn` — **Corollary 19.3.1 with both halves**, the attainment half having existed only on the surface. **The second half of this row was false**: §16 did not carry the missing clause in its `## What is not here`; the string `polyhedral` did not occur in `Part3/Section16.lean` at all, so the clause was neither stated nor recorded as absent. It is stated now, as `theorem_16_3_polyhedral` and `theorem_16_3_polyhedral_attained` |
| 12.5 | **`indicatorFn_finsetSum`**, in `Indicator.lean`: `∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i)`, the `m`-ary `indicatorFn_add`. That lemma’s own docstring says "every intersection corollary in the book is the indicator instance of a statement about sums"; Corollary 23.8.1 is the `m`-ary one | §23 | **closed** — `indicatorFn_finsetSum` in `Indicator.lean`, beside `indicatorFn_add`. No `s.Nonempty` is needed: over `∅` both sides are `0`, since `⋂ i ∈ ∅, C i = univ`. It landed **below layer A** — the `Basic` section needs no algebraic structure on `E` at all |
| 12.6 | **`exists_monotone_ne_bot_ne_top_monotoneCurve_eq`** — every `∂f` on `ℝ` is the curve of a monotone `φ` that is finite somewhere | §24 | **closed**, in `Subgradient/Primitive.lean`, on `monotone_of_forall_ne_of_le_of_le` and `monotoneCurve_eq_of_forall_ne`. **The case split the item prescribed was unnecessary**: there is no need to treat `dom f` a singleton separately, because `ri (dom f)` is non-empty for any proper convex `f` and a subgradient there is real and lies between the two one-sided limits, so `Function.update (rightDeriv f) a y₀` works uniformly. §24 gains the book’s 9181 ⟺ 9195 in full and its `## Backbone gaps` is now "None" |
| 12.7 | **`∇(cl f) = ∇f` for a proper convex `f`** | §25 | **closed, and wider than asked** — `hasGradientAt_clFn_iff` and `differentiableAtFn_clFn_iff` in `Subgradient/Uniqueness.lean`, on the missing `ConvexFn.interior_dom_clFn` (`int (dom (cl f)) = int (dom f)`), plus pairing-general closedness-free forms of Corollaries 25.1.2 and 25.1.3. §25’s two corollaries lose `ClosedFn` and `corollary_25_1_2_clFn` is deleted — its reason for existing is gone. **The row said the book uses the remark for both corollaries; it uses it for 25.1.2 only**, and 25.1.3 inherits closedness-freedom *through* 25.1.2 — which costs two extra facts in Lean, because the backbone’s form of 25.1.3 is about subgradients |
| 12.8 | **`StrictConvexOnFn` has no supporting API** | §26 | **both API items closed, and the row contradicted itself about the home.** `strictConvexOnFn_iff_strictConvexOn` is in `StrictlyConvex.lean` as the row said; the sum rule is in **`Preservation.lean`** as `ConvexFn.add_strictConvexOnFn`, because `Preservation.lean` *imports* `StrictlyConvex.lean` — so it could not have been "`add_convexFn` with the arguments the other way round" in the latter without a twelve-line near-duplicate. Renamed too: the `X.add_Y` convention makes the receiver the first summand, which here is the convex one. **The dividend claim was also wrong**: the two §26 counterexamples were never blocked on this API — see §12.16 |
| 12.9 | **the conjugate’s `innerₗ` / `topDualPairing` bridge** | §26 | **closed** — `conj_innerL_eq_conj_topDualPairing` in `Subgradient/Rademacher.lean`, with the pointwise `topDualPairing_flip_toDual` beside it, which `mem_subgradient_innerL_iff` now also runs on (its local `key` step is gone). §26’s `private conj_pairing_eq` deleted |
| 12.10 | **`linFn_eq_toDual`** | §25 | **closed** — in `Surface/Common/Euclidean.lean` with `toDual_apply_eq_pairing` beside it; §25’s copy and §26’s `private` copy are both deleted, and no call site changed, since the bare names resolve through `Tdaf.Surface` |
| 12.11 | **`recessionCone_subgradient_eq_normalCone`** — the book’s p. 218 exercise (line 8477) | §25 | **closed, and the row named the wrong home.** It said "beside `subgradient_add_normalCone_dom_subset`", i.e. `Subgradient/Calculus.lean`. The four-line proof needs the `⊆` half *and* `add_smul_mem_subgradient`, both of which live in **`Subgradient/Reconstruction.lean`**, four levels above `Calculus.lean` in the import DAG (`Calculus → Uniqueness → Rademacher → Reconstruction`); moving them down is not possible. Worse, `Calculus.lean` is §12.1’s home, so following the row literally would have collided with the other backbone agent. `Reconstruction.lean`’s design note, which said the equality "is never needed", now says never needed *there* |
| 12.12 | **`Bifunction/Cofinite.lean` has one of the closing discussion’s three co-finiteness facts** (book 16693–16729), and its own `## What is not here` contradicts the paragraph §38 will need. Present: `cofiniteBifun_infConvBifun`, `adjointBifun_infConvBifun_of_cofinite`. Absent: that `Fλ`, `GF` and `F*` preserve co-finiteness (which needs the closedness-and-properness half of Theorem 38.3, and, for `GF`, `IsExactSum` over four spaces), and `dom F = ℝᵐ ∧ dom F* = ℝⁿ ⇒ co-finite`, which is Theorem 34.2 | §4.1 | open — **the one real gap Part VIII inherits.** Schedule it with `Section38.lean`, not ahead of it |

### What the Part VI round closed here

**§12.1 through §12.5 are all done**, and with them **§4.4 in full** — the `m`-ary consequence now
exists and Corollary 23.8.1 consumes it. `Part5/Section23.lean` lost its `## Backbone gaps` section
entirely, along with six `private` lemmas, and **Theorem 16.3's polyhedral clause is stated for the
first time**. That clause is not part of Theorem 16.3 in the book: it is an unnumbered remark at
line 5869, deferred there to Corollary 19.3.1, and no entry for it existed anywhere in this
repository.

Two of the five landed *below* the layer the surface proof sat at, which is the recurring dividend
of hoisting: `conj_compLin_eq_conj_compLin_clFn` needs no topology on `E` and no finite dimension on
`G`, and `indicatorFn_finsetSum` needs no algebraic structure at all.

| # | item | status |
|---|---|---|
| 12.13 | **Rename `IsExactImage.of_relint` → `of_relint_closed`**, and `of_relint_proper` → `of_relint`. `Duality/Exact.lean`'s docstring states the convention — "the unprimed name is the book's proper-convex statement" — and `IsExactSum` follows it while `IsExactImage` now does not. A future agent will guess `of_relint`, get the closed case, and pay the closure reduction a fourth time | **closed** — `of_relint` is now the book's proper-convex statement and `of_relint_closed` the closed one, matching `IsExactSum`. **The row's cost estimate was wrong**: not one call site but four, in `Subgradient/Preservation.lean`, `Part3/Section16.lean`, `Part5/Section23.lean` and `Part6/Section31.lean`, across six files once prose is counted. Two of the four sit in two different fix agents' fences, which is why this was done centrally rather than delegated |
| 12.14b | **Relocate `polyhedralFn_compLin`** from `Saddle/Correspondence.lean` (§37) to `Optimization/Perturbation.lean` — *its own docstring says that is where it belongs*. §31 cannot import a §37 module, so it restates the lemma locally as `polyhedralFn_neg_comp`. The same shape as §12.14, found independently from the other end of the library | §31 | **closed — but not at the named home, which was stale rather than wrong.** The row justifies its home by naming a neighbour, "beside `polyhedralFn_mapLin`" — and §12.14, three rows away, *moves that neighbour* in the same batch. It landed in `Polyhedral/Duality.lean`, which additionally serves `Part4/Section19.lean`, a third copy the row's literal home would have left in place. **Isolated in commit `12e6f71`** so the literal target can be restored independently. General rule: resolve a relocation row's named neighbour *after* applying the batch, not from the row text |
| 12.14 | **Relocate `polyhedralFn_mapLin`** from `Optimization/Perturbation.lean` (§29) to `Polyhedral/Duality.lean` (§20). It is Corollary 19.3.1's polyhedrality half and it is *above* the module that needs it in the import order, so `IsExactImage.of_polyhedral` carries a three-line local `have` instead of citing it. Everything its proof uses is already in the lower module's closure, and all four of its consumers sit above | **closed, and the row's consumer claim is false.** Only §19's `corollary_19_3_1_image` had `Polyhedral/Duality.lean` in its closure; `Optimization/Perturbation.lean` and `Saddle/Correspondence.lean` each needed a **new import** (acyclic, three modules of closure each). Had the cycle run the other way this would have been unbuildable exactly like §12.4 was. And there are **five** call sites, not four — the row omits `Part6/Section31.lean:593`. **An import-closure check has two halves — prerequisites below and consumers above — and a row can be right about the first and wrong about the second.** The same false claim sat in `Polyhedral/Duality.lean`'s design notes and in `api.md:1141`; both corrected |
| 12.16 | **§26's two counterexamples of pp. 253–254**, whose positive halves are still unproved. They were filed as a dividend of §12.8 and **were never blocked on it**: `ConvexFn.add_strictConvexOnFn` does not apply, because neither summand of `ξ₂²/2ξ₁ + ξ₂²` is strictly convex on the open quadrant — the first is positively homogeneous of degree 1 and so affine along every ray, the second is constant in `ξ₁`. What makes the sum strict is that their directions of affineness are disjoint, which is a case split, not a sum rule. And past the new bridge lies a wall Mathlib shares: `strictConvexOn_of_deriv2_pos` is one-dimensional and there is no positive-definite-Hessian criterion in several variables anywhere in Mathlib. What the claims actually need, in order: `ri (dom f)` computed (~40 lines, no convex-analytic content), strict convexity by the case split, and for `essStrictlyConvexFn` also the blow-up of `‖∇f‖` at the quadrant boundary — the larger half | §26 | **the p. 254 half is closed; the p. 253 half stays open, and its scope warning is confirmed.** Closing it needs essential smoothness — gradient blow-up at the quadrant boundary for a two-variable function with a square root — which is real-analysis work, not convex analysis, and so falls under the round's standing scope limit. Left deliberately, not forgotten |
| 12.17 | **Two relocations out of `Subgradient/Uniqueness.lean`**, both parked there because that is the file §12.7 named. `ConvexFn.interior_dom_clFn` belongs beside `ConvexFn.relint_dom_clFn` (Corollary 7.4.1) in `RelativeInterior.lean`, which it is proved from; only `Convex.interior_subset_relint` from `Subgradient/Bounded.lean` stands in the way. `posHomogeneous_clFn_and_supportSet_clFn` should be split in two and moved beside `clFn_eq_supportFn_of_posHomogeneous` in `Duality/Support.lean`; note the first half's statement does not mention `B`, so it needs `include B in` (PAIR4) unless a pairing-free proof is written — and the natural one wants "the closure of a cone is a cone", which exists only as a *surface* declaration in `Part2/Section06.lean` (LIB16) | sweep | **closed, and both of the row's warnings were confirmed accurate** — the `include B in` requirement and `isCone_closure` being surface-only. Recorded as confirmed because that is the rarer outcome this round. The `Convex.interior_subset_relint` move the row identifies as the blocker was done post-merge (it is the whole content of a `section Relint` in a file about subgradient boundedness, both ingredients at or below `RelativeInterior.lean:197`, three call sites), and the backbone `isCone_closure` with it. Worth generalising from the second half: **check whether the named blocker is itself a three-line consequence of the destination** — this one was |
| 12.18 | **Two backbone modules still have no `api.md` record**, against the file's own "one record per module under `Tdaf/`": `Subgradient/EssentiallySmooth.lean` and `Subgradient/StrictlyConvex.lean` — 21 records for 23 modules in that directory. `Legendre.lean`'s record names both in passing but gives neither a declaration list, which is what the file exists for. §11.22 was closed on the *new* modules of the product round and never audited the old ones | sweep | **done** — both records written; the `Subgradient/` directory now has 23 records for 23 modules |
| 12.28 | **`Subgradient/Calculus.lean` has every sum rule and no scaling rule at all.** Wanted: `subgradient_coe_mul` (`∂(cf) = c ∂f` for `c > 0`); `subgradient_coe_mul_affineMap`, the same for an **arbitrary real** `c` when `f` is affine, which equality-constraint multipliers need because theirs may be negative; `subgradient_coe_affineMap` (`∂a(x)` is the Riesz vector of `a.linear`, Theorem 23.2's affine case); and `subgradient_zero_mul`. Rockafellar uses the first two without comment at line 11169. **This is the most reusable gap the Part VI round found** | §28 | **closed** — all four in `Subgradient/Calculus.lean`, and the row's "most reusable" estimate held up: three of the four immediately became consumers of `injective_of_separatingDual` (§12.20), which is how that row's own undercount was found |
| 12.29 | **Non-negative scalar multiples of an `EReal`-valued convex function have no API.** Wanted in `Convex/Epigraph.lean` and `Convex/Closure.lean`: `convexFn_coe_mul`, `closedFn_coe_mul`, `proper_coe_mul`, `dom_coe_mul`, `epi_coe_mul` and the `scaleSnd` map they run on; plus `closedProperConvexFn_coe_affineMap` (an affine function read into `EReal` is closed proper convex — used four times in §28 alone, and wanted by every section with affine constraints) and `closedProperConvexFn_finsetSum` (`properConvexFn_finsetSum` exists; the closed version does not). The supporting `EReal` step is `coe_mul_add_coe_le_coe_mul_iff` (`cA + ct ≤ cB ↔ A + t ≤ B` for `c > 0`) → `Order/EReal.lean`, which has `coe_mul_le_coe_mul_iff` and no distribution lemma to feed it | §28 | **the `EReal` step closed** — `coe_mul_add_coe_le_coe_mul_iff` and the `coe_mul_add_coe` that distributes for it are public in `Tdaf/Order/EReal.lean`, and §28's private copy is gone. The convex-function API (`scaleSnd`, `convexFn_coe_mul`, `closedFn_coe_mul`, `proper_coe_mul`, `dom_coe_mul`, `epi_coe_mul`, `closedProperConvexFn_coe_affineMap`) is closed too. Only `closedProperConvexFn_finsetSum` remains, and **neither home the row names can hold it**: `Closure.lean`'s entire import closure is five modules (`Epigraph`, `Indicator`, `Operations/Epi`, `Separation`, `Order/EReal`), while the proof needs `ClosedProperConvexFn.add` (`Recession/Closedness.lean`) and `ConvexFn.sum` (`Operations/Basic.lean`) — neither in the closure, and `Epigraph.lean` is lower still. Home is **beside the binary rule** in `Recession/Closedness.lean`; `Section28.lean` keeps its `private` copy meanwhile. Noted in passing: `ClosedProperConvexFn.add` is *itself* misfiled — it carries `omit [FiniteDimensional ℝ E]`, uses no recession theory, and is `ConvexFn.add` plus `LowerSemicontinuous.add'`. LIB28 again: the prerequisite is misfiled, not the new lemma |
| 12.30 | **`isCompact_setOf_le` is `private` in `Optimization/Minimum.lean`.** Corollary 28.1.1 had to route through `isCompact_iff_recessionCone_eq_zero` plus `recessionCone_setOf_le` instead; making it public shortens that proof by **four** lines — not the twelve this row claimed for four rounds. F4 measured it: Corollary 28.1.1 uses that pair *three* times, and only one is the ⇒ direction `isCompact_setOf_le` packages; the other two run the ⇐ direction, compactness *out of* a recession-cone computation, for which there is no lemma at all. Trivial, and a reminder that `private` is a claim about who needs a lemma | §28 | **closed** — public, with a docstring saying why (it is not an implementation detail of Theorem 27.2; Corollary 28.1.1 wants exactly that set with exactly those hypotheses) and a `Main results` entry so the next search finds it. Collected by F4 — and worth **four** lines, not the dozen I asserted when closing this. I inherited that figure from §28's gap note and repeated it into both the row and the docstring without measuring; **the docstring still says “a dozen” and must be corrected after the merge** |
| 12.31 | **The `s`-fold product decomposition `ℝ^{n₁} × ⋯ × ℝ^{n_s} ≃ ℝⁿ`**, with transport of `dom`, `argmin` and `ri`. `EuclideanProd.lean` has only the binary `euclideanProdEquiv`. This is what §28's **decomposition principle** (11309–11596) needs, and why that passage is not carried: its core is one sentence — separable `fᵢ` makes `h = h₁ + ⋯ + h_s`, so Theorem 28.1's reduction splits into `s` problems — and carrying a binary special case of an `s`-fold principle would misrepresent the book. Everything after 11395 is a numerical illustration with no statement a later section cites | §28 | **closed — in a different shape, because the row asks for the wrong object.** The decomposition passage (11309–11385) never uses the isometry and **never mentions `ri`**: the string `ri` does not occur in that range, verified directly. What it needs is the separable-sum dictionary on a **dependent** finite product — `dom_sepSum` and `argmin_sepSum`, now in a `Pi` section of `Optimization/Minimum.lean`, **below every layer of D9** (`argmin`, `dom`, `Proper` all take a bare `{E : Type*}`). Where the isometry dissolves is precise: the coordinate splitting is hypothesised as a `≃ₗ[ℝ]`, not an `≃` — a bare bijection `∀ k, Rn (nk k) ≃ Rn n` exists for *any* `nk`, both sides having cardinality continuum, so an `≃` would carry none of `n₁ + ⋯ + n_s = n` — and the transport is then just `argmin_comp_of_surjective`. Properness is load-bearing, not decoration: the `⊆` direction cancels an erased sum and `EReal` is not cancellative (ER1); `dom_sepSum` needs only `∀ i z, h i z ≠ ⊥` because `⊥ + ⊤ = ⊥` lets a sum be finite while a summand is `+∞`, while `argmin_sepSum` needs both halves (over `Fin 2` with `h₀ ≡ ⊤` and `h₁ = id`, dropping `dom_nonempty` makes the left side everything and the right side empty). **Generalise: an item asking for an isomorphism to transport a property is usually asking for the wrong object** — read the head symbols, and if they are `dom`, `argmin`, `epi`, `Set.preimage`, a bare surjection does it. Recorded so nobody budgets for it: *if* the isometry is ever wanted it is three Mathlib names — `LinearIsometryEquiv.piLpCurry`, `LinearIsometryEquiv.piLpCongrLeft`, `finSigmaFinEquiv` — but it should not be built, because the principle does not need it |
| 12.32 | **`pairing_two` is written three times, privately.** `Rn 2`'s pairing formula `⟨u, v⟩ = u₀v₀ + u₁v₁` is proved verbatim in `Part5/Section23.lean:316`, `Part5/Section26.lean:383` and `Part6/Section32.lean:749` — three agents, three rounds, one statement, character for character. It is what every two-dimensional counterexample in the book needs, and there will be more of them. Belongs in `Surface/Common/Euclidean.lean`, public, with the `Fin n` general form (`pairing n u v = ∑ i, u i * v i`) beside it | merge of Part VI | **closed, and the row undercounts: four copies, not three** — `Part6/Section28.lean` had a fourth. "Character for character" was true of the **statements only**: three different proofs, three different docstrings. A duplicate sweep that greps the signature line finds them; one that greps the proof text does not. The same pass found `continuous_coord` written `private` at `Fin 1` and at `Fin 2` in two more sections, and it is now public beside them |
| 12.33 | **`lift_mem_coneHull_liftPD` is proved twice, and the second file imports the first.** `Caratheodory.lean:665` has it `private` on `convexHull ℝ P + cone D`; `HullDirections.lean:366` has it public on `convexHullPD P D`, which is that expression by `rfl` — and `HullDirections` imports `Caratheodory`. The two proofs take different routes (finite representation vs. `convexHull_min` induction), so this is not a copy-paste but an independent rediscovery, which is worse: nothing pointed the second author at the first. Drop `private` in `Caratheodory.lean` and make `HullDirections`' version the one-line restatement | merge of Part VI | **closed — but the row names the wrong copy to keep.** Dropping `private` in `Caratheodory.lean` would have kept the finite-dimensional proof and discarded the layer-A one; the correct move was to relocate `HullDirections.lean`'s proof **down** into `Caratheodory.lean`. And "make it the one-line restatement" is not an option at all: two public declarations of the same name in two modules is a collision, and with the statements `rfl`-equal the restatement should simply not exist. Consequence recorded in place: `Recession/Cone.lean`'s `## Layers` note said finite-dimensionality "enters exactly once"; it now enters twice |
| 12.23 | **Six small gaps from §30, all in the concave mirror.** `domBifun_neg` (`domBifun (-G) = domConcaveBifun G`, two lines) → `Optimization/Normal.lean`; without it `ConcaveStronglyConsistent G` cannot be turned into `StronglyConsistent (-G)` and Cor 30.5.2's primal half cannot start. **Theorem 30.1's properness clause as a biconditional** — `properConcave_graphFn_adjointBifun_iff`; the backbone has only "somewhere `≠ ⊥`", one direction — → `Optimization/Adjoint.lean`, on `proper_compLin_of_surjective` (`Proper (compLin g A) ↔ Proper g` for surjective `A`, eight lines) → `Operations/Image.lean`. `mem_argmax_iff_eq_iSup` → `Optimization/Minimum.lean` beside `argmax`; every §30 statement about "an optimal solution to `(P*)`" pays it once. `le_zero_of_forall_le_pos` (four lines from `EReal.lt_iff_exists_real_btwn`) → `Order/EReal.lean`; both §30 counterexamples run on it | §30 | **closed** — `le_zero_of_forall_le_pos` was done centrally with §12.22 (three agents wanted `Order/EReal.lean`); `domBifun_neg`, the Theorem 30.1 properness biconditional, `proper_compLin_of_surjective` and `mem_argmax_iff_eq_iSup` followed in the fix round. Note the row says "six" and lists five |
| 12.24 | **The concave-side biadjoint**, the mirror of `concaveAdjointBifun_adjointBifun_eq_clBifun` → `Optimization/Adjoint.lean`. There is no `clConcaveBifun` either. It is what the **surjectivity half of Theorem 30.1's one-to-one correspondence** needs, which is the one clause of §30 with no declaration | §30 | **the clause is closed; the row was false in the same way §4.6 was.** The backbone does **not** lack a concave biadjoint: `lowerAdjointBifun_lowerAdjointBifun_eq_clBifun` in `Bifunction/Algebra.lean`, read at `F = G⁎`, *is* it — and its own docstring says so. Worse, the row's proposed home `Optimization/Adjoint.lean` is **imported by** `Bifunction/Algebra.lean`, so the theorem that already exists sits above the home and could never be cited from it; building it natively there meant ~120 lines near-duplicating the module above. The clause the row exists for was delivered directly instead, as `theorem_30_1_surjective`, so **§30 now has a declaration for every numbered clause**. Only the *name* `clConcaveBifun` is still missing, and its home is `Bifunction/Algebra.lean`, not `Optimization/Adjoint.lean` |
| 12.25 | **`Optimization/Maximum.lean` proves the two *ends* of Theorem 32.3 and not the statement between them**, so §32 re-ran the whole lineality decomposition on the surface (~55 lines) to recover the book's form. Wanted: `ConvexFn.iSup_extremePoints_inter_of_isCompl` and `exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl`, stated for an arbitrary complement `N` of the lineality space — **strictly more general than the book's `L⊥` and needing no inner product** — with `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` re-derived from the second rather than duplicating the decomposition inline | §32 | **closed — and the *mechanism* the row proposes is impossible.** `exists_isMaxOn_of_polyhedral_of_bddAboveOnRays` cannot be "re-derived from" the attainment clause: that clause **transfers** a maximiser it is given, while Corollary 32.3.3 must **produce** one. Two shared helpers removed the duplication instead. Layer dividend worth keeping: `ConvexFn.exists_mem_inter_eq_of_isCompl` needs no topology at all, so it sits at layer A |
| 12.26 | **`ConvexFn.iSup_extremePoints_of_containsNoLine` asks for a uniform bound where its proof needs only `BddAboveOnRays`.** Replacing the hypothesis changes nothing in the proof — only `bddAboveOnRays_of_forall_le hbdd` disappears, `ConvexFn.exists_mem_convexHull_extremePoints_le` having already been generalised. As stated it does **not** cover the `L = 0` case of Theorem 32.3, contrary to `Maximum.lean`'s own `## What is not here`, which calls it one of Theorem 32.3's "two specialisations". Separating witness: `C = {(ξ₁, ξ₂) | ξ₁² ≤ ξ₂}` with `f (ξ₁, ξ₂) = ξ₁` — every half-line in `C` is vertical so `f` is constant along it, but `f` is unbounded above on `C` | §32 | **closed, and the row was exactly right** — hypothesis replaced, proof unchanged but for the line the row predicted would vanish, and the separating witness verified and now quoted in the backbone docstring. Recorded as accurate deliberately: of the rows this round touched, this is one of the few that needed no correction |
| 12.27 | **Two more small §32 gaps.** `FinitelyGenerated.finite_extremePoints` → `Representation.lean` beside `extremePoints_convexHullPD_subset`: it is derived inline inside `exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays` and again on the surface, three times in all. `normalCone_innerₗ_closedBall` — the normal cone to the Euclidean unit ball at a unit vector, which is the whole content of the book's remark at line 14061 — → `Subgradient/Rademacher.lean` beside the inner-product bridges; proved on `Rn n` in ~30 lines via the equality case of Cauchy–Schwarz, and the proof is space-agnostic | §32 | **`FinitelyGenerated.finite_extremePoints` closed, at a different home; `normalCone_innerₗ_closedBall` open.** The row's home is **unbuildable, for a failure mode not seen before**: `FinitelyGenerated` is defined in `Polyhedral/Defs.lean` and `finite_extremePoints_convexHullPD` in `Representation.lean`, and those two modules are **incomparable** in the import DAG — neither imports the other — so *neither* can host the lemma. Every previous instance of a bad home was "prerequisite above target", which moving one module fixes; this one has no such fix. It landed in `Polyhedral/Faces.lean`, which imports both, in the layer-A `Counting` section |
| 12.21 | **Three more backbone gaps from §31**, none blocking a numbered result, each proved `private`. **Corollary 30.5.2** → `Optimization/Normal.lean` (`exists_infBifun_eq_of_concaveStronglyConsistent`); the backbone has Theorem 30.4(b) and stops there, and this is what Cor 31.2.1(b)'s attainment runs on. **Theorem 30.5's concave side** → same module: both halves exist (`mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker`, `concaveAdjointBifun_zero_apply`) and are never put together — note **§30 reported this same gap independently**, so two surface files now carry it. **`conj` of a finite direct sum** → `Duality/FiniteProduct.lean` (`conj_piFn`); nothing computes it, which is why §31's Problems (I)/(II) cannot be stated at all | §31, §30 | **closed** — all three landed; `conj_piFn` is public in `Duality/FiniteProduct.lean:340`. One correction to the row: it says the three were "each proved `private`", but `conj_piFn` had **never been proved anywhere** — `grep -rn "piFn" Tdaf/` at the base commit found only a docstring wish. §31's own gap note was the accurate one ("cannot be stated at all"); the ledger row overstated what was on hand |
| 12.22 | **An `EReal` infimum over a product does not split anywhere public.** Wanted in `Order/EReal.lean`: `iInf_prod_add`, with `add_iInf` / `iInf_add` / `coe_add_iInf` beside it. `Order/EReal.lean` has only the *supremum* form `biSup_add_biSup`, whose hypothesis is on the values rather than on the extrema; `Bifunction/Algebra.lean` has the `≠ ⊥` variants and all three are `private`. Both finiteness hypotheses are necessary — `ψ i = -i` on `ℕ` and `φ ≡ ⊤` break it | §31 | **closed** — `Tdaf/Order/EReal.lean` gained ten public lemmas: `coe_add_iInf`, `coe_sub_iInf`, `add_iInf_of_ne_bot`, `iInf_add_of_ne_bot`, `iInf_add_eq_bot`, `iInf_add_iInf_of_ne_bot` and `iInf_prod_add`, plus `le_zero_of_forall_le_pos`, `coe_mul_add_coe` and `coe_mul_add_coe_le_coe_mul_iff`. **The row understated what already existed**: `Bifunction/Algebra.lean` had four of the seven infimum lemmas written out and `private`, so most of this was promotion, not proof. All six private copies (five there, one in `Part6/Section28.lean`) are deleted and their call sites repointed. `iInf_prod_add` is stated under `(⨅ ψ) ≠ ⊤ ∧ (⨅ φ) ≠ ⊤` rather than the witness-value hypotheses §31 proposed — strictly more general, since it *handles* the `⊥` corners instead of excluding them. Done centrally, before the fix agents were spawned, because three of them would have contended over this file |
| 12.19 | **`autoImplicit` is still on in this repository.** `lakefile.toml` sets `relaxedAutoImplicit = false` but never `autoImplicit = false`, so a single-letter identifier in a theorem statement is silently auto-bound as an implicit with its type inferred from surrounding applications — and the file builds with **zero warnings**. Mathlib sets `autoImplicit = false`; this repository does not. One instance was found and fixed in `Part6/Section27.lean`; there is no telling how many others exist, because the symptom is nothing at all | §27 | open — **a six-module probe with `-DautoImplicit=false` came back clean** (`Indicator`, `Optimization/Minimum`, `Part5/Section26`, `Duality/Polar`, `Surface/Common/Euclidean`, `Order/EReal`), so flipping the flag looks cheap. Do it as its own change, with a full build, once no agent is live |
| 12.20 | **Five relocations out of `Part6/Section27.lean` and `Optimization/Minimum.lean`**, each proved `private` and none blocking anything: `proper_indicatorFn` → `Indicator.lean` (both halves exist, `dom_indicatorFn` and `indicatorFn_ne_bot`, and nothing packages them — every §27/§28 statement minimising `h + δ(·|C)` wants it); `Polyhedral.biInter` and `Polyhedral.iInter` → `Polyhedral/Ops.lean` (the binary `Polyhedral.inter` exists, the finite-family forms do not); `polyhedralFn_setOf_le` → `Polyhedral/Function.lean` (`{x | f x ≤ 0}` is a preimage of `epi f` by `Iff.rfl`, then `Polyhedral.preimage`); and `injective_of_separatingDual` → `Duality/Level.lean`, beside `separatingRight_flip_of_separatingDual`. **The last has a consequence worth stating centrally**: `Gradient.lean`'s `subgradient_eq_singleton_of_dirDeriv_eq` and `Perturbation.lean`'s `kuhnTucker_eq_singleton_of_dirDeriv_eq` both take `Function.Injective B.flip` as an explicit hypothesis — genuinely needed, since they are layer A — but **no normed-space caller ever has to supply it**, and callers do not currently know that | §27 | **closed, and three of the row's five names were wrong.** `Polyhedral.biInter` and `Polyhedral.iInter` are `polyhedral_biInter` / `polyhedral_iInter` (now in `Polyhedral/Ops.lean`); `polyhedralFn_setOf_le` **already existed** as `PolyhedralFn.polyhedral_sublevel` in `Polyhedral/Function.lean:86`, so that quarter of the row was a duplicate request, not a gap; and `Polyhedral.preimage`, which the row's proposed proof cites, **is not a name at all**. Fixed so the next grep hits. The final item's own claim *was* right, and its undercount is the interesting part: `injective_of_separatingDual` has **five** consumers, not two — `Subgradient/Calculus.lean`'s three single-point rules take the same hypothesis |
| 12.15 | **The `m`-ary normal-cone pair** in `Subgradient/Calculus.lean`: `normalCone_finsetSum_subset` and `IsExactFinsetSum.normalCone_biInter`, the `m`-ary mirrors of the two the binary section already has. About twelve lines on the now-hoisted `indicatorFn_finsetSum`; they would make §23's Corollary 23.8.1 a one-liner and remove its last private induction | open — deliberately not done, as outside the item as briefed |
| 12.34 | **`invBifun` and `inverseBifun` are the same definition, declared twice, both public.** `Bifunction/Algebra.lean:482` and `Saddle/Minimax.lean:872`, bodies identical (`fun x u => -(F u x)`), each with its own `@[simp]` apply-lemma and its own involution lemma. **Neither module imports the other, so Lean's “already declared” error — the mechanism that has caught LIB1 seven times — never fires.** Found by grepping *bodies* rather than names | merge of Part VI | **closed** — one definition, named `inverseBifun` (Rockafellar's own word, book 15507; `inv` is `Inv.inv` in Mathlib), in `Optimization/Perturbation.lean` beside `Bifun` and `graphFn`. That home adds **no import edge**: it is already in the transitive closure of both claimants, though not a direct import of either, which is why a first check for a direct `import` line said otherwise. Renaming cost 74 sites in `Algebra.lean`, 1 in `Cofinite.lean`, 10 in `Part6/Section30.lean`, and pushed eight lines past 100 codepoints in two BLD7 rounds. **The live hazard this removed**: `Part6/Section29.lean` and `Part6/Section30.lean` each had *both* names in scope, so a goal could be written with one and the lemma about it stated with the other — `rfl`-equal, with nothing (not `simp`, not the elaborator, not a name clash) to report the mismatch |

### What the fix round found about the ledger itself

Eight agents worked these rows. **Every one of them found at least one row wrong**, and two of the
wrong rows were written by me, in the same session that dispatched them. This is not a tally of
carelessness — it is a measurement of how a ledger row decays, and the failure modes are worth
naming because each one is invisible to the check that would seem to catch it.

* **Wrong home, unbuildable (§12.24).** The row asked for a concave biadjoint "the backbone lacks",
  in `Optimization/Adjoint.lean`. The thing exists — in `Bifunction/Algebra.lean`, which *imports*
  the proposed home. A row can name a home that the thing it asks for could never be cited from.
* **Wrong home, unbuildable in a new way (§12.27).** `Representation.lean` and `Polyhedral/Defs.lean`
  are **incomparable** in the import DAG. Every prior bad home was "prerequisite above target",
  which moving one module fixes. This one has no fix, and no import-closure check phrased as
  "is X below Y" reports it, because the answer is *neither*.
* **Wrong home, stale rather than wrong (§12.14b).** The row justified its home by naming a
  neighbour, and another row *in the same batch* moved that neighbour. Resolve a row's landmarks
  after applying the batch, never from the row text.
* **Right about prerequisites, wrong about consumers (§12.14).** "All four of its consumers sit
  above" — one did, and there were five. **An import-closure check has two halves.**
* **Wrong names (§12.20).** Three of five declaration names did not exist; one of the three named a
  lemma that *did* exist under another name, so a quarter of the row was a duplicate request rather
  than a gap; and the proof sketch cited `Polyhedral.preimage`, which is not a name at all.
* **Wrong mechanism (§12.25).** The row's proposed derivation is impossible in the direction it
  states: one clause *transfers* a maximiser, the other must *produce* one.
* **Wrong object entirely (§12.31).** The row asked for an isometry to transport `dom`, `argmin`
  and `ri`. The book passage never mentions `ri` and never uses an isometry. Read the head symbols:
  when they are `dom`, `argmin`, `epi`, `Set.preimage`, a bare surjection does it.
* **Wrong copy named as the survivor (§12.33, §11.15).** Twice, the copy the row implied should die
  had the better proof or the better layer. A duplicate sweep must read both **bodies**, not just
  decide which *home* is right.
* **Wrong count, in both directions (§11.16, §12.14, §12.20, §12.23, §12.32).** Undercounts are the
  norm. §12.32 said three copies and there were four; §11.16 said two call sites in two files and
  there were four in three — and the missed one **does not match the grep the row's own phrasing
  tells you to run**, because it spells the same coercion differently. §12.23 says "six" and lists
  five.
* **A blocker that was itself three lines from the destination (§12.17).** Worth asking of every
  blocker a row names.
* **A blocker recorded in our own documentation that did not exist (§11.18).** `api.md` warned of a
  name clash between `convex_polarSet` and `Duality/Polar.lean` — which has `convex_polarCone`, a
  different spelling. That false warning is why the lemmas sat misfiled, and it blocked the row for
  two rounds. **A warning in our records earns the same grep a remediation row does.**
* **A blocker no import check can see (§11.18 again).** `convex_polarSet` was declared 650 lines
  below the target section **in the same file**. The grep finds it; the elaborator does not.

Two of the errors were mine and are worth stating plainly. I wrote "about a dozen lines" into both
§12.30's row and the docstring it produced, having inherited the figure from §28's gap note without
measuring; it is four. And I closed §12.22 with "all six private copies are deleted" after sweeping
the files I already knew about rather than the tree; five more were still there. **An item closed
centrally is not closed everywhere** — that is LIB24, at the ledger's own expense.

The reusable conclusion: a remediation row is a claim with a shelf life, and the parts that decay
first are the ones a reader is least likely to re-check — the home, the count, and the names. The
mathematical content held up almost everywhere. §12.26 is the row that needed no correction at all,
and it is recorded as accurate for exactly that reason.

### What the Part V round closed

Three remediation items, and two of them by finding out that they were not what they said.

* **§2.2 and §2.3 are done.** `reflect` occurs in no hypothesis of `Bifunction/Process.lean`:
  `coadjointProcess_add` and `coadjointProcess_comp` now carry Theorems 39.5’s and 39.8’s own
  hypotheses verbatim, and the six closed halves are stated about the adjoints themselves. The
  involutions are bundled as `reflectAut : AddAut` and `saddleSwapOrderIso`. **Part VIII’s §2.2
  gate is closed.**
* **§4.1 is closed by measurement.** See the row above: 32 statements, not ~100; four of the six
  named sections contribute zero, because the book’s `A*` there is a *defined operation* and not a
  transpose; and the surface discharges the datum at eight call sites in all of Parts I–IV. The
  right response to "this is the largest single friction on both future surfaces’ critical path"
  was to count it, and counting it cost a fraction of what building `HasTranspose` would have.
  One module came out of the exercise — `Bifunction/LinearProcess.lean`, which is the one thing in
  Part VIII that a transpose of a linear map is actually about.
* **§4.4’s constructors are done and its consequence is not** — §12.1. A gate is not closed because
  the interface it asked for exists.

### Documentation errors the round found

`part5.md` was wrong five times, and `inventory.md` inherited two of them.

* **Corollary 24.2.1 was recorded as deferred by scope**, as "one-dimensional Lebesgue theory". The
  backbone proves it in full in `Subgradient/Integral.lean`, and *that module’s own docstring says
  the stated reason does not apply*: the fundamental theorem of calculus applies directly, with no
  improper integral and no Lebesgue theory of monotone functions. A scope deferral is a claim too,
  and LIB17 covers it.
* **Theorem 24.2’s existence clause was recorded as out of reach.** `Subgradient/Primitive.lean`
  builds `f` from the graph `Γ(φ)`, which is a maximal monotone relation, with no integral
  anywhere. Only the *formula* `f(x) = ∫ₐˣ φ` is genuinely deferred, and nothing in the book uses
  it — Theorem 24.9’s proof cites Corollary 24.2.1, not the formula.
* **Three of the four "backbone it specialises" columns were incomplete**, and in each case the
  missing modules were the ones that closed the section’s hardest items: §24 also needs
  `Subgradient/{Primitive,Integral}.lean`, §25 six modules rather than three, §26 seven rather
  than two.
* **§25’s row said `0/11 G`** — no result of the section general. Three are: Theorem 25.1’s
  forward half, both halves of Corollary 25.1.1, and Theorem 25.4’s density clause.
* **The advice on Theorem 23.8 was backwards.** `part5.md` recommended the book’s ALTERNATIVE PROOF
  as "the better route for a port, since it avoids §16’s conjugacy machinery". It reduces `m` to
  `2` by induction on Theorem 6.5 and omits the polyhedral clause; the printed proof runs on
  `IsExactFinsetSum.of_relint`, which is `m`-ary and discharges the qualification once. The
  alternative is the one that puts the induction back.

And one error of the *briefs*, not of the plan: the `G/C` column of a Part table is the
general/concrete split, and three section agents in a row were handed it as a theorem/corollary
split. §23 is 10 theorems + 6 corollaries, §24 is 9 + 2, §25 is 7 + 4, §26 is 5 theorems +
2 lemmas + 4 corollaries. Where a plan’s table is terse, the brief that quotes it should quote the
header too.

### Book findings from the round

* **Line 8477’s exercise is not discharged where the book says it is.** Rockafellar leaves
  `rec (∂f(x)) = N_{dom f}(x)` as an exercise in §23 and says the verification "will be given later
  as part of the proof of Theorem 25.6". The proof of Theorem 25.6 uses only the inclusion `⊆`, so
  nothing discharges it on the way. §25 discharges it directly, in four lines and independently of
  Theorem 25.6 (§12.11), and §23 assumes it nowhere.
* **Theorem 26.5 says "closed convex function" where its own proof needs "closed *proper*
  convex".** Its first assertion is deduced from Corollary 26.3.1 and its Legendre-conjugate clause
  from Corollary 26.4.1, both stated for proper functions. Nothing is lost by adding `Proper`: an
  improper closed convex function is `+∞` everywhere or `−∞` on `cl (dom f)`, and in neither case
  is it differentiable on a non-empty interior, so both sides of the equivalence fail.
* **Theorem 26.4’s hypotheses exceed what its first two clauses need.** Well-definedness of `g` and
  the formula `g = f*` on `D` follow from convexity alone, at each point where a gradient happens
  to exist. The book’s closedness and global differentiability are what make the *domain* `D`
  interesting, not what make the value well defined.
* **Corollary 26.3.3’s "`A` maps `ℝⁿ` onto `ℝᵐ`" is used only through injectivity of `A*`** — the
  book’s own proof says so, parenthetically.
* **Theorem 24.5 leaves properness implicit.** Rockafellar asks only that `f` be convex and finite
  on the open convex `C`, never proper. The two are the same here — an improper convex function is
  `-∞` throughout `ri (dom f)` (Theorem 7.2), `C` is open and inside `dom f`, and the theorem
  quantifies over a point of `C` where `f` is finite — so §24 pays one eight-line `private` lemma
  and states the book’s hypotheses verbatim rather than adding one. Not a defect: a place where a
  naive transcription would have been *stronger* than the book.
* **Two theorems need less than the book gives them.** Theorem 23.5’s clauses (a), (b) and (c) need
  neither convexity nor properness, and Theorem 24.4 needs neither convexity nor closedness, only
  lower semicontinuity and properness — the backbone writes the graph of `∂f` as an intersection of
  preimages of `epi f` and never uses convexity. In both cases the surface states the book’s
  hypotheses and records the difference.
* **Theorem 24.7’s constant is at least the book’s `α`, not equal to it.** Rockafellar defines
  `α = sup {|x*| : x* ∈ ∂f(S)}` and proves two inequalities for it; the backbone produces a Lipschitz
  constant on a compact collar of `S` and reads all three statements off it. What is stated is the
  existence of *some* `α` with the three properties — implied by, not equivalent to, the book’s
  sharper reading, and what every consumer uses.
* **Rockafellar’s warning at line 9631 is load-bearing and is honoured.** Maximal *monotonicity* of
  `∂f` (Corollary 31.5.2) does **not** follow from Theorem 24.9 plus "cyclically monotone implies
  monotone": a mapping maximal in the smaller class need not be maximal in the larger. §24 states
  `theorem_24_9` for maximal *cyclic* monotonicity only and `isMonotoneRel_subgradientRel_rn` for
  plain monotonicity, with no bridge, and the `n = 1` coincidence separately — which is exactly why
  Theorem 24.3 can be stated for maximal chains at all.

---
