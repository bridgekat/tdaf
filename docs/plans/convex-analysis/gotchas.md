# Lean and Mathlib gotchas

Only what cost real time to find. Trivia that an error message explains on its own does not belong
here, and neither does anything a reader would derive from the entry above it.

**This file is grouped by cause, not by date.** Nine tenths of what goes wrong is one of a dozen
recurring failures wearing a new head symbol, so the shape is: one entry per cause, with the
instances that have actually bitten listed under it. If you hit something new, add it to the entry
it belongs to rather than to the end — an entry that already carries six instances is telling you
something a 385th numbered paragraph would not.

Entries are tagged by section — `EL` elaboration, `LINT` linters, `DEP` deprecations, `ER` `EReal`,
`SET` sets and cones, `PAIR` the pairing classes, `LIB` this library, `BLD` the toolchain — so a
reference like `EL2` says where to look without a lookup. The tags deliberately do not collide with
the plans' design decisions `D0`–`D12`, and the numbering within a section carries no history: the
384-entry chronological list this replaced is in the git history of `NOTES.md` if a specific episode
is ever wanted.

---

## EL — Elaboration, unification, rewriting

**EL1. Dot notation dies on any `def` that unfolds to a Π-type, and the error names `Function`.**
`hC.foo` for `hC : Convex ℝ C` reports *"The environment does not contain `Function.foo`"*, because
elaboration whnf's the type and looks up the head. Write `Convex.foo hC …`. The predicates that
behave this way: `Convex`, `IsCompact`, `ContinuousAt`, `Monotone`, `LipschitzOnWith`,
`AffineIndependent`, `ClosedFn` / `ClosedBifun` / `ConvexBifun` (they unfold to `Eq`), and
`ConvexFn.convex_dom`'s *result*, which prints unfolded. Structures — `ConvexFn`, `Proper`,
`ConcaveConvexOn` — are fine.

Two corollaries worth having separately:

* **A `Function.foo` error can also mean a missing import.** If `Foo.foo` exists upstream but not in
  this file's import closure, the lookup falls through to the unfolded head and gives the same
  message. `Convex.sum_mem` is in `Mathlib.Analysis.Convex.Combination`, *not* in
  `Mathlib.Analysis.Convex.Function`, and its absence reads as `Function.sum_mem`.
* **Names in this project are not reachable by dot notation at all.** `Convex.foo` here is
  `Tdaf.ConvexAnalysis.Convex.foo`, and generalised field notation resolves against the *root*
  namespace. Declare a `_root_.Convex.*` name only when the lemma is a pure Mathlib gap, never to
  buy dot notation. Name lemmas about such predicates prefix-style — `…_of_monotone`,
  `polyhedralFn_mapLin` — not `Monotone.…`, `PolyhedralFn.mapLin`.

**EL2. A term applied to a lambda leaves a beta-redex, and `rw` cannot see into it.** This is the
most common failure in the library. `(h x d).2 h₀ h₁ ha hb hab` has type
`(fun t => f (x + t • d)) (a • 0 + b • 1) ≤ …`; the goal is its beta-reduction, and every `rw`
pattern inside reports "did not find an occurrence".

*The rule*: **argument positions and `exact` check up to defeq; `rw` and `simp` are syntactic.** Put
the defeq step where a term is checked *against* an expected type, never where it creates one —
ascribe the `have`'s type explicitly, or `simp only [] at h` to beta-reduce it, or hand the fact to
the lemma as an argument instead of rewriting it in.

Where it shows up: structure projections applied to a lambda (`ConvexOn.2`, `ConcaveOn.2`,
`Convex.2`, `IsGreatest.2`); `PosHomogeneous f` instantiated at a lambda; `MonotoneOn` at a point;
`tendsto_order.2`; `Finset.sum_erase`; `rw [mapLin_fst_apply]`; a bifunction theorem applied at
`F := fun y v => -(G y v)`; and every destructuring of pointwise `Set` arithmetic —
`rintro ⟨a, ha, b, hb, hab⟩` on `z ∈ S + T` gives `hab : (fun x₁ x₂ => x₁ + x₂) a b = z`, and
`x ∈ a • S` gives `(fun y => a • y) p = x`. A `change` to the reduced form, or a restatement as
`have hab' : a + b = z := hab`, fixes all of them. It must be `change`, not `show` (LINT4).

A `Prod` cousin with a surprising casualty: destructuring membership in a `setOf` over pairs —
`{q | 0 ≤ q.2 ∧ q.1 ∈ q.2 • C}` — leaves `0 ≤ (c • q).2`, and **`positivity` fails**, because it
cannot see `0 ≤ c * q.2` through the unreduced projection. `rw` does not iota-reduce a projection of
a pair literal either: `(u', 0).2` defeats `rw [dirDerivReal_zero]`, and `Fintype.card ↑↑t` does not
rewrite to `t.card` (`simpa using h` closes it). Note that structure *eta* does work the other way:
`((ps i).1, (ps i).2)` is definitionally `ps i` and `exact` closes it with no `Prod.mk.eta`.

**EL3. `rw` also fails on eta, on coercions, and on `Sub`.** The same syntactic-versus-defeq split at
three more heads:

* **Eta.** A `have` stated as `(fun p => partialCl₁ g p) = …` will not rewrite a goal containing
  `partialCl₁ g`. State `have`s eta-contracted and let `funext` introduce the point.
* **Coercions.** `⇑(LinearMap.fst ℝ E F) '' s` and `Prod.fst '' s` do not match; `↑↑(hull ℝ S)` (a
  `PointedCone` coerced through `ConvexCone`) does not match `↑(hull ℝ S)`; `↑(↑A : E →ₗ[ℝ] G) x`
  does not match `⇑A x` for a `LinearEquiv`. State the helper against the coercion the *caller's*
  lemma produces, or re-ascribe the datum once in a `have` that typechecks by `rfl`.
* **`Sub` is a separate head from `Neg`.** On `EReal`, `a - -b` does not contain the pattern
  `- -?x`, so `rw [neg_neg]` finds nothing; `change a + -(-b) = a + b` first. Likewise
  `compLin (fun w => -(g w)) A` versus `fun x => -(compLin g A x)`: `rw`'s trailing `rfl` runs at
  *reducible* transparency and will not unfold `compLin`, so finish with a bare `rfl`.

**EL4. `rw` rewrites every occurrence of the *instantiated* pattern.** Two consequences that read as
bugs:

* List a rewrite once per **distinct instantiation**, not once per occurrence.
  `rw [polarCone_neg, polarCone_neg]` errors on the second, because the first caught both sides.
* `rw [← h]` with `h : f C = C`, or `h : p.1 = 1`, rewrites inside the term you were building — the
  `1` inside `liftAt 1 P`, the second `C` in `C ⊆ closure (convexHull ℝ …)`, the `s` inside
  `s ^ (q-1)`. Build the equation you actually want (`Prod.ext h rfl`), or start a `calc` from it,
  where it is used at exactly one position. An `abel` that "should" close a goal often fails for
  this reason.

  A third face of the same problem: `rw [hM]` with `hM : M = ↑(vectorSpan ℝ M) + {a}` gives
  **"motive is not type correct"** as soon as any local term's *type* mentions `M` — an
  `e : vectorSpan ℝ M₁ ≃ₗ[ℝ] vectorSpan ℝ M₂` is enough. Introduce such equivalences opaquely with
  `obtain ⟨e⟩ : Nonempty (…)`, and state membership criteria as `have`s *before* the offending
  term appears.

Relatedly, `rw` traverses **outside-in**, so `map_zero` collapses `(B 0) 0` in one step and a
following `LinearMap.zero_apply` has nothing to do; and a bare `rw [map_sub]` / `rw [map_neg]` in a
goal with nested applications unifies with the wrong one — `map_neg`'s pattern `?f (-?a)` matches
both `B (-x)` and `(B (-x)) (-y)`. Always supply the arguments: `map_sub (B a) y b`, `map_neg B x`.
Two more of the same family: `rw [norm_sub_rev]` with no arguments hits the *first* `‖a - b‖`, which
is almost never the one meant; `real_inner_comm a b : ⟪b, a⟫ = ⟪a, b⟫` takes its explicit arguments
in the opposite order to the one they appear in.

**EL5. A `Set` equality does not rewrite a goal written as the underlying predicate.** With
`hset : {x | f x ≤ ↑α} = {x | k x ≤ ↑c}`, `rw [hset] at hv` fails on `hv : f v ≤ ↑α`: membership in
a set-builder and the predicate are only definitionally equal. Name the membership first
(`have hmem : v ∈ {x | f x ≤ ↑α} := hv`), rewrite that, and let the consumer's `exact` take the
defeq step back. Both conversions are free; only the rewrite is not. The same ascription is what
`linarith` needs — an unascribed `h : x ∈ {z | P z}` never enters its context, and the tactic
reports "failed to find a contradiction" with the hypothesis simply absent from the printed state.

**EL6. Anonymous constructors need an expected type, and `⟨…⟩` is where elaboration gives up.**
`Set.insert_eq_self.2 (Or.inr h)` elaborates `insert` at `Prop`; `subset_convexHull ℝ _ ⟨h₁, h₂⟩`
reports "the expected type of this term could not be determined"; `hsub ⟨hw, hv⟩` for `s ×ˢ t`
leaves `?p.1 ∈ s` unsolved; `⟨hz, le_rfl⟩` for `C ×ˢ Ici 0` fails because `(z, 0).2 ∈ Ici 0` is not
unfolded to `0 ≤ 0`; `⟨h₁, h₂⟩` against `z ∈ s \ t` fails because `Set.diff` is no longer reducibly
an `And`; `LinearMap.id - f` inside a `refine ⟨…⟩` reports "Function expected". Spell the set out,
ascribe the term, or use the named constructor — `Set.mk_mem_prod`, `mem_Ici.2`,
`Set.mem_sdiff_of_mem`. Destructuring in the other direction is fine; only construction fails.

**EL7. `▸` and `have` both fail when the type is only defeq.** `heq ▸ h` reports "the equality does
not contain the expected result type" when the target is a `def` hiding the rewritten term
(`ConvexBifun G` unfolding to `ConvexFn (graphFn G)`) — go through the `_iff` lemma first. And
`h ▸ iInf_le f x` on `EReal` fails with a stuck `OrderTop ?m`, because `▸`'s motive is not fixed
before the instance is demanded; use `by rw [← h]; exact …`. In the other direction, a `have` whose
stated type is merely defeq can flip the elaboration around and fail: state the `have` in the
lemma's own shape and let the *argument* position take the defeq step.

**EL8. Higher-order unification: supply the function.** `?f (x - a) =?= h (A (x - a))` is not a
Miller pattern, so `rw [conj_comp_sub]` either fails or picks a constant `?f`. `convexFn_add_coe`'s
`l`, `card_le_finrank_succ_of_affineIndependent`'s `p` and `Finset.sum_erase`'s summand are all in
this class. Pass them by name — `(l := fun r => -(Bx r.2 y))`, `(p := fun j => (zz j).1)` — and
state the side hypothesis with the same lambda applied, so the two match up to beta. Chaining the
rows of a long identity with typed `have`s rather than `rw` turns each beta-reduction into a
*typechecking* obligation, which Lean discharges by `rfl`.

The same shape catches a *bundled* argument whose implicits are not yet solved:
`convexFn_compLin (LinearMap.proj i) hg` will not unify against an expected
`ConvexFn fun p => g (p i)`, because the elaborator tries the unification before it can solve
`proj`'s `φ` and `R`. Build the term first and let `exact` close the defeq:
`have h := convexFn_compLin (E := ι → E) (LinearMap.proj (R := ℝ) (φ := fun _ => E) i) hg; exact h`.
Same for maps built with `LinearMap.prod`.

**EL9. When a lemma's implicit argument occurs only in a hypothesis or an instance, nothing infers
it.** The symptom differs by position and none of them says "missing implicit":

| position | message |
|---|---|
| `have h := hp.le_add_conj x z` | *don't know how to synthesize implicit argument `B`* |
| `obtain ⟨y, hy⟩ := lemma …` | *typeclass instance problem is stuck: `IsCompatiblePairing ?m`* |
| `refine lemma hf ?_` | the same, naming `LinearMap.flip ?m` |
| `exact`/`refine` against a goal that fixes `B` | fine |

Pass it: `(B := B)`, `(p := …)`, `(𝕜 := ℝ)`, `(m := 1)`, `(x := x)`. Instance binders are the usual
cause — `[IsCompatiblePairing B]` never pins `B` the way a hypothesis mentioning `B` used to. Two
that catch everyone: `isCompact_stdSimplex _` feeds the underscore to `ι` and leaves `𝕜` open;
`iInf₂_le i hi` cannot elaborate without an expected type, because the family is a metavariable
(`biInf_le` is not a name in this Mathlib; it is `iInf₂_le`). See PAIR4 for the section-variable side.

**EL10. `refine`'s holes: `?_` under a binder is rejected, and the goal order is not the hole
order.** `refine f (fun n => g ?_) …` gives "Unknown identifier"; hoist the body into a `have`. And
`refine le_trans (iInf₂_le _ ⟨…, ?_⟩) (le_of_eq ?_)` emits the `le_of_eq` goal *first*. Name the
holes, or read the order off the first error. `obtain ⟨…⟩ := f ?_ …` followed by focusing bullets
gives "No goals to be solved" for the same reason — hoist the side condition into a `have`.

**EL11. A metavariable inside a `by` block is elaborated too early.**
`closedBall_subset_ball (by linarith)` inside a term whose radius is still `?m` makes `linarith`
fail on `r ≤ ?m`; name the inequality first and pass it. Same reason `hcu.comp (by fun_prop)` can
never work: `Continuous.comp` leaves the inner function a metavariable and `fun_prop` reports "was
unable to prove `Continuous ?m`" with an empty issue list.

**EL12. `relaxedAutoImplicit = false` turns one missing import into a landslide.** A missing
`TopologicalSpace`, or `Basis` where `Module.Basis` was meant, produces a dozen cascading errors
with `sorry`-typed hypotheses and "Unknown identifier `ι`" that reads like a `variable`-scoping
problem. **Only the first error is real.** The same holds after a failed instance declaration,
which produces "Not a definitional equality" everywhere downstream.

**EL13. Timeouts are usually a layer or import problem, not a slow proof.** Mixing layers gives
`(deterministic) timeout at isDefEq`, and a lemma stated over `[NormedAddCommGroup E]` applied at a
bare topological group gives `timeout at whnf` — check the *cited* lemma's `variable` line before
optimizing anything. Two more shapes: `exact` against a `ClosedFn` goal can time out where the same
move against `ConvexFn` is instant, because `ClosedFn f` unfolds to the equation `clFn f = f` and
unification pushes a reflection through `clFn`; and a `rw` whose implicit type argument has to be
solved as `↥V` for a `Submodule` *diverges* (a `maxHeartbeats` bump does not save it) — bind the
fact to a typed `have` first, which pins the implicits before instance search starts. Relatedly,
**a subspace you will take `Set ↥V` over must be a variable, not a definition**: take
`V : Submodule ℝ E` with `hV : V = span …` as a hypothesis and let the caller supply an opaque one
with `obtain ⟨V, hV⟩ : ∃ V, V = … := ⟨_, rfl⟩`.

**EL14. Two naming traps that produce baffling errors.** Inside `theorem Foo.bar`, a bare `bar`
resolves to the theorem *being defined* — `rw [hasSaddleValue_iff]` inside
`SaddleEquiv.hasSaddleValue_iff` fails with **"fail to show termination"**. And a theorem named
`Foo.bar` whose statement mentions `bar` has the same problem from the other side:
`theorem PolyhedralFn.mapLin … : PolyhedralFn (mapLin A f)` reports "application type mismatch …
expected `PolyhedralFn f`". Write `_root_.foo`, or rename to `polyhedralFn_mapLin`.

---

## LINT — Linters and the zero-warning bar

The bar is **no errors and no warnings**, deprecations included. These are the linters that fail a
build.

**LINT1. The file header is mandatory and exact.**

```
/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
```

**LINT2. `omit … in` and `include … in` go *before* the doc comment.** A doc comment must be
immediately followed by its declaration, so `/-- … -/ omit [Inst] in theorem …` is a parse error,
`unexpected token 'omit'; expected 'lemma'`, which does not say what is wrong. The order is
`omit … in`, then `/-- … -/`, then `theorem`. A blank line between them trips
`linter.style.emptyLine` — the three are one command. And `omit` accepts only instances that really
are section variables in scope.

**LINT3. The unused-section-variable linter cascades, and over-`omit`ting turns a warning into an
error one declaration later.** Each `omit` changes what the *next* declaration needs, so the
warnings must be driven to a fixed point — six rounds for `Optimization/Prox.lean`, four for
`Optimization/ConeDuality.lean` — and the reported line numbers move each round, since every `omit`
inserts a line. Three rules that save most of it:

* **Never trim a `variable` block on the strength of a build that also had errors.** The linter
  reports what the *incomplete* term does not mention; `IsTopologicalAddGroup E`,
  `ContinuousSMul ℝ E` and `LocallyConvexSpace ℝ E` were all reported unused, removed, and then
  immediately needed once the proof compiled.
* **Split a mixed-space section instead of `omit`-ing per declaration.** In a section over `U` and
  `X` with `[FiniteDimensional]` on both, half the declarations trip the linter with a *different*
  list each. One section with the finite-dimensional instances and one without removed six `omit`s.
* **`omit` cannot remove an instance a `def` genuinely takes.** `def infConvBifun (F₁ F₂ : Bifun U
  X)` picks up `[AddCommGroup U] [Module ℝ U]` because `Bifun U X` mentions `U`; `omit` breaks the
  definition rather than silencing the linter. Split the section.

The linter is also a **useful signal**: when it fires unexpectedly it is usually reporting that the
result belongs in a weaker layer of ER9. That is how the upper half of Corollary 8.5.2 was found to
be layer A, and how three `RelativeInterior.lean` lemmas were found not to need finite dimension.
Note the contrast in reporting: `omit …` violations are all listed in one build, unused *section
variables* are reported a few at a time.

**LINT4. `show` may not change the goal — use `change`.** `linter.style.show` treats `show` as a
readability device (restating the goal you are already looking at) and `change` as the defeq
conversion. Every "unfold a `Set` membership to the underlying inequality" step is a `change`.

**LINT5. `haveI` is rejected for `Prop`-valued instances — use `have`.** `linter.style.haveILetI`. This
is not a loss: **a local `have` whose type is a class does participate in instance search**, which
is how `IsCompatiblePairing ((innerₗ E).flip)` gets supplied locally (PAIR1). Same for
`obtain ⟨hι⟩ := nonempty_fintype ι` — no `letI` needed.

**LINT6. `[Fintype ι]` trips `linter.unusedFintypeInType` when the *statement* does not mention it.**
That is the normal situation for a theorem about `convexHull ℝ (range v)` or about
`Module.Basis ι ℝ E`, where the finiteness is only needed inside the proof. Declare `[Finite ι]`
and open with `obtain ⟨hι⟩ := nonempty_fintype ι`.

**LINT7. `linter.unusedSimpArgs` computes each hint against the *original* list.** Two warnings each
saying "omit this one" can both be wrong: removing either alone leaves the goal unsolved. Re-derive
the minimal list rather than applying the hints one at a time. It also fires on the lemmas that look
most essential — after `set ξ := fun j => b.repr w j with hξdef`, the goal is closed by
`simp [hξdef]` alone and adding `Module.Basis.equivFun_apply` is an error-level warning. And
`finrank_euclideanSpace_fin` is already in the default simp set.

**LINT8. `simp` closing a goal you were about to hand to another tactic is an error, not a bonus.**
A `simp only [defn, Set.mem_iUnion, exists_prop]` you expect merely to unfold can close the goal,
and the following `tauto` errors with "No goals to be solved". Same for `field_simp; ring`, where
`field_simp` alone sometimes finishes — and `try ring` then trips `linter.unnecessarySeqFocus`, so
`<;> (field_simp; try ring)` is the spelling that survives. Two sibling members of this family:
`abel` emits an `info` "Try this: abel_nf" when normalisation alone suffices (only an info, but it
clutters the log), and `induction a <;> induction b <;> simp_all <;> …` trips `linter.flexible`,
`linter.unusedSimpArgs` and `linter.unnecessarySeqFocus` at once — for nine-case `EReal` arithmetic
the deterministic route is cheaper anyway.

**LINT9. `set x := e with h` and an unused `h` do *not* trip the linter.** Only genuinely unused
binders are reported. Drop the `with h` for tidiness, not to satisfy a linter. What `set` really
costs is elsewhere: **it stops abstracting once a later `rw` reintroduces `e`**, so the goal shows
`e` where the hypotheses show `x`. Do all the rewriting before the `set`, or write `e` out. When a
proof must mention a bundled map twice and `set` cannot be used, abstract it into a `private`
auxiliary that takes the map and its defining equation, discharged at the call site by
`fun _ => rfl`.

---

## DEP — Deprecated and renamed Mathlib

A deprecation warning fails the bar, so these are hard errors in practice. The suggested replacement
is sometimes *also* deprecated, and sometimes does not drop in.

| old | new | note |
|---|---|---|
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | simp lemma is `Set.mem_ofPred`; or just use defeq |
| `Set.mem_diff_of_mem` | `Set.mem_sdiff_of_mem` | |
| `Set.diff_eq_empty`, `Set.diff_subset`, `Set.inter_union_diff` | `Set.sdiff_…` | grep `Set.diff_`
|
| `push_neg` | `push Not` | with a space and a capital N; `push_not` does not exist |
| `if_pos`, `if_neg`, `dif_pos`, `dif_neg` | — | replacements are *iffs*, not substitutions; use
`split` and `exact absurd h ‹_›` |
| `ite_cond_eq_true/false` | `ite_eq_left_of_eq_true _ _ (eq_true h)` | the suggested replacements
are themselves deprecated |
| `le_or_lt` | `le_or_gt` | |
| `continuous_mul_right` | `continuous_mul_const` | |
| `Ioo_mem_nhdsWithin_Ioi/Iio` | `Ioo_mem_nhdsGT` / `Ioo_mem_nhdsLT` | |
| `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection` | `Submodule.isCompl_orthogonal` | takes
`K` **explicitly**; the drop-in does not typecheck |
| `Submodule.linearProjOfIsCompl` | `Submodule.projectionOnto` / `.projection` | whole supporting
API renamed with it |
| `ContinuousLinearMap.add_apply`, `.zero_apply`, `.coe_comp'` | `add_apply`, `zero_apply`,
`ContinuousLinearMap.coe_comp` | for a hand-built CLM, skip the `simp only` list: `+`, `.comp`,
`.fst`, `innerSL` apply *definitionally* |
| `cond_true`, `cond_false` | `Bool.cond_true`, `Bool.cond_false` | replacements take *implicit*
arguments |
| `Basis` | `Module.Basis` | see DEP1 |
| `NormedSpace.Dual` | `StrongDual` | usually avoidable: `DFunLike.congr_fun h w` needs no
ascription |
| `Real.IsConjExponent` | `Real.HolderConjugate` | an `abbrev` for `HolderTriple p q 1` |
| `EReal.continuous_coe_real` | `EReal.continuous_coe_iff.2` | never existed |
| `add_right_eq_self` | — | unstable across versions; `simpa using h` is the portable move |

**DEP1. `Basis` is `Module.Basis`.** Prefix forms need the namespace — `Module.Basis.ofVectorSpace ℝ
E`, `Module.Basis.span`, `Module.Basis.equivFun_apply` — while dot notation on a basis (`b.repr`,
`b.equivFun`, `b.constr`, `b.addHaar`) is unchanged, so only the *first* mention needs correcting.
`Module.finBasis` is not renamed. With `relaxedAutoImplicit = false` the single unknown identifier
becomes a landslide (EL12).

**DEP2. `dif_pos`'s deprecation kills the `dite`-plus-`Exists.choose` idiom for a total selector.**
`if h : s.Nonempty then h.choose else 0` can only be unfolded through `dif_pos`. Use
`Classical.epsilon (· ∈ s)` instead: `Classical.epsilon_spec` takes the nonemptiness proof directly
and no rewriting is needed. `Nonempty E` is found automatically for any `AddCommGroup`.

**DEP3. `to_additive`-generated names are invisible to a grep of Mathlib's source.**
`Set.mem_vadd_set_iff_neg_vadd_mem` occurs nowhere in Mathlib's `.lean` files; only its
multiplicative parent `Set.mem_smul_set_iff_inv_smul_mem` does. Grep for the multiplicative name and
translate, or "Mathlib does not have it" will be wrong. Two more names that hide: `norm_fst_le` /
`norm_snd_le` live at the **root**, not in `Prod`; `AffineSubspace.affineSpan_eq_top_iff_…` is
namespaced even though Mathlib's own proof calls its neighbour unqualified.

**DEP4. Search Mathlib *semantically* before concluding it lacks something.** Grepping for names
misses whole files: `Mathlib/Analysis/LocallyConvex/WeakSpace.lean` holds the compatible-topology
theorem and no declaration in it contains the word "compatible";
`LinearMap.dualEmbedding_surjective` is the Weak Representation Theorem and says neither word;
`SecondCountableTopology EReal` is in `Mathlib/Topology/MetricSpace/ProperSpace/Real.lean`;
`Set.Countable.dense_compl` is filed as a *cardinality* fact. Use LeanSearch (`POST /search`, body
`{"query": ["…"], "num_results": 8}`) or the MCP semantic tools, and only then grep. Every one of
the survey corrections in DEP5 was first missed by grepping for a name instead of for the concept.

**DEP5. Survey corrections worth keeping.** `LinearMap.Nondegenerate` already is
`SeparatingLeft ∧ SeparatingRight`. `LinearMap.IsAdjointPair` pairs a module with *itself*, so a
four-space version has to be written. There is no `ContinuousLinearMap.dualMap`, but the thing it
names is `ContinuousLinearMap.precomp`. `asymptoticCone` exists and is `0⁺(cl C)`, with
`isBounded_iff_asymptoticCone_subset_singleton` giving Theorem 8.4 in three lines. The usable
`{x | l x ≤ c}` form of `iInter_halfSpaces_eq` exists only in the `RCLike` namespace.
`innerSL_apply` does not exist — it is `innerSL_apply_apply`, and `innerSL_inj` already gives that
the inner product separates points. `Ioc_mem_nhdsWithin_Ioi` is not a name and has no renaming; when
a filter argument on `𝓝[>] a` needs a two-sided bound it is cheaper to drop the filter and run the
estimate by `by_contra` with an explicit `t = min (1/2) (d / (2*c))`.

---

## ER — `EReal`

**ER1. What `EReal` is not.** It is a `def` over `WithBot (WithTop ℝ)`, not an `abbrev`, so `WithBot`
big-operator lemmas do not transfer. It is **not a semiring** (`Finset.mul_sum` and relatives do not
apply), **not a `SubNegMonoid`**, **not a `SubtractionMonoid`** (no `zero_sub`), **not an
`AddGroup`** (root-namespace `neg_le_neg` asks for one; use `EReal.neg_le_neg_iff`), and **not
cancellative** (`Finset.sum_lt_sum` into a strict bound, and "subtract the same thing from both
sides", are unavailable — budget a factor of two, `ε/(2λ)` where the book writes `ε/λ`). There is
no `SMul ℝ EReal`: write `(a : EReal) * z`. There is no `PosMulStrictMono EReal`, so
`le_of_mul_le_mul_left` cannot reflect an order — multiply through by `(a⁻¹ : EReal)`, which is what
`Tdaf.EReal.coe_mul_le_coe_iff` packages. `PosMulMono EReal` is in `Mathlib/Data/EReal/Inv.lean`.
`inv_inv` is **false** (`(⊤⁻¹)⁻¹ = 0`); push double inverses back to `ℝ` first.
`Tdaf/Order/EReal.lean` exists to fill these gaps.

**ER2. Negation and subtraction: which lemma produces which head.** `a - b` *is* `a + -b` by `rfl`
(`EReal`'s `Sub` instance is literally `⟨fun x y => x + -y⟩`), so a goal left as `a - b = a + -b` is
closed by a bare `rfl`, and `simp only [sub_eq_add_neg]` is the way to expose sums before
`add_assoc` / `add_comm` / `add_right_comm` — a plain `rw [add_assoc]` will not match through the
`HSub` head. Then:

* `EReal.neg_add` concludes `-x - y`, **not** `-x + -y`. The two are defeq, so a typed `have`
  works; `rw` leaves a `Sub`-headed term and a following `rw [neg_neg]` fails.
* `EReal.neg_sub h₁ h₂ : -(x - y) = -x + y`, **not** `y - x`. A follow-up `rw [sub_eq_add_neg]`
  then reports "no occurrence" — the subtraction is already gone. To reach `y + ↑(-c)` from
  `-(↑c - y)` the chain is `EReal.neg_sub`, `add_comm`, `← EReal.coe_neg`.
* `rw [EReal.neg_add h₁ h₂]` takes its implicit `a`, `b` from **the types of the side conditions you
  pass**, so supplying `hG.proper.ne_bot (x, y)` makes it look for `-(graphFn G (x,y) + …)` even
  where the goal is written `G x y`. Bind the side conditions in the goal's own spelling.
* **The side conditions are usually free.** `EReal.neg_add` wants `¬(a = ⊥ ∧ b = ⊤)` and its mirror;
  a *coerced real* is neither, so `EReal.coe_ne_bot` / `coe_ne_top` discharge both. Of 26 uses in
  the library, 17 go this way, and the condition reaches the statement of at most 8 of 240 concave
  declarations.
* `neg_zero`, `neg_neg` and `mul_neg` come from `InvolutiveNeg`/`HasDistribNeg` and apply at the
  **root**; `neg_bot`, `neg_top`, `coe_neg`, `coe_add`, `coe_eq_coe_iff` live in the `EReal`
  namespace. Inside `namespace Tdaf.ConvexAnalysis` the bare names do not resolve and the
  half-qualified `EReal.neg_bot` can be captured by `Tdaf.EReal` — write `_root_.EReal.neg_bot`.
  `EReal.le_neg`, `EReal.neg_le` and `EReal.lt_neg_of_lt_neg` are `protected`.

**ER3. Orientation of the arithmetic lemmas.** Every one of these has cost time by being read the
natural way round:

| lemma | actual statement |
|---|---|
| `EReal.le_sub_iff_add_le (hb) (ht)` | `a ≤ c - b ↔ a + b ≤ c` — `b` is the **subtrahend**, `c` the
minuend |
| `EReal.sub_le_sub (h : x ≤ y) (h' : t ≤ z)` | `x - z ≤ y - t` — the subtrahends cross over |
| `Tdaf.EReal.coe_mul_coe` | `↑a * ↑r = ↑(a*r)`; forward combines, `←` splits |
| `Tdaf.EReal.iSup_add_coe`, `iInf_add_coe` | `(⨆ u) + r = ⨆ (u + r)` — the constant goes on the
**right** |
| `eq_or_lt_of_le` | `a ≤ b → a = b ∨ a < b` — subject first, so `le_top` gives `f z = ⊤` |
| `EReal.eq_bot_iff_forall_lt` | takes the `EReal` **explicitly**; `.2` is an invalid projection |

Two more shapes: pulling a constant out of a supremum as a *subtrahend* needs `c ≠ ⊥`, not `c ≠ ⊤`
(`(⨆ i, u i) - c = ⨆ i, (u i - c)`), and it is **not** the mirror of
`Tdaf.EReal.biSup_add_biSup`, whose hypothesis dualises the other way. `a + ⨅ B = ⨅ i, (a + B i)`
needs nothing about `a`, only `⨅ B ≠ ⊥`. And the infimal mirror of `biSup_add_biSup` needs the two
*infima* to avoid `⊥` — dualising "the values avoid `⊥`" to "the values avoid `⊤`" is useless for
bifunctions, where `F u x = ⊤` off the domain.

**ER4. `⊤ + ⊥ = ⊥`, so check every `a ≤ u + v` at the improper values.** Fenchel's inequality
`⟨x,y⟩ ≤ f x + f* y` is *false* for `f ≡ ⊤`; the unconditional content is
`sub_le_conj : ⟨x,y⟩ - f x ≤ f* y`. More generally **sign transfer reverses the order but not the
arithmetic**: a convex statement `a ≤ u + v` and its concave mirror `u + v ≤ a` need *different*
hypotheses, because `⊥` absorbs on one side only. Check each mirror rather than assuming the
symmetry. The one `EReal` symmetry that *is* unconditional is
`Tdaf.EReal.coe_sub_le_comm : (a:ℝ) - z ≤ w ↔ (a:ℝ) - w ≤ z` (all eight `⊥`/`⊤` combinations work,
because `a` is finite) — it is what makes `conj_le_iff`, the conjugacy Galois connection and
`biconj B f ≤ f` hypothesis-free, and it is why `add_iSup`/`iSup_add`/`iSup_sub`, long expected to
carry every conjugacy proof, are **not needed for §12 at all**.

Note also that this totalisation is **not Rockafellar's convention**: he leaves `∞ − ∞` undefined
and then fixes it per operator. Every backbone statement that could meet the collision carries
`∀ x, f x ≠ ⊥` or properness, so the junk value is never consulted — but a surface statement that
*drops* that hypothesis will silently prove something the book does not state.

**ER5. Two `simp` loops, and one of them was an orientation bug.** `simp [Tdaf.EReal.coe_mul_coe]`
loops against Mathlib's `EReal.coe_mul`; use `rw`. A set containing `← EReal.neg_lt_neg_iff` loops
against `neg_neg`/`neg_bot`/`neg_top`. **But** the recorded conclusion that "the concave API cannot
be generated by `simp`-normalising through negation" was overstated: a simp set containing *both*
members of an inverse pair diverges, and one orientation terminates. The three pairs in the library
are `concaveConj_eq_neg_conj_neg` / `conj_eq_neg_concaveConj_neg`, `hypo_neg` / `epi_neg`,
`clConcave_apply` / `neg_clConcave`; a set containing only the concave → convex direction
terminates, because nothing in it reintroduces a concave head symbol.

**ER6. `⨅ _ : p, f` for a `Prop` `p` is the decidability-free `if p then f else ⊤`.** `iInf_pos` and
`iInf_neg` are the defining equations; `⨆ _ : p, f` gives `… else ⊥`. Prefer it to
`f + indicatorFn C` for restricting a function to a set: it needs no `f x ≠ ⊥` hypothesis
(`⊥ + ⊤ = ⊥` corrupts the sum off `C`), and `⨅ x, (fun x => ⨅ _ : x ∈ C, f x) x` is
*definitionally* `⨅ x ∈ C, f x`, so a bounded-below hypothesis transports with no rewriting. The
same trick applies to a *value* rather than a proposition:
`⨅ t : ℝ, ⨅ _ : k x ≤ (t : EReal), g t` is `g ∘ k` extended by `g(+∞) = +∞`, and its convexity falls
out of `convexFn_iff_forall_lt` with no monotonicity at all. And this is what lets a statement avoid
`Decidable`: `f y = if y = a then c else ⊤` needs an instance no layer-A section has — state it as
`indicatorFn {a} + fun _ => (c : EReal)` with the two pointwise values as separate lemmas.

The `Finset` version of the same rule: **an `if i ∈ s` inside a *statement* needs `[DecidableEq I]`,
and `classical` cannot rescue it** (`Finset.decidableMem` is derived from it) — and adding the
instance then risks a mismatch against a caller's `Classical.propDecidable`. Keep the `if` out of
the statement: hypothesise `∀ i ∈ u, i ∉ s → w i = 0` and build the padded function inside the
proof with `obtain ⟨w', h₁, h₂⟩ : ∃ w' : I → ℝ, … := ⟨fun i => if i ∈ s then w i else 0, …⟩`.

**ER7. `EReal.rec` is a definitional combinator, not just an eliminator.** `EReal.rec (⊥ : EReal) φ
⊤` defines a function by cases, with `rec_bot`/`rec_coe`/`rec_top` `@[simp]` and `rfl`. Write
`_root_.EReal.rec` inside `namespace Tdaf.ConvexAnalysis`. Also, `induction A with | bot | coe c |
top` is the cheapest proof that an empty `EReal` interval is degenerate — and
`EReal.lt_iff_exists_real_btwn` is the whole toolkit for endpoint arguments: `by_contra`, push the
negation, extract a real strictly between the two candidate endpoints, bound it at the other end.
Four copies of that prove `A₁ = A₂ ∧ B₁ = B₂` with no `⊥`/`⊤` case analysis.

**ER8. `simp` does not close the `⊥`/`⊤` branches of a subtraction identity, and `norm_num` undoes
your coercion work.** For `(p : EReal) - (u + q) = ↑(p - q) - u`, `simp` in the `bot` branch leaves
`⊤ = ↑p - ↑q - ⊥`: it pushes the coercion apart and has no lemma for `_ - ⊥`. Spell out
`EReal.sub_bot (h : a ≠ ⊥)`, `EReal.sub_top`, `EReal.bot_add`, `EReal.top_add_coe`. Likewise after
`rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_sub]` the goal is `↑p = ↑q`; `norm_num` pushes
the coercions back apart, while `rw [_root_.EReal.coe_eq_coe_iff]` then `ring` finishes. Note
`EReal.sub_add_cancel` and `EReal.add_sub_cancel_right` are hypothesis-free, because the subtrahend
is a *real* by the statement. `EReal.bot_add_of_ne_bot` does not exist although
`EReal.top_add_of_ne_bot` does; `simp [EReal.coe_mul_bot_of_pos hl]` covers the gap.
`((max a b : ℝ) : EReal) = max ↑a ↑b` is `exact_mod_cast rfl` — there is no `EReal.coe_max`.

**ER9. Topology and limits on `EReal`.** There is **no `Filter.Tendsto.add`** — addition is
discontinuous at `(⊥,⊤)` and `(⊤,⊥)`. The idiom is
`(EReal.continuousAt_add h h').tendsto.comp (h₁.prodMk_nhds h₂)` with `h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥` and
`h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤`; when both limits are `≠ ⊥` — what properness of a *closure* gives — both
are immediate. The composite's `Function.comp` unifies definitionally with `fun a => (f + g) (…)`,
so `exact` closes the goal without `Pi.add_apply`. To move a real-valued limit into `EReal`, rewrite
the *argument* first and use `EReal.tendsto_coe.2`; going the other way leaves a `Function.comp`
that does not always unify. `EReal` is a `CompleteLinearOrder` with the order topology, so
`IsCompact.exists_isMaxOn` accepts an `EReal`-valued function directly — no `toReal` transport —
and `Monotone.countable_not_continuousAt` applies verbatim.

**ER10. To compare two `EReal` conjugates, go through real upper bounds and `by_contra`.**
`conj_le_iff` relates `f*` to a *function*, not to another conjugate. Prove
`∀ c : ℝ, conj B h₂ y ≤ c → conj B h₁ y ≤ c` — each side unfolds by `conj_le_coe_iff` into a
statement about affine minorants, where limits can be taken — then `by_contra` and
`EReal.lt_iff_exists_real_btwn` to produce the separating real. This handles `⊤` and `⊥` with no
case split. Note the dual fact: **a sum of two conjugates cannot be proved by comparing affine
minorants at all**, because `u + v ≤ c` is not a condition on `u` and `v` separately —
`conj_infConv` goes through `conj_ofEpi` and `biSup_add_biSup`, interchanging two suprema over the
epigraphs, and is the only row of §16 that does.

---

## SET — Sets, products, cones

**SET1. Pointwise `+`, `•` and `-` on `Set` need `open scoped Pointwise`, and no error says so.** In a
statement it is `failed to synthesize HAdd (Set E) (Set E) ?m`, with a metavariable in the third
slot, which reads like an elaboration-order problem. It is **per file**: a module that merely
*mentions* `P + (PointedCone.hull ℝ D : Set E)` needs its own `open scoped Pointwise`, above
`namespace Tdaf.ConvexAnalysis` rather than inside a section. Two consolations: `Set` scaling is a
`MulAction`, so `smul_smul` applies verbatim (`a • b • s = (a*b) • s` needs no set-specific lemma);
and membership unfolds with the equation the *other* way round — `p ∈ {q} + V` gives
`∃ u ∈ {q}, ∃ v ∈ V, u + v = p`, so a hypothesis `hy : p.1 = a` has to be `.symm`-ed. For the
beta-redexes this produces, see EL2.

**SET2. `PointedCone ℝ E` is `Submodule {c : ℝ // 0 ≤ c} E`, and the subtype scalars bite
everywhere.** `PointedCone.hull` (renamed from `span`) is an `abbrev` for `Submodule.span`, so
`Submodule.span_induction` works directly — but in the `smul` case the scalar is the *subtype*.
The recipe:

* `Submodule.smul_mem p (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hx`, **not** `p.smul_mem ⟨a, ha⟩ hx` — with dot
  notation the anonymous constructor is elaborated against the wrong expected type and the error
  mentions `Real.le✝`. The bare-real form is `PointedCone.smul_mem`.
* `a • x` for the subtype scalar is defeq to `(a : ℝ) • x` but **invisible to `rw` and `simp`**, and
  even `show` "changes the goal" while leaving the smul in subtype form. Prove the statement for
  `(a : ℝ) • …` and close with `exact`, which unifies up to defeq.
* Wrap it once — `smul_mem_graph (ha : 0 ≤ a) (hp : p ∈ A.graph) : a • p ∈ A.graph` — and never
  touch the subtype again.
* To push a cone hull along a linear map, define the map over `{c : ℝ // 0 ≤ c}` by hand and use
  `Submodule.map_span`; `LinearMap.restrictScalars` drags in an `IsScalarTower` search.
* Set inclusion between coerced cones is closed by the `≤` proof itself: `exact hle` discharges
  `(hull ℝ S : Set E) ⊆ (hull ℝ T : Set E)`, with no `SetLike.coe_subset_coe` round trip. But
  `Submodule.span_le.2 h` proves a `Submodule` `≤`, not a `Set` `⊆` — bind it to a `have` with an
  explicit `PointedCone` ascription first.
* `PointedCone.lineal` needs `[LinearOrder R]`, so wrappers over `ℝ` must be `noncomputable`, and
  the error blames `Real.linearOrder`.
* **`Submodule.span_induction` auto-reverts every hypothesis mentioning the bound variable**, so a
  step that already has `hab : a + b = q` in context turns the induction hypothesis into an
  implication. Hoist the claim into a standalone `have` outside the step. And
  `Submodule.mem_span_finset.1` returns a *three*-component existential in this Mathlib —
  `∃ f, Function.support f ⊆ ↑t ∧ ∑ i ∈ t, f i • i = x`; destructure as `⟨c, -, hc⟩`.

`PointedCone` is the bundling to reach for: it has a span and `lineal` already *is* `C ⊓ -C` with
the "largest subspace inside" Galois connection. `ConvexCone` has no span at all, and there is no
`IsCone` predicate on bare sets — though `ConvexCone.convex` does accept an anonymous-constructor
cone `⟨s, _, _⟩` whose coercion is `rfl`-equal to `s`, which gives "closed under `+` and positive
`•` ⇒ convex" directly. The converse is not in Mathlib.

**SET3. `⋃ a > 0, a • s` and `∃ a > 0, x + a • y ∈ S` silently elaborate `a : ℕ`.** The `ℕ`-`SMul`
instance from `AddMonoid.toNatSMul` is found first, and the statement quietly becomes one about
integer multiples. The tell is an "unused section variable `[Module ℝ E]`" warning on a statement
that visibly scales by a real; the failure otherwise surfaces much later as an application type
mismatch at the *use* site. Write `⋃ a > (0 : ℝ), …` and `∃ a : ℝ, 0 < a ∧ …`.

**SET4. A product of inner-product spaces is not an `InnerProductSpace`.** Mathlib's `Prod` carries
the *supremum* norm. So `innerSL`, `InnerProductSpace.toDual` and Mathlib's `gradient` are unavailable
for a function of a pair, and a gradient must be built by hand as
`(innerSL ℝ q.1).comp (.fst ℝ U X) + (innerSL ℝ q.2).comp (.snd ℝ U X)`. **`WithLp 2 (E × F)` is not
the fix**: it *replaces* the topology instance, so every `ClosedFn`, `Continuous` and `IsClosed`
statement about `U × X` has to be transported across a type synonym. Generalising off the inner
product — stating the theory over a symmetric positive-definite jointly continuous pairing — touches
two files and leaves the topology alone. (`Metric.ball p r` in `U × X` *is* the product of the two
balls, which is the one place the supremum metric helps.) Note `WithLp` is a *structure* in this
toolchain — goals display `x.ofLp j` — but `x j` still elaborates for
`x : EuclideanSpace ℝ (Fin n)`, and `⟨fun x => x j, fun _ _ => rfl, fun _ _ => rfl⟩` is a valid
`Rn n →ₗ[ℝ] ℝ`.

**SET5. Structure-field and type-ascription traps.**
`Submodule.toAffineSubspace` is a coercion that type ascription will **not** trigger — write it
explicitly. `AffineSubspace`'s field is `smul_vsub_vadd_mem'` with the three points *implicit*, so
they cannot be named positionally; use `by intro t p₁ p₂ p₃ h₁ h₂ h₃`. A `def` producing a structure
whose fields mention section variables must live *inside* the section that binds them, or you get
`failed to synthesize AddCommMonoid (E × ℝ)` rather than a scoping error. A one-field structure gets
no usable `ext` — add `@[ext] theorem ext (h : A.graph = B.graph) : A = B` by hand. `Prod.swap ⁻¹'
s` as a `SetLike` carrier breaks `Iff.rfl`; spell the carrier as `{p : X × U | (p.2, p.1) ∈
A.graph}`. And `AddCommMonoid` on a type synonym cannot use the `nsmul` default (`nsmulRecAuto`
needs an `AddSemigroup` *instance*, which does not exist while the instance is being elaborated) —
declare `Add`/`Zero` first, then `nsmul := nsmulRec` with `fun _ => rfl` proofs.

Two more inside structure-instance notation: **`by simp` is greedy** and swallows the following
`, field := …`, giving "unexpected identifier; expected `}`" — put each field on its own line with
`?_` and discharge in bullets, noting that `Submodule.mk`'s goal order is `add_mem'`, `zero_mem'`,
`smul_mem'` (parent-structure order, not source order). And when building an `OrderIso` by
`⟨⟨toFun, invFun, _, _⟩, _⟩`, the `map_rel_iff'` goal is stated against the *constructor blob*
rather than against the function, so tactics that pattern-match on the relation fail; open with
`change f a ≤ f b ↔ _` (not `show` — LINT4).

**SET6. `open Set` makes bare `restrict` ambiguous** with `Set.restrict`; write
`Tdaf.ConvexAnalysis.restrict`. And `𝓝` is scoped in `Topology`, not `Filter` — `open Filter` alone
leaves it to `autoImplicit` and the error is "Function expected at `𝓝`".

**SET7. `Filter.Tendsto.fst`/`.snd`/`.prodMk` are about product *filters*, not `𝓝` of a pair.** For
`hlim : Tendsto u atTop (𝓝 p)` with `p : ℝ × E`, use `(continuous_fst.tendsto p).comp hlim`. In the
other direction, `rw [nhds_prod_eq]` first and then `Tendsto.prodMk` works — and
`Filter.eventually_iff_seq_eventually` plus `rw [nhds_prod_eq]` converts a sequential theorem into a
neighbourhood-filter one on a product, after which `hps.fst`/`.snd` are available. Two related
shapes: `Continuous.add` builds `Continuous (f + g)`, which does not unify with
`Continuous fun x => f x + g x` under `simpa` (`Pi.add` versus a lambda) — state the sum as its own
typed `have`; and do not `rw [Function.comp_def]` to line up a composed sequence, use
`(hlim.comp hφ.tendsto_atTop).congr fun n => …`, since `Function.comp_apply` is `rfl`.

---

## PAIR — The pairing classes

**PAIR1. Instance search does not see through `LinearMap.flip`.** `flip` is a plain `def`, and defeq at
default transparency is not defeq at instance transparency. The state of play:

* `B.flip.flip` **is** found — `inferInstance` discharges `IsCompatiblePairing B.flip.flip` from
  `[IsCompatiblePairing B]`, and seven workarounds in the library existed for a problem that was
  never there. The real constraint is unrelated: the `flip` instances need a `TopologicalSpace` in
  scope, so a file that has not imported one gets a failure that *looks* like the `flip.flip`
  problem.
* A flip that is not syntactically a double flip **is not** found: `(prodPairing Bu Bx).flip`,
  `(epiPairing B).flip`, `(innerₗ E).flip`. Bridge it with a local
  `have : IsContinuousPairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance` — a plain
  `have`, since a local hypothesis of class type participates in instance search (LINT5) — or, better,
  declare the named instance once. `isContinuousPairing_flip_innerL` and
  `isCompatiblePairing_flip_innerL` are those instances, and
  `Duality/InnerPairing.lean` supplies the general flip instances for *any* symmetric pairing.
* Where the bridge cannot be an instance, state the pairing-parametrised lemma in the orientation
  that lets callers instantiate it at a **literal** `prodPairing` — `farkas_of_pairing` versus
  `farkas`.

**PAIR2. A pairing alias must be an `abbrev`, not a `def`.** The surface's ambient setting is
`pairing n := innerₗ (Rn n)`. Written as a `def`, *not one* pairing class is found, because instance
search does not unfold a plain `def` and every instance is stated about `innerₗ`. Written as an
`abbrev` all 31 classes resolve with no hypothesis. The failure is invisible until the *second*
class in the chain, so it reads as a missing instance deep in the tower rather than as a
reducibility problem at the alias.

**PAIR3. A pointwise identity cannot feed instance search; the classes are about a `LinearMap`.**
`negFst_prodPairing_apply` had said `negFst (prodPairing Bu Bx) p q = -Bu p.1 q.1 + Bx p.2 q.2`
since §30 was written, and it is what every *rewrite* inside a `conj` uses — but
`IsCompatiblePairing` takes the bilinear map itself, so no amount of pointwise agreement gets search
from `negFst (prodPairing Bu Bx)` to `prodPairing (-Bu) Bx`. The one-line `LinearMap.ext` version is
what unlocks four instances and with them every §29–§30 surface statement. **When a class is stated
about a bundled object, the dictionary entry has to be about the bundled object too.**

**PAIR4. Section variables and the pairing: three failures, three different fixes.**

* **The conclusion does not mention `B`, so the section variable is not inserted at all.** Automatic
  inclusion is driven by the statement; the symptom is "unknown identifier `B`" deep inside the
  proof. Fix with `include B in` before the doc comment — local, changes nothing else. Making `B`
  an explicit argument also works but changes every call site.
* **A theorem binder repeating a section variable's name silently detaches the instance binders
  before it.** `theorem foo [IsContinuousPairing B.flip] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) …` resolves
  `B.flip` against the *section* `B` and then shadows it. Drop the explicit binder — or, if you take
  the explicit-argument route above, *remove* `B` from the `variable` line rather than shadowing it.
* **A variable forced in by `include` is implicit and un-inferrable at call sites.** Every caller
  must write `(Bu := Bu) (Bx := Bx)`; the failure is a stuck-instance message, not "unknown
  implicit". This is the price of the first fix (EL9).

**PAIR5. Instance search here is order-sensitive, and `maxSynthPendingDepth` is why.**
`lakefile.toml` sets `maxSynthPendingDepth = 3`; the pairing classes chain deeply enough that a
search which would succeed at the default depth fails here, and the failure looks like a missing
instance rather than an exhausted budget. Raise the depth before concluding an instance is absent.

**PAIR6. Record a fact as an `instance` when an instance is what consumers want.**
`isCompatiblePairing_neg` sat as a *theorem* while three call sites re-derived it inline; the flip
instances sat in `Subgradient/StrictlyConvex.lean`, a file no surface `Setup.lean` will ever import.
Each is invisible until a *different* file needs it, which is why they surfaced in a
surface-instantiation audit rather than in the build. Where a bridge must not be an instance
(because it would loop or is not syntactically matchable), say so in a comment.

**PAIR7. Do not use `LinearMap.IsContPerfPair` for the pairing hypotheses.** The name is inviting and
the trap is quiet: it demands *joint* continuity of `(x, y) ↦ B x y` (so `F` needs a topology) and
bijectivity on both sides where we need surjectivity on one, and its only `topDualPairing` instance
carries `[FiniteDimensional 𝕜 E] [T2Space E]` — adopting it silently reimposes exactly the
hypothesis design decision D0 exists to avoid. Mathlib's own precedent (`LinearEquiv.image_closure_of_convex`) is to
leave the two conditions **unbundled**; our case differs only in scale — 67 signatures, not 3 —
which is the argument for a class here and not there.

**PAIR8. Joint continuity is a separate hypothesis.** `IsContinuousPairing` gives
`Continuous fun x => B x y` for each fixed `y`; `isClosed_subgradientRel` (Theorem 24.4) needs
`Continuous fun p : E × F => B p.1 p.2`, because the subgradient inequality moves both arguments at
once. Every caller passes it by hand, and a `prodPairing` needs one per factor.

**PAIR9. Do not reach for the weak topology.** The duality theorems hold in whatever topology `E`
carries, provided its continuous dual is the `F` side of the pairing — that is
`IsCompatiblePairing`, and it is trivial when `E` is paired with its own dual. `σ(E, F)` is one
instance of it, the coarsest, never the mechanism. `WeakBilin B` is besides a type synonym, so
`simp`/`rw` do not fire through it.

---

## LIB — Working in this library

**LIB1. Grep for the identifier before writing anything, including three-line utilities.** This has
now happened **seven** times. `Tdaf.lean` imports everything, so two same-named declarations in
mutually non-importing modules build fine module-by-module and then collide at the top-level import
— reported at the *older* file, in a module nobody touched. Worse, a *near*-duplicate does not
report at all (`le_of_forall_le_coe` and `le_of_forall_coe_le`), and a duplicate can surface as a
*type error at an old consumer* three files away. The realisations: `posHomGen` and eight companions
(with *different* definitions agreeing only for convex `f`), `add_coe_le_coe_iff` (three copies),
`recessionFn_eq_supportFn_dom_conj`, `recessionCone_coe_submodule`, `convexBifun_neg_adjointBifun`,
`smul_coe_submodule`. `grep -rn "theorem <name>\b\|def <name>\b" Tdaf/` over the whole tree costs
one second; a per-module `lake build` catches none of it. A `private` declaration gives no
protection — adding one import to a fourth file turned latent duplication into a hard error at the
private copy. Note also that inside `namespace Tdaf.EReal` a local `EReal.foo` shadows a future
Mathlib `EReal.foo`.

**LIB2. Before writing a concave proof, grep for the convex twin; before writing a mirror, check
whether it is the convex statement at the negation.** `ConcaveNormal G` unfolds to `Normal (-G)` up
to `neg_inj` — a four-line lemma that turned two clauses of Theorem 30.4 from "blocked on concave
mirrors" into two-line corollaries. Three concave proofs in the library re-derive their convex
counterpart instead of citing it, each written in a session where the convex version was not on
screen. And `ConcaveFn g ↔ ConvexFn (-g)` is `Convex.linear_preimage` applied twice, not a hand
proof: a nineteen-line proof of that shape means the epigraph/hypograph reflection was expanded by
hand instead of cited.

**LIB3. Measure *proof* lines, not declaration lines, before deciding a block is duplicated.**
Counting whole declarations — signature, docstring, proof — reported "246 declarations, 36 of them
over 20 lines". On proofs alone the same set is 240 declarations of which **151 have a proof of at
most three lines** and only five exceed twenty. Any "how much would this refactor save" estimate
that has not separated the three is wrong by a factor of several. In the same vein: of 240
concave-named declarations, 145 are **bridges**, where a convex and a concave object both appear
because their *interaction* is the content, and there is nothing to forward them to. Grepping for
`concave` and calling the result duplication over-counts by 3.4×.

**LIB4. Symmetries: bundle the involution at the point of definition, and never let it leak into the
statements it transports.** `reflect` and `saddleSwap` are bare `def`s, so `Function.Involutive`,
`Equiv`, `AddEquiv` and `OrderIso` never apply to them — `saddleSwap_injective` is hand-proved where
`Function.LeftInverse.injective` would do, and `saddleSwap` is antitone so it wants to be an
`OrderIso _ _ᵒᵈ` and instead is nothing. Bundling after the fact means touching every use site;
bundling at definition costs one line. Separately, eight public theorems in
`Bifunction/Process.lean` carry `.reflect` in their *hypotheses*, so a caller has to reason about
the reflection to discharge them — the transport stopped one lemma short of being invisible. A
prototype confirmed the goal is reachable: transporting a whole block through `saddleSwap`
produced hypotheses **identical** to the re-proved versions. Note that the double negation of a real-valued companion is
*not* `rfl`: `swapReal (swapReal K) = K` needs `neg_neg` and a `funext`, even though the pair-swap
half is `rfl`.

**State a sign dictionary as an equation between *objects*, not between values.** The library states
its convex/concave bridges pointwise (`(-g)ᶜᵒⁿʲ y = …` at a point), which forces every downstream
mirror to open with `funext`/`intro` plumbing before it can rewrite; stating the same fact as an
equation of functions lets the mirror be a `rw` chain. Measured over eight declarations, the
object-level form took **92 proof lines to 27** at a cost of six lines of infrastructure. And when a
saddle-function is swapped **the binder types of `iSup`/`iInf` swap too** — naming them by analogy
with the unswapped statement typechecks the `refine` and fails three lines later inside a `have`.
Read binder types off the pairing arguments.

**LIB5. Recording a Galois connection is not the same as using it.** `conjClosure`,
`polarConeClosure`, `polarSetClosure`, `epiClosure`, `clFnClosure` and `lscHullClosure` are each
referenced only by their own `_apply` and `isClosed_iff` lemmas; not one downstream theorem is
proved from them. Meanwhile `subset_polarCone_polarCone`, `polarCone_polarCone_polarCone` and
`conj_biconj` are hand-proved and are exactly `GaloisConnection.le_u_l`, `l_u_l_eq_l` and
`u_l_u_eq_u`. Two related notes: **Mathlib has no "a Galois connection restricts to an order
isomorphism between the closed elements"** (`ClosureOperator.gi` is one-sided) — the missing lemma
is twelve lines and generalises six hand-built `Equiv`s here; and **antitone Galois connections need
the `OrderDual` dance, which is only half free** — the connection itself is `rfl`-easy, but
transporting `gc.u_iInf` back through `toDual` does not `simp` away, so prove `epi_iSup`-style
lemmas directly.

**LIB6. Instantiate the Mathlib interface that has emerged, eagerly.** If a definition turns out to be
a Galois connection, a closure operator, a cone, a module, a lattice — say so and get the machinery
and the lemma names free. `Rel` is now `SetRel α β := Set (α × β)` (an `abbrev`), which is *the*
bundling for a multivalued map and is what makes Corollary 23.5.1 read as `∂(f*) = (∂f)⁻¹` rather
than as a `∀ x y` biconditional. `GaloisCoinsertion.liftCompleteLattice` computes by `rfl` and keeps
the ambient `PartialOrder` syntactically, so use `abbrev`, not `def`, for the bundled subtype.

**LIB7. A three-line consequence of a theorem you are reading is exactly what already exists.** See
LIB1. The corollary for *plans*: a design decision that names a primitive is worth re-checking against
`lean_references` once the development it describes has been written — `partialConj₂`, which a
design decision called "the organizing operation" of the bifunction development, has zero consumers
outside its own file, while `bracket` appears in thirteen modules.

**LIB8. Infinite dimensions cost hypotheses, not generality.** In the category of topological vector
spaces the arrows are the *continuous* linear maps, so a discontinuous linear functional is not a
morphism, and a subspace expected to behave like a finite-dimensional one must be assumed *closed*.
Both are automatic in finite dimensions, which is why Rockafellar never writes them. When one of his
statements fails here, restore one of those two hypotheses rather than abandoning the
generalisation. **Before transcribing an `ℝⁿ` statement quantifying over "proper", "≠ ℝⁿ" or
"closed", test it against a discontinuous functional** — it is the standard witness for exactly
this. Two structural consequences: a layer-D result and a layer-C result about the same object often
cannot sit in one module (the relative-interior clauses of a support-function theorem need
`RelativeInterior.lean`, which is not below `Duality/Support.lean`) — insert a thin module rather
than moving one; and `PolyhedralFn` does *not* carry `[FiniteDimensional ℝ E]` even though it is
declared inside a section that has it, because auto-inclusion drops what the definition does not
mention, so a lemma about polyhedral functions on a non-finite-dimensional dual space typechecks and
then fails three lines later. `#check @PolyhedralFn` before guessing.

**LIB9. Mathematical shortcuts worth remembering.**

* **`epi_injective` is usually the whole proof.** Every result about a *set* operation on epigraphs
  — supremum (`⋂`), composition with a linear map (preimage) — is a one-line
  `refine epi_injective ?_; rw [epi_lscHull, epi_iSup, …]`. Reach for segment-limit machinery only
  when the operation is not a set operation on epigraphs, which among §9's cases means only the sum.
* **`IsClosed.csSup_mem` replaces a whole `liminf`/sequence argument** for "a nondecreasing lsc
  function attains its crossing level": `{t | 0 ≤ t ∧ g t ≤ α}` is `Ici 0 ∩ g ⁻¹' Iic α`, closed by
  `lowerSemicontinuous_iff_isClosed_preimage`, and its `sSup` lies in it.
* **`Metric.isBounded_range_of_tendsto` bounds the whole range**, so no reindexing is needed before
  `IsCompact.tendsto_subseq`. `Tendsto.isBoundedUnder_le` gives only an eventual bound and forces
  one.
* **Look for the fixed-`ε` decomposition before formalising a "triangulate around `x`" step.** The
  weights satisfy `w = (1-ε) • μ + ε • ((w - (1-ε) • μ)/ε)`, which exhibits the point directly *for
  an `ε` fixed in advance*. The same shape — fix the small parameter from the target bound, then use
  compactness for the neighbourhood — is worth trying wherever a proof reads "for `z` close enough
  to `x`".
* **Run Carathéodory's elimination on a `Finset` of *indices*, never on a set of vectors.** Indexed
  elimination can only drop indices, so a "one generator per `Cᵢ`" invariant survives for free and
  the book's post-hoc coalescing disappears. Merge first, eliminate second. Note the elimination can
  be steered by a cost only in the **affine** case: an affine dependency has coefficients summing to
  zero so both signs occur; a conical dependency can be one-signed. That is exactly why Corollary
  17.1.3 is provable and 17.1.4 / 17.1.6 are false.
* **`LinearMap.toSpanSingleton ℝ E x` is the ray as a linear map, and every step through it is
  `rfl`.** "Restrict `f` to a ray" is then two lines.
* **`lscHull` is `liminf` unconditionally; `clFn` is not.** `clFn f x = liminf f (𝓝 x)` fails
  exactly when `clFn f x = ⊥` and `liminf = ⊤`. This is the source of Rockafellar's "except in cases
  where…".
* **`intrinsicInterior` is defined through the subspace topology**, so prove the ambient metric
  characterisation first and nothing else needs torsor transport. The stuck-instance error to expect
  is `AddTorsor ?V E`.
* **Almost every convexity proof needs `a = 0` and `b = 0` separately** — `combo_of_pos` discharges
  both degenerate branches by `simpa`. And `nlinarith` usually fails on `a*p + b*q < r`; feed it
  `mul_lt_mul_of_pos_left` twice plus `linear_combination r * hab`, which is the reliable way to use
  `a + b = 1` in a nonlinear identity.
* **`ring` handles `a⁻¹` as an atom**; `field_simp` is needed only when `a * a⁻¹` must cancel — and
  it needs the `≠ 0` hypothesis in the *local context*, not merely derivable.
* **`★` (U+2605) is not a valid Lean identifier character.** Rockafellar's starred variables must be
  renamed.
* **`Finset.cons_induction` (cases `empty`/`cons`) needs no `DecidableEq`**, and
  `Finset.Nonempty.cons_induction` has **one** major premise — write
  `induction hs using Finset.Nonempty.cons_induction`, not `induction s, hs using …`. Both
  auto-revert hypotheses mentioning `s`, so `ih` is the full implication.
* **`hasFDerivAt_iff_isLittleO_nhds_zero` plus `Asymptotics.isLittleO_iff` is the ε-δ entry point
  to `HasFDerivAt`**: the goal becomes
  `∀ c > 0, ∀ᶠ h in 𝓝 0, ‖f (x+h) - f x - f' h‖ ≤ c * ‖h‖`, which is what a "sandwich the increment"
  proof produces. Working at `𝓝 0` also makes `(u, v) + h = (u + h.1, v + h.2)` a bare `rfl`.
* **`abel` fails where `module` succeeds** on goals mixing `ℝ`-smul with additive structure — and
  it fails by leaving the goal open rather than erroring, which reads as a broken proof.
* **`positivity` cannot see through a plain `def`.** `pairingNorm B x = √(B x x)` is a `def`, so
  `positivity` fails on `0 ≤ pairingNorm B x + pairingNorm B y` even though `Real.sqrt_nonneg`
  would close it. Feed the API lemma instead.
* **Two ways to quotient out a subspace; pick by what the conclusion is about.** Building a
  projection `A` and working with `A '' C` is right when the target theorem is about an *image*,
  because then `recessionCone_image` is the load-bearing step. When the conclusion only needs
  "every point of `C` carries the same value as some point of `C ∩ N`",
  `eq_add_inter_of_isCompl` is strictly cheaper — no image lemma, no `recessionCone_image`, and no
  dependency on the module that owns the projection.

---

## BLD — Toolchain, build, worktrees

**BLD1. `lake` keys on content hashes, not mtimes, so `touch` does nothing.** "Touch every file you
changed before the final build" is a no-op: `touch f && lake build` prints only "Build completed
successfully" and re-runs **no linter**. To make the linters actually re-run, delete the module's
artifact — `rm .lake/build/lib/lean/<Module>.olean` plus `Tdaf.olean` — and rebuild.

**BLD2. A `.lake/build` can be silently stale, and `lake` will not notice.** The symptom is "Unknown
identifier `foo`" in a file you did not touch, where `foo` was added by a commit the checkout *does*
contain, reproducible across runs, and `lake build --rehash` does not detect it: the `.trace` files
were regenerated without the `.olean`s. It surfaces only when some *other* edit forces a dependent
module to rebuild, so it looks like a mysterious missing lemma. Diagnose with
`grep -c foo <Module>.olean` — Lean 4 oleans store declaration names verbatim, so a zero count on a
module whose source defines `foo` proves the artifact is stale — or by comparing olean mtimes with
the checkout time. Fix by deleting that module's `.olean`, `.trace` and `.ilean` and rebuilding,
which cascades correctly.

Distinguish this from **intermittent contention**: `lake build` sometimes reports
`failed to read file '….olean'` naming a *different* file each run, including toolchain and Mathlib
files. That is parallel `lean` processes, not a stale artifact and not a signal about your proof —
`ls` the named file, and if it exists just re-run. `lake env lean` on a scratch file has its own
version, `failed to read file '….olean.private'`, because the shared Mathlib build tree carries no
`.olean.private` files; for `#print axioms` use the MCP `lean_verify`, or append the block to a
project module and read the LSP diagnostics.

**BLD3. Worktree setup on Windows.** Two steps, both worth doing *before* spawning agents rather than
after one reports a two-hour Mathlib rebuild:

* **`.lake/packages` must be a *junction*, not a POSIX symlink.** `ln -sfn` reports
  `cannot overwrite directory` against the empty `packages` directory already there, and `rm -rf` of
  it races with whatever recreates it, so the loop appears to fail for no reason.
  `New-Item -ItemType Junction -Path … -Target …` works first time.
* **`cp -r` the primary's `.lake/build`** (312 MB) whenever
  `git diff <worktree-base> <primary-head> -- Tdaf/ lakefile.toml lean-toolchain` is empty; `lake`
  re-verifies the traces in seconds instead of a forty-minute cold build. Do **not** junction it —
  several worktrees writing one build directory is how BLD2 happens.

A lighter alternative when you only need to typecheck: set `LEAN_PATH` to a sibling checkout's
`.lake/packages/*/.lake/build/lib` and `.lake/build/lib` and run `lake env lean file.lean`. The
oleans are read-only so the sibling is safe. It does not let you `lake build` in the worktree.

**BLD4. `lake` 5.0.0 has no `-j` / `--jobs` option.** The job count cannot be capped from the command
line; `LEAN_NUM_THREADS=3` caps threads *inside* each `lean` process instead. Also: a module does
**not** need to be listed in `Tdaf.lean` to be built by name.

**BLD5. Scripting edits safely.** Three separate ways a patch script has destroyed a Lean file:

* **`open(p, 'w')` truncates before the value is evaluated**, so a `UnicodeEncodeError` mid-write
  leaves a 0-byte file. Write to `p + '.tmp'` and `os.replace`.
* **Python text mode on Windows defaults to cp936 here and emits CRLF.** The repository is LF
  throughout, so a three-line patch comes back as an 11,000-line diff. Always
  `io.open(tmp, 'w', encoding='utf-8', newline='\n')`, and **run `git diff --stat` before every
  commit**: if the numbers are far larger than the edit you made, this is why.
* **A mathematical letter written as a surrogate pair in a Python literal is not encodable as
  UTF-8.** `"𝓝"` is a lone surrogate; use `"\U0001D4DD"`, or extract the character from
  the file being edited rather than hand-writing an escape the shell may also mangle.

Recovery when the file was clean at `HEAD`: `git show HEAD:<path> > <path>` — *not*
`git checkout --`, which would also discard unrelated working-tree edits. And prefer targeted
`(old, new)` pairs that each `assert count == 1` over a blanket substitution: on a ≈500-line
generalisation pass that caught three places where the obvious substitution would have been wrong.

**BLD6. Bash heredocs break at roughly 8 KB.** The command is cut mid-string, leaving a quote open,
and bash reports "unexpected EOF while looking for matching quote" at a line number in the *middle*
of a valid script. Use the `Write` tool for a new file, or `Write` the Python script to the
scratchpad and run it with `python <path>`. Related: `/tmp` in the Bash tool is Git Bash's `/tmp`,
which the Windows `python` on PATH **cannot see** — put anything a Python script will read in the
scratchpad directory, which is a real Windows path. The scratchpad is shared across sessions, so
prefix scratch filenames with the task or `Write` fails with "File has not been read yet" against a
previous session's file.

**BLD7. Checking the 100-character line limit with `awk 'length > 100'` gives false positives.** `awk`
counts UTF-8 *bytes*, so every line containing `ℝ`, `≤`, `∈`, `•` or `₂` looks three to fifteen
characters over and a clean file appears to have dozens of violations. Count codepoints, or just
build and trust `linter.style.longLine`.

**BLD8. `#print axioms` wraps long declaration names, so grepping its output under-counts.** Piping
through `grep 'depends on axioms: \[propext, Classical.choice, Quot.sound\]'` silently misses every
declaration whose name pushes the list past the pretty-printer width — the output breaks after
`[propext,`. Collapse whitespace first (`re.sub(r'\s+', ' ', out)`), then match, and check the
record count against the number of `#print axioms` lines you emitted.

**BLD9. Probing Mathlib names with a scratch file that does `import Mathlib` takes over ten minutes.**
Import a project module instead — it is already built.

**BLD10. `Tdaf.lean` is one flat list ordered by full module path**, with no grouping by directory.
The check is `grep "^import " Tdaf.lean | LC_ALL=C sort -c`. Nothing depends on the order, but a
future "insert alphabetically" instruction looks wrong wherever you put the new line — which is how
three separate violations accumulated before anyone checked.
