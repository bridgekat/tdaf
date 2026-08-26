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

A third instance, from the fix round: `PosHomogeneous.clFn` is not a usable name. Inside
`theorem PosHomogeneous.clFn … : PosHomogeneous (clFn f)` the bare `clFn` in the statement resolves
to the theorem being defined, and because `clFn` lives in `Tdaf.ConvexAnalysis` rather than at the
root, `_root_.clFn` does not rescue it either. The prefix spelling `posHomogeneous_clFn` works and
matches the neighbours `posHomogeneous_indicatorFn` and `posHomogeneous_supportFn`.

**EL15. `rw` at a hypothesis rewrites the scalar in *both* the set action and the vector action,
and the follow-up `simp` lemma fires on only one.** `rw [hb1, one_smul] at hmem` on
`hmem : z₁ + b • (v + z₂) ∈ recessionCone C + b • D` replaces `b` by `1` in both places, and then
`one_smul` fires on `(1 : ℝ) • (D : Set E)` but leaves `(1 : ℝ) • (v + z₂ : E)` alone — the two are
different instantiations of the same lemma (EL4). The hypothesis silently becomes a statement about
`recessionCone C + D` while the goal still says `b • D`, and the mismatch surfaces later as a type
error naming neither. The fix is not `simp only [one_smul]`, which over-normalises the goal: prove
the *value* equation on its own — `have hval : z₁ + b • (v + z₂) = x := by rw [hb1, one_smul, …]` —
and `rwa [hval] at hmem`, so the membership term is never rewritten.

**EL16. `clFn` must never be unfolded.** `simp only [clFn, h]` with `h : lscHull f = lscHull g`
rewrites the `else` branch of `clFn`'s `if` but not the `∃ x, lscHull f x = ⊥` condition, leaving a
goal whose two branches disagree. Go through the defining equations `clFn_of_exists_eq_bot` /
`clFn_of_forall_ne_bot` under a `by_cases`.

**EL17. `ContinuousOn.congr` cannot infer its source function from a `?_`.**
`continuousOn_const.congr h` fails with *"don't know how to synthesize implicit argument `f`"*,
because `f` is determined only by the `EqOn` proof, which is still a hole. Bind the constant to a
typed `have` first — `have : ContinuousOn (fun _ : Rn n => (⊥ : EReal)) C := continuousOn_const` —
and use dot notation on that. Same family as EL9.

**EL18. `rw` with a biconditional-shaped equation rewrites *every* occurrence, including the one
inside the operator you are rewriting under.** Three instances, all from the Part III round:

* `rw [← hbi]` with `hbi : f** = f` rewrites the `f` under `monotoneConjOrthant f` as well, and the
  goal only becomes unprovable several lines later.
* `rw [conj_apply, conj_apply]` rewrites the *left*-hand side twice — after the first rewrite the
  inner `conj B f y` matches again — instead of left-then-right.
* `rw [← isClosed_convex_isCone_eq_iInter_halfSpaceCone …]`, whose right-hand side is `K` and whose
  left-hand side *indexes* over `∀ y ∈ K`, rewrites the index condition too.

The reliable shape is to name both unfoldings as `have`s and rewrite with those, or `refine
Eq.trans ?_ thm` when only one side should move. Same family as EL4.

**EL19. Defeq is not syntactic equality, and `rw` only sees the syntax.** `inner ℝ x y` and
`pairing n x y` are definitionally equal — `pairing` is an `abbrev` for `innerₗ` — but a surface
statement written in the book's `⟨x, x*⟩` makes `rw [backbone_lemma]` fail with *"did not find an
occurrence of the pattern"* while `exact` succeeds. The idiom that works: instantiate the backbone
lemma as a `have`, `rw` the *set-level* hypotheses into that, and close with `exact`. §13 hit it
five times in one file. The same asymmetry is why `rw [← flip_pairing n]` can time out `isDefEq`
where the targeted `conj_flip_pairing` / `polarCone_flip_pairing` rewrite goes straight through:
prefer the specific `*_flip_pairing` lemma whenever the `.flip` sits under an operator.

**EL20. `rw` will not unfold `Ne`.** `rw [← linFn_eq_zero_iff]` on a goal `b ≠ 0` reports
*"did not find `?m = 0`"*. Lead with `rw [Ne, …]`, or better `intro hzero` and work forwards.

**EL21. A lambda whose binder type is only inferable from the *expected* type needs an ascription.**
`fun x hx => le_of_lt hx` inside `mem_interior.2 ⟨…⟩` fails with a metavariable type mismatch,
because `x ∈ {x | k x ≤ 1}` is not yet known to be what `le_of_lt` should produce. Write
`fun x (hx : k x < 1) => le_of_lt hx`. Same root as EL17: an implicit argument determined only by a
term that is still a hole.

**EL22. An `EReal`-valued bridge lemma cannot rewrite a real-valued goal.**
`IsNorm.coe_toSeminorm` reads `((p x : ℝ) : EReal) = k x`, so it does nothing to `0 < p (x - y)`.
Rewrite the `EReal` hypothesis backwards — `rw [← hk.coe_toSeminorm z] at h` — and finish with
`exact_mod_cast`.

**EL23. `IsFace` and `IsExtreme` are structures, not `And`s, and `.1`/`.2` land on fields.**
`IsExtreme 𝕜 A B` has fields `subset` and `left_mem_of_mem_openSegment` — the *right*-endpoint
clause is the separate lemma `IsExtreme.right_mem_of_mem_openSegment`, not `.2.2`. This library's
`IsFace C C'` has fields `toIsExtreme` and `convex`, so `h.1` is the extreme-set structure and not
the convexity that reads first in the docstring. Both mistakes typecheck far enough to be reported
somewhere else entirely: because `𝕜 := ℝ` the unifier ends up comparing `Real`'s `CauSeq`
representation, and the error names `CauSeq.Completion` at a line with no `ℝ` in it. **Write the
field name.**

**EL24. Two more beta-redex sites, both from the Part IV round** (the general rule is EL2).
`refine ⟨(a, b), ?_, ?_⟩` against `∃ p, P p.1 ∧ Q p.2` leaves goals displayed as `P (a, b).1`,
which `rw` will not match — `dsimp only` first, or supply the pair with `exact ⟨_, _⟩` and let
elaboration reduce it. And `x ∈ S + T` unfolds to `∃ a ∈ S, ∃ b ∈ T, (fun x₁ x₂ => x₁ + x₂) a b = x`,
so every `rw` against the membership fails; go through `Set.mem_add` / `Set.add_mem_add` instead of
unfolding.

**EL25. A lemma with strict-implicit binders `⦃x⦄` does not fire under `simp`.**
`Finset.forall_mem_image : (∀ y ∈ s.image f, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x)` is the one that bites —
`simp [Finset.forall_mem_image]` changes nothing and reports no error. Apply it by hand:
`Finset.forall_mem_image.2 fun q hq => …`.

**EL26. Three more places the elaborator needs a type it cannot infer.**

* **A `Finset` coercion in a position whose expected type is still a hole** elaborates to a
  metavariable, and the error names something else entirely: `↑p` for `p : Finset E` inside a
  statement about `Set.InjOn` produced *"stuck at solving universe constraint"* and a type mismatch
  at three unrelated lines. **Always ascribe: `(↑p : Set E)`.**
* **`▸` fails against a `def`-wrapped predicate.** `hlift ▸ h` for a goal whose head is a `def` and
  an equation whose sides are the unfolded form reports *"the equality does not contain the expected
  result type on either the left or the right hand side"*. `change` to the unfolded form, then `rw`.
  Same family as EL7.
* **`Submodule.span_induction` hands the `add` step its induction hypotheses as set membership**, so
  `add_le_add hy hz` fails with *"`hz` has type `z ∈ {x | … ≤ 0}` but is expected to have type
  `?a ≤ ?b`"* — while the `mem` and `zero` branches close by `exact` and take the defeq step
  silently. Three of four branches green is the tell. Ascribe as in EL5.

**EL27. `IsExposed 𝕜 A B` is `B.Nonempty → ∃ l, …`, so the empty case can vanish on one side of a
construction and reappear on the other.** `isExposed_empty` is free, but `0⁺∅ = univ` is never
empty, so a theorem transporting exposedness through `recessionCone` must case-split on `C' = ∅`
and *produce* a functional (`l = 0`, via `IsExposed.refl`). The extreme/face version needs no split,
because its extremality clause is vacuous over an empty face. Symptom: the proof works for every set
you test and then a hole opens at the `⟨l, …⟩`.

**EL28. Four coercion traps from the product round, all of which report somewhere else.**

* **A `≃L` does not coerce to a `≃ₗ` by ascription.** `((e : E ≃L[ℝ] F) : E ≃ₗ[ℝ] F)` is a hard type
  mismatch, and the *visible* symptom is a `(deterministic) timeout at whnf` **at the next
  declaration**. Write `e.toLinearEquiv`. Check the coercion before raising heartbeats (EL13).
* **`IsAdjointPair`'s two coercions of a `LinearEquiv` are not syntactically equal.** `hA u z` uses
  the `LinearMap` coercion, while a `have h : A u = v` proved by `simp` uses `⇑A`, so `rw [h] at hA`
  reports "did not find an occurrence". `simp only [LinearEquiv.coe_coe] at h` first.
* **`indicatorFn_of_mem rfl` elaborates the set as a metavariable.** On a goal containing
  `indicatorFn {0} 0` it reports *"did not find an occurrence of `indicatorFn (Eq ?m) ?m`"* — `rfl`
  was taken as a proof of `?x ∈ ?s` with both open. Pin the set:
  `indicatorFn_of_mem (s := ({0} : Set E)) (Set.mem_singleton_iff.2 rfl)`. SET8 records the singleton
  half of this; the metavariable is the other half.
* **`simpa using convex_univ` fails against `IsRealInterval univ`** — `simpa` elaborates the term
  against the simplified goal without unfolding the `def`, even though `IsRealInterval` *is*
  `Convex ℝ`. `rw` the argument and close with `exact`, which takes the defeq.

**EL29. `le_iSup₂_of_le i j h` is the tool for a nested `⨆ a ∈ s, ⨆ b ∈ t`.** Chaining `le_iSup₂`
with an explicit `(f := fun a (_ : a ∈ s) => …)` at each level is where these proofs go to die
(EL8/EL9); `le_iSup₂_of_le` takes the two witnesses and the residual inequality and needs no
ascription.

**EL30. Two more explicit-argument traps whose errors name a type, not a missing argument.**
`Fin.addCases_left`/`Fin.addCases_right` take **only** the index explicitly, so
`Fin.addCases_left _ _ j` reports *"Function expected"*. And `ContinuousLinearMap.single` and
`ContinuousLinearMap.sum_comp_single` take `R` and `φ` explicitly — Mathlib re-declares
`variable (R φ)` just before them — so `ContinuousLinearMap.sum_comp_single g x` reports *"the
argument `g` has type `StrongDual ℝ (ι → E)` but is expected to have type `Type ?u`"*. Write
`ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => E) g x`. That pair is the whole proof that a
finite product of compatible pairings is compatible, so it is the one blocker on the `ι → E` tower.

**EL31. `obtain ⟨a, ha, rfl⟩` cannot substitute a variable occurring in the term that produced the
hypothesis.** `∃ a, 0 ≤ a ∧ y = a • g (halfLine x y)` will not take `rfl`, because `y` occurs on the
right. Name the equation and feed it forward instead of rewriting.

**EL32. Three explicit-argument traps from the Part V round, each reporting as something else.**

* **`Filter.limsup_le_of_le`'s first explicit argument is the `isBoundedDefault` autoParam, not the
  hypothesis.** `limsup_le_of_le ?_` feeds the `∀ᶠ … ≤ a` proof into the *cobounded* slot, and the
  error is an application type mismatch reporting `(∀ᶠ n in ?f, ?u n ≤ ?a) → limsup ?u ?f ≤ ?a`
  "but is expected to have type `limsup … ≤ ?a`" — which reads as a broken lemma rather than a slot
  mix-up. Write `limsup_le_of_le (h := hev)`. Same family as EL30.
* **`Tdaf.Surface.pairing_comm` takes `n` implicitly**, so `pairing_comm n w y` elaborates `n` into
  the first *vector* slot and `rw` reports *"did not find an occurrence of the pattern `(?m w) y`"*
  against a goal that visibly contains `((pairing n) w) y`. Write `pairing_comm w y`.
* **`InnerProductSpace.toDual_apply` is not a name.** It is `toDual_apply_apply`, and it is `rfl`,
  so `(toDual v) x = pairing n x v` is `real_inner_comm x v` and nothing more.

**EL33. `iInf_pos` / `iInf_neg` unfold `def f x := ⨅ _ : p, c` only in *term* position.**
`rw [iInf_neg h]` on a goal mentioning `f x` reports "did not find an occurrence". Give the
`_of_not_mem` equation its own lemma and prove it in term mode. The `⨅ _ : p, c` encoding is still
the right way to write a piecewise `EReal` function — it keeps `Decidable` out of the statement
(ER6) — but it costs one equation lemma per branch.

**EL34. `field_simp` normalises `A / c = 0` to `A = c * 0`, not `A = 0`.** Symptom is a leftover
goal naming `x.ofLp 1 * 4 * 0`. Follow with `simpa using`.

**EL35. Four explicit-argument and slot traps from the Part VI round.**

* **`Filter.limsup_le_of_le`'s first explicit argument is the `isBoundedDefault` autoParam.**
  `limsup_le_of_le ?_` feeds the `∀ᶠ … ≤ a` proof into the *cobounded* slot, and the error reports
  `(∀ᶠ n in ?f, ?u n ≤ ?a) → limsup ?u ?f ≤ ?a` "but is expected to have type `limsup … ≤ ?a`",
  which reads as a broken lemma rather than a slot mix-up. Write `limsup_le_of_le (h := hev)`.
* **`add_le_add_left h _` picks its orientation from the goal, and picks wrong under `EReal`
  coercions.** It unified the wrong summand and reported a mismatch naming two different sides. Use
  `add_le_add le_rfl h`, which fixes both arguments explicitly.
* **`rw [f_of_mem h] at k` rewrites the *first* occurrence, which is usually not the one you meant.**
  For a piecewise definition, declare explicit value lemmas at the points you care about
  (`foo_zero_zero`, `foo_zero_of_ne`) instead of rewriting with a hypothesis-carrying general lemma.
* **An implicit section variable that is a *function* will not unify against a caller's lambda.**
  With `variable {h : Rn n → EReal}`, `refine thm ?_ ?_ hz` fails with a type mismatch on `hz` —
  which is obviously fine — because `h`'s metavariable was never assigned and the later arguments
  were elaborated against garbage. Pass it by name: `(h := fun u => quadFn (pairing n) (a - u))`.

**EL36. `rw` cannot key on a two-function product pattern.** A lemma concluding
`⨅ p : α × β, (ψ p.1 + φ p.2) = (⨅ ψ) + ⨅ φ` is unusable by `rw`: the left side is
`?ψ p.1 + ?φ p.2`, which is not a higher-order pattern, and `rw` reports "did not find an
occurrence" against the very goal it was written for. Instantiate both functions first —
`have h := lemma (fun w => …) (fun x => …) h₁ h₂` — then `rw [h]`. Metavariable instantiation
beta-reduces, so `h` comes out in exactly the form the goal is in. EL24 is the sibling for pairs
supplied to `refine`.

**EL37. A `whnf` timeout is not always a layer mismatch — sometimes the term is just large.**
`Convex.relint_image` timed out at 200 000 heartbeats when its two sets were
`dom (conj (pairing n) f)` and `domConcave (concaveConj (pairing m) g)`, while the identical call
over `dom f` and `domConcave g` elaborated instantly. Neither raising heartbeats nor EL13's import
check helps. State the computation once as a private lemma with the sets as opaque
`{S : Set _} {T : Set _}` and apply that, so the elaborator never sees the conjugates. Worth doing
prophylactically for any `ri`/`Convex.*` computation whose arguments are conjugates or bifunction
domains.

**EL38. Ascribing an unfolded membership inside `obtain … : … := …` makes the elaborator solve the
ascription before it knows the set.** `obtain ⟨x, hx⟩ : ∃ x, F 0 x ≠ ⊤ := intrinsicInterior_subset hs`
reports *two* errors, neither mentioning the ascription: a mismatch claiming `hs` is expected to have
type `(fun x => F 0 x ≠ ⊤) ∈ intrinsicInterior ?m Exists`, and a failure to synthesize
`AddTorsor ?m (Rn n → Prop)`. Bind the membership at its own type first, then `obtain` from it.

**EL39. Never add an instance binder a section already derives.** Adding `[TopologicalSpace E]` to a
section that has `[NormedAddCommGroup E]` produces an application type mismatch between two copies of
the same `def`'s instance argument — `Proper (@clFn E PseudoMetricSpace.toUniformSpace.toTopologicalSpace f)`
against `Proper (@clFn E inst✝⁶ f)` — which reads as a broken lemma about `clFn`. **The tell is two
different instance expressions in one message.** `LocallyConvexSpace ℝ E`, `IsTopologicalAddGroup E`
and `ContinuousSMul ℝ E` are all derivable from `NormedSpace ℝ E`; add none of them.

**EL40. `fun_prop` inside a `.comp` argument cannot infer the function it is asked about.**
`hgc.comp (by fun_prop)` fails with *"`fun_prop` was unable to prove `Continuous ?m.35`"* and an
empty `Issues:` list, because `Continuous.comp` leaves the inner function a metavariable. Name it
first with a typed `have`, then compose.

---

**EL41. `rw` inside a `subgradient` membership leaves a beta-redex, and `exact_mod_cast` then
reports the redex as if it were a cast failure.** Rewriting under `x ∈ subgradient B f y` produces a
goal whose head is `(fun z => …) a` rather than the applied form. `exact_mod_cast` sees the redex,
cannot line the casts up through it, and the error it prints names the coercion — so the natural
reading is that a `↑` is in the wrong place, and the natural response is to add `push_cast`, which
does nothing. `beta_reduce` (or `simp only []`) first, then the cast tactic works unchanged. The
tell is that the reported cast looks *already correct*.

**EL42. In a module with no topology import at all, `[TopologicalSpace E]` reports "invalid binder
annotation, type is not a class instance ?m.4" — which reads as a `variable`-syntax error.** It is
not: it is a missing import, and no part of the message says so. `autoImplicit` (BLD18) then makes
it worse, binding `closure` as an implicit variable and producing *"Function expected at `closure` …
but this term has type `?m.2`"*. Three cascading errors, only the first of which is real, and none
of which mentions `Mathlib.Topology.Algebra.ConstMulAction`. When a class in a `variable` line is
reported as "not a class instance", check the imports before the syntax.

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

**LINT10. `unusedVariables` fires on a binder that occurs only inside the *type* of the next
hypothesis.** Unfolding `mem_recessionCone`'s `∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → …` as
`fun _ hy x hx l hl => …` warns *"Variable name `l` is not explicitly referenced"* even though
`hl : 0 ≤ l` mentions it. Make the binder anonymous. This hits every eta-expansion of a
`∀ a, 0 ≤ a → …` predicate.

**LINT11. Two tactics that fail the zero-warning bar by succeeding too well.** `field_simp`
frequently closes the goal outright, and the `ring` written after it out of habit then errors with
*"No goals"*. And a `change` added defensively in front of a `rw` that would have gone through
anyway trips `linter.unusedTactic`. Add neither pre-emptively; run the proof without them first.

**LINT12. Two more, both from porting a proof rather than writing one.** `letI` is rejected for a
*data* class when the goal is a proposition — `letI : Fintype ↥b := …` warns *"the goal is a
proposition, so `let` is preferred"*; anonymous `let : Fintype ↥b := …` is accepted and still
participates in instance search (LINT5 records only the `haveI`/Prop case). And **a `simp only`
copied from a binary lemma often closes the `Set.pi` version outright**, so the copied trailing
`tauto` errors with "No goals to be solved" at a line that points at the closer, not at the simp
set. When porting `Prod` → `Set.pi`, drop the closer and re-add it only if needed.

---

**LINT13. Deleting a duplicate can drop the survivor a layer, and the unused-section-variable linter
is what tells you.** When two copies of a lemma live at different layers and you delete one, the
survivor often no longer needs every instance its section declares — the deleted copy was the reason
the section sat where it did. `linter.unusedSectionVars` then fires on the survivor. **Read that
warning as a layer report, not as noise**: per LINT3 the fix is to move the declaration to the
section that matches its real hypotheses, not to `omit` the instance and stay put. Four layer drops
came out of one round's duplicate removal this way, and three of the four were found by the linter
rather than by a person.

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

**DEP6. Four more renames, two of which are not drop-in.**

| deprecated | current | note |
|---|---|---|
| `Set.restrict` | `Set.domRestrict` | and `continuousOn_iff_continuous_restrict` → `…_domRestrict` |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | |
| `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection` | `Submodule.isCompl_orthogonal` | takes the submodule **explicitly** |
| — | `closure_empty_iff` | takes its set **explicitly** |

The last two are the trap: `eq_add_inter_of_isCompl Submodule.isCompl_orthogonal` is an application
type mismatch and `closure_empty_iff.1` reports *"Invalid projection … has function type"*. Write
`Submodule.isCompl_orthogonal _` and `(closure_empty_iff T).1`. Both old names still appear in
backbone docstrings.

**DEP7. Three more renames from the v4.34.0-rc1 pin.** `ContinuousLinearMap.zero_apply` and
`ContinuousLinearMap.neg_apply` are deprecated in favour of the *root* `zero_apply` / `neg_apply`,
so dot notation has to change, not just the name; and the `push_neg` tactic is deprecated in favour
of `push Not`. A `simp only` list naming any deprecated lemma builds but warns, and a warning
fails the bar.

**DEP8. `abs_add` is gone; the name is `abs_add_le`.** And grepping Mathlib for either finds
nothing, because both are `to_additive`-generated from `mabs_mul_le` — DEP3 in its purest form.

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
* **`w - ↑c = w + ↑(-c)` is closed by a bare `rfl` and by nothing else.** Both `EReal.coe_neg` and
  the `Sub` instance are `rfl`, but `rw`'s trailing `rfl` runs at *reducible* transparency, so
  `rw [Tdaf.EReal.neg_coe_sub]` reports *"unsolved goals ⊢ w - ↑c = w + ↑(-c)"* — which reads as
  the rewrite having fired on the wrong side. Put `rfl` on the next line. Same family as EL3.
* **`simp` cannot turn `w - -↑c` into `w + ↑c`.** There is no `sub_neg_eq_add` on `EReal` (not a
  `SubtractionMonoid`, ER1), and `simp` leaves exactly that goal with no error.
  `change w + -(-(c : EReal)) = _` then `rw [neg_neg]` is the route.

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

**ER11. `EReal` is not cancellative, but two-sided bounds pin equality, and
`Tdaf.EReal.le_coe_of_add_le_coe_add` is the tool.** From `↑p ≤ u`, `↑q ≤ v` and `u + v ≤ ↑(p+q)` it
concludes `u ≤ ↑p`. Symptom: you have `x + ↑ν ≤ 0`, want `x ≤ ↑(-ν)`, reach for
`EReal.le_sub_iff_add_le`, and then fight `0 - ↑ν` (there is no `zero_sub`, ER1) plus two side
conditions. Applying the lemma twice with the summands swapped gives both bounds with no subtraction
and no `⊥`/`⊤` split.

**ER12. `bot_add` is not a root name on `EReal`.** `exact bot_add _` reports *"unknown identifier"*
inside `namespace Tdaf.ConvexAnalysis`; write `_root_.EReal.bot_add`. Same family as the
`neg_bot`/`neg_zero` split in ER2. Relatedly, do not hand an `EReal` coercion side goal to `simp`:
discharging `¬ (↑(a - b) ≤ ⊥)` by `simp` leaves `¬ ↑a - ↑b = ⊥`, because `simp` pushes the coercion
apart. Use `le_bot_iff.1` and `_root_.EReal.coe_ne_bot`.

**ER13. The supremum of a separable sum over a product is an induction, not an ε argument.**
For `⨆ x ∈ ∏ Cᵢ, ∑ i, gᵢ (xᵢ) = ∑ i, ⨆ z ∈ Cᵢ, gᵢ z`, induct on the index `Finset`; at `cons i t`
use `Function.update` to prove `⨆ x ∈ ∏C, (f (xᵢ) + g x) = ⨆ z ∈ Cᵢ, ⨆ x ∈ ∏C, (f z + g x)` — both
directions by `le_iSup₂_of_le` — then close with `Tdaf.EReal.biSup_add_biSup`, the same interchange
`conj_infConv` runs on. **No `⊤` case split and no ε appear**; the only side condition is
`∑ j ∈ t, ↑rⱼ ≠ ⊥`, which is `Tdaf.EReal.coe_sum` then `_root_.EReal.coe_ne_bot`. Two successive
plans budgeted this as the expensive piece and both were wrong. Note `Tdaf.EReal.coe_sum` **exists**
(`Order/EReal.lean`) — it is *Mathlib* that lacks it.

**ER14. `bot_add` is not a root name, and neither is much else.** Covered by ER12; the product round
added `continuous_finset_sum` → `continuous_finsetSum` to DEP's table, and found that
`Set.mem_fintype_sum` is `to_additive`-generated and so invisible to a grep of Mathlib (only
`Set.mem_fintype_prod` occurs) — it is what makes `piSum '' univ.pi C = ∑ i, C i` a six-line proof.
DEP3, again.

**ER15. `EReal` is `DenselyOrdered` in this Mathlib, and that is the clean route from a
junk-value-free bound to the book's `limsup`.** `le_of_forall_gt_imp_ge_of_dense` plus
`EReal.lt_iff_exists_real_btwn` turns "every real `μ` above the bound eventually dominates" into
`limsup ≤ …` in two lines; `theorem_24_5_limsup` and `theorem_24_6_limsup` are four lines each this
way. Worth knowing before reaching for a filter argument.

**ER16. More renames, from §26.** `div_le_div_iff` → `div_le_div_iff₀`, with `le_div_iff₀` and
`div_le_iff₀` beside it. `zero_lt_top` is not a root `EReal` name. `EReal.coe_mul_top_of_pos`,
`EReal.add_top_of_ne_bot` and `EReal.top_add_of_ne_bot` all need the `_root_.` prefix from inside
`Tdaf.EReal`. DEP3, again.

**ER17. `neg_eq_zero` does not apply on `EReal`.** `rw [neg_eq_zero]` on `-a = 0` fails with
"did not find an occurrence" naming `SubtractionMonoid.toSubNegZeroMonoid`, because the lemma needs a
`SubtractionMonoid` and `EReal` is not one (ER1: `EReal` subtraction is not a group operation).
Instead: `rw [← neg_neg a, h, neg_zero]`. Same shape for `neg_ne_zero`, `neg_le_neg_iff`, and
anything else routed through `SubtractionMonoid`.

**ER18. `EReal` is `DenselyOrdered`, and `eq_top_iff_forall_lt` takes its argument explicitly.**
`EReal.eq_top_iff_forall_lt : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x`, like `eq_bot_iff_forall_lt`, is the
clean way to prove a supremum is `⊤`: `rw [_root_.EReal.eq_top_iff_forall_lt]; intro c`, then exhibit
a point beating `c`, with no `⊥`/`⊤` case split.

---

**ER19. `EReal` is not a semiring, so a scalar does not distribute over a `Finset.sum`.**
`Finset.mul_sum` and `Finset.sum_mul` do not apply: there is no `NonUnitalNonAssocSemiring EReal`
instance, because multiplication does not distribute over addition once `⊥` and `⊤` are in play
(`⊤ * (1 + -1)` against `⊤ * 1 + ⊤ * -1`). The concrete consequence: "each `fᵢ` is separable ⟹
`∑ᵢ λᵢ fᵢ` is separable" **cannot be proved by distributing `λᵢ` through the sum**, and there is no
side condition on the `λᵢ` alone that rescues it. Hypothesise the separability of the combination
instead — which is what Rockafellar does, asserting the step without proof. Related: ER1, `EReal` is
not cancellative.

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

**SET8. `indicatorFn_of_mem rfl` fails for a singleton.** `rfl : x ∈ s` unifies `s := Eq x`,
whereas `Set.singleton x` is `{y | y = x}` — the other orientation. The error names
`indicatorFn (Eq ?m) ?m`, which looks like an elaboration bug and is not. Use `Set.mem_singleton _`.

**SET9. Building an element of `Rn n = EuclideanSpace ℝ (Fin n)` from coordinates.** A bare
`(fun j => …)` does not elaborate at that type; the spelling is `WithLp.toLp 2 fun j => …`, and
`toLp p x j = x j` is `rfl`, so the `@[simp]` `_apply` lemma costs nothing. Reading goes the other
way: `x j` displays as `x.ofLp j`. Coordinate continuity is
`PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) j` — `β` is explicit and `p` is not inferable
from the goal, so both must be supplied or the application silently eats `j` as `β`.

**SET11. Spell a `Finset` split membership-wise, not as `s = t ∪ u`.** `Finset.union` and
`Finset.sdiff` both put `[DecidableEq ι]` in the *statement*, which ER6 warns will not match a
caller's `Classical.propDecidable`. Take `(hdisj : Disjoint t u)` and
`(hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)`, which are decidability-free, and recover `Finset.sum_union`
inside the proof with `classical; have : s = t ∪ u := Finset.ext …; subst`. Same trick for a
combined witness: `⟨fun i => if i ∈ t then a i else b i, …⟩`.

**SET12. `Finite ↥{x | P x}` and `Finite {x // P x}` are the same type and not the same
instance-search key.** `Set.Finite.to_subtype` produces the `↥`-form; `Finite.of_equiv _ e` needs the
`Subtype`-form its domain is written in, and reports *"failed to synthesize `Finite { C' // … }`"* at
the `of_equiv` line with a `have` of the "same" fact one line above. Instance search is syntactic
where `exact` is not; bounce through three `have`s, taking the defeq at each `exact`.

**SET13. The `Rn 2` counterexample toolkit.** Everything the three §26 counterexamples and the
§23 one needed, and nothing more: `(a • x + b • y) i = a * x i + b * y i` and `(u - v) i = u i - v i`
are both `rfl`; `WithLp.toLp 2 ![a, b]` with `rfl` coordinate lemmas plus `ext i; fin_cases i`
discharges every concrete vector goal; and `positivity` **does** consult hypotheses about atoms, so
a `0 < ξ₁` in context is enough for it. `fderiv` on `Rn 2` can be avoided entirely — compute the
subgradient by hand and finish with `hasGradientAt_toDual_of_subgradient_eq_singleton`.

**SET14. A concrete counterexample usually needs fewer test points than it looks.** For the p. 257
parabola, testing the subgradient inequality at just `s = ξ₂`, `ξ₂ + 1` and `ξ₂/2` on the ray
`(2su₀, s)` forces `u₀² + u₁ = 0` *and* the completed square to vanish, with no case split at all.
Pick the test points before writing the proof, not during it.

**SET15. `nlinarith` on a Jensen-style two-point inequality: supply the algebraic identity.**
`a·x² + b·y² ≥ (a·x + b·y)²` under `a + b = 1` defeats `nlinarith` even with the obvious hints,
because the identity `a x² + b y² − (a x + b y)² = a b (x − y)²` holds only *modulo* `a + b = 1` and
`nlinarith` will not find that use of the hypothesis. Prove the identity first with
`linear_combination (-(a * x ^ 2 + b * y ^ 2)) * hab`, then finish with `linarith`. The `t ↦ t⁴` case
is this one squared (`pow_le_pow_left₀`), not a second `nlinarith`.

**SET16. `Mathlib.Analysis.Convex.Mul` is not in this project's import closure**, so
`Even.convexOn_pow` is an "unknown constant" although it is in Mathlib. Rather than widening a
surface file's imports for one lemma, state the two-point inequality directly, as in SET15.

---

**SET17. State `⋂ i ∈ s` lemmas over a bare predicate, so one lemma serves `Set` and `Finset`
alike.** Writing the hypothesis as `(s : Finset ι)` forces a second, near-identical lemma the first
time a caller has a `Set ι`, and the two proofs are the same proof. Take `{p : ι → Prop}` (or an
implicit `s : Set ι`) and write `⋂ i ∈ s`; `Finset` callers supply `↑s` and pay one coercion lemma,
`Finset.mem_coe`. This is what `polyhedral_biInter` and `polyhedral_iInter` do, and it is why the
`Finite ι` form is three lines on top of the indexed one rather than a parallel development.

**SET18. Split a weighted strict-convexity proof by which half actually needs `a + b = 1`.** For
`f (a•x + b•y) < a • f x + b • f y` the two obligations behave differently: the *strict* inequality
on the open segment needs only `0 < a`, `0 < b`, while the identification of `a•x + b•y` as a point
of the segment needs `a + b = 1`. Proving them in one pass means carrying the normalisation
hypothesis through steps that do not use it, and the resulting proof will not generalise to the
`a + b ≤ 1` statements that arise from epigraph arguments. Do the positivity half first, unnormalised.

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

**PAIR10. On a self-paired space every polarity theorem hands back `B.flip`.** `polarSet_polarSet`,
the four bundled Theorem 14.1 statements, `polarCone_setOf_forall_le_zero`,
`recessionCone_eq_polarCone_polarSet`, `polarGauge_polarGauge`, `polarFn_polarFn` — all of them.
`flip_pairing` is a `simp` lemma but *not* a `rfl`, so `exact` fails where `simpa using` succeeds.
`Surface/Common/Euclidean.lean` carries six `*_flip_pairing` rewrites for the heads that occur
(`conj`, `subgradient`, `supportSet`, `supportFn`, `polarCone`, `polarSet`); `polarGauge` and
`polarFn` are not yet among them. Add the rewrite there rather than `simpa`-ing at each site.

**SET10. `Set E` under `open scoped Pointwise` is an ordered additive monoid, so the `Finset.sum`
API applies verbatim.** `∑ i ∈ s, A i ⊆ ∑ i ∈ s, B i` is `Finset.sum_le_sum h` — no set-specific
lemma and no hand induction. Note `∑ i ∈ (∅ : Finset ι), A i` is `0 = {0}`, **not** `∅`; that,
together with `∅ + {0} = ∅`, is why an `m`-ary statement about `⋃ i ∈ s` needs no `s.Nonempty`.
The way in and out of `{x ∈ A | p x}` is `Set.mem_sep_iff`, which both destructures and constructs
without tripping EL6.

---

**PAIR11. `include B in` is a symptom of a misfiled statement, not a fix for one.** PAIR4 says the
section variable is not inserted when the conclusion does not mention `B`, and that `include B in`
is how you force it. The deeper reading: a theorem whose *statement* names no pairing usually
belongs in the module where its statement's own vocabulary lives, and there it will not need a
pairing at all. `posHomogeneous_clFn` names `PosHomogeneous` and `clFn` and nothing else; moved to
the module where both are in scope it proves in **three lines** with no pairing — and shed two of
its three hypotheses on the way, since `ConvexFn g` and `∃ y, g y ≠ ⊤` existed only to feed the
pairing route. Symptom to act on: an `include B in` whose docstring has to warn callers that they
must pass `(B := B)`.

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

The same caution applies to a duplicate-*name* sweep: **count orientations, not names.** Of five
spellings of "negate a difference with a real minuend", three were the same statement and two had
folded an `add_comm` or a `neg_neg` into the *statement*. Those two cannot be removed by qualifying
the call site — the call sites depend on the orientation the statement produces — so "delete the
copies" is a promise about three of them, and the other two shrink to one-line aliases at best.

**LIB4. Symmetries: bundle the involution at the point of definition, and never let it leak into the
statements it transports.** `reflect` and `saddleSwap` are bare `def`s, so `Function.Involutive`,
`Equiv`, `AddEquiv` and `OrderIso` never apply to them — `saddleSwap_injective` is hand-proved where
`Function.LeftInverse.injective` would do, and `saddleSwap` is antitone so it wants to be an
`OrderIso _ _ᵒᵈ` and instead is nothing. Bundling after the fact means touching every use site;
bundling at definition costs one line. Both are now bundled —
`ConvexProcess.reflectAut : AddAut (ConvexProcess U X)` and
`saddleSwapOrderIso : (U × X → EReal) ≃o (X × U → EReal)ᵒᵈ` — and it cost nothing at the use sites,
because the bare `def` stays and the bundle is built *from* it. Two things to know before copying
that: **`AddAut` needs only `[Add]`**, not a group, so a mere semigroup of objects qualifies; and a
swap between two *different* products is **not** `Function.Involutive` at all — it is not an
endomorphism — so its two-sided inverse has to be recorded as an `Equiv`, which is what the
`OrderIso` does.

**A mirror that leaks is a wrong *proof*, not a wrong statement, and the fix is the other
intertwining lemma.** Eight public theorems in `Bifunction/Process.lean` carried `.reflect` in
their *hypotheses*. Pushing the value lemma `eval_reflect` through does **not** fix it: it trades
the involution for two sign flips (`A₁.eval (-u)` read at `-y`) and the caller is no better off.
The cause was that both mirrors reflected the *argument* —
`adjointProcess Bu Bx A.reflect = coadjointProcess Bu Bx A` — which forces the hypothesis to be
taken at `A.reflect`. The same dictionary carries the other orientation,
`coadjointProcess Bu Bx A = (adjointProcess Bu Bx A).reflect`, which puts the involution on the
*conclusion*, where the homomorphism laws (`reflect_add`, `reflect_comp`) cancel it; with that the
hypotheses are the originals, verbatim, and no proof grew. **Symptom**: a mirror whose hypothesis
mentions the involution and whose proof opens `rw [← intertwining_lemma …]`. Look for the entry
that rewrites the conclusion instead. A prototype confirmed the goal is reachable: transporting a
whole block through `saddleSwap` produced hypotheses **identical** to the re-proved versions. Note that the double negation of a real-valued companion is
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

**LIB10. `restrict` is ambiguous in a surface file.** `open Set` together with
`open Tdaf.ConvexAnalysis` makes `restrict s f` resolve both ways, and the failure arrives as a
*deprecation warning* (`Set.restrict` → `Set.domRestrict`) followed by
`failed to synthesize AddCommGroup ↑(closure C)`, which reads like an instance bug. Write
`Tdaf.ConvexAnalysis.restrict` in full. Backbone modules already do, which is why it does not bite
there.

**LIB11. Two `RelativeInterior.lean` names that read backwards.**
`closure_sdiff_intrinsicInterior C` is `closure C \ ri C = intrinsicFrontier ℝ C` — the opposite
direction from what the name suggests. And `intrinsicInterior_prod_eq` takes **both** sets
explicitly, so a term-mode `:= intrinsicInterior_prod_eq` fails with a metavariable-laden type
mismatch rather than "explicit argument missing".

**LIB12. EL1's list is not a blanket rule.** Dot notation *does* work on `Convex` in a surface file
(`hC.closure`) and on the surface's own `IsAffineSet` (`h.toAffineSubspace`). EL1 names the
predicates where it fails; it is not a reason to avoid dot notation everywhere.

**LIB13. `open Tdaf.ConvexAnalysis` does not open `Tdaf.EReal`.** So
`exists_coe_of_ne_bot_of_lt_top`, `coe_mul_le` and the rest of the `EReal` helpers are unreachable
by their bare names from inside `namespace Rockafellar`, and the error is the unhelpful
*"unknown identifier"* rather than an ambiguity. Qualify as `Tdaf.EReal.…`, the way the backbone
does at its own call sites, or add the `open`.

**LIB14. `recessionCone` is not monotone, and no lemma pretends it is.** `C' ⊆ C` does *not* give
`0⁺C' ⊆ 0⁺C` — that direction is Theorem 8.3 and needs `C` closed convex and `C'` non-empty.
Symptom: you reach for a `recessionCone_mono` that does not exist, then weaken the theorem. The
right move is to make `0⁺C' ⊆ 0⁺C` a *hypothesis*: the resulting statement is layer A and the closed
convex case is a one-line corollary.

**LIB15. Two names worth knowing before you write them yourself.**
`exists_linearIndepOn_id_extension` (Mathlib) extends a linearly independent subset to a maximal one
*drawn from the same ambient set* — exactly "choose additional vectors from `S′` to make a basis";
`LinearIndependent.finite_of_isNoetherian` then makes it finite (there is no `LinearIndepOn.finite`,
and dot notation on `LinearIndepOn` dies per EL1). It is `Set.ncard_coe_finset`, lowercase `f`.
There is no `Submodule.finrank_prod`: for `finrank (A ⊔ B)` with `A ⊓ B = ⊥` use
`Submodule.finrank_sup_add_finrank_inf_eq` with `finrank_bot ℝ M`.

**LIB16. LIB1's eighth and ninth instances, both found by agents who then wrote the third copy.**
`polarCone_hull` (`Duality/Polar.lean`, `@[simp]`) and `polarCone_coe_hull`
(`Recession/Conjugate.lean`) are the same statement proved twice, and each has its own callers. And
a "what is not here" note may be false rather than merely stale: `Recession/ConeHull.lean` declined
Corollary 9.8.3 because "the project has the convex hull only for a single function", while both
`convFn` and `convFn₂` had existed all along. **A note naming a reason is a claim; check it before
believing it**, and when you close a gap, fix the note that pointed away from it.

**LIB17. A remediation item that names a home is a claim too — check where the definition actually
is before planning the move.** §11.19 says `posHomGen` is defined in `Duality/Level.lean`. It is
defined in `Recession/ConeHull.lean`, and `Level.lean`'s own module docstring says so ("the
operator's basic API … is there, not here"). Following the item would have put a three-line
consequence of `le_posHomGen` one layer *above* the five lemmas its proof cites, and only the
`Recession/ConeHull.lean` home is common to both consumers. Grep for `def <name>` before believing
any "it belongs in X"; the whole cost is one second. Same family as LIB16.

**LIB18. A `Finset`-indexed exactness interface is unsatisfiable at `s = ∅`.** An `exact_le` field
demanding a splitting `y = ∑_{i ∈ s} yᵢ` for every `y` forces `F` trivial when the sum is `0`.
Symptom: the induction's base case looks free, and then the *equality* base case needs
`conj B 0 = δ(· | 0)`, which needs `SeparatingDual`. Base every `m`-ary constructor at a singleton
and carry `s.Nonempty`; the `≤` half is fine at `∅`.

**LIB19. Prefer a total choice function with junk values over `choose!` on a long set-builder.**
`choose!` over `∀ C' ∈ {long set expression}, ∃ y, …` forces the expression to be written three
times and cannot be shortened with `set`, whose fvar is opaque to `.1`. Hypothesise the
*disjunction* instead — `∀ C', ∃ y, (the good case) ∨ (the degenerate case)` — take the total
function, and discard the junk by intersecting its image with the set you actually wanted.

**LIB20. `omit` lists must be re-derived per declaration.** `PolyhedralFn.add` needs
`[FiniteDimensional ℝ E]` even though `PolyhedralFn` does not: the *definition* drops the instance by
auto-inclusion, the *lemmas about it* do not. Symptom: an `omit` copied from a neighbour produces
*"failed to synthesize"* pointing at the `exact`, not at the `omit`. Relatedly, `[Fintype ι]` trips
two different linters with two different fixes — `linter.unusedSectionVars` when the *proof* does not
use it (fix: `omit`), and `linter.unusedFintypeInType` when the *type* does not mention it although
the proof does (fix: `[Finite ι]` plus `obtain ⟨hι⟩ := nonempty_fintype ι`; `omit` is impossible).
A theorem about `ri (univ.pi C)` is the second case, because the statement's topology is `Pi.topologicalSpace`
and the proof's is the normed one.

**LIB21. Do not hand-roll `Fin.append`.** `PiLp.sumPiLpEquivProdLpPiLp` composed with
`LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv` *is* `ℝᵐ × ℝⁿ ≃ₗᵢ ℝᵐ⁺ⁿ`, and
`simp [defn, Equiv.piCongrLeft']` computes every coordinate and the inverse. But
`LinearIsometryEquiv.inner_map_map` does **not** apply to `WithLp 2 (E × F)` — the module instance
found is `WithLp.instModule` and the one demanded is `InnerProductSpace.toNormedSpace.toModule`;
derive inner-product identities from the coordinate lemmas plus `Fin.sum_univ_add` instead.

**LIB22. Check for a `to_additive`-generated name by its multiplicative source, not by grepping.**
`Set.finsetSum_mem_finsetSum` (the `m`-ary `Set.add_mem_add`) exists and a grep of Mathlib's source
for that name returns nothing — only `finsetProd_mem_finsetProd` occurs. It was written by hand in
§23 first and then found. Same family as DEP3, and the same fix: search for the multiplicative name
and let `to_additive` supply the additive one.

**LIB23. A scope deferral is a claim, and LIB17 applies to it.** `part5.md` recorded Corollary
24.2.1 as deferred by scope — "one-dimensional Lebesgue theory, not convex analysis" — while
`Subgradient/Integral.lean` proved it in full, *and that module's own docstring said the stated
reason does not apply*. An item that says why something is out of scope is asserting something about
the library; check it the same way you would check a named prerequisite.

**LIB24. A gate is not closed because the interface it asked for exists.** Remediation §4.4 asked
for an `m`-ary `IsExactSum`; the round that closed it built `IsExactFinsetSum` with both
constructors and marked the item done. `Subgradient/Calculus.lean` still had only the *binary*
consequence, which is what the section actually needed. When closing an item, name the consumer and
check that the consumer can now be written — not that the definition exists.

**LIB25. `SeparatingDual ℝ E` is automatic for any `[NormedAddCommGroup E] [NormedSpace ℝ E]`**,
so in every normed section `[IsCompatiblePairing B]` alone already gives `Function.Injective B`, via
`separatingRight_flip_of_separatingDual` (`Duality/Level.lean`). **Symptom**: you are about to add an
injectivity or separation hypothesis to a normed-space theorem, or to record a clause as needing "a
reflexive pairing". Check first — this is what made remediation §4.6 free after five rounds of being
recorded as blocked.

**LIB26. Search for the *statement*, not for the name you would have given it.**
`mem_subgradient_clFn_iff` is exactly "`∂(cl f) x = ∂f x` wherever `(cl f) x = f x`", and it is filed
in `Subgradient/Defs.lean` as Theorem 23.5 `(a) ⟺ (a**)`, with nothing in its name about closures. An
agent drafted `subgradient_clFn_eq_of_mem_relint_dom` before grepping. Grep for two of the
statement's head symbols on one line (`clFn` and `subgradient`), not for a hoped-for name.

**LIB27. A surface lemma specialised to `Rn` on *both* sides will not fit a map out of a product.**
`Rockafellar.theorem_6_6_ri` is stated for `Rn n →ₗ[ℝ] Rn m`, so the `(w, x) ↦ w - A x` that writes
`dom g - A (dom f)` as one image does not match, and `rw` reports "did not find an occurrence of
`ri (⇑?m '' ?s)`" against a goal that visibly has that shape. Use the backbone `Convex.relint_image`,
which is stated over arbitrary `E F`; likewise `intrinsicInterior_prod_eq` rather than
`Rockafellar.relint_prod`. The general rule: when a surface rewrite mysteriously fails to match, check
whether the surface statement fixed a type the goal has not.

**LIB28. Check the target module's *import closure*, not just that the prerequisite exists.**
Remediation §12.4 placed a lemma in `Polyhedral/Duality.lean` whose prerequisite lives in
`Optimization/Perturbation.lean`, a §29 module *above* it — so the item as written was unbuildable.
`grep -rn "theorem <name>"` finds the lemma and tells you nothing about whether you can cite it from
where you are going. Compute the closure (thirty lines of Python over the `import` lines) before
planning a move. **The usual answer is that the *prerequisite* is misfiled, not the new lemma.**

**LIB29. A scope deferral is a claim, and LIB17 applies to it.** `part5.md` recorded Corollary 24.2.1
as deferred by scope — "one-dimensional Lebesgue theory, not convex analysis" — while
`Subgradient/Integral.lean` proved it in full, *and that module's own docstring said the stated
reason does not apply*. An item that says why something is out of scope is asserting something about
the library.

**LIB30. A gate is not closed because the interface it asked for exists.** Remediation §4.4 asked for
an `m`-ary `IsExactSum`; the round that closed it built `IsExactFinsetSum` with both constructors and
marked the item done, while `Subgradient/Calculus.lean` still had only the *binary* consequence,
which is what the section actually needed. When closing an item, name the consumer and check that the
consumer can now be written.

---

**LIB31. Grep the *body*, not only the name — two identical public definitions in non-comparable
modules produce no error at all.** `invBifun` in `Bifunction/Algebra.lean` and `inverseBifun` in
`Saddle/Minimax.lean` were `fun x u => -(F u x)` twice, each with its own `@[simp]` apply-lemma and
its own involution lemma, and they coexisted for a full round. Lean's "already declared" error — the
mechanism that has caught LIB1 seven times — fires only when one module is in the other's import
closure *and* the names match. Neither condition held. The live hazard is not the duplication but
what it enables downstream: a third module that imports both has **both names in scope**, so a goal
can be written with one and the lemma about it stated with the other, `rfl`-equal, with nothing —
not `simp`, not the elaborator, not a name clash — to report the mismatch. Sweep by normalising
definition bodies, not by listing names.

**LIB32. A duplicate sweep must key on the signature line, not the proof text.** Three copies of
`pairing_two` were reported as identical "character for character"; only the **statements** were.
The three had three different proofs and three different docstrings, and a fourth copy in a fourth
file was missed entirely by a scan that looked for repeated proof bodies. Normalise the statement —
name, binders, conclusion — and compare that. Corollary: the count in a duplicate report is a lower
bound. Related: BLD24, the aggregator module is where a collision first appears.

**LIB33. An import-closure check has two halves, and a claim can be right about one and wrong about
the other.** "Everything its proof uses is already in the lower module's closure, and all four of
its consumers sit above" — the first half was right, the second false: one consumer of four (really
five) had the target in its closure, and two needed a **new** import. Relocations fail in both
directions, and the consumer direction is the one that turns a move into a cycle. Check *both*
before writing a relocation into a plan, and count the consumers with a grep rather than from
memory.

**LIB34. Two modules can be *incomparable* in the import DAG, and then neither can host a lemma
about both.** Every earlier bad-home diagnosis in this project was "the prerequisite is above the
target", which moving one module fixes. `Polyhedral/Defs.lean` (which defines `FinitelyGenerated`)
and `Representation.lean` (which has `finite_extremePoints_convexHullPD`) import neither each other
nor anything that would make them comparable, so a lemma mentioning both **cannot be typed in
either**. No check phrased as "is X below Y" reports this, because the answer is *neither*. The fix
is a third module that imports both — here `Polyhedral/Faces.lean` — not a move.

**LIB35. A relocation's named home can be stale because another row in the same batch moved the
landmark it points at.** Rows are written independently and applied together. "Beside
`polyhedralFn_mapLin`" was correct when written and wrong by the time it was applied, because a row
three lines away relocated `polyhedralFn_mapLin`. **Resolve a relocation's named neighbour after
applying the batch, not from the row text**, and prefer homes named by module over homes named by
neighbour. Related: LIB17.

**LIB36. An item asking for an isomorphism to transport a property is usually asking for the wrong
object.** Read the head symbols of what is actually being transported. If they are `dom`, `argmin`,
`epi`, `Set.preimage` — anything that is a preimage or a fibrewise condition — a bare **surjection**
does the whole job, and the isomorphism is decoration that costs a development. One ledger row asked
for an `ℝ^{n₁} × ⋯ × ℝ^{n_s} ≃ ℝⁿ` isometry with transport of `dom`, `argmin` and `ri`; the book
passage it cited never mentions `ri` and never uses an isometry, and what it needs is
`argmin_comp_of_surjective` plus a separable-sum dictionary on a dependent product. A related tell:
if the hypothesis is stated as a bare `≃` rather than a `≃ₗ[ℝ]`, it is carrying none of the
arithmetic the passage depends on — a bijection `∀ k, Rn (nk k) ≃ Rn n` exists for *any* `nk`.

**LIB37. Deferral notes, scope warnings and "will name-clash if added there" warnings are claims,
and they are not exempt from the grep a remediation row gets.** Three instances in one round: an
`api.md` record warned of a name clash between `convex_polarSet` and `Duality/Polar.lean`, which has
`convex_polarCone` — a different spelling, no clash, and that false warning is what kept two lemmas
misfiled for two rounds; a `## What is not here` note named `Surface/Common/Euclidean.lean` as the
home of `euclideanProdEquiv`, whose own docstring says it is backbone; and a gap note said no
polyhedral `IsExactImage` constructor existed when one had landed a full round earlier. **The
warnings in our own records decay exactly like the rows do**, and they are read as settled because
they look like documentation rather than like a task. Related: LIB16, LIB23, LIB17.

**LIB38. Check whether the blocker a note names is itself a three-line consequence of the
destination.** A note said a pairing-free proof "wants the closure of a cone is a cone, which exists
only as a surface declaration" — true, and the missing lemma was three lines from what the
destination module already had. The shape recurs: a note names a blocker to explain a deferral, and
the blocker is smaller than the deferral. Price the blocker before accepting the deferral.

**LIB39. A prerequisite can block you from inside the file you are editing, hundreds of lines below
the target section.** `convex_polarSet` was declared 650 lines below the section that needed it, in
the **same file**. No import-closure check detects this — the module is trivially in its own closure
— and a grep for the name finds it and reports success, because the grep does not know about
declaration order. The elaborator is the only thing that objects, and it objects at the point of
use. When a move into a specific section of a large file fails on "unknown identifier", check the
line number of the thing you are citing against the line number of the section, before looking at
imports at all.

**LIB40. Compute the import closure against every name the *proof* cites, not against the names the
row lists.** LIB33 says an import-closure check has two halves; this is the half that bites even
when both are done. A row named `Recession/Closedness.lean` as a home and listed two prerequisites,
both of which checked out — and the private proof's real citation was a third name the row never
mentioned, `properConvexFn_finsetSum`, which lives in a module that **imports** the proposed home.
Symptom: you verify everything the row names, then the first `exact` reports an unknown identifier
for something you never looked at. The follow-up question is the useful one: **what was the
unreachable citation doing?** Here it placed one point in `dom (∑ …)`, and strengthening the
induction to carry that point in its own conclusion removed the dependency entirely, which is why
the row's home turned out to be right after all.

**LIB41. A call-site count is irrelevant when the move goes *down* the DAG — check the direction
before counting.** A relocation note said "three call sites"; there were **24, in 9 modules**, and
not one needed touching, because every caller already imported the destination. The count only
matters for a sideways or upward move, where each site must be re-checked for import reach. A
relocation note that leads with a call-site count is usually describing an upward move, or has not
worked out which kind it is.

**LIB42. When amending a record, check that the anchor you matched belongs to the record you meant.**
An `api.md`-style file is a long list of `### <module>` sections with similar prose in each, so a
distinctive-looking phrase is not evidence of which section you are in: a paragraph about faces
intended for `Representation.lean` will happily anchor in `Face.lean`, and both files legitimately
discuss faces. Locate the section header first and assert the insertion offset is after it, or
match on a phrase that names the module. The same care the code side takes over declaration
*homes* is owed to record homes, and nothing rebuilds to catch a mistake.

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

**BLD7. The 100-character bar is not enforced by anything, and both obvious ways of checking it are
wrong.** `awk 'length > 100'` counts UTF-8 *bytes*, so every line containing `ℝ`, `≤`, `∈`, `•` or
`₂` looks three to fifteen characters over and a clean file appears to have dozens of violations.
**Corrected.** This entry used to say `linter.style.longLine` never fires here. It does — a full
`lake build` reports `This line exceeds the 100 character limit`, twice in the round that found
this. What is true is narrower, and is already **BLD20**: `lake env lean` does not run the style
linters, and the "verified empirically" experiment behind the old claim was run with `lake env
lean`. So the symptom is real but the cause is not the linter set: **a file can be silent through
every iteration and warn only on the final full build.**

Practical consequence: `lake build` is a real check, but it is the *slowest* one and it arrives
last. **Count codepoints** (`len(line.rstrip('\n')) > 100` in Python) before every commit anyway —
it is instant, it covers files the build would not rebuild, and it catches the cascade where
rewrapping one long line pushes the overflow onto the next (three iterations in one paragraph, this
round). An earlier version of this entry said to build and trust the linter, and that advice let two
over-long lines through in one round.

**Confirmed twice more since**, independently: an agent hit the same cascade in its own fence, and a
central four-character rename (`invBifun` → `inverseBifun`) pushed seven lines over, then pushed an
eighth over while rewrapping the seventh. Reflow the whole paragraph, not the offending line — a
per-line fix guarantees a second round.

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

**BLD11. Do not edit anything while a `lake build` is in flight.** The build completes, reports
success, and the artifact was produced from the *pre-edit* source — indistinguishable from BLD2
staleness afterwards. Adding an import to `Tdaf.lean` mid-build is worse: it fails with
`object file '….olean' of module … does not exist`, naming a module that was never scheduled. A
one-word docstring fix costs a full rebuild of that module's dependent tree, which for
`Duality/Polar.lean` is 100 modules and twelve minutes. **Make every edit before starting the
build.** After a terminal crash, an orphaned build may still be writing to the worktree's
`.lake/build`: wait until `find .lake/build -newermt '-70 seconds' -type f` comes back empty rather
than looking for `lean.exe` in `ps -W`, which shows every worktree's processes.

**BLD12. `grep -c "theorem <name>\b"` under-counts any name ending in a subscript.** `\b` after
`₂` — a non-ASCII, non-word character — does not match, so the LIB1 duplicate-name check reports
zero for `epi_convFn₂` even though it is right there. Use a trailing space:
`grep -rn "theorem [A-Za-z._]*<name> "`.

**BLD13. Two more contention symptoms that are not signals about your proof.** `Lean exited with
code 3221226505` (Windows `STATUS_STACK_BUFFER_OVERRUN`) on a module that built fine minutes
earlier, and `failed to read file '….olean'` naming a file that is present and unchanged. Both went
away on a bare re-run; each happened about once in five full builds. **Re-run before
investigating** — this is BLD2's second paragraph, now with two more faces.

**BLD14. Piping a patch script to `python -` through a bash heredoc decodes stdin with the Windows
locale, not UTF-8.** A script whose match strings contain `⋯`, `—` or subscripts then fails its own
`assert count == 1` on a substring you can read verbatim in the file. Escape every non-ASCII
character as `\uXXXX`, or write the script to the scratchpad with the `Write` tool and run it by
path. Same family as BLD5's surrogate-pair bullet.

**BLD15. `lake env lean <a project module>` typechecks that module against the oleans already on
disk, and that is how to verify an edit without waiting for the tree to rebuild.** After changing
`Tdaf/Order/EReal.lean` — which everything imports — `lake build Tdaf.Order.EReal` takes ten
seconds, and `lake env lean Tdaf/Analysis/Convex/Bifunction/Algebra.lean` then checks that file in
about a minute *even though every olean between the two is now stale*: **adding** declarations to a
dependency does not invalidate a dependent's olean for this purpose. Linters run, so the
zero-warning bar is checked too, and a clean run prints nothing at all. It is not a substitute for
the final `lake build`: a declaration you **removed** or whose statement you **changed** is exactly
what a stale olean will hide (BLD2), so the real rebuild still has to happen before the commit is
believed. The complement of BLD3's `LEAN_PATH` trick, and it needs no sibling checkout.

**BLD16. `lake env lean FILE | head -N` reports `head`'s exit code, and empty output is not proof of
a clean file.** One §26 run gave zero output through the pipe; the identical lemma failed with a hard
`unknown constant` on the next, unpiped run. Echo a marker after the pipeline and check that the
marker printed — BLD15's "a clean run prints nothing at all" is only safe when nothing can swallow
the output.

**BLD17. `grep -rn "theorem <name> "` before every new declaration, and mean it.** §26 wrote a
`private` copy of `Tdaf.EReal.coe_mul_ne_bot`, which already existed in a *weaker* form (`0 ≤ a`).
The build accepted both, because one was `private`; only the pre-commit grep caught it. LIB1's
duplicate-name sweep catches public collisions after the fact — this is the check that stops a
`private` shadow being written in the first place.

**BLD18. `autoImplicit` was on in this repository, and turning it off found exactly one thing.**
`lakefile.toml` used to set `relaxedAutoImplicit = false` and never `autoImplicit = false`, where
Mathlib sets both, so a single-letter identifier in a theorem statement was silently auto-bound as
an implicit with its type inferred from the surrounding applications, and **the file built with zero
warnings**. The symptom was the absence of one. **Now fixed** — the flag is set and the tree builds
clean (remediation §12.19) — but two lessons from the flip are worth keeping.

*A spot-check under-predicts a defect whose symptom is nothing.* Six modules built with
`-DautoImplicit=false` came back clean, and that was read as evidence the flip was free. The full
flip found an instance in a module none of the six was. A probe tells you about the modules you
probed; for this failure mode the only honest test is the whole tree.

*The shape to look for is a section boundary, not a typo.* In `RelativeInterior.lean`,
`end Functions` closed the section declaring `variable {f : E → EReal}` four lines **before** two
theorems that went on using `f`. Both statements were correct — `ConvexFn f` pins the type, so the
auto-bound `f` and the section's `f` elaborate identically — which is precisely why nothing
complained for as long as the file existed; turning the flag off produced fifteen
`Unknown identifier f` errors at once. When an `end` sits above declarations that read as though
they belong to the section, that is the tell. One instance in 164 modules: a small exposure, but not
zero, and no amount of building would have surfaced it.

**BLD19. Never trust an exit code through a pipe.** `lake build | tail -30` reports `tail`'s status,
so a failed build exits 0 — and `tail` is worse than `head` here, because the failure line
*is* in the tail and reads like ordinary output. `lake env lean FILE | head -N` has the same problem
in the other direction: empty output is not proof of a clean file. **Grep the output for
`Build completed successfully`**, and echo a marker after any pipeline whose silence you intend to
trust.

**BLD20. `lake env lean` does not run the style linters that `lake build` runs.** A 1087-line file
was silent under `lake env lean` and then produced `unclosed sections or namespaces; expected: 'end
Rockafellar'` on the first real build. `linter.style.missingEnd` and its neighbours fire only on the
`lake build` path. BLD15's fast-iteration advice is for *errors* only; the last check before a commit
is always a full `lake build`.

**BLD21. `lake env lean <dependent>` reads the dependency's olean, not its source.** A declaration
you have just added to a dependency is reported as `Unknown identifier`, followed by a cascade of
unsolved goals. BLD15's "adding declarations does not invalidate a dependent's olean" cuts both ways:
it also does not put the new declaration *into* the dependency's olean. `lake build <the dependency
module>` first — seconds, not a full rebuild.

**BLD22. Two traps in the `#print axioms` sweep, both of which silently under-count.** A declaration
name ending in `'` truncates under the obvious `'([^']+)'` pattern, so a 83-declaration probe reported
80 records and the three missing were exactly the primed names; match
`'(\S+?)' depends on axioms: \[(.*?)\]` instead. And a name-extraction regex anchored at
`^(theorem|def|…)` misses `@[simp] theorem foo`, because the line starts with the attribute — use
`^(?:@\[[^\]]*\]\s*)?((?:private\s+|protected\s+|noncomputable\s+)*)(theorem|lemma|def|abbrev|instance)\s+(\S+)`.
Always cross-check the record count against the number of names fed in; BLD8's whitespace collapse
alone is not enough. The same anchoring trap applies to BLD17's duplicate-name grep, and to any sweep
that scans a module docstring — fenced ```lean blocks and prose beginning with the word *lemma*
produce phantom names that only surface when the generated file is run.

**BLD23. Contention across many worktrees fails a *different* random handful of modules each run.**
With eight worktrees building against one junctioned Mathlib tree, a full `lake build` failed six
modules on one run, seven different ones on the next, and was clean on the third — always at an
`import` line, with `failed to read file '….olean'`, `'….olean.private'`, or
`Lean exited with code 3221226505`. None was ever a real diagnostic. `'….olean.private'` in this
shape is **not** BLD2's scratch-file case; it happens for ordinary project modules, and for toolchain
files too. Re-run before investigating.

**BLD24. A Part's aggregator module is the first place a name collision can appear.** Section
modules of one Part do not import each other unless they need to, so two agents writing two sections
in parallel can define the same name and *both files compile clean*. The clash surfaces only when
`PartN.lean` imports both:
`environment already contains 'X' from Tdaf.Surface.Rockafellar.Part6.Section29`.

Not hypothetical: §29 and §30 both defined `linearIndicatorBifun`, because Rockafellar presents the
same example twice (11639 and 12313) and neither agent could see the other's file. The resolution is
the general one — keep the definition in the *earlier* section, have the later one import it — and
cross-section imports are already the surface's convention.

Scan for duplicate declaration names across a parallel round's files *before* building the
aggregator. Note that `private` copies do **not** collide, being name-mangled: a scan that skips
`private` misses real duplication (three `pairing_two` copies, remediation §12.32), and one that
includes it reports non-blockers. Both are worth seeing; only the public ones stop the build.

**BLD25. Removing a public declaration needs the module you deleted it *from* rebuilt, and the
symptom is a name collision in an unrelated third file.** Deleting a duplicate and rebuilding only
the survivor's module leaves the deleted declaration live in the stale `.olean` of the module you
edited. The next module that imports both then fails with "environment already contains `foo`" —
pointing at a **third** file that you did not touch and that contains only one declaration of `foo`.
The instinct is to look for a second declaration in the file named in the error; there is none.
Rebuild the module you deleted from (or delete its `.olean`), then the importer. This is BLD2 and
BLD21 in the *removal* direction, which is the direction that reads as a mystery.

**BLD26. A full `lake build` outruns the 10-minute tool timeout, and the kill is indistinguishable
from a hang.** 2994 jobs takes well past 600 s on this tree, `lake` buffers its output so a live
build can show **zero bytes** for twenty minutes, and a timed-out call looks exactly like a wedged
one. Run it with `run_in_background` from the start. To tell a live build from a dead one without
waiting, check for `lean` worker processes burning CPU (`Get-Process lean | Select Name,Id,CPU`) —
several with rising CPU means it is working; the absence of workers while `lake` is alive is the
real hang.

**BLD27. Printing matched Lean text from Python dies on the Windows console encoding, and the scan
aborts *mid-file*.** `UnicodeEncodeError: 'gbk' codec can't encode character` fires the moment a
scan prints a line containing `ℝ`, `∈`, `⨅` — i.e. on the first interesting hit. The damage is not
the traceback but what it hides: the script dies partway through the tree, having printed real
findings for the files it reached, so the output **looks like a completed scan that found three
things**. Always run these with `PYTHONIOENCODING=utf-8`, and prefer writing results to a UTF-8 file
over printing them.

**BLD28. Three separate ways a `bash` heredoc corrupts a Python payload.** (a) **Size**: over
roughly 8 KB the heredoc truncates, and the failure surfaces as a `bash` syntax error —
"unexpected EOF while looking for matching quote" — naming a line number inside your script, which
reads as a quoting bug in the text rather than as truncation. Hit three times in one session; the
fix is to write the file with the file-writing tool and run it by path. (b) **Backslashes**: a
literal `\\` in the payload arrives as `\`, so `.replace('\\', '/')` becomes an unterminated
string and `os.sep` is the right thing to use anyway. (c) **`$TMPDIR` is unset** in Git Bash here,
so `> "$TMPDIR/x.py"` writes to `/x.py` and fails with permission denied — and `/tmp` redirection is
invisible to the Windows `python` on `PATH`, which resolves the path differently from the shell that
created it. Use the absolute scratchpad path.

**BLD29. Build staleness reaches a `#print axioms` probe, and there the symptom is `Unknown
constant`.** A batch of `#print axioms` lines appended to a downstream module reported records for
seven declarations and *unknown constant* for the eighth — the one added to a dependency that had
not been rebuilt — which reads as a typo in a fully-qualified name. `lake build <the dependency>`
first. The record-count cross-check (BLD22) is what catches it: a probe that returns fewer records
than declarations probed has not proved anything about the missing one. This is BLD21 in the
`#print axioms` direction.

**BLD30. Do not patch a patch script in place with an offset-based splice.** Rewriting a generated
script by `s.index(...)` on a marker that also occurs earlier in the file silently duplicates the
whole body, and the duplicate then re-runs every substitution against already-substituted text and
fails with an assertion that looks like a bad anchor. Rewrite the script whole. The one saving
grace in the incident that produced this entry is worth designing for on purpose: **the script did
all its `assert`-guarded substitutions in memory and wrote the file once at the end**, so the failed
second pass left the target untouched. Write batch editors that way — read, substitute with
assertions, write last — and a mid-script failure costs nothing.

**BLD31. A module missing from `Tdaf.lean` builds green forever, because some other module imports
it.** `Tdaf/Analysis/Convex/Line.lean` sat unregistered for many rounds: `Saddle/Differential.lean`
imports it directly, so it was always compiled, always up to date, and the aggregator — which
BLD24 makes the reliable detector of *name collisions* — has nothing to say about a module it never
hears of. This is the one project invariant with no mechanical check behind it, and no amount of
building will produce one. Difference the two lists instead, next to the line-length check and just
as cheap:

```python
reg = {l.split()[1] for l in open('Tdaf.lean') if l.startswith('import ')}
mods = {os.path.join(r, f)[:-5].replace(os.sep, '.')
        for r, _, fs in os.walk('Tdaf') for f in fs if f.endswith('.lean')}
assert mods == reg, sorted(mods ^ reg)
```

The same run should assert the import list is sorted, which is the other half of the convention and
equally invisible to the build.

