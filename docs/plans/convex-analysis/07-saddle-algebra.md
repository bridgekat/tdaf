# Sub-plan 7 — Saddle-functions, minimax, and the algebra of bifunctions

Covers Rockafellar §33–§39 (Parts VII and VIII).

These are the most original and least formalised parts of the book, and the ones where
[D8](00-overview.md#d8) — everything is partial conjugation — does the most work. Rockafellar
develops the saddle-function closure calculus by hand over §33–§34; the backbone should get it from
a single `partialConj` / `partialClosure` API applied twice, once in each variable.

---

## 7.1 The one abstraction

**Status: `partialConj₂`, `partialCl₁`, `partialCl₂` and the concave closure they need are done**
(`Saddle/Defs.lean`, and `clConcave` in `Duality/ConcaveConj.lean`).

```lean
/-- Conjugate in the second variable only. -/
noncomputable def partialConj₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : U × X → EReal) : U × Y → EReal :=
  fun p => conj Bx (fun x => f (p.1, x)) p.2

/-- Close in the second variable only, convexly (Rockafellar's `cl₂`). -/
noncomputable def partialCl₂ [TopologicalSpace X] (K : U × X → EReal) : U × X → EReal :=
  fun p => clFn (fun x => K (p.1, x)) p.2

/-- Close in the first variable only, **concavely** (Rockafellar's `cl₁`). -/
noncomputable def partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : U × X → EReal :=
  fun p => clConcave (fun u => K (u, p.2)) p.1
```

Facts to prove once:

- `partialConj₂` preserves convexity in the second variable and *reverses* it in the first
  (Theorem 33.1: `⟨Fu, x*⟩` is concave-convex) — **done** (`convexFn_bracket`, `concaveFn_bracket`);
- `partialConj₂ ∘ partialConj₂` (with the flipped pairing) is `partialCl₂` — **done**
  (`bracket_bifunOfSaddle`);
- `partialCl₁` and `partialCl₂` commute up to equivalence (this is the substance of §34) —
  **done** (`upperClosedFn_upperCl`, `lowerClosedFn_lowerCl`, and Theorem 34.2's constancy of both
  closures on an interval).

Rockafellar's bracket `⟨Fu, x*⟩ = (Fu)*(x*)` is `partialConj₂ (graphFn F)` (`bracket`, with
`partialConj₂_graphFn` recording that they agree), and the Lagrangian of
[sub-plan 6](06-optimization.md#63-optimizationlagrangianlean--2829-via-partial-conjugation) is
the *concave conjugate* in the first variable. Naming these once collapses §33, §34, §36 and §37
substantially.

### What actually happened

**The composition law in the plan had the wrong sign, and the right one goes through the concave
conjugate.** `conj (prodPairing Bu Bx)` is a supremum over `U × X`, whereas
`partialConj₁ ∘ partialConj₂` is a sup-of-inf: the two are not equal, and no amount of `negFst`
bookkeeping makes them so. What *is* true, and is what §30 and §33 both use, is

```lean
adjointBifun Bu Bx F y v = concaveConj Bu (fun u => bracket Bx F u y) v
```

(`adjointBifun_eq_concaveConj_bracket`): the adjoint is the partial conjugate in `x`, taken
convexly, followed by the partial conjugate in `u`, taken **concavely**. That is D8's real content.
The proof is `iInf_prod` plus `Tdaf.EReal.iInf_add_coe`, the same real-constant-through-an-infimum
lemma §29 and §30 needed. With it in hand Theorem 33.2's first equation
`⟨u, F* y⟩ = cl₁ ⟨Fu, y⟩` is one rewrite followed by concave Fenchel–Moreau
(`concaveConj_adjointBifun_eq_partialCl₁`), which is the payoff the design predicted.

**`cl₁` is not `cl₂` conjugated by `Prod.swap`.** `cl₂` closes convexly, `cl₁` closes concavely, so
`partialCl₁` needs the concave closure. `Duality/ConcaveConj.lean` had recorded that
`clConcave = -(cl (-g))` "should arrive with §34"; it arrives now, and lives there rather than in
`Saddle/Defs.lean`, because `Duality/ConcaveConj.lean` is the first file with both `ConcaveFn` and
`clFn` in scope. `biconcaveConj_eq_clConcave` restates concave Fenchel–Moreau against it, as that
file's design note asked.

## 7.2 `Saddle/Defs.lean` — §33 (and `Saddle/{Closure,Correspondence,Equiv}.lean` — §33–§34)

**Status: all of §33 and all of §34 are done.**
Theorems 33.1, 33.2, 33.3, 34.1, 34.2 with Corollaries 33.1.1 and 33.3.1 are in
`Saddle/{Defs,Closure,Correspondence,Equiv}.lean`; Theorem 34.2's `ri` and `dom` clauses,
Corollaries 34.2.1–34.2.4, and Theorems 34.3–34.5 with Corollary 34.5.1 are in
`Saddle/Kernel.lean` — see §7.2b.

```lean
structure ConcaveConvexFn (K : U × X → EReal) : Prop where
  concave_fst : ∀ x, ConcaveFn fun u => K (u, x)
  convex_snd  : ∀ u, ConvexFn fun x => K (u, x)

def SaddleFn (K : U × X → EReal) : Prop := ConcaveConvexFn K ∨ ConvexConcaveFn K

/-- The effective domains of a saddle-function (Rockafellar §34): **intersections**, not unions. -/
def dom₁ (K : U × X → EReal) : Set U := {u | ∀ x, ⊥ < K (u, x)}
def dom₂ (K : U × X → EReal) : Set X := {x | ∀ u, K (u, x) < ⊤}

/-- Rockafellar's `⟨Fu, y⟩`. -/
noncomputable def bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U → Y → EReal :=
  fun u y => conj Bx (F u) y

/-- The bifunction attached to a saddle-function, `F u = K(u, ·)*`. -/
noncomputable def bifunOfSaddle (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) : Bifun U X :=
  fun u x => conj Bx.flip (fun y => K (u, y)) x
```

| Lean name | book | status |
|---|---|---|
| `convexFn_bracket`, `closedFn_bracket`, `concaveFn_bracket`, `concaveConvexFn_bracket` | **Thm 33.1**, first half | done |
| `clFn_eq_conj_bracket` | **Thm 33.1**, the inversion formula `cl (Fu) = ⟨Fu, ·⟩*` | done |
| `convexBifun_bifunOfSaddle`, `bracket_bifunOfSaddle` | **Thm 33.1**, converse half | done |
| `convexFn_partialCl₂`, `convexClosedFn_partialCl₂`, `concaveFn_partialCl₁`, `concaveClosedFn_partialCl₁` | **Cor 33.1.1**, the pointwise clauses | done |
| `concaveConvexFn_partialCl₂`, `concaveConvexFn_partialCl₁` | **Cor 33.1.1**, the clauses that need the correspondence | done |
| `ConcaveConvexFn.convex_dom₁`, `.convex_dom₂` | **§34**, convexity of the effective domains | done |
| `adjointBifun_eq_concaveConj_bracket` | the §30 ↔ §33 bridge | done |
| `concaveConj_adjointBifun_eq_partialCl₁`, `concaveBracket_adjointBifun_eq_partialCl₁` | **Thm 33.2**, first equation `⟨u, F*y⟩ = cl₁ ⟨Fu, y⟩` | done |
| `concaveBracket`, `convexFn_concaveBracket`, `concaveAdjointBifun_eq_conj_concaveBracket` | the concave bracket `⟨u, G y⟩` and its **Thm 33.1** clauses | done |
| `saddleOfBifun`, `saddleOfBifun_bifunOfSaddle`, `bifunOfSaddle_saddleOfBifun`, `bifunSaddleEquiv` | **Cor 33.1.2** as an `Equiv` | done (`Saddle/Correspondence.lean`) |
| `polyhedralFn_bracket`, `polyhedralFn_neg_bracket`, `polyhedralFn_concaveBracket`, `imageClosedBifun_of_polyhedralBifun`, `eq_conj_bracket_of_polyhedralBifun`, `eq_iSup_sub_bracket_of_polyhedralBifun` | **Cor 33.1.3** (polyhedral) | done (`Saddle/Correspondence.lean`). Clause 1 is Thm 19.2, clause 2 is Cor 19.3.1, clause 3 is Thm 33.1 once the bifunction is image-closed. Clause 1 needs finite dimension only on `X` |
| `domConcave_bracket`, `bracket_eq_concaveBracket_adjointBifun_of_mem_relint` | **Cor 33.2.1** | done (`Saddle/Kernel.lean`) |
| `bracket_eq_concaveBracket_adjointBifun_of_mem_domBifun`, `bracket_eq_concaveBracket_adjointBifun_of_mem_domConcaveBifun`, `bracket_eq_concaveBracket_adjointBifun_of_polyhedral`, `bracket_eq_bot_and_concaveBracket_eq_top`, `closedBifun_of_polyhedralBifun`, `polyhedralFn_neg_graphFn_adjointBifun` | **Cor 33.2.2** (polyhedral) | done (`Saddle/Kernel.lean`, with the polyhedral support in `Correspondence.lean`). The `u`-side half needs no properness at all; the `y`-side half needs `V` and `Y` finite-dimensional as well as `U` and `X`, since the concave bracket is a partial minimisation over `V`. The exceptional pair is always the same way round — `⟨Fu, y⟩ = -∞` and `⟨u, F*y⟩ = +∞` — and that needs neither polyhedrality nor properness |
| `bracket_concaveAdjointBifun_eq_partialCl₂`, `partialCl₂_concaveBracket_adjointBifun` | **Thm 33.2**, second equation `cl₂ ⟨u, F*x*⟩ = ⟨(cl F)u, x*⟩` | done |
| `lowerCl`, `upperCl`, `LowerClosedFn`, `UpperClosedFn`, `FullyClosedFn`, `fullyClosedFn_iff` | **§33–§34**, the closedness notions | done (`Saddle/Closure.lean`) |
| `upperClosedFn_upperCl`, `lowerClosedFn_lowerCl` | **Thm 34.1** | done (`Saddle/Closure.lean`) |
| `ImageClosedBifun`, `eq_of_bracket_eq` | the uniqueness half of the correspondence | done (`Optimization/Adjoint.lean`, `Saddle/Correspondence.lean`) |
| `partialCl₁_bracket`, `partialCl₂_concaveBracket_adjoint`, `lowerClosedFn_bracket`, `exists_unique_convexBifun_bracket_eq` | **Thm 33.3** | done (`Saddle/Correspondence.lean`) |
| `le_of_partialCl₂_eq`, `exists_unique_bifun_of_closure_pair` | **Cor 33.3.1** | done (`Saddle/Correspondence.lean`) |
| `upperClosedFn_partialCl₁`, `lowerClosedFn_partialCl₂`, `lowerUpperClosedEquiv` | **Cor 33.3.2** | done (`Saddle/Correspondence.lean`) |
| `lowerClosedFn_lowerSimpleExt`, `upperClosedFn_upperSimpleExt`, `exists_unique_bifun_of_simpleExt` | **Cor 33.3.3** | done (`Saddle/Kernel.lean`) |

**Corollary 33.2.2's second half is asserted in the book, not proved.** Rockafellar's proof covers
only the `u`-side — "the proof of Corollary 33.2.1 may be sharpened accordingly" — but the
statement's "except when **both**" needs the dual-side sharpening as well, i.e. that the adjoint
of a polyhedral convex bifunction is polyhedral concave. The book never states that;
`polyhedralFn_neg_graphFn_adjointBifun` is it, and it is the only genuinely new mathematics in the
two corollaries. Two smaller slips in the same proof: "the function `u ↦ ⟨Fu, x*⟩` is polyhedral
by **Theorem 33.1**" should cite **Corollary 33.1.3** (Theorem 33.1 gives concavity, not
polyhedrality), and "since `F` is polyhedral, `cl F = F`" is false without properness — an
improper polyhedral convex function has `cl f ≡ -∞`. The corollary does assume properness, so it
is the sentence that is loose, and `closedBifun_of_polyhedralBifun` carries both hypotheses.

**No `PolyhedralConcaveBifun` was introduced.** Both corollaries are stated in the book "for a
convex *or concave*" bifunction, and Cor 33.2.2's second half genuinely needs "`F*` is polyhedral
concave". That is written out as `PolyhedralFn fun q => -(graphFn G q)`, the definition unwound; a
named predicate would buy one line and cost a duplicated API, since D2's negation transfers are
hand-written. If §38–§39 ever needs concave polyhedral bifunctions in bulk, that is when to add
it.
| `SaddleEquiv`, `ClosedSaddleFn`, `saddleClass`, `partialCl₂_eq_of_mem_saddleClass`, `partialCl₁_eq_of_mem_saddleClass`, `saddleEquiv_of_mem_saddleClass`, `closedSaddleFn_of_mem_saddleClass`, `exists_unique_bifun_of_closedSaddleFn` | **Thm 34.2** | done (`Saddle/Equiv.lean`) |
| — | **Thm 34.2**'s `dom K = dom F × dom F*` and `ri` clauses, Cors 34.2.1–4 | not done — need `ri` |
| `closedSaddleFn_iff_saddleStructure` | **Thm 34.3** | done (`Saddle/Kernel.lean`) |
| `saddleEquiv_iff_kernel_eq` | **Thm 34.4** | done (`Saddle/Kernel.lean`) |
| `exists_unique_saddleEquiv_class_of_kernel`, `exists_unique_saddleEquiv_class_of_finite` | **Thm 34.5**, Cor 34.5.1 | done (`Saddle/Kernel.lean`) |

Theorem 33.3 is the "bilinear functions ↔ linear transformations" analogy made precise, and it is
the theorem the whole of Part VII is built on. With §7.1 in place it is Fenchel–Moreau in the second
variable, uniformly in the first — which is exactly what `bracket_bifunOfSaddle` delivers
pointwise; the packaging into a bijection is `exists_unique_convexBifun_bracket_eq`, and
Theorem 34.2 upgrades it from lower closed representatives to whole equivalence classes.

The §34 apparatus still to be written:

```lean
/-- The kernel is the **restriction of `K`** to `ri (dom₁ K) × ri (dom₂ K)` (book, line 14887) —
a *function*, not its domain. Defining it as the domain would make Theorem 34.4 refutable, since
`K` and `K + 1` would share a kernel without being equivalent.

As formalized it is a **total** function rather than a `Set.restrict`: equalities of
subtype-restrictions are ill-typed unless the two rectangles are already known equal, which would
split Theorem 34.4 into a rectangle equality plus a transport. `⊤` off the rectangle is faithful,
because a proper concave-convex `K` is finite on `ri (dom K)`, and `kernel_eq_iff` recovers exactly
the book's pair "same rectangle ∧ `Set.EqOn` there". -/
def kernelSet (K : U × X → EReal) : Set (U × X) := ri (dom₁ K) ×ˢ ri (dom₂ K)

noncomputable def kernel (K : U × X → EReal) : U × X → EReal :=
  fun p => if p ∈ kernelSet K then K p else ⊤
```

### What actually happened

**The correspondence is about slices, and needed a predicate weaker than `ClosedBifun`.** The
bracket `⟨Fu, y⟩` is `conj Bx (F u)`, so it depends on `F` only through the *slice-wise* closures
`cl (F u)`; two convex bifunctions with the same bracket agree as soon as each slice is closed
(`eq_of_bracket_eq`, via Theorem 33.1's inversion formula `F u = ⟨Fu, ·⟩*`). `ImageClosedBifun`
is that predicate; `ClosedBifun.imageClosedBifun` is the one implication, and there is no converse.
Uniqueness in Theorem 33.3 then follows from existence: the candidate is `bifunOfSaddle Bx K`, and
its closedness comes from Theorem 33.2 rather than being assumed.

**Theorem 34.2 is an order argument on top of Theorem 33.2, with no new duality.** Read the two
equations of Theorem 33.2 as saying that the brackets `K̲ = ⟨Fu, y⟩` and `K̄ = ⟨u, F*y⟩` of a
closed convex bifunction form a *closure pair* — `cl₁ K̲ = K̄` and `cl₂ K̄ = K̲`. Then for any `K`
with `K̲ ≤ K ≤ K̄`, monotonicity of `cl₂` gives `K̲ = cl₂ K̲ ≤ cl₂ K ≤ cl₂ K̄ = K̲`, so `cl₂ K = K̲`
identically, and symmetrically `cl₁ K = K̄`. Constancy of the two closures on the interval *is*
Theorem 34.2: it gives at once that the interval lies in a single equivalence class, that every
member is closed, and that the two ends are the unique lower and upper closed representatives.
Only `partialCl₁_mono` and `partialCl₂_mono` had to be added (and `clConcave_mono` under them).

**`ClosedSaddleFn` is weaker than `LowerClosedFn` and `UpperClosedFn`.** Rockafellar's closedness
asks that `cl₁ K` and `cl₂ K` be *equivalent* to `K`, not equal — which is what lets a whole
interval be closed while only its two ends are lower and upper closed. Stating it as the two
equations `cl₁ cl₂ K = cl₁ K` and `cl₂ cl₁ K = cl₂ K` makes `exists_unique_bifun_of_closedSaddleFn`
a direct call to Corollary 33.3.1 with `K̲ := cl₂ K` and `K̄ := cl₁ K`.

**Corollary 33.1.1 was half-finished and the missing half needed the correspondence.** That `cl₂ K`
is convex in the second variable is pointwise (`convexFn_partialCl₂`); that it is *concave in the
first* is not — it is Theorem 33.1 applied to `bifunOfSaddle`, since `cl₂ K` is a bracket. The
mirror clause for `cl₁` comes from `saddleSwap`, the same involution §34 uses.

**The plan's `dom₁`/`dom₂` were existentials; the book's are universals.** Rockafellar (§34) defines
`dom₁ K = {u | K(u, v) > -∞ for all v}` and remarks that it is *the intersection* of the effective
domains of the concave functions `K(·, v)`. The plan had written `{u | ∃ x, K (u, x) ≠ ⊥}`, under
which `dom₁ K` need not be convex at all — the convexity claim in the plan's own next sentence would
have been false. With the universal reading, `ConcaveConvexFn.convex_dom₁` is `convex_iInter` over
`ConcaveFn.convex_domConcave`, three lines.

**Theorem 33.1's easy direction is genuinely free.** `bracket Bx F u = conj Bx (F u)`, so convexity
and closedness in `y` are `convexFn_conj` and `closedFn_conj` with *no* hypothesis on `F` — not
convexity, not properness. Only concavity in `u` uses `ConvexBifun F`, and it is Theorem 5.7 at the
projection `(u, x) ↦ u` once `-⨆ = ⨅ -` has been applied: `-⟨Fu, y⟩ = ⨅ x (f(u, x) - ⟨x, y⟩)`.

**Two small lemmas carried most of the weight and had to be written.**
`ConvexBifun.convexFn_apply` — each slice `F u` of a convex bifunction is convex — is not a
`compLin` instance, because `x ↦ (u, x)` is affine rather than linear; it is `epi_combo` applied by
hand, using `a • u + b • u = u`. And `convexFn_add_coe` — a convex function plus a real-valued
"affine coordinate" is convex — is the workhorse of both halves of Theorem 33.1; it is stated
against the combination law `l (a • x + b • y) = a * l x + b * l y` rather than linearity, so that
one lemma covers a pairing coordinate and a product projection alike.

**Beware higher-order unification against `iSup` and `clFn`.** `convexFn_iSup` states its
conclusion as `ConvexFn fun x => ⨆ i, f i x`; leaving `f` to be inferred makes Lean guess
`ι := ↑(Set.range …)` and fail. Worse, `closedFn_clFn _` against a goal mentioning
`partialCl₂` sends `isDefEq` into `clFn`'s `if ∃ x, lscHull f x = ⊥` and times out at 200 000
heartbeats. Both are fixed by supplying the function explicitly; the file adds `partialCl₂_slice`
and `partialCl₁_slice` (`rfl` lemmas) so that `rw` can do the reduction instead of unification.

## 7.2a Why the equivalence classes are unavoidable

A finite concave-convex `K` on `C × D` has *two* natural extensions to `U × X` (the lower and upper
simple extensions, §33), and they differ exactly off `C × D`. Rockafellar's resolution — work with
the equivalence class, which has a least and a greatest member — is the right one and should be
formalised as stated, not worked around. Corollary 34.2.2 (each class has a unique lower closed and
a unique upper closed member) makes the class computationally usable: pick a canonical
representative when needed.

**This is exactly how `saddleClass` came out.** The class is an order interval, its ends are the
two brackets of the corresponding closed convex bifunction, and `partialCl₂_eq_of_mem_saddleClass`
and `partialCl₁_eq_of_mem_saddleClass` say the canonical representatives are computed by a single
partial closure from *any* member. Corollary 34.2.2 is therefore already available in the form that
matters; the `dom`/`ri` description of the class and the kernel characterisation are §7.2b.

## 7.2b `Saddle/Kernel.lean` — §34, the finite-dimensional half

**Status: done.** Theorem 34.2's `ri` and `dom` clauses, Corollaries 34.2.1–34.2.4, Theorems
34.3–34.5 and Corollary 34.5.1.

| Lean name | book | status |
|---|---|---|
| `domSaddle`, `ProperSaddleFn`, `relint_domSaddle`, `ClosedSaddleFn.dom₂_partialCl₂`, `.dom₁_partialCl₁`, `.eq_partialCl₂_of_mem_relint_dom₁` | **Thm 34.2**, the `ri` and `dom` clauses | done |
| `SaddleEquiv.dom₁_eq`, `.dom₂_eq`, `.domSaddle_eq`, `.eq_of_mem_relint_dom₁` | **Cor 34.2.1** | done — the `dom L = dom K` clause needs **no** closedness |
| `LowerClosedFn.closedSaddleFn`, `SaddleEquiv.eq_partialCl₂_of_lowerClosedFn` | **Cor 34.2.2** | done |
| `ClosedSaddleFn.eq_const_of_not_properSaddleFn`, `not_saddleEquiv_const_bot_const_top` | **Cor 34.2.3** | done |
| `ConvexSliceStructure`, `SaddleStructure`, `closedSaddleFn_iff_saddleStructure` | **Thm 34.3** | done |
| `kernelSet`, `kernel`, `kernel_eq_iff`, `SaddleEquiv.kernel_eq`, `saddleEquiv_iff_kernel_eq` | **Thm 34.4** | done |
| `lowerCl_idem`, `upperCl_idem`, `closedSaddleFn_lowerCl` | **Thm 34.1**, reproved | done — no duality, layer B |
| `SimpleSaddleFn`, `saddleEquiv_lowerCl_upperCl`, `exists_unique_saddleEquiv_class_of_kernel` | **Thm 34.5** | done |
| `lowerSimpleExt`, `upperSimpleExt`, `exists_unique_saddleEquiv_class_of_finite` | **Cor 34.5.1** | done |
| `mem_saddleClass_simpleExt_iff`, `mem_saddleClass_simpleExt_iff_saddleEquiv` | **Cor 34.2.4** | done — needs neither Cor 33.3.3 nor joint continuity |

### What actually happened

**Theorem 34.1 needs no duality.** `Saddle/Closure.lean` derives it through Theorems 33.2 and 30.1,
which costs two compatible pairings and locally convex partners. `lowerCl_idem` is four lines from
monotonicity and idempotence of `cl₁`/`cl₂`, so Theorem 34.1 and its corollaries are layer B.

**Corollary 33.3.2's two round trips are definitional.** `LowerClosedFn K` *is* `cl₂ cl₁ K = K` and
`UpperClosedFn K` *is* `cl₁ cl₂ K = K`, so `left_inv` and `right_inv` of the `Equiv` are the
hypotheses themselves; the only content of the corollary is that `cl₁` lands in the upper closed
class and `cl₂` in the lower closed one, which is the same unfolding once more.

**Corollary 33.2.1 is one lemma past Theorem 33.2.** Theorem 33.2 already says the two brackets
differ by `cl₁`, and a concave function agrees with its closure on `ri` of its effective domain; the
missing step is `domConcave_bracket`, that the concave domain of `u ↦ ⟨Fu, y⟩` is `dom F` on the
nose, for *every* `y` — the bracket is `⊥` exactly where the slice `F u` is identically `⊤`.

**Corollary 33.3.3 is Corollary 33.3.1 on a closure pair that is already proved.**
`partialCl₁_lowerSimpleExt` and `partialCl₂_upperSimpleExt` are in `Saddle/Kernel.lean` for
Corollary 34.2.4, so the corollary is their composition and nothing else. Its `dom F = C` and
`dom F* = D` clauses are `dom₁_lowerSimpleExt` / `dom₂_lowerSimpleExt` read through Theorem 34.2,
and the explicit formulas the book gives for `F` and `F*` are the definitions of the conjugate and
the concave conjugate of the slices.

**Corollary 34.2.4 does not need Corollary 33.3.3, nor joint continuity.** Separate continuity of
`K` in each variable on the closed `C`, `D` suffices, and the proof is direct: closedness of the
slices plus `clFn`/`clConcave` of an improper slice.

**A large §6/§7 block had to be built on the way**, and it wants relocating:
`lscHull_eq_of_eqOn_relint_dom`, `clFn_eq_of_eqOn_relint_dom`, `clConcave_eq_of_eqOn_relint_domConcave`,
`Convex.relint_eq_of_subset_of_subset_closure` (the Cor 6.3.1 sandwich),
`ConcaveFn.clConcave_eq_of_mem_relint_domConcave` (Theorem 7.4's concave mirror, also proved
independently in `Optimization/Normal.lean` — see gotcha 74), `clFn_eq_bot_of_eq_bot`,
`clConcave_eq_top_of_eq_top`, `domConcave_neg`, and the `closedFn_restrict_coe` family. They belong
in `RelativeInterior.lean`, `Closure.lean`, `Concave.lean` and `ConcaveConj.lean`; the blocker is
that `ConcaveConj.lean` is layer C and does not import `RelativeInterior`. The fix is to split
`ConcaveConj.lean`'s `clConcave` block — which needs only `Closure.lean` and `Concave.lean` — into
a `ConcaveClosure.lean` that `RelativeInterior.lean` can import.

**Most of §34 is not finite-dimensional.** Theorem 34.1 and its corollaries need only a topological
group; all of Corollary 34.2.4 and the simple-extension value and domain lemmas use no `ri` at all;
`dom₁_mono`, `dom₂_anti`, `domSaddle`, `ProperSaddleFn` and `ConcaveConvexFn.partialCl₂`/`.partialCl₁`
(Cor 33.1.1 with the pairing supplied) are layer B or C. Only the kernel itself is layer D.

**OCR**: in Theorem 34.3's proof the first two displayed relations print `K` where `K̲` is meant.

## 7.3 `Saddle/Continuity.lean` — §35

**Status: Theorems 35.1–35.5 are done.** Analogues of §10, §24, §25 for saddle-functions.
Layer D.

```lean
structure ConcaveConvexOn (C : Set U) (D : Set X) (K : U × X → ℝ) : Prop where
  concave_fst : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)
  convex_snd  : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x)
```

| Lean name | book | status |
|---|---|---|
| `ConcaveConvexOn` | the section's hypothesis, bundled | done |
| `ConcaveConvexOn.continuousOn`, `.exists_lipschitzOnWith_of_isCompact`, `.exists_forall_abs_le_of_isCompact` | **Thm 35.1** | done |
| `exists_forall_abs_le_and_lipschitzOnWith_prod`, and its two halves `..._fst` / `exists_forall_lipschitzOnWith_snd` | **Thm 35.2** | done |
| `exists_isCompact_mem_nhdsWithin_relint`, `exists_isCompact_collar_relint` | `ri C` is locally compact, and a compact subset of it has a compact relative collar | done — both belong in `RelativeInterior.lean` |
| `uniformCauchySeqOn_of_equiLipschitz` | the metric core of Thms 10.8 and 35.4 | done |
| `continuousOn_prod_of_concaveConvexOn`, `…'` | **Thm 35.3** | done |
| `uniformCauchySeqOn_prod_of_dense`, `exists_tendstoUniformlyOn_prod_of_dense`, `…'`, `tendstoUniformlyOn_prod_of_tendsto` | **Thm 35.4** | done |
| `exists_subseq_tendstoUniformlyOn_prod` | **Thm 35.5** | done |
| — | **Thm 35.6**, Thm 35.7, Cor 35.7.1 | not done — directional derivatives |
| — | **Thm 35.8**, Cor 35.8.1 | not done |
| — | **Thm 35.9**, Thm 35.10 | not done — needs Rademacher |

**The plan's advice was right and paid off.** §10's convergence theorems were written for families
indexed by an arbitrary type, and Theorem 35.2 is exactly Theorem 10.6 applied four times — twice
to bound the family, once in each variable with the second consuming the first, and twice to make
it equi-Lipschitz — with the families indexed by `ι × ↑T` and `ι × ↑S`. Theorem 35.1 is the
one-element family. No §10 statement had to be reproved.

**§10 transports to `ri` by a chart; §35 cannot.** `Convergence.lean` proves each theorem for an
*open* convex set and pulls it back along `exists_chart_retraction`. The chart of `C ×ˢ D` is not
the product of the charts of `C` and of `D`, and it is the product structure the concave-convex
hypothesis lives on — so 35.3–35.5 are proved directly in `ri`. What replaces the `interior`
proofs' `IsCompact.exists_cthickening_subset_open` is `exists_isCompact_collar_relint`:
`cthickening ε S ⊆ U` is *false* relatively, since points off the affine hull of `C` are near `S`
and not in `ri C`, so the collar must be a set rather than a thickening. Its proof is the chart
again.

**Theorem 35.4 takes an arbitrary dense `A ⊆ ri C ×ˢ ri D`, not a product.** Theorem 35.2 does need
a product — it bounds one variable at a time — but Theorem 35.5's diagonal extraction produces a
*countable* dense set, and a countable dense subset of a product is not a product.

**The Lipschitz constant is `k₁ + k₂`, not the book's `2(α₁ + α₂)`** — Mathlib's product metric is
the supremum metric.

## 7.4 `Saddle/Minimax.lean` — §36, §37

```lean
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop :=
  (∀ u, K (u, p.2) ≤ K p) ∧ (∀ x, K p ≤ K (p.1, x))

/-- The saddle-value exists when the two iterated extrema agree. -/
def HasSaddleValue (K : U × X → EReal) : Prop :=
  (⨆ u, ⨅ x, K (u, x)) = (⨅ x, ⨆ u, K (u, x))
```

**Status: all of §36 and all of §37 are done**, except Corollary 37.5.1's homeomorphism clause
and Corollary 37.5.2, which need Corollaries 31.5.1 and 31.5.2 (`Optimization/Moreau.lean`).
§37 is spread over `Saddle/Minimax.lean` (the vocabulary and Theorem 37.1),
`Saddle/Conjugate.lean` (Cors 37.1.2–37.1.3, the `D*` halves of Thm 37.2, Cor 37.2.1, Thm 37.3
and Cor 37.3.1), `Saddle/Subgradient.lean` (Thms 37.4–37.6 and Cor 37.5.3) and
`Saddle/Existence.lean` (the `C*` halves, Cors 37.3.2, 37.5.1, 37.6.1 and 37.6.2). The names below are the ones
actually used; each plan entry above split into several statements, as usual.

| Lean name | book | status |
|---|---|---|
| `IsSaddlePoint`, `IsSaddlePointOn`, `maximin`, `minimax`, `HasSaddleValue`, `saddleLagrangian`, `flipBifun` | the §36 vocabulary | done |
| `maximin_le_minimax` | **Lemma 36.1** | done |
| `isSaddlePoint_iff_attained`, `isSaddlePoint_iff_iSup_eq_iInf`, `IsSaddlePoint.maximin_eq`, `.minimax_eq`, `.hasSaddleValue` | **Lemma 36.2** | done |
| `isSaddlePointOn_iff_biSup_eq_biInf`, `isSaddlePointOn_univ_univ` | the `C × D` ↔ `ℝᵐ × ℝⁿ` translation | done |
| `maximin_eq_biSup_dom₁`, `minimax_eq_biInf_dom₂` | §36, the outer restriction | done — **no hypotheses at all** |
| `biInf_dom₂_eq_iInf_slice`, `biSup_dom₁_eq_iSup_slice`, `maximin_eq_biSup_biInf`, `minimax_eq_biInf_biSup`, `isSaddlePoint_iff_isSaddlePointOn_dom` | **Thm 36.3** | done |
| `IsSaddlePoint.mem_domSaddle`, `IsSaddlePoint.exists_maximin_eq_coe` | **Cor 36.3.1** | done — needs only `ProperSaddleFn` |
| `SaddleEquiv.iInf_slice_eq`, `.iSup_slice_eq`, `.maximin_eq`, `.minimax_eq`, `.hasSaddleValue_iff`, `.isSaddlePoint_iff` | **Thm 36.4** | done — layer B |
| `saddleSwap_saddleLagrangian`, `concaveConvexFn_saddleLagrangian`, `upperClosedFn_saddleLagrangian`, `exists_unique_closedBifun_saddleLagrangian_eq` | **Thm 36.5** | done |
| `mem_argmin_iff_exists_isSaddlePoint_lagrangian`, `isSaddlePoint_lagrangian_iff_mem_kuhnTucker`, `…_of_stronglyConsistent` | **Thm 36.6** (= Cor 29.3.1) | done |
| `isSaddlePoint_lagrangian_iff`, `iSup_lagrangian`, `iSup_lagrangian_eq`, `iInf_lagrangian_ne_top` | **Thm 29.3** | done — `Optimization/Lagrangian.lean` lists it as missing |
| `isSaddlePoint_lagrangian_iff_normal_and_optimal`, `isSaddlePoint_lagrangian_iff_le_adjointBifun`, `iInf_lagrangian_eq_adjointBifun_zero` | **Cor 30.5.1** | done — `Optimization/Normal.lean` lists it as "needs §36" |
| `inverseBifun`, `inverseBifun_inverseBifun`, `convexBifun_inverseBifun`, `closedBifun_inverseBifun` | `F_*` and its involution | done |
| `lowerConjSaddle`, `upperConjSaddle`, `bifunSaddleClass`, `lowerConjSaddle_le_upperConjSaddle` | the §37 vocabulary, and `K̲* ≤ K̄*` by Lemma 36.1 | done |
| `minimax_eq_neg_lowerConjSaddle_zero`, `maximin_eq_neg_upperConjSaddle_zero`, `hasSaddleValue_iff_conjSaddle_zero_eq` | §37, the displays before Cor 37.1.3 | done |
| `upperConjSaddle_eq_saddleLagrangian`, `lowerConjSaddle_eq_bracket_inverseBifun` | **Thm 37.1**, both equations | done |
| `concaveConvexFn_upperConjSaddle`, `upperClosedFn_upperConjSaddle`, `concaveConvexFn_lowerConjSaddle`, `lowerClosedFn_lowerConjSaddle` | **Cor 37.1.1** | done |
| `adjointBifun_flip_inverseBifun`, `adjointBifun_flip_inverseBifun_adjointBifun`, `upperConjSaddle_eq_concaveBracket_adjointBifun`, `partialCl₁_lowerConjSaddle`, `partialCl₂_upperConjSaddle`, `saddleClass_conjSaddle`, `saddleEquiv_lowerConjSaddle_upperConjSaddle`, `properSaddleFn_upperConjSaddle`, `properSaddleFn_lowerConjSaddle`, `dom₁_conjSaddle_eq`, `dom₂_conjSaddle_eq`, `domSaddle_conjSaddle_eq`, `lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁`, `…_dom₂` | **Cor 37.1.2** | done (`Saddle/Conjugate.lean`) |
| `hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle`, `hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle`, `exists_maximin_eq_coe_of_mem_relint_domSaddle` | **Cor 37.1.3** | done (`Saddle/Conjugate.lean`) |
| `dom₁_eq_domBifun_of_mem_bifunSaddleClass`, `dom₂_upperConjSaddle`, `supportFn_dom₂_upperConjSaddle`, `supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn` | **Thm 37.2**, the `D*` half | done (`Saddle/Conjugate.lean`) — it does need **Thm 6.8** |
| `zero_mem_interior_dom₂_upperConjSaddle_iff` | **Cor 37.2.1**, the `D*` half | done (`Saddle/Conjugate.lean`) |
| `zero_mem_interior_dom₁_lowerConjSaddle_iff` | **Cor 37.2.1**, the `C*` half | done (`Saddle/Existence.lean`) — through `saddleSwap`, not through a second `supportFn` computation |
| `hasSaddleValue_of_no_common_direction_of_recession` | **Thm 37.3**, condition (a) | done (`Saddle/Conjugate.lean`) |
| `hasSaddleValue_of_no_common_direction_of_recession_neg` | **Thm 37.3**, condition (b) | done (`Saddle/Existence.lean`) |
| `lt_recessionFn_of_isBounded_dom`, `hasSaddleValue_of_isBounded_dom₂`, `hasSaddleValue_of_isBounded_dom₁` | **Cor 37.3.1** | done (`Saddle/Conjugate.lean`, `Saddle/Existence.lean`) |
| `saddleStructure_lowerSimpleExt`, `maximin_lowerSimpleExt`, `minimax_lowerSimpleExt`, `exists_bifunSaddleClass_lowerSimpleExt`, `biSup_biInf_eq_biInf_biSup_of_isBounded_left`, `…_right` | **Cor 37.3.2** | done (`Saddle/Existence.lean`) |
| `concaveSubgradient`, `saddleSubgradient`, `domSaddleSubgradient`, `saddleTilt`, `mem_saddleSubgradient_iff_isSaddlePoint`, `domSaddleSubgradient_subset_domSaddle`, `kernelSet_subset_domSaddleSubgradient` | **Thm 37.4** | done (`Saddle/Subgradient.lean`) |
| `IsBifunSubgradientPair`, `mem_saddleSubgradient_iff_isBifunSubgradientPair`, `mem_saddleSubgradient_upperConjSaddle_iff` | **Thm 37.5**, (a) ⇔ (d) ⇔ (b) | done (`Saddle/Subgradient.lean`) |
| `isBifunSubgradientPair_iff_mem_subgradient_graphFn` | **Thm 37.5**, (c) ⇔ (d) | done (`Saddle/Existence.lean`) — **no hypothesis on `F` at all** |
| `isClosed_setOf_mem_saddleSubgradient` | **Cor 37.5.1**, closedness clause | done (`Saddle/Existence.lean`) |
| — | **Cor 37.5.1**, homeomorphism clause; **Cor 37.5.2** | not done — need **Cor 31.5.1** and **Cor 31.5.2**, i.e. the attainment/uniqueness half of Thm 31.5 (`prox`) |
| `mem_saddleSubgradient_upperConjSaddle_zero_iff`, `convex_setOf_isSaddlePoint`, `exists_isSaddlePoint_iff_zero_mem_domSaddleSubgradient` | **Cor 37.5.3** | done (`Saddle/Subgradient.lean`) |
| `exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle`, `exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle`, `exists_isSaddlePoint_of_no_common_direction_of_recession` | **Thm 37.6** | done (`Saddle/Subgradient.lean`, `Saddle/Existence.lean`) |
| `exists_isSaddlePoint_of_isBounded_domSaddle`, `exists_maximin_eq_coe_of_isBounded_domSaddle` | **Cor 37.6.1** | done (`Saddle/Existence.lean`) |
| `exists_saddlePoint_of_isBounded` | **Cor 37.6.2** | done (`Saddle/Existence.lean`) — proved from Rockafellar's unbounded machinery, not from Mathlib's `Sion` |
| `swapAdjointBifun`, `adjointBifun_neg_flipBifun`, `adjointBifun_swapAdjointBifun`, `saddleSwap_mem_bifunSaddleClass`, `upperConjSaddle_saddleSwap`, `lowerConjSaddle_saddleSwap`, `proper_graphFn_of_properSaddleFn`, `separatingRight_neg_flip` | the `saddleSwap` dictionary §37 needs | done (`Saddle/Existence.lean`) |

**The `C*` half of §37 is the `D*` half at `saddleSwap`, and the dictionary is four lemmas.**
`Saddle/Conjugate.lean` left the `C*` halves open, saying that what was missing was "the dictionary
carrying `bifunSaddleClass` across that swap". It is: `saddleSwap` carries `Ω (F)` onto `Ω (F♯)` at
the **negated flipped** pairings `-Bx.flip`, `-Bu.flip`, where `(F♯ y) v = -(F* y)(v)`
(`saddleSwap_mem_bifunSaddleClass`), and it exchanges the two conjugates
(`upperConjSaddle_saddleSwap`). Nothing else is needed — no second support-function computation, no
mirror of Theorem 6.8. The one piece of real content is `adjointBifun_neg_flipBifun`, the identity
`(-Bx, -Bu)-adjoint of flipBifun F = flipBifun of the (Bu, Bx)-adjoint`, which is one reindexing of
an infimum over a product; through it the biadjoint identity `(F_*^*)^* = F_*` becomes
`adjointBifun_swapAdjointBifun`, "the adjoint of `F♯` is `-F`".

**`F♯` is *not* `F_*^*`.** `F_*^* = inverseBifun (adjointBifun Bu Bx F)` goes from `V` to `Y` and
belongs to the *conjugate* class on `V × X`; the swapped class lives on `Y × U` and its bifunction
goes from `Y` to `V`. The two differ by `flipBifun`, and the difference is not cosmetic — the
pairings sit in the other order.

**`Proper (graphFn F)` is a hypothesis of every §37 statement and had to be derived.** Theorem 34.3
and Corollary 34.2.4 deliver `ProperSaddleFn K`, not properness of the bifunction, and the two are
related by `proper_graphFn_of_properSaddleFn`: `dom₂ K ≠ ∅` rules out `F u x = -∞`, because that
makes the bracket `⟨Fu, ·⟩` identically `+∞`, and `dom₁ K ≠ ∅` rules out `F ≡ +∞`, because that
makes the upper bracket identically `-∞`. Both halves of properness are needed and neither is
optional.

**Corollary 37.3.2 must be stated in `EReal`.** The book writes `inf_D sup_C K = sup_C inf_D K` for
a *finite* `K`, but with only one of `C`, `D` bounded the two iterated extrema can be `±∞` — take
`C` a point, `D` a line and `K` linear and non-constant on `D`. The equality is still true, and is
what `biSup_biInf_eq_biInf_biSup_of_isBounded_left` states; only Corollary 37.6.2, where both sets
are bounded, can be stated with real inequalities, and it is.

**`HasSaddleValue` must not build in finiteness.** The book calls the common value the saddle-value
when the two iterated extrema are *equal*, and states finiteness separately (Cor 36.3.1, Cor 37.1.3,
Thm 37.3). Folding it in would make Corollary 36.3.1 vacuous.

**Three hypothesis corrections.** Corollary 36.3.1 needs only `ProperSaddleFn` — not closedness,
not concave-convexity, not finite dimension; the book states it inside Theorem 36.3's closed-proper
hypothesis, but it is strictly weaker. Theorem 36.4 needs only a topology on each factor (layer B,
not C or D): its substance is `iInf_clFn_eq_iInf` and its concave mirror. And the *outer*
restriction in Theorem 36.3 is free — `maximin_eq_biSup_dom₁` and `minimax_eq_biInf_dom₂` have
zero hypotheses, since `u ∉ dom₁ K ↔ ∃ x, K (u, x) = ⊥`; only the *inner* restriction to `ri` needs
Corollary 7.3.1 and the Theorem 34.3 sandwich.

**Theorem 36.5 does not need a concave mirror of Theorem 33.3.** Reading the identity after
`saddleSwap` turns it into the *convex* Theorem 33.3 for the pairing `-Bu`, at the price of two
three-line lemmas (`isCompatiblePairing_neg`, `flip_neg`).

**`F_*` is a flip composed with a negation, and the halves must stay separate.** `flipBifun`
preserves convexity and closedness; `inverseBifun` swaps convex ↔ concave. Theorem 36.5 wants the
first, Theorem 37.1 the second.

**`(F_*)^* = (F^*)_*` should be a *definition*, not a lemma.** The backbone has no adjoint of a
concave bifunction in the direction Rockafellar needs; defining the object as
`inverseBifun (adjointBifun Bu Bx F)` makes his commutation a triviality and lets Theorem 33.3
apply to it verbatim. §7.5 below needs the same object.

Corollary 37.6.2 (a continuous finite concave-convex function on a product of compact convex sets
has a saddle-point) is the classical minimax theorem — von Neumann's, in Kakutani/Ky Fan form — and
is the headline result of Part VII. It should be stated in the surface exactly in that form, since
it is the version everyone cites.

**Correction:** Mathlib *does* have a minimax theorem — `Mathlib/Topology/Sion.lean` (Sion–von
Neumann, including a saddle-point form). So Corollary 37.6.2 should be **derived from Mathlib's**
rather than reproved, and the "genuinely new contribution" argument for prioritising §36/§37 does not
stand. What is genuinely new here is Rockafellar's unbounded versions (Theorems 37.3, 37.6), reached
through conjugate saddle-functions; those remain worth doing, but after §34 rather than before it.

## 7.5 `Bifunction/Algebra.lean` — §38

The "convex algebra": operations on bifunctions mirroring the linear algebra of linear maps.

| operation | definition | linear-algebra analogue |
|---|---|---|
| `F₁ □ F₂` | infimal convolution in the second variable, pointwise in the first | `A₁ + A₂` |
| `F λ` | right scalar multiplication | `λ A` |
| `F f` | image of a convex function under a bifunction | `A x` |
| `G ∘ F` | composition | `B ∘ A` |
| `⟨f, g⟩` | the extremal value in Fenchel's duality theorem | inner product |

```lean
/-- The "inner product" of a convex `f` and a concave `g`: the common value in Fenchel duality. -/
noncomputable def fenchelPairing (f : E → EReal) (g : E → EReal) : EReal :=
  ⨅ x, f x - g x     -- when it equals ⨆ y, g* y - f* y; existence is part of the theory
```

**Status: done except Theorem 38.2 with Corollary 38.2.1, and Corollaries 38.4.1 and 38.5.1.**
The operations are `infConvBifun`, `smulRightBifun`, `imageBifun` / `concaveImageBifun`,
`compBifun` / `concaveCompBifun`, `invBifun` (`F⫶`) and `lowerAdjointBifun` (`F⫶*`); the inner
product is `fenchelSup` / `fenchelInf` with `HasFenchelPairing` and `fenchelPairing`.

| Lean name | book | status |
|---|---|---|
| `domBifun_infConvBifun`, `convexBifun_infConvBifun`, `graphFn_infConvBifun`, `bracket_infConvBifun` | **Thm 38.1** | done |
| — | **Thm 38.2**, Cor 38.2.1 | not done — needs the *concave* orientation of Thm 16.4, and a concave `supConv` that does not exist |
| `convexBifun_smulRightBifun`, `graphFn_smulRightBifun`, `bracket_smulRightBifun` | **Thm 38.3** | done |
| `convexFn_imageBifun`, `conj_imageBifun`, `exists_conj_imageBifun_eq`, `conj_imageBifun_eq_iSup`, `conj_imageBifun_of_bracket_eq_top`, `lowerAdjointBifun_eq_concaveAdjointBifun`, `convexBifun_lowerAdjointBifun` | **Thm 38.4** | done, against `IsExactSum` |
| `convexBifun_compBifun`, `invBifun_compBifun` | **Thm 38.5** | done |
| — | Cors 38.4.1, 38.5.1 | not done — both need "closure commutes with `imageBifun`/`compBifun`", which is Thm 38.2's argument again |
| `hasFenchelPairing_conj`, `fenchelPairing_conj`, `fenchelSup_le_fenchelInf`, `hasFenchelPairing_of_le` | **Lemma 38.6** | done |
| `hasFenchelPairing_adjointBifun`, `conj_imageBifun_eq_fenchelPairing` | **Cor 38.7.1** | done |
| `fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun` and its supports | **Thm 38.7** | done |

**Rockafellar's `⟨f, g⟩` is not §31's Fenchel setup.** His inner product pairs a convex `f` on `E`
with a concave `g` on the *paired* space `F`; §31 has both on `E`. The two differ by a concave
closure, so Lemma 38.6 **cannot** be derived from `fenchel_duality` and is proved from scratch.

**Weak duality for `⟨f, g⟩` is unconditional.** `fenchelSup B f g ≤ fenchelInf B f g` needs neither
properness nor exactness — both `∞ - ∞` collisions land on the correct side. That is why every
"the extremum is attained" claim in §38 reduces to a single inequality, and why Corollary 38.7.1's
existence half is free.

**Theorem 38.4 needs no case split.** The book splits on whether `y ∈ dom F*`; `IsExactSum`'s
`proper_right` field already excludes the degenerate branch, and that branch is stated separately
and unconditionally as `conj_imageBifun_of_bracket_eq_top`.

**`(F* g*)(v) ≠ ⊤` is not automatic** — a supremum of finite terms can be `⊤` — but it *is* bounded
uniformly in `y`, because the two `⟨x₀, y⟩` terms cancel. That is
`concaveImageBifun_adjointBifun_ne_top`, under "`F` finite at `(u₀, x₀)` and `g` finite at `x₀`",
which Theorem 38.7's `ri`-hypothesis implies.

Theorem 38.7 is the payoff — "adjoints move across the inner product", exactly as in linear algebra
— and Rockafellar calls it "remarkable and non-trivial". Its hypotheses are again `ri`-intersection
conditions, so it should be stated against `IsExactSum`/`IsExactImage`.

## 7.6 `Bifunction/Process.lean` — §39

```lean
/-- A convex process: a multivalued map whose graph is a convex cone containing the origin. -/
structure ConvexProcess (U X : Type*) [AddCommGroup U] [Module ℝ U] … where
  graph : Set (U × X)
  isConvexCone : Convex ℝ graph ∧ ∀ a > (0:ℝ), a • graph = graph
  zero_mem : (0, 0) ∈ graph
```

**Status: Theorems 39.1, 39.2 and Corollary 39.7.1 are done.** `ConvexProcess U X` wraps a
`PointedCone ℝ (U × X)` — not a raw `Set` with side conditions, as this plan sketched — with
`eval`, `dom`, `range`, `image`, `inv`, `ofLinearMap`, `comp`, an `Add` instance,
`indicatorBifun`, `adjointProcess` and `coadjointProcess`.

| Lean name | book | status |
|---|---|---|
| `convex_eval`, `convex_dom`, `convex_range`, `convex_image`, `add_eval_zero_subset`, `inv_inv`, `dom_inv`, `range_inv`, `smul_graph` | §39's elementary theory | done |
| `exists_linearMap_of_isBounded`, `eval_zero_eq_zero_of_isBounded`, `exists_eval_eq_singleton`, `eval_ofLinearMap`, `dom_ofLinearMap` | **Thm 39.1**, both directions | done |
| `adjointBifun_indicatorBifun`, `isClosed_graph_adjointProcess`, `graph_coadjointProcess_adjointProcess_eq_closure`, `coadjointProcess_adjointProcess_eq_self_iff` | **Thm 39.2** | done |
| `isClosed_image`, `isClosed_image_of_isBounded`, `image_eq_image_snd` | **Cor 39.7.1** | done |
| `graphFn_indicatorBifun`, `convexBifun_indicatorBifun`, `domBifun_indicatorBifun`, `indicatorBifun_add`, `indicatorBifun_comp`, `dom_add`, `eval_comp`, `inv_comp` | the §38 ↔ §39 dictionary | done |
| — | Thms 39.3, 39.4 | not done — they specialize Thms 33.1–33.3 and Cor 33.2.1 to processes, which are now available, so they should be short |
| — | Thms 39.5–39.8 | not done |

**Corollary 39.7.1 is Theorem 9.1, not Theorem 39.7.** Rockafellar derives it by specializing
Theorem 39.7 and separating the barrier cone of `C` from the range of `A*`. But `A C` is the
projection of `graph A ∩ (C × X)` onto the second factor; a pointed convex cone is its own recession
cone, so `0⁺(graph A ∩ (C × X)) = graph A ∩ (0⁺C × X)`, and its intersection with the projection's
kernel is exactly `{(v, 0) | v ∈ A⁻¹0 ∩ 0⁺C}` — which is Theorem 9.1's hypothesis. **The §39.7 and
barrier-cone prerequisite can be dropped from the plan entirely**: 39.7.1 needs no duality at all,
only `isClosed_image_of_recessionCone_inter_ker`, `recessionCone_inter`,
`recessionCone_coe_pointedCone` and `recessionCone_prod`.

**Orientation in §39 hides a real sign trap.** Rockafellar carries "supremum- or infimum-oriented"
as informal side data and says the adjoint of an infimum-oriented process is defined "in the same
way, except the inequality is reversed". That sentence is load-bearing: using the
supremum-oriented definition twice gives `{p | ∀ w ∈ K°, 0 ≤ ⟨p, w⟩}` instead of the bipolar `K°°`,
and `A** = cl A` becomes **false**. Two separate definitions — `adjointProcess` and
`coadjointProcess` — is the right formalization; a boolean orientation field would double every
statement.

Convex processes are exactly `ConvexCone ℝ (U × X)` viewed as relations, so Mathlib's `ConvexCone`
should carry most of the structure. Corollary 39.7.1 (`A C` closed when `A` is a closed convex
process and `C` is compact, or more generally under a recession condition) is the §9-flavoured
result that makes processes useful; note it is the natural generalisation of Theorem 9.1.

Convex processes are also the right home for the "positively homogeneous" fragment of set-valued
analysis (`SetValued`/`Rel` in Mathlib terms) and are the algebraic skeleton behind linear
programming duality — the highest-leverage part of §39 for downstream users.
