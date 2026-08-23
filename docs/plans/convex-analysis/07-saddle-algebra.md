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

**Status: all of §34 is done, and §33 except Cors 33.1.2, 33.1.3, 33.2.1–33.2.2 and 33.3.2–33.3.3.**
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
| — | **Cor 33.1.2** as an `Equiv` | not done — needs `ImageClosed` and a subtype |
| — | **Cor 33.1.3** (polyhedral) | not done — needs polyhedral bifunctions |
| `bracket_concaveAdjointBifun_eq_partialCl₂`, `partialCl₂_concaveBracket_adjointBifun` | **Thm 33.2**, second equation `cl₂ ⟨u, F*x*⟩ = ⟨(cl F)u, x*⟩` | done |
| `lowerCl`, `upperCl`, `LowerClosedFn`, `UpperClosedFn`, `FullyClosedFn`, `fullyClosedFn_iff` | **§33–§34**, the closedness notions | done (`Saddle/Closure.lean`) |
| `upperClosedFn_upperCl`, `lowerClosedFn_lowerCl` | **Thm 34.1** | done (`Saddle/Closure.lean`) |
| `ImageClosedBifun`, `eq_of_bracket_eq` | the uniqueness half of the correspondence | done (`Optimization/Adjoint.lean`, `Saddle/Correspondence.lean`) |
| `partialCl₁_bracket`, `partialCl₂_concaveBracket_adjoint`, `lowerClosedFn_bracket`, `exists_unique_convexBifun_bracket_eq` | **Thm 33.3** | done (`Saddle/Correspondence.lean`) |
| `le_of_partialCl₂_eq`, `exists_unique_bifun_of_closure_pair` | **Cor 33.3.1** | done (`Saddle/Correspondence.lean`) |
| — | **Cors 33.3.2–33.3.3** | not done |
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

Analogues of §10, §24, §25 for saddle-functions. Layer D.

| Lean name | book |
|---|---|
| `ConcaveConvexFn.continuousOn_relint`, `.lipschitzOn` | **Thm 35.1** |
| `equiLipschitz_of_pointwise_bounded` | Thm 35.2 |
| `continuous_of_saddle_in_uv_continuous_in_t` | Thm 35.3 |
| `tendsto_uniformlyOn_of_pointwise` | Thm 35.4, 35.5 |
| `dirDeriv_saddle` | **Thm 35.6**, Thm 35.7, Cor 35.7.1 |
| `differentiableAt_iff_unique_subgradient` | **Thm 35.8**, Cor 35.8.1 |
| `ae_differentiableAt_saddle` | **Thm 35.9**, Thm 35.10 |

Every one of these is the saddle version of a §10/§24/§25 statement; if those are written with the
right generality (a statement about a family of convex functions depending on a parameter), most of
§35 should be an application rather than a reproof. Worth checking before writing §10 and §25:
**state the §10 convergence theorems for families indexed by an arbitrary set**, which is what §35
consumes.

## 7.4 `Saddle/Minimax.lean` — §36, §37

```lean
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop :=
  (∀ u, K (u, p.2) ≤ K p) ∧ (∀ x, K p ≤ K (p.1, x))

/-- The saddle-value exists when the two iterated extrema agree. -/
def HasSaddleValue (K : U × X → EReal) : Prop :=
  (⨆ u, ⨅ x, K (u, x)) = (⨅ x, ⨆ u, K (u, x))
```

| Lean name | book |
|---|---|
| `iSup_iInf_le_iInf_iSup` | **Lemma 36.1** |
| `isSaddlePoint_iff_extrema_attained` | **Lemma 36.2** |
| `saddleValue_of_closedProper` | **Thm 36.3**, Cor 36.3.1 |
| `saddleEquiv_saddleValue_eq` | **Thm 36.4** |
| `lagrangian_iff_upperClosed_concaveConvex` | **Thm 36.5** |
| `kuhnTucker_theorem` (general form) | **Thm 36.6** |
| `conjugateSaddle` and its involution | **Thm 37.1**, Cor 37.1.1–3 |
| `supportFn_dom_conjugateSaddle` | **Thm 37.2**, Cor 37.2.1 |
| `hasSaddleValue_of_recession` | **Thm 37.3**, Cor 37.3.1–2 |
| `subgradient_saddle_iff_isSaddlePoint_shift` | **Thm 37.4**, Cor 37.4.1 |
| `graph_subgradient_saddle_homeomorph` | **Thm 37.5**, Cor 37.5.1–3 |
| `exists_isSaddlePoint` | **Thm 37.6**, Cor 37.6.1–2 |

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

| Lean name | book |
|---|---|
| `convexBifun_infConv`, `dom_infConv` | Thm 38.1 |
| `adjoint_infConv` | **Thm 38.2**, Cor 38.2.1 |
| `adjoint_smulRight` | Thm 38.3 |
| `adjoint_apply_fn` | **Thm 38.4**, Cor 38.4.1 |
| `adjoint_comp` | **Thm 38.5**, Cor 38.5.1 |
| `fenchelPairing_conj` | Lemma 38.6 |
| `fenchelPairing_adjoint` : the four-way identity `⟨Ff, g*⟩ = ⟨f, F*g*⟩ = -⟨f*, F_* g⟩ = -⟨F_*^* f*, g⟩`, for proper concave `g` and the *lower* adjoint `F_*` | **Thm 38.7**, Cor 38.7.1 |

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

| Lean name | book |
|---|---|
| `isLinearMap_of_dom_univ_of_isBounded` | **Thm 39.1** |
| `adjoint_adjoint_eq_cl` | **Thm 39.2** |
| `bracket_posHomogeneous` | **Thm 39.3**, Thm 39.4 |
| `adjoint_infConv` | Thm 39.5, Thm 39.6 |
| `adjoint_apply_fn` | **Thm 39.7**, Cor 39.7.1 (closedness of `A C`) |
| `adjoint_comp` | Thm 39.8 |

Convex processes are exactly `ConvexCone ℝ (U × X)` viewed as relations, so Mathlib's `ConvexCone`
should carry most of the structure. Corollary 39.7.1 (`A C` closed when `A` is a closed convex
process and `C` is compact, or more generally under a recession condition) is the §9-flavoured
result that makes processes useful; note it is the natural generalisation of Theorem 9.1.

Convex processes are also the right home for the "positively homogeneous" fragment of set-valued
analysis (`SetValued`/`Rel` in Mathlib terms) and are the algebraic skeleton behind linear
programming duality — the highest-leverage part of §39 for downstream users.
