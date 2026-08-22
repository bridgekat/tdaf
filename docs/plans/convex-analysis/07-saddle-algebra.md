# Sub-plan 7 — Saddle-functions, minimax, and the algebra of bifunctions

Covers Rockafellar §33–§39 (Parts VII and VIII).

These are the most original and least formalised parts of the book, and the ones where
[D8](00-overview.md#d8) — everything is partial conjugation — does the most work. Rockafellar
develops the saddle-function closure calculus by hand over §33–§34; the backbone should get it from
a single `partialConj` / `partialClosure` API applied twice, once in each variable.

---

## 7.1 The one abstraction

```lean
variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] …
variable (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)

/-- Conjugate in the second variable only. -/
noncomputable def partialConj₂ (f : U × X → EReal) : U × Y → EReal :=
  fun p => conj Bx (fun x => f (p.1, x)) p.2

/-- Close in the second variable only (Rockafellar's `cl₂`). -/
noncomputable def partialCl₂ (f : U × X → EReal) : U × X → EReal :=
  fun p => clFn (fun x => f (p.1, x)) p.2
```

with `partialConj₁`, `partialCl₁` the mirror images — and, from `Duality/Pairing.lean`, the product
pairing `prodPairing Bu Bx` with its sign-flip `negFst`, plus the composition law
`conj (prodPairing Bu Bx) = partialConj₁ Bu ∘ partialConj₂ Bx`. That law is the entire technical
content of [D8](00-overview.md#d8); see D8's sign
table for which of {bracket, Lagrangian, adjoint, `cl₁`, `cl₂`} uses which convention.

Facts to prove once:

- `partialConj₂` preserves convexity in the second variable and *reverses* it in the first
  (Theorem 33.1: `⟨Fu, x*⟩` is concave-convex);
- `partialConj₂ ∘ partialConj₂` (with the flipped pairing) is `partialCl₂`;
- `partialCl₁` and `partialCl₂` commute up to equivalence (this is the substance of §34).

Rockafellar's bracket `⟨Fu, x*⟩ = (Fu)*(x*)` is `partialConj₂ (graphFn F)`, and the Lagrangian of
[sub-plan 6](06-optimization.md#63-optimizationlagrangianlean--2829-via-partial-conjugation) is
`-partialConj₁`. Naming these once collapses §33, §34, §36 and §37 substantially.

## 7.2 `Saddle/Defs.lean` — §33, §34

```lean
/-- `K` is concave-convex on `U × X`: concave in the first argument, convex in the second. -/
structure ConcaveConvexFn (K : U × X → EReal) : Prop where
  concave_fst : ∀ x, ConcaveFn (fun u => K (u, x))
  convex_snd  : ∀ u, ConvexFn (fun x => K (u, x))

def SaddleFn (K : U × X → EReal) : Prop := ConcaveConvexFn K ∨ ConcaveConvexFn (fun p => -(K p))

/-- The effective domains of a saddle-function. These are **not** projections of a single `dom`,
and they must be defined before anything in §34 can even be stated. Rockafellar §34:
`dom₁ K = {u | K (u, ·) ≢ -∞}`, `dom₂ K = {v | K (·, v) ≢ +∞}` for concave-convex `K`. -/
def dom₁ (K : U × X → EReal) : Set U := {u | ∃ x, K (u, x) ≠ ⊥}
def dom₂ (K : U × X → EReal) : Set X := {x | ∃ u, K (u, x) ≠ ⊤}

/-- Two saddle-functions are equivalent when their partial closures agree.
Rockafellar (line 14641) uses the **single** partial closures, not the doubled ones: `K` and `L` are
equivalent iff `cl₁ K = cl₁ L` and `cl₂ K = cl₂ L`. Theorem 34.4's proof concludes exactly that. -/
def SaddleEquiv (K L : U × X → EReal) : Prop :=
  partialCl₁ K = partialCl₁ L ∧ partialCl₂ K = partialCl₂ L

/-- The kernel is the **restriction of `K`** to `ri (dom₁ K) × ri (dom₂ K)` (book, line 14887) —
a *function*, not its domain. Defining it as the domain would make Theorem 34.4 refutable, since
`K` and `K + 1` would share a kernel without being equivalent. -/
noncomputable def kernel (K : U × X → EReal) : (ri (dom₁ K) ×ˢ ri (dom₂ K) : Set (U × X)) → EReal :=
  (ri (dom₁ K) ×ˢ ri (dom₂ K)).restrict K
```

| Lean name | book |
|---|---|
| `concaveConvex_bracket` : `⟨Fu, y⟩` is concave-convex and convex-closed | **Thm 33.1**, Cor 33.1.1–3 |
| `bracket_relint_eq` | **Thm 33.2**, Cor 33.2.1–2 |
| `bifun_saddle_correspondence` : closed convex bifunctions ↔ **lower closed** concave-convex functions (and closed concave bifunctions ↔ **upper closed** ones) | **Thm 33.3**, Cor 33.3.1–3 |
| `saddleFn_partialCl` | **Thm 34.1** |
| `saddleEquiv_class_of_closed_bifun` — the *equivalence-class* form of the correspondence | **Thm 34.2**, Cor 34.2.1–4 |
| `closed_iff_structural` | **Thm 34.3** |
| `saddleEquiv_iff_kernel_eq` | **Thm 34.4** |
| `exists_unique_saddleEquiv_class_of_kernel` | **Thm 34.5**, Cor 34.5.1 |

Theorem 33.3 is the "bilinear functions ↔ linear transformations" analogy made precise, and it is
the theorem the whole of Part VII is built on. With §7.1 in place it is Fenchel–Moreau in the second
variable, uniformly in the first.

## 7.2a Why the equivalence classes are unavoidable

A finite concave-convex `K` on `C × D` has *two* natural extensions to `U × X` (the lower and upper
simple extensions, §33), and they differ exactly off `C × D`. Rockafellar's resolution — work with
the equivalence class, which has a least and a greatest member — is the right one and should be
formalised as stated, not worked around. Corollary 34.2.2 (each class has a unique lower closed and
a unique upper closed member) makes the class computationally usable: pick a canonical
representative when needed.

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
