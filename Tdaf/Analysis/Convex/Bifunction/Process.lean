/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Bifunction.Algebra
import Tdaf.Analysis.Convex.Recession.Closedness

/-!
# Convex processes

Rockafellar's §39. A **convex process** from `U` to `X` is a multivalued map `A : u ↦ A u`
satisfying `A (u₁ + u₂) ⊇ A u₁ + A u₂`, `A (λ u) = λ (A u)` for `λ > 0`, and `0 ∈ A 0`. Rockafellar
observes immediately that these three conditions say exactly that

  `graph A = {(u, x) | x ∈ A u}`

is a convex cone containing the origin, so that is what `ConvexProcess` *is*: a bundled
`PointedCone ℝ (U × X)`, with `A.eval u` the `u`-slice of the cone. Convex processes sit between
linear transformations and convex bifunctions: `ConvexProcess.ofLinearMap` embeds the former, and
`ConvexProcess.indicatorBifun` embeds a process into the latter.

## Main definitions

* `ConvexProcess U X` — a convex process, carried by its graph.
* `ConvexProcess.eval`, `dom`, `range`, `image`, `inv` — `A u`, `dom A`, `range A`, `A C`, `A⁻¹`.
* `ConvexProcess.ofLinearMap` — a linear transformation as a convex process.
* `ConvexProcess.indicatorBifun` — the indicator bifunction `(F u)(x) = δ(x | A u)` of a
  supremum-oriented process.
* `ConvexProcess.comp`, and the `Add` and `SMul` instances — the product `B A`, the sum
  `A₁ + A₂` and the scalar multiple `λ A`.
* `ConvexProcess.adjointProcess`, `ConvexProcess.coadjointProcess` — the adjoint `A*` of a
  supremum-oriented process, and the adjoint of an infimum-oriented one (the same definition with
  the inequality reversed).

## Main results

* `ConvexProcess.convex_eval`, `convex_dom`, `convex_range`, `convex_image`,
  `add_eval_zero_subset` — the elementary properties §39 opens with.
* `ConvexProcess.exists_linearMap_of_isBounded` — **Theorem 39.1**: a convex process with full
  domain and bounded `A 0` is a linear transformation.
* `ConvexProcess.graphFn_indicatorBifun`, `convexBifun_indicatorBifun`,
  `domBifun_indicatorBifun` — the dictionary between §39 and §38.
* `ConvexProcess.dom_add`, `eval_comp`, `inv_comp`, `indicatorBifun_add`,
  `indicatorBifun_comp` — the algebra of processes and its translation into §38: the indicator
  bifunction of `A₁ + A₂` is `F₁ □ F₂` and that of `B A` is `G F`.
* `ConvexProcess.adjointBifun_indicatorBifun` — **Theorem 39.2**, last assertion: the adjoint of
  the indicator bifunction of `A` is the indicator bifunction of `A*`.
* `ConvexProcess.isClosed_graph_adjointProcess` — **Theorem 39.2**, first assertion: `A*` is
  always closed.
* `ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure`,
  `coadjointProcess_adjointProcess_eq_self_iff` — **Theorem 39.2**, second assertion:
  `A** = cl A`, and `A** = A` exactly for closed `A`.
* `ConvexProcess.isClosed_image`, `isClosed_image_of_isBounded` — **Corollary 39.7.1**: `A C` is
  closed when `A` is a closed convex process, `C` is a nonempty closed convex set, and no non-zero
  vector of `A⁻¹ 0` recedes `C`.
* `ConvexProcess.adjointProcess_smul`, `coadjointProcess_smul` — **Theorem 39.6**:
  `(λ A)* = λ (A*)` for `λ > 0`, in both orientations.
* `ConvexProcess.adjointProcess_add` — **Theorem 39.5**: `(A₁ + A₂)* = A₁* + A₂*`, under the
  exactness hypothesis of Theorem 16.4 for the two support functions `⟨Aᵢ ·, x*⟩`. The auxiliary
  `infConv_indicatorFn`, `supConv_neg_indicatorFn` and `indicatorFn_injective` are the dictionary
  between sums of sets and (supremal or infimal) convolution of their indicators.
* `ConvexProcess.bracket_indicatorBifun`, `bracket_indicatorBifun_apply`,
  `posHomogeneous_bracket_indicatorBifun`, `convexFn_bracket_indicatorBifun`,
  `closedFn_bracket_indicatorBifun`, `posHomogeneous_bracket_indicatorBifun_arg`,
  `concaveFn_bracket_indicatorBifun` — **Theorem 39.3**, first two assertions: `⟨Au, x*⟩` is the
  support function of `A u`, hence positively homogeneous, closed and convex in `x*`, and it is
  positively homogeneous and concave in `u`.
* `ConvexProcess.concaveBracket_adjointBifun_indicatorBifun` — the second of the two extremum
  problems, `⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}`.
* `ConvexProcess.concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁` — **Theorem 39.3**,
  third assertion: `⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`.
* `indicatorFn_injective`, `ConvexProcess.indicatorBifun_injective`,
  `ConvexProcess.bracket_indicatorBifun_zero_zero` — the two facts **Theorem 39.4** needs on this
  side of the correspondence: a process is determined by its indicator bifunction, and `⟨Au, x*⟩`
  vanishes at the origin.
* `exists_pairing_sandwich` — Fenchel's duality theorem read at a positively homogeneous pair: a
  concave `p` below a convex `q`, both straddling `0` at the origin, admit a linear `⟨·, y⟩`
  between them.
* `ConvexProcess.comp_adjointProcess_le`, `ConvexProcess.adjointProcess_comp` —
  **Theorem 39.8**: `(BA)* = A* B*`, under the exactness hypothesis of Theorem 16.4 for
  `⟨B·, z*⟩` and `⟨·, u*⟩` on `A⁻¹`.
* `ConvexProcess.indicatorBifun_inv`, `ConvexProcess.coadjointProcess_inv`,
  `ConvexProcess.lowerAdjointBifun_indicatorBifun` — the last entries of the §38/§39 dictionary:
  `(A⁻¹)* = A*⁻¹`, and `F⁎*` for an indicator bifunction is the indicator bifunction of `A*⁻¹`.
* `ConvexProcess.conj_imageBifun_indicatorBifun`,
  `ConvexProcess.exists_imageBifun_indicatorBifun_adjointProcess_eq` — **Theorem 39.7**, first
  two assertions: `(Af)* = A*⁻¹ f*`, with the infimum defining `(A*⁻¹ f*)(x*)` attained.

## Design notes

**A convex process is its graph, and the graph is a `PointedCone`.** Rockafellar's three axioms are
never used again after he proves they amount to "the graph is a convex cone containing the origin",
so `ConvexProcess` is a one-field structure wrapping `PointedCone ℝ (U × X)` and every elementary
property is a `Submodule` fact in disguise (`smul_mem_graph`, `add_mem_graph`, `zero_mem_graph`).
The structure wrapper, rather than an abbreviation, is what lets `A.eval`, `A.dom` and `A.inv` be
dot notation and keeps `ConvexProcess X U` and `ConvexProcess U X` from being confused.

**Corollary 39.7.1 is Theorem 9.1, not Theorem 39.7.** Rockafellar deduces it by specializing
Theorem 39.7 and separating the barrier cone of `C` from the range of `A*`. But `A C` is the
projection of `graph A ∩ (C × X)` on the second factor (`image_eq_image_snd`), the recession cone
of that intersection is `graph A ∩ (0⁺C × X)` — a pointed convex cone is its own recession cone —
and its intersection with the kernel of the projection is `{(v, 0) | v ∈ A⁻¹ 0 ∩ 0⁺C}`. So the
hypothesis of Theorem 9.1 is literally Rockafellar's hypothesis, and the proof needs no duality at
all. Only the projection's source needs to be finite-dimensional, which is where
`isClosed_image_of_recessionCone_inter_ker` puts it.

**Orientation is a second adjoint, not a flag.** Rockafellar carries "supremum oriented" and
"infimum oriented" as extra data on a convex set, and defines the adjoint of an infimum-oriented
process by reversing the inequality. Rather than bundle an orientation into the structure — which
would double every statement — the two adjoints are two definitions, `adjointProcess` and
`coadjointProcess`, and `A**` is spelled
`coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)`. This is not bookkeeping: with
`adjointProcess` used twice the sign flips *add* instead of cancelling,
and one gets `{p | ∀ w ∈ K°, 0 ≤ ⟨p, w⟩}` instead of the bipolar `K°°`.

**Theorem 39.5 carries an `IsExactSum` per `x*`, not a relative-interior condition.**
Rockafellar's hypothesis is `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`. Converting it into the exactness of
`(⟨A₁ ·, x*⟩ + ⟨A₂ ·, x*⟩)*` would go through `IsExactSum.of_relint`, which demands that both
summands be *closed* proper convex functions; `u ↦ -⟨Aᵢ u, x*⟩` is proper and convex but is not
concave-closed even for closed `Aᵢ` — its concave closure is `⟨u, Aᵢ* x*⟩`, and the gap between the
two is exactly Theorem 39.3's third assertion. So the exactness is taken as the hypothesis, one
instance per `x*`. `IsExactSum.of_relint` no longer demands closedness (it asks only for proper
convex summands with a common relative interior point of the effective domains), so discharging the
hypothesis from Rockafellar's `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅` is now available and simply has not
been done. The same remark applies to Theorem 38.2.

**Theorem 39.8 does not need Theorem 38.5.** Rockafellar deduces `(BA)* = A* B*` from the adjoint
formula for a product of bifunctions. Read directly, `(z*, u*) ∈ (BA)*` says that the concave
`x ↦ ⟨Bx, z*⟩` lies below the convex `x ↦ ⟨u*, A⁻¹x⟩`, and a factorisation through `A*` and `B*` is
precisely a linear functional running between them. `exists_pairing_sandwich` produces one from
Fenchel's duality theorem: both functions are positively homogeneous and straddle `0` at the
origin, so the two extrema are pinned at `0` and the attained dual value splits into the two
inequalities. No convexity hypothesis has to be stated, because `IsExactSum` already carries it.

**The adjoint is the polar of the graph, with a sign flip on one factor.**
`mem_graph_adjointProcess_iff_mem_polarCone` says `(y, v) ∈ graph A*` if and only if
`(-v, y) ∈ (graph A)°` for the product pairing, which is the same sign convention §30 uses for
`adjointBifun`. Everything topological about `A*` then comes from §14 for free:
`isClosed_polarCone` gives Theorem 39.2's first assertion (proved here directly, to avoid
transporting the pairing instance across `LinearMap.flip`), and `polarCone_polarCone` gives
`A** = cl A`.

## What is not here

* **Theorem 39.4**, the one-to-one correspondence between closed convex processes and the
  saddle-like kernels `K (u, x*) = ⟨Au, x*⟩`. It needs the closure operations of §33 and hence a
  topology, so it lives in `Bifunction/ProcessDuality.lean` with the rest of the layer-B material;
  the two ingredients contributed from this side are listed above.
* The closed halves of **Theorems 39.5 and 39.8** — `A₁ + A₂` and `BA` closed, with the adjoint
  the closure of the sum resp. product of the adjoints. They specialize Corollaries 38.2.1 and
  38.5.1, neither of which is available; see the `What is not here` list in
  `Bifunction/Algebra.lean` for what each is blocked on.
* The closed half of **Theorem 39.7** — `Af` closed, its infimum attained, and
  `(Af)* = cl (A*⁻¹ f*)`. It needs a topology, so it lives in `Bifunction/ProcessDuality.lean`
  with the rest of the layer-B material; the open half is here.
* The infimum-oriented mirrors of Theorems 39.3, 39.5 and 39.8. Rockafellar states each for both
  orientations with "convexity and concavity reversed"; only the supremum-oriented one is here,
  and by gotcha 9 the mirror is not obtainable by `simp`-normalising through negation.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39.
-/

open Pointwise Set

namespace Tdaf.ConvexAnalysis

/-! ### The definition -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- A **convex process** from `U` to `X`: a multivalued map `A : u ↦ Au` with

* `A (u₁ + u₂) ⊇ A u₁ + A u₂`,
* `A (λ u) = λ (A u)` for `λ > 0`,
* `0 ∈ A 0`,

which Rockafellar shows is the same thing as a convex cone in `U × X` containing the origin — that
is, a `PointedCone ℝ (U × X)`, read as a relation. -/
structure ConvexProcess (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X]
    [Module ℝ X] where
  /-- The graph of the process. -/
  graph : PointedCone ℝ (U × X)

namespace ConvexProcess

variable {A : ConvexProcess U X} {u u₁ u₂ : U} {x x₁ x₂ : X}

/-- The value `A u` of the process at `u`: the `u`-slice of its graph. -/
def eval (A : ConvexProcess U X) (u : U) : Set X := {x | (u, x) ∈ A.graph}

@[simp] theorem mem_eval : x ∈ A.eval u ↔ (u, x) ∈ A.graph := Iff.rfl

/-- The graph of a convex process, as a relation. -/
def toSetRel (A : ConvexProcess U X) : SetRel U X := (A.graph : Set (U × X))

@[simp] theorem mem_toSetRel {p : U × X} : p ∈ A.toSetRel ↔ p ∈ A.graph := Iff.rfl

/-- The **effective domain** of a convex process: the `u` at which `A u` is nonempty. -/
def dom (A : ConvexProcess U X) : Set U := {u | (A.eval u).Nonempty}

@[simp] theorem mem_dom : u ∈ A.dom ↔ (A.eval u).Nonempty := Iff.rfl

/-- The **range** of a convex process. -/
def range (A : ConvexProcess U X) : Set X := {x | ∃ u, (u, x) ∈ A.graph}

@[simp] theorem mem_range : x ∈ A.range ↔ ∃ u, (u, x) ∈ A.graph := Iff.rfl

/-- The **image** of a set under a convex process: `A C = ⋃ {A u | u ∈ C}`. -/
def image (A : ConvexProcess U X) (C : Set U) : Set X := {x | ∃ u ∈ C, (u, x) ∈ A.graph}

@[simp] theorem mem_image {C : Set U} : x ∈ A.image C ↔ ∃ u ∈ C, (u, x) ∈ A.graph := Iff.rfl

theorem image_univ (A : ConvexProcess U X) : A.image univ = A.range := by
  ext x; simp

/-- Two convex processes with the same graph are equal. -/
@[ext] theorem ext {A B : ConvexProcess U X} (h : A.graph = B.graph) : A = B := by
  cases A
  cases B
  simp only [ConvexProcess.mk.injEq]
  exact h

/-- A linear transformation, read as a convex process. Its graph is the graph of `T`, a linear
subspace and hence in particular a pointed convex cone. -/
def ofLinearMap (T : U →ₗ[ℝ] X) : ConvexProcess U X where
  graph :=
    { carrier := {p : U × X | p.2 = T p.1}
      zero_mem' := by simp
      add_mem' := by
        rintro ⟨u₁, x₁⟩ ⟨u₂, x₂⟩ h₁ h₂
        simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
        rw [Prod.mk_add_mk, map_add, h₁, h₂]
      smul_mem' := by
        rintro c ⟨u, x⟩ h
        simp only [Set.mem_ofPred_eq] at h ⊢
        change (c : ℝ) • x = T ((c : ℝ) • u)
        rw [map_smul, h] }

@[simp] theorem mem_graph_ofLinearMap {T : U →ₗ[ℝ] X} {p : U × X} :
    p ∈ (ofLinearMap T).graph ↔ p.2 = T p.1 := Iff.rfl

@[simp] theorem eval_ofLinearMap (T : U →ₗ[ℝ] X) (u : U) : (ofLinearMap T).eval u = {T u} := by
  ext x
  simp [eval]

@[simp] theorem dom_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).dom = univ := by
  ext u
  simp

/-- The **inverse** of a convex process, again a convex process. -/
def inv (A : ConvexProcess U X) : ConvexProcess X U where
  graph :=
    { carrier := {p : X × U | (p.2, p.1) ∈ A.graph}
      zero_mem' := A.graph.zero_mem
      add_mem' := fun h₁ h₂ => A.graph.add_mem h₁ h₂
      smul_mem' := fun c _ h => Submodule.smul_mem A.graph c h }

@[simp] theorem mem_graph_inv {p : X × U} : p ∈ A.inv.graph ↔ (p.2, p.1) ∈ A.graph := Iff.rfl

@[simp] theorem mem_eval_inv : u ∈ A.inv.eval x ↔ (u, x) ∈ A.graph := Iff.rfl

theorem inv_inv (A : ConvexProcess U X) : A.inv.inv = A := by
  ext p
  rfl

theorem dom_inv (A : ConvexProcess U X) : A.inv.dom = A.range := by
  ext x
  simp only [mem_dom, mem_range, Set.Nonempty, mem_eval_inv]

theorem range_inv (A : ConvexProcess U X) : A.inv.range = A.dom := by
  ext u
  simp only [mem_range, mem_dom, Set.Nonempty, mem_eval, mem_graph_inv]

/-! ### Elementary structure -/

/-- The graph of a convex process is a convex set. -/
theorem convex_graph (A : ConvexProcess U X) : Convex ℝ (A.graph : Set (U × X)) :=
  ((A.graph : ConvexCone ℝ (U × X))).convex

/-- Membership of a nonnegative multiple, in the form the `PointedCone` coercion hides. -/
theorem smul_mem_graph {a : ℝ} (ha : 0 ≤ a) {p : U × X} (hp : p ∈ A.graph) : a • p ∈ A.graph := by
  have h := Submodule.smul_mem A.graph (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hp
  exact h

theorem add_mem_graph {p q : U × X} (hp : p ∈ A.graph) (hq : q ∈ A.graph) : p + q ∈ A.graph :=
  A.graph.add_mem hp hq

theorem zero_mem_graph (A : ConvexProcess U X) : ((0 : U), (0 : X)) ∈ A.graph :=
  A.graph.zero_mem

@[simp] theorem zero_mem_eval_zero (A : ConvexProcess U X) : (0 : X) ∈ A.eval 0 :=
  A.zero_mem_graph

/-- **Rockafellar, §39**: each value `A u` is a convex set. -/
theorem convex_eval (A : ConvexProcess U X) (u : U) : Convex ℝ (A.eval u) := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab
  have h : a • ((u, x₁) : U × X) + b • (u, x₂) ∈ A.graph :=
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)
  have hfst : (a • ((u, x₁) : U × X) + b • (u, x₂)) = (u, a • x₁ + b • x₂) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hfst] at h

/-- **Rockafellar, §39**: `A 0` is a convex cone containing the origin. -/
theorem smul_mem_eval_zero (A : ConvexProcess U X) {a : ℝ} (ha : 0 ≤ a) (hx : x ∈ A.eval 0) :
    a • x ∈ A.eval 0 := by
  have h := smul_mem_graph ha hx
  rwa [Prod.smul_mk, smul_zero] at h

/-- **Rockafellar, §39**: `A u + A 0 ⊆ A u`, so `A 0` is the set of directions along which every
value of the process is invariant. -/
theorem add_eval_zero_subset (A : ConvexProcess U X) (u : U) :
    A.eval u + A.eval 0 ⊆ A.eval u := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have h : ((u, x) : U × X) + (0, y) ∈ A.graph := add_mem_graph hx hy
  rwa [Prod.mk_add_mk, add_zero] at h

/-- The effective domain of a convex process is a convex cone containing the origin. -/
theorem convex_dom (A : ConvexProcess U X) : Convex ℝ A.dom := by
  rintro u₁ ⟨x₁, h₁⟩ u₂ ⟨x₂, h₂⟩ a b ha hb hab
  exact ⟨a • x₁ + b • x₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

/-- The range of a convex process is convex. -/
theorem convex_range (A : ConvexProcess U X) : Convex ℝ A.range := by
  rintro x₁ ⟨u₁, h₁⟩ x₂ ⟨u₂, h₂⟩ a b ha hb hab
  exact ⟨a • u₁ + b • u₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

/-- **Rockafellar, §39**: the image of a convex set under a convex process is convex. -/
theorem convex_image (A : ConvexProcess U X) {C : Set U} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) := by
  rintro x₁ ⟨u₁, hu₁, h₁⟩ x₂ ⟨u₂, hu₂, h₂⟩ a b ha hb hab
  refine ⟨a • u₁ + b • u₂, hC hu₁ hu₂ ha hb hab, ?_⟩
  simpa [Prod.smul_mk, Prod.mk_add_mk] using
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)

/-- The image `A C` is the projection of `graph A ∩ (C × X)` on the second factor. This is what
turns Corollary 39.7.1 into an instance of Theorem 9.1. -/
theorem image_eq_image_snd (A : ConvexProcess U X) (C : Set U) :
    A.image C = (LinearMap.snd ℝ U X) '' ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) := by
  ext x
  constructor
  · rintro ⟨u, hu, hp⟩
    exact ⟨(u, x), ⟨hp, hu, mem_univ x⟩, rfl⟩
  · rintro ⟨⟨u, z⟩, ⟨hp, hu, -⟩, rfl⟩
    exact ⟨u, hu, hp⟩

end ConvexProcess

end Defs

/-! ### The indicator bifunction -/

section IndicatorInjective

variable {W : Type*}

/-- The indicator function determines its set.

Proof idea: `δ(· | S)` takes the value `0` exactly on `S` and `⊤` off it, and `0 ≠ ⊤` in
`EReal`. -/
theorem indicatorFn_injective : Function.Injective (indicatorFn : Set W → W → EReal) := by
  intro S T h
  ext w
  constructor
  · intro hw
    by_contra hc
    have h0 : indicatorFn S w = 0 := indicatorFn_of_mem hw
    rw [h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)
  · intro hw
    by_contra hc
    have h0 : indicatorFn T w = 0 := indicatorFn_of_mem hw
    rw [← h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)

end IndicatorInjective

section Indicator

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

namespace ConvexProcess

/-- The **indicator bifunction** of a supremum-oriented convex process: `(F u)(x) = δ(x | A u)`.
This is the dictionary entry that makes every result of §39 a result of §38. -/
noncomputable def indicatorBifun (A : ConvexProcess U X) : Bifun U X :=
  fun u => indicatorFn (A.eval u)

theorem indicatorBifun_apply (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x = indicatorFn (A.eval u) x := rfl

/-- The graph function of the indicator bifunction of `A` is the indicator function of the graph
of `A`. -/
@[simp] theorem graphFn_indicatorBifun (A : ConvexProcess U X) :
    graphFn A.indicatorBifun = indicatorFn (A.graph : Set (U × X)) := by
  funext p
  obtain ⟨u, x⟩ := p
  rw [graphFn_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show x ∈ A.eval u from h), indicatorFn_of_mem h]
  · rw [indicatorFn_of_notMem (show x ∉ A.eval u from h), indicatorFn_of_notMem h]

theorem indicatorBifun_ne_bot (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x ≠ ⊥ := indicatorFn_ne_bot _ _

/-- **A convex process is determined by its indicator bifunction.** A process *is* its graph, and
the indicator function of a set determines the set, so this is `indicatorFn_injective` read through
`graphFn_indicatorBifun`. It is what makes the correspondence of Theorem 39.4 one-to-one. -/
theorem indicatorBifun_injective :
    Function.Injective (indicatorBifun : ConvexProcess U X → Bifun U X) := by
  intro A₁ A₂ h
  refine ConvexProcess.ext (SetLike.ext' (indicatorFn_injective ?_))
  rw [← graphFn_indicatorBifun, ← graphFn_indicatorBifun, h]

/-- **Rockafellar, §39**: the indicator bifunction of a convex process is convex. -/
theorem convexBifun_indicatorBifun (A : ConvexProcess U X) : ConvexBifun A.indicatorBifun := by
  rw [convexBifun_iff, graphFn_indicatorBifun]
  exact convexFn_indicatorFn.2 A.convex_graph

/-- **Rockafellar, §39**: `dom F = dom A`. -/
@[simp] theorem domBifun_indicatorBifun (A : ConvexProcess U X) :
    domBifun A.indicatorBifun = A.dom := by
  ext u
  simp only [mem_domBifun, mem_dom, Set.Nonempty, indicatorBifun_apply]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    by_contra h
    exact hx (indicatorFn_of_notMem h)
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [indicatorFn_of_mem hx]; simp⟩

/-- Positive multiples do not move the graph of a convex process: it is a cone. -/
theorem smul_graph (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) :
    a • (A.graph : Set (U × X)) = (A.graph : Set (U × X)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem_graph ha.le hq
  · intro hp
    refine ⟨a⁻¹ • p, smul_mem_graph (inv_nonneg.2 ha.le) hp, ?_⟩
    change a • a⁻¹ • p = p
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- **Rockafellar, §39**, axiom (b): `A (λ u) = λ (A u)` for `λ > 0`.

Both inclusions are one application of `smul_mem_graph`, to `a` and to `a⁻¹`: a cone is stable
under *both* directions of a positive scaling, which is what turns the inclusion Rockafellar's
axiom would give into an equality. -/
theorem eval_smul_arg (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) (u : U) :
    A.eval (a • u) = a • A.eval u := by
  ext x
  constructor
  · intro hx
    have hmem : ((u, a⁻¹ • x) : U × X) ∈ A.graph := by
      have h := smul_mem_graph (A := A) (inv_nonneg.2 ha.le) hx
      rwa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
    have hval : a • a⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact ⟨a⁻¹ • x, hmem, hval⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : a • z = x := hzx
    have h := smul_mem_graph (A := A) ha.le (show ((u, z) : U × X) ∈ A.graph from hz)
    rw [Prod.smul_mk, hzx'] at h
    exact h

end ConvexProcess

end Indicator

/-! ### The algebra of convex processes, and its bifunction dictionary -/

section Algebra

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

omit [Module ℝ X] in
/-- The infimal convolute of two indicator functions is the indicator function of the sum of the
sets. Rockafellar makes this observation in §5; `Operations/InfConv.lean` has only the special case
of a singleton, so it is proved here. -/
theorem infConv_indicatorFn (S T : Set X) :
    infConv (indicatorFn S) (indicatorFn T) = indicatorFn (S + T) := by
  have hepi : epi (indicatorFn S) + epi (indicatorFn T) = epi (indicatorFn (S + T)) := by
    rw [epi_indicatorFn, epi_indicatorFn, epi_indicatorFn]
    ext p
    constructor
    · rintro ⟨q, ⟨hq, hq0⟩, r, ⟨hr, hr0⟩, rfl⟩
      exact ⟨⟨q.1, hq, r.1, hr, rfl⟩,
        Set.mem_Ici.2 (add_nonneg (Set.mem_Ici.1 hq0) (Set.mem_Ici.1 hr0))⟩
    · rintro ⟨hw, hc⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hw
      refine ⟨(a, p.2), ⟨ha, hc⟩, (b, 0), ⟨hb, Set.mem_Ici.2 (le_refl 0)⟩, ?_⟩
      have hab2 : a + b = p.1 := hab
      change ((a, p.2) : X × ℝ) + (b, 0) = p
      rw [Prod.mk_add_mk, hab2, add_zero]
  rw [infConv_def, hepi, ofEpi_epi]

namespace ConvexProcess

/-- **Rockafellar, §39**: the **sum** of two convex processes, `(A₁ + A₂) u = A₁ u + A₂ u`. -/
instance : Add (ConvexProcess U X) where
  add A₁ A₂ :=
    { graph :=
        { carrier := {p : U × X | ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y}
          zero_mem' := ⟨0, A₁.zero_mem_eval_zero, 0, A₂.zero_mem_eval_zero, (add_zero 0).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, y₁, k₁, rfl⟩ ⟨x₂, h₂, y₂, k₂, rfl⟩
            exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, y₁ + y₂, add_mem_graph k₁ k₂,
              add_add_add_comm x₁ y₁ x₂ y₂⟩
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, hx, y, hy, rfl⟩
            exact ⟨(c : ℝ) • x, smul_mem_graph c.2 hx, (c : ℝ) • y, smul_mem_graph c.2 hy,
              smul_add (c : ℝ) x y⟩ } }

@[simp] theorem mem_graph_add {A₁ A₂ : ConvexProcess U X} {p : U × X} :
    p ∈ (A₁ + A₂).graph ↔ ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y := Iff.rfl

@[simp] theorem eval_add (A₁ A₂ : ConvexProcess U X) (u : U) :
    (A₁ + A₂).eval u = A₁.eval u + A₂.eval u := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- **Rockafellar, §39**: `dom (A₁ + A₂) = dom A₁ ∩ dom A₂`. -/
@[simp] theorem dom_add (A₁ A₂ : ConvexProcess U X) : (A₁ + A₂).dom = A₁.dom ∩ A₂.dom := by
  ext u
  constructor
  · rintro ⟨_, x, hx, y, hy, -⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x + y, x, hx, y, hy, rfl⟩

/-- **Rockafellar, §39**: the **scalar multiple** `λ A`, defined by `(λ A) u = λ (A u)`.

The graph `{(u, λ x) | (u, x) ∈ graph A}` is a pointed convex cone for *every* real `λ`, so the
definition needs no positivity; Rockafellar's `λ > 0` is needed only from Theorem 39.6 on, where
the inverse scaling is used. The action is a `MulAction` — `1 • A = A` and `(ab) • A = a • (b • A)`
both hold — but it is not additive: `2 • A` and `A + A` differ. -/
instance : SMul ℝ (ConvexProcess U X) where
  smul a A :=
    { graph :=
        { carrier := {p : U × X | ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x}
          zero_mem' := ⟨0, A.zero_mem_graph, (smul_zero a).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, hz₁⟩ ⟨x₂, h₂, hz₂⟩
            refine ⟨x₁ + x₂, add_mem_graph h₁ h₂, ?_⟩
            have hz₁' : z₁ = a • x₁ := hz₁
            have hz₂' : z₂ = a • x₂ := hz₂
            change z₁ + z₂ = a • (x₁ + x₂)
            rw [smul_add, hz₁', hz₂']
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, h, hz⟩
            refine ⟨(c : ℝ) • x, smul_mem_graph c.2 h, ?_⟩
            have hz' : z = a • x := hz
            change (c : ℝ) • z = a • (c : ℝ) • x
            rw [hz', smul_comm] } }

@[simp] theorem mem_graph_smul {a : ℝ} {A : ConvexProcess U X} {p : U × X} :
    p ∈ (a • A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x := Iff.rfl

/-- **Rockafellar, §39**: `(λ A) u = λ (A u)`, the defining equation of the scalar multiple. -/
@[simp] theorem eval_smul (a : ℝ) (A : ConvexProcess U X) (u : U) :
    (a • A).eval u = a • A.eval u := by
  ext x
  constructor
  · rintro ⟨z, hz, hx⟩
    have hx' : x = a • z := hx
    exact ⟨z, hz, hx'.symm⟩
  · rintro ⟨z, hz, hx⟩
    have hx' : a • z = x := hx
    exact ⟨z, hz, hx'.symm⟩

/-- **Rockafellar, §39**: the **product** of convex processes, `(B A) u = B (A u)`. -/
def comp (B : ConvexProcess X Z) (A : ConvexProcess U X) : ConvexProcess U Z where
  graph :=
    { carrier := {p : U × Z | ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph}
      zero_mem' := ⟨0, A.zero_mem_graph, B.zero_mem_graph⟩
      add_mem' := by
        rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, k₁⟩ ⟨x₂, h₂, k₂⟩
        exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, add_mem_graph k₁ k₂⟩
      smul_mem' := by
        rintro c ⟨u, z⟩ ⟨x, h, k⟩
        exact ⟨(c : ℝ) • x, smul_mem_graph c.2 h, smul_mem_graph c.2 k⟩ }

@[simp] theorem mem_graph_comp {B : ConvexProcess X Z} {A : ConvexProcess U X} {p : U × Z} :
    p ∈ (B.comp A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph := Iff.rfl

@[simp] theorem eval_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) (u : U) :
    (B.comp A).eval u = B.image (A.eval u) := by
  ext z
  exact Iff.rfl

/-- **Rockafellar, §39**: `(B A)⁻¹ = A⁻¹ B⁻¹`. -/
theorem inv_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).inv = A.inv.comp B.inv := by
  ext p
  constructor <;> rintro ⟨x, h, k⟩ <;> exact ⟨x, k, h⟩

/-- **Rockafellar, §39**: the indicator bifunction of `A₁ + A₂` is `F₁ □ F₂` (Theorem 38.1). -/
theorem indicatorBifun_add (A₁ A₂ : ConvexProcess U X) :
    (A₁ + A₂).indicatorBifun = infConvBifun A₁.indicatorBifun A₂.indicatorBifun := by
  funext u
  change indicatorFn ((A₁ + A₂).eval u)
    = infConv (indicatorFn (A₁.eval u)) (indicatorFn (A₂.eval u))
  rw [eval_add, infConv_indicatorFn]

/-- **Rockafellar, §39**: the indicator bifunction of `B A` is `G F` (Theorem 38.5). -/
theorem indicatorBifun_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).indicatorBifun = compBifun B.indicatorBifun A.indicatorBifun := by
  funext u z
  rw [compBifun_apply]
  by_cases h : z ∈ (B.comp A).eval u
  · rw [indicatorBifun_apply, indicatorFn_of_mem h]
    obtain ⟨x₀, hx₀, hz₀⟩ := h
    symm
    refine le_antisymm ?_ (le_iInf fun x => ?_)
    · refine le_of_le_of_eq (iInf_le _ x₀) ?_
      rw [indicatorBifun_apply, indicatorFn_of_mem (show x₀ ∈ A.eval u from hx₀),
        indicatorBifun_apply, indicatorFn_of_mem (show z ∈ B.eval x₀ from hz₀), add_zero]
    · refine add_nonneg ?_ ?_
      · rw [indicatorBifun_apply]
        by_cases hx : x ∈ A.eval u <;> simp [hx]
      · rw [indicatorBifun_apply]
        by_cases hz : z ∈ B.eval x <;> simp [hz]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem h]
    symm
    refine le_antisymm le_top (le_iInf fun x => ?_)
    by_cases hx : x ∈ A.eval u
    · have hz : z ∉ B.eval x := fun hc => h ⟨x, hx, hc⟩
      rw [indicatorBifun_apply, indicatorFn_of_mem hx, indicatorBifun_apply,
        indicatorFn_of_notMem hz, zero_add]
    · rw [indicatorBifun_apply, indicatorFn_of_notMem hx]
      by_cases hz : z ∈ B.eval x
      · rw [indicatorBifun_apply, indicatorFn_of_mem hz, add_zero]
      · rw [indicatorBifun_apply, indicatorFn_of_notMem hz]
        simp

end ConvexProcess

end Algebra

/-! ### Theorem 39.2: the adjoint of a convex process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {A : ConvexProcess U X}

namespace ConvexProcess

/-- The **adjoint** of a supremum-oriented convex process:
`A* x* = {u* | ⟨u, u*⟩ ≥ ⟨x, x*⟩ for every x ∈ A u and every u}`. It is a convex process from `Y`
to `V`, and it is infimum oriented. -/
def adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2}
      zero_mem' := by
        intro p _
        change Bx p.2 (0 : Y) ≤ Bu p.1 (0 : V)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bx p.2 (y₁ + y₂) ≤ Bu p.1 (v₁ + v₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bx p.2 ((c : ℝ) • y) ≤ Bu p.1 ((c : ℝ) • v)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

/-- The **adjoint of an infimum-oriented convex process**: the same definition with the inequality
reversed. Keeping the two apart is what makes `A** = cl A` come out right. -/
def coadjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1}
      zero_mem' := by
        intro p _
        change Bu p.1 (0 : V) ≤ Bx p.2 (0 : Y)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bu p.1 (v₁ + v₂) ≤ Bx p.2 (y₁ + y₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bu p.1 ((c : ℝ) • v) ≤ Bx p.2 ((c : ℝ) • y)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

@[simp] theorem mem_graph_adjointProcess {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2 :=
  Iff.rfl

@[simp] theorem mem_graph_coadjointProcess {q : Y × V} :
    q ∈ (coadjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1 :=
  Iff.rfl

@[simp] theorem mem_eval_adjointProcess {y : Y} {v : V} :
    v ∈ (adjointProcess Bu Bx A).eval y ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 y ≤ Bu p.1 v :=
  Iff.rfl

/-- The graph of `A*` is the polar of the graph of `A`, up to the sign flip on the first factor
that all of §30 carries. -/
theorem mem_graph_adjointProcess_iff_mem_polarCone {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔
      ((-q.2, q.1) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X)) := by
  simp only [mem_graph_adjointProcess, mem_polarCone, prodPairing_apply, map_neg,
    SetLike.mem_coe]
  constructor
  · intro h p hp
    have := h p hp
    linarith
  · intro h p hp
    have := h p hp
    linarith

/-- **Rockafellar, Theorem 39.2**, last assertion: the adjoint of the indicator bifunction of `A`
is the indicator bifunction of `A*`. `A*` carries the opposite orientation, which is why the
indicator appears negated: an infimum-oriented set is identified with `-δ(· | ·)`. -/
theorem adjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) (v : V) :
    adjointBifun Bu Bx A.indicatorBifun y v = -((adjointProcess Bu Bx A).indicatorBifun y v) := by
  rw [adjointBifun_eq_neg_conj_graphFn, graphFn_indicatorBifun,
    conj_indicatorFn_eq_indicatorFn_polarCone (fun a ha => A.smul_graph ha)
      ⟨0, A.zero_mem_graph⟩]
  congr 1
  by_cases h : ((-v, y) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))
  · rw [indicatorFn_of_mem h, indicatorBifun_apply,
      indicatorFn_of_mem (show v ∈ (adjointProcess Bu Bx A).eval y from
        mem_graph_adjointProcess_iff_mem_polarCone.2 h)]
  · rw [indicatorFn_of_notMem h, indicatorBifun_apply,
      indicatorFn_of_notMem (show v ∉ (adjointProcess Bu Bx A).eval y from fun hc =>
        h (mem_graph_adjointProcess_iff_mem_polarCone.1 hc))]

/-- The graph of `A**` is the bipolar of the graph of `A`. The two sign flips cancel, which is why
the second adjoint must be the *infimum-oriented* one. -/
theorem graph_coadjointProcess_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = polarCone (prodPairing Bu Bx).flip
          (polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))) := by
  ext q
  simp only [SetLike.mem_coe, mem_graph_coadjointProcess, mem_polarCone, LinearMap.flip_apply,
    prodPairing_apply]
  constructor
  · rintro h ⟨a, b⟩ hab
    have hmem : ((b, -a) : Y × V) ∈ (adjointProcess Bu Bx A).graph :=
      mem_graph_adjointProcess_iff_mem_polarCone.2 (by simpa using hab)
    have hb := h (b, -a) hmem
    simp only [map_neg] at hb
    linarith
  · rintro h ⟨y, v⟩ hyv
    have hmem := mem_graph_adjointProcess_iff_mem_polarCone.1 hyv
    have hb := h (-v, y) hmem
    simp only [map_neg] at hb
    linarith

/-- Dividing an inequality by a positive real, as an iff. Used twice in Theorem 39.6, once in each
direction of the set equality. -/
private theorem mul_le_iff_le_inv_mul {a : ℝ} (ha : 0 < a) (r s : ℝ) :
    a * r ≤ s ↔ r ≤ a⁻¹ * s := by
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha.le)
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · intro h
    have h' := mul_le_mul_of_nonneg_left h ha.le
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

/-- The mirror of `mul_le_iff_le_inv_mul`, for the infimum-oriented adjoint. -/
private theorem le_mul_iff_inv_mul_le {a : ℝ} (ha : 0 < a) (r s : ℝ) :
    s ≤ a * r ↔ a⁻¹ * s ≤ r := by
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha.le)
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · intro h
    have h' := mul_le_mul_of_nonneg_left h ha.le
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

/-- **Rockafellar, Theorem 39.6**: `(λ A)* = λ (A*)` for `λ > 0`.

Rockafellar deduces this from Theorem 38.3, the adjoint formula for `Fλ`. It is cheaper here as a
direct computation on cones: `(y, v) ∈ graph (λA)*` says `λ⟨x, y⟩ ≤ ⟨u, v⟩` on `graph A`, which is
`(y, λ⁻¹ v) ∈ graph A*` after dividing by `λ`, and that is exactly `v ∈ λ (A* y)`. Positivity of
`λ` is used only to divide. -/
theorem adjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    adjointProcess Bu Bx (a • A) = a • adjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_adjointProcess, mem_graph_smul]
  constructor
  · intro h
    refine ⟨a⁻¹ • q.2, fun p hp => ?_, ?_⟩
    · have hmem : ((p.1, a • p.2) : U × X) ∈ (a • A).graph := ⟨p.2, hp, rfl⟩
      have h' := h (p.1, a • p.2) hmem
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h' ⊢
      exact (mul_le_iff_le_inv_mul ha _ _).1 h'
    · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨w, hw, hv⟩ p ⟨x, hx, hz⟩
    have hz' : p.2 = a • x := hz
    have hv' : q.2 = a • w := hv
    have hle := hw (p.1, x) hx
    rw [hz', hv']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hle ha.le

/-- **Rockafellar, Theorem 39.6** for an infimum-oriented process: `(λ A)* = λ (A*)`, with the
adjoint taken in the reversed sense. The proof is `adjointProcess_smul` with both inequalities
turned round. -/
theorem coadjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    coadjointProcess Bu Bx (a • A) = a • coadjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_coadjointProcess, mem_graph_smul]
  constructor
  · intro h
    refine ⟨a⁻¹ • q.2, fun p hp => ?_, ?_⟩
    · have hmem : ((p.1, a • p.2) : U × X) ∈ (a • A).graph := ⟨p.2, hp, rfl⟩
      have h' := h (p.1, a • p.2) hmem
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h' ⊢
      exact (le_mul_iff_inv_mul_le ha _ _).1 h'
    · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨w, hw, hv⟩ p ⟨x, hx, hz⟩
    have hz' : p.2 = a • x := hz
    have hv' : q.2 = a • w := hv
    have hle := hw (p.1, x) hx
    rw [hz', hv']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hle ha.le

end ConvexProcess

end Adjoint

/-! ### Theorem 39.2: `A*` is closed, and `A** = cl A` -/

section AdjointTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

section Closed

variable [TopologicalSpace V] [TopologicalSpace Y]

/-- **Rockafellar, Theorem 39.2**, first assertion: the adjoint of a convex process is a *closed*
convex process, being an intersection of homogeneous closed half-spaces. -/
theorem isClosed_graph_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] [IsContinuousPairing Bx.flip] (A : ConvexProcess U X) :
    IsClosed ((adjointProcess Bu Bx A).graph : Set (Y × V)) := by
  have h : ((adjointProcess Bu Bx A).graph : Set (Y × V))
      = ⋂ p ∈ (A.graph : Set (U × X)), {q : Y × V | Bx p.2 q.1 ≤ Bu p.1 q.2} := by
    ext q
    simp [mem_graph_adjointProcess]
  rw [h]
  refine isClosed_biInter fun p _ => isClosed_le ?_ ?_
  · exact (continuous_pairing Bx.flip p.2).comp continuous_fst
  · exact (continuous_pairing Bu.flip p.1).comp continuous_snd

end Closed

section Bipolar

variable [TopologicalSpace U] [TopologicalSpace X] [IsTopologicalAddGroup U]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ U] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ U]
  [LocallyConvexSpace ℝ X]

/-- **Rockafellar, Theorem 39.2**, second assertion: `A** = cl A`. Read through
`graph_coadjointProcess_adjointProcess`, this is exactly the bipolar theorem `K°° = cl K`
(Theorem 14.1) for the graph. -/
theorem graph_coadjointProcess_adjointProcess_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = closure (A.graph : Set (U × X)) := by
  rw [graph_coadjointProcess_adjointProcess]
  exact polarCone_polarCone A.convex_graph (fun a ha => A.smul_graph ha) ⟨0, A.zero_mem_graph⟩

/-- **Rockafellar, Theorem 39.2**: a convex process is closed exactly when it is its own second
adjoint. -/
theorem coadjointProcess_adjointProcess_eq_self_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A) = A ↔
      IsClosed (A.graph : Set (U × X)) := by
  constructor
  · intro h
    rw [← closure_eq_iff_isClosed,
      ← graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h]
  · intro h
    refine ConvexProcess.ext (SetLike.ext' ?_)
    rw [graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h.closure_eq]

end Bipolar

end ConvexProcess

end AdjointTopology

/-! ### Theorem 39.3: the two inner products

`⟨Au, x*⟩` is §33's bracket of the indicator bifunction of `A`, and `⟨u, A* x*⟩` is the concave
bracket of its adjoint. Both are ordinary extremum problems over the values of a process: a
maximisation of `⟨·, x*⟩` over `A u`, and a minimisation of `⟨u, ·⟩` over `A* x*`. -/

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**: the inner product `⟨Au, x*⟩` is the **support function** of the
convex set `A u`. Every clause of Theorem 39.3 about the `x*` variable is a property of support
functions, cited from §13; the identity itself is `supportFn_eq_conj_indicatorFn` read backwards,
since `⟨Fu, ·⟩` is by definition the conjugate of `F u = δ(· | A u)`. -/
theorem bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    bracket Bx A.indicatorBifun u = supportFn Bx (A.eval u) :=
  (supportFn_eq_conj_indicatorFn Bx (A.eval u)).symm

/-- The first of Rockafellar's two extremum problems: `⟨Au, x*⟩ = sup {⟨x, x*⟩ | x ∈ A u}`. -/
theorem bracket_indicatorBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : bracket Bx A.indicatorBifun u y = ⨆ x ∈ A.eval u, ((Bx x y : ℝ) : EReal) := by
  rw [bracket_indicatorBifun, supportFn_apply]

/-- **Rockafellar, Theorem 39.3**: `⟨Au, ·⟩` is positively homogeneous, being a support
function. -/
theorem posHomogeneous_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (u : U) : PosHomogeneous (bracket Bx A.indicatorBifun u) := by
  rw [bracket_indicatorBifun]
  exact posHomogeneous_supportFn Bx _

/-- **Rockafellar, Theorem 39.3**: `⟨Au, ·⟩` is convex, being a conjugate. -/
theorem convexFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    ConvexFn (bracket Bx A.indicatorBifun u) :=
  convexFn_bracket Bx A.indicatorBifun u

/-- **Rockafellar, Theorem 39.3**: `⟨A ·, x*⟩` is positively homogeneous. This is the one clause
that uses the definition of a convex process rather than §33: `A (λ u) = λ (A u)` is axiom (b)
(`eval_smul_arg`), and the support function of a positive multiple of a set is the corresponding
multiple of the support function. -/
theorem posHomogeneous_bracket_indicatorBifun_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) :
    PosHomogeneous fun u => bracket Bx A.indicatorBifun u y := by
  intro a ha u
  change bracket Bx A.indicatorBifun (a • u) y = (a : EReal) * bracket Bx A.indicatorBifun u y
  rw [bracket_indicatorBifun, bracket_indicatorBifun, eval_smul_arg A ha, supportFn_smul Bx ha]

/-- **Rockafellar, Theorem 39.3**: `⟨A ·, x*⟩` is concave. This is Theorem 33.1 for the indicator
bifunction, which is convex. -/
theorem concaveFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (y : Y) : ConcaveFn fun u => bracket Bx A.indicatorBifun u y :=
  concaveFn_bracket A.convexBifun_indicatorBifun Bx y

/-- **Rockafellar, Theorem 39.4**, the normalisation `K (0, 0) = 0`: the inner product `⟨Au, x*⟩`
vanishes at the origin, because `A 0` contains `0` and the support function of a nonempty set is
`0` at `0`. -/
@[simp] theorem bracket_indicatorBifun_zero_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) : bracket Bx A.indicatorBifun 0 (0 : Y) = 0 := by
  rw [bracket_indicatorBifun]
  exact supportFn_zero ⟨0, A.zero_mem_eval_zero⟩

end ConvexProcess

end Bracket

section BracketClosed

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsContinuousPairing Bx.flip]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**: `⟨Au, ·⟩` is closed as well as convex and positively
homogeneous. -/
theorem closedFn_bracket_indicatorBifun (A : ConvexProcess U X) (u : U) :
    ClosedFn (bracket Bx A.indicatorBifun u) :=
  closedFn_bracket (F := A.indicatorBifun) u

end ConvexProcess

end BracketClosed

section ConcaveBracket

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The second of Rockafellar's two extremum problems: `⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}`.

Together with `bracket_indicatorBifun_apply` this is the pair of linear programs displayed after
Theorem 39.4, whose values agree "usually" by Theorem 39.3. The proof is the definition of the
concave bracket plus `adjointBifun_indicatorBifun` (Theorem 39.2): the indicator of `A* x*` turns
the unrestricted infimum into a restricted one. -/
theorem concaveBracket_adjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y
      = ⨅ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal) := by
  rw [concaveBracket_apply]
  refine iInf_congr fun v => ?_
  rw [adjointBifun_indicatorBifun]
  by_cases hv : v ∈ (adjointProcess Bu Bx A).eval y
  · rw [indicatorBifun_apply, indicatorFn_of_mem hv, neg_zero, sub_zero, iInf_pos hv]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem hv, iInf_neg hv]
    simp

end ConvexProcess

end ConcaveBracket

section ConcaveBracketClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.3**, third assertion: `⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`.

The concave closure in the first variable is the *only* difference between the two inner products,
for every convex process — closedness of `A` plays no part. This is Theorem 33.2's first equation
(`concaveBracket_adjointBifun_eq_partialCl₁`) applied to the indicator bifunction. -/
theorem concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁ (A : ConvexProcess U X) (y : Y) :
    (fun u => concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2) (u, y) :=
  concaveBracket_adjointBifun_eq_partialCl₁ A.convexBifun_indicatorBifun y

end ConvexProcess

end ConcaveBracketClosure

/-! ### Theorem 39.5: the adjoint of a sum -/

section SupConvIndicator

variable {X : Type*} [AddCommGroup X]

/-- The concave mirror of `infConv_indicatorFn`: the supremal convolute of two *negated* indicator
functions is the negated indicator function of the sum of the sets. Infimum-oriented convex sets
are carried by `-δ(· | ·)` (see `ConvexProcess.adjointBifun_indicatorBifun`), so this is the form
in which Theorem 38.2 speaks about processes.

Proof idea: `supConv` is `infConv` conjugated by negation, so the two negations inside cancel and
`infConv_indicatorFn` applies verbatim. -/
theorem supConv_neg_indicatorFn (S T : Set X) :
    supConv (fun x => -(indicatorFn S x)) (fun x => -(indicatorFn T x))
      = fun x => -(indicatorFn (S + T) x) := by
  funext x
  change -(infConv (fun w => -(-(indicatorFn S w))) (fun w => -(-(indicatorFn T w))) x) = _
  simp only [neg_neg]
  rw [infConv_indicatorFn]

end SupConvIndicator

section Thm395

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.5**: `(A₁ + A₂)* = A₁* + A₂*`.

Proof idea: pass to indicator bifunctions. `(A₁ + A₂)` has indicator bifunction `F₁ □ F₂`
(`indicatorBifun_add`, Theorem 38.1), Theorem 38.2 (`adjointBifun_infConvBifun`) turns its adjoint
into the supremal convolute of the two adjoints, and `adjointBifun_indicatorBifun` (Theorem 39.2)
identifies each of those with `-δ(· | Aᵢ* y)`. `supConv_neg_indicatorFn` collapses the supremal
convolute to `-δ(· | A₁* y + A₂* y)`, and `indicatorFn_injective` reads off the sets. Since a
convex process is determined by its values, that is the theorem.

The hypothesis is Rockafellar's relative-interior condition in `IsExactSum` form, one instance per
`y` — the support functions `u ↦ ⟨A₁ u, y⟩` and `u ↦ ⟨A₂ u, y⟩` are the two concave functions of
`u` whose sum must be conjugated exactly (Theorem 16.4). -/
theorem adjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A₁ A₂ : ConvexProcess U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(supportFn Bx (A₁.eval u) y))
      (fun u => -(supportFn Bx (A₂.eval u) y))) :
    adjointProcess Bu Bx (A₁ + A₂) = adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂ := by
  have hex' : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx A₁.indicatorBifun u y))
      (fun u => -(bracket Bx A₂.indicatorBifun u y)) := by
    intro y
    have e₁ : (fun u => -(bracket Bx A₁.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₁.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₁ u) y)
    have e₂ : (fun u => -(bracket Bx A₂.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₂.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₂ u) y)
    rw [e₁, e₂]
    exact hex y
  have key : ∀ y : Y, (adjointProcess Bu Bx (A₁ + A₂)).eval y
      = (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂).eval y := by
    intro y
    have hL : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = adjointBifun Bu Bx (A₁ + A₂).indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx (A₁ + A₂) y v).symm
    have hR₁ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y) v))
        = adjointBifun Bu Bx A₁.indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx A₁ y v).symm
    have hR₂ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₂).eval y) v))
        = adjointBifun Bu Bx A₂.indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx A₂ y v).symm
    have heq : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y
            + (adjointProcess Bu Bx A₂).eval y) v) := by
      rw [hL, ← supConv_neg_indicatorFn, hR₁, hR₂, indicatorBifun_add]
      exact adjointBifun_infConvBifun Bu Bx _ _ (hex' y)
    have hsets : (adjointProcess Bu Bx (A₁ + A₂)).eval y
        = (adjointProcess Bu Bx A₁).eval y + (adjointProcess Bu Bx A₂).eval y :=
      indicatorFn_injective (funext fun v => neg_injective (congrFun heq v))
    rw [hsets, eval_add]
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  obtain ⟨y, v⟩ := q
  rw [← mem_eval, ← mem_eval, key y]

end ConvexProcess

end Thm395

/-! ### Theorem 39.8: the adjoint of a product -/

section Sandwich

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **A linear sandwich.** If a concave `p` lies below a convex `q`, the two add exactly, and each
straddles `0` at the origin from its own side, then some `⟨·, y⟩` runs between them.

This is Fenchel's duality theorem read at a *positively homogeneous* pair. The two extrema are
`p*(y) ≤ 0` and `q*(y) ≥ 0` for free, so the attained dual value `p*(y) - q*(y) ≥ 0` forces both to
vanish, and `p*(y) = 0` and `q*(y) = 0` say precisely `p ≤ ⟨·, y⟩` and `⟨·, y⟩ ≤ q`. No convexity
hypothesis appears: `IsExactSum` already carries it. -/
theorem exists_pairing_sandwich {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {p q : E → EReal}
    (hex : IsExactSum B q fun x => -(p x)) (hle : ∀ x, p x ≤ q x)
    (hp0 : (0 : EReal) ≤ p 0) (hq0 : q 0 ≤ 0) :
    ∃ y : F, (∀ x, p x ≤ ((B x y : ℝ) : EReal)) ∧ ∀ x, ((B x y : ℝ) : EReal) ≤ q x := by
  have hex' : IsExactSum B q (-p) := hex
  have hqnb : ∀ x, q x ≠ ⊥ := hex'.proper_left.ne_bot
  have hpnt : ∀ x, p x ≠ ⊤ := fun x hx => hex'.proper_right.ne_bot x (by simp [hx])
  have hinf : (0 : EReal) ≤ ⨅ x, q x - p x := by
    refine le_iInf fun x => ?_
    rw [_root_.EReal.le_sub_iff_add_le (.inr (hqnb x)) (.inl (hpnt x)), zero_add]
    exact hle x
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq (B := B) hex'
  have hcc_le : concaveConj B p y ≤ 0 := by
    have h := concaveConj_le_sub B p 0 y
    simp only [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero] at h
    refine h.trans ?_
    have hz : (0 : EReal) - p 0 = -(p 0) := zero_add _
    rw [hz]
    exact _root_.EReal.neg_le.2 (by rw [neg_zero]; exact hp0)
  have hconj_ge : (0 : EReal) ≤ conj B q y := by
    have h := sub_le_conj B q 0 y
    simp only [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero] at h
    refine le_trans ?_ h
    have hz : (0 : EReal) - q 0 = -(q 0) := zero_add _
    rw [hz]
    exact _root_.EReal.le_neg.2 (by rw [neg_zero]; exact hq0)
  have hbne : conj B q y ≠ ⊥ := by
    intro h
    rw [h] at hconj_ge
    exact absurd hconj_ge (by simp)
  have hcne : concaveConj B p y ≠ ⊤ := by
    intro h
    rw [h] at hcc_le
    exact absurd hcc_le (by simp)
  have hkey : conj B q y ≤ concaveConj B p y := by
    have h0 : (0 : EReal) ≤ concaveConj B p y - conj B q y := by rw [hy]; exact hinf
    rwa [_root_.EReal.le_sub_iff_add_le (.inl hbne) (.inr hcne), zero_add] at h0
  refine ⟨y, fun x => ?_, fun x => ?_⟩
  · have hmem : ((0 : ℝ) : EReal) ≤ concaveConj B p y := by
      rw [_root_.EReal.coe_zero]
      exact hconj_ge.trans hkey
    have h3 := coe_le_concaveConj_iff.1 hmem x
    rwa [affineFn_apply, _root_.EReal.coe_zero, sub_zero] at h3
  · have hmem : conj B q y ≤ ((0 : ℝ) : EReal) := by
      rw [_root_.EReal.coe_zero]
      exact hkey.trans hcc_le
    have h3 := conj_le_coe_iff.1 hmem x
    rwa [affineFn_apply, _root_.EReal.coe_zero, sub_zero] at h3

end Sandwich

section Thm398

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]

namespace ConvexProcess

/-- **Rockafellar, Theorem 39.8**, the inclusion that costs nothing: `A* B* ⊆ (BA)*`.

A pair `(z*, u*)` that factors through `B*` and then `A*` chains the two defining inequalities,
`⟨z, z*⟩ ≤ ⟨x, x*⟩ ≤ ⟨u, u*⟩`, for every factorisation `u ↦ x ↦ z` in `BA`. -/
theorem comp_adjointProcess_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z) :
    ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B)).graph
      ≤ (adjointProcess Bu Bz (B.comp A)).graph := by
  rintro ⟨w, v⟩ ⟨y, hwy, hyv⟩ ⟨u, z⟩ ⟨x, hux, hxz⟩
  exact le_trans (hwy (x, z) hxz) (hyv (u, x) hux)

/-- **Rockafellar, Theorem 39.8**: `(BA)* = A* B*`.

Rockafellar deduces this from Theorem 38.5's adjoint formula for a product of bifunctions, which
the library does not have. Proved directly it is a *sandwich*: `(x*, u*) ∈ (BA)*` says that the
concave function `x ↦ ⟨Bx, z*⟩` lies below the convex function `x ↦ ⟨u*, A⁻¹x⟩`, and a
factorisation through `A*` and `B*` is exactly a linear functional `⟨·, x*⟩` running between them.
`exists_pairing_sandwich` produces one from Fenchel's duality theorem; both functions are
positively homogeneous and straddle `0` at the origin, which is what turns the attained dual value
into the two inequalities.

The hypothesis is Rockafellar's `ri (range A) ∩ ri (dom B) ≠ ∅` in `IsExactSum` form, one instance
per `(z*, u*)`: the two effective domains involved *are* `range A` and `dom B`. As for Theorem
39.5, the exactness is taken as the hypothesis rather than derived; `IsExactSum.of_relint` no longer
demands closed summands, so the derivation is available and simply has not been done. -/
theorem adjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z)
    (hex : ∀ (w : W) (v : V), IsExactSum Bx
      (fun x => ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal)))) :
    adjointProcess Bu Bz (B.comp A)
      = (adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨w, v⟩ := r
  refine ⟨fun hr => ?_, fun hr => comp_adjointProcess_le Bu Bx Bz A B hr⟩
  have hle : ∀ x : X, (⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal))
      ≤ ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal) := by
    intro x
    refine iSup₂_le fun z hz => le_iInf₂ fun u hu => ?_
    exact_mod_cast hr (u, z) ⟨x, hu, hz⟩
  have hp0 : (0 : EReal) ≤ ⨆ z ∈ B.eval (0 : X), ((Bz z w : ℝ) : EReal) :=
    le_iSup₂_of_le (0 : Z) B.zero_mem_eval_zero (by simp)
  have hq0 : (⨅ u ∈ A.inv.eval (0 : X), ((Bu u v : ℝ) : EReal)) ≤ 0 :=
    iInf₂_le_of_le (0 : U) A.inv.zero_mem_eval_zero (by simp)
  obtain ⟨y, hpy, hqy⟩ := exists_pairing_sandwich (hex w v) hle hp0 hq0
  refine ⟨y, ?_, ?_⟩
  · rintro ⟨x, z⟩ hxz
    have h := le_trans (le_iSup₂_of_le z hxz le_rfl) (hpy x)
    exact_mod_cast h
  · rintro ⟨u, x⟩ hux
    have h := le_trans (hqy x) (iInf₂_le_of_le u hux le_rfl)
    exact_mod_cast h

end ConvexProcess

end Thm398



/-! ### Theorem 39.7: the conjugate of an image under a convex process -/

section Thm397

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The indicator bifunction of `A⁻¹` is the indicator bifunction of `A` read backwards: both
values are `δ(· | ·)` of the same membership `(u, x) ∈ graph A`. -/
@[simp] theorem indicatorBifun_inv (A : ConvexProcess U X) (x : X) (u : U) :
    A.inv.indicatorBifun x u = A.indicatorBifun u x := by
  rw [indicatorBifun_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show u ∈ A.inv.eval x from h),
      indicatorFn_of_mem (show x ∈ A.eval u from h)]
  · rw [indicatorFn_of_notMem (show u ∉ A.inv.eval x from h),
      indicatorFn_of_notMem (show x ∉ A.eval u from h)]

/-- **Rockafellar, §39**, `(A⁻¹)* = A*⁻¹`. The inverse of a supremum-oriented process is infimum
oriented, so its adjoint is the `coadjointProcess`; with that reading the identity is an
unfolding, both sides being `{(v, y) | ⟨x, y⟩ ≤ ⟨u, v⟩ for every (u, x) ∈ graph A}`. -/
theorem coadjointProcess_inv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    coadjointProcess Bx Bu A.inv = (adjointProcess Bu Bx A).inv := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  exact ⟨fun h p hp => h (p.2, p.1) hp, fun h p hp => h (p.2, p.1) hp⟩

/-- **The `F⁎*` entry of the §38/§39 dictionary**: the lower adjoint of the indicator bifunction
of `A` is the indicator bifunction of `A*⁻¹`.

This is `adjointBifun_indicatorBifun` with the two negations of `lowerAdjointBifun` cancelling
against the negation the opposite orientation of `A*` puts on its indicator, and the reversal
`indicatorBifun_inv` absorbing the transposition. It is the last thing Theorem 39.7 needs. -/
theorem lowerAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    lowerAdjointBifun Bu Bx A.indicatorBifun = (adjointProcess Bu Bx A).inv.indicatorBifun := by
  funext v y
  rw [lowerAdjointBifun_apply, adjointBifun_indicatorBifun, neg_neg, indicatorBifun_inv]

/-- The indicator bifunction of a convex process is finite at the origin, `0` being in `A 0`.
This is the "finite somewhere" side condition Corollary 38.4.1 asks of `F`. -/
theorem indicatorBifun_zero_zero_ne_top (A : ConvexProcess U X) :
    A.indicatorBifun 0 0 ≠ ⊤ := by
  rw [indicatorBifun_apply, indicatorFn_of_mem A.zero_mem_eval_zero]
  simp

/-- **Rockafellar, Theorem 39.7**, first assertion: `(Af)* = A*⁻¹ f*`, where `Af` is the image
`Ff` of `f` under the indicator bifunction `F` of `A`, i.e. `(Af)(x) = inf {f u | x ∈ A u}`.

Rockafellar's proof is "this specializes Theorem 38.4", and so is this one: the only work is the
dictionary `lowerAdjointBifun_indicatorBifun`. His relative-interior hypothesis
`ri (dom f) ∩ ri (dom A) ≠ ∅` becomes the `IsExactSum` of Theorem 38.4, `dom F` being `dom A`. -/
theorem conj_imageBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) {f : U → EReal} (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    conj Bx (imageBifun A.indicatorBifun f) y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (conj Bu f) y := by
  rw [← lowerAdjointBifun_indicatorBifun]
  exact conj_imageBifun_eq_imageBifun A.indicatorBifun_ne_bot hf hex

/-- **Rockafellar, Theorem 39.7**, second assertion: the infimum defining `(A*⁻¹ f*)(x*)` is
attained. This is Theorem 38.4's attainment clause read through the same dictionary. -/
theorem exists_imageBifun_indicatorBifun_adjointProcess_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) {f : U → EReal} (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    ∃ v : V, conj Bu f v + (adjointProcess Bu Bx A).inv.indicatorBifun v y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (conj Bu f) y := by
  obtain ⟨v, hv⟩ := exists_conj_imageBifun_eq (Bu := Bu) (Bx := Bx) A.indicatorBifun_ne_bot hf hex
  refine ⟨v, ?_⟩
  rw [← conj_imageBifun_indicatorBifun Bu Bx A hf hex, ← hv, ← lowerAdjointBifun_indicatorBifun]
  rfl

end ConvexProcess

end Thm397


/-! ### Theorem 39.1: bounded values force a linear transformation -/

section Linear

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : ConvexProcess U X}

namespace ConvexProcess

/-- `A 0` is a convex cone containing the origin, so if it is bounded it is `{0}`. -/
theorem eval_zero_eq_zero_of_isBounded (A : ConvexProcess U X)
    (hb : Bornology.IsBounded (A.eval 0)) : A.eval 0 = {0} := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hR0 : (0 : ℝ) ≤ R := by simpa using hR _ A.zero_mem_eval_zero
  refine Set.Subset.antisymm (fun x hx => ?_) (by simpa using A.zero_mem_eval_zero)
  by_contra hx0
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hc0 : (0 : ℝ) ≤ (R + 1) / ‖x‖ := div_nonneg (by linarith) (norm_nonneg x)
  have hmem := A.smul_mem_eval_zero hc0 hx
  have hle := hR _ hmem
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, div_mul_cancel₀ _ (ne_of_gt hxn)] at hle
  linarith

/-- If `A 0` is bounded and `A` has full domain, every value of `A` is a single point. -/
theorem exists_eval_eq_singleton (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) (u : U) : ∃ x, A.eval u = {x} := by
  obtain ⟨x, hx⟩ : (A.eval u).Nonempty := by rw [← mem_dom, hdom]; trivial
  obtain ⟨y, hy⟩ : (A.eval (-u)).Nonempty := by rw [← mem_dom, hdom]; trivial
  refine ⟨x, Set.Subset.antisymm (fun z hz => ?_) (by simpa using hx)⟩
  have hzy : z + y ∈ A.eval 0 := by
    have h := add_mem_graph hz hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  have hxy : x + y ∈ A.eval 0 := by
    have h := add_mem_graph hx hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  rw [A.eval_zero_eq_zero_of_isBounded hb, Set.mem_singleton_iff] at hzy hxy
  exact Set.mem_singleton_iff.2 (add_right_cancel (hzy.trans hxy.symm))

/-- **Rockafellar, Theorem 39.1**: a convex process whose domain is everything and whose value at
the origin is bounded is (the graph of) a linear transformation.

Linear transformations are exactly the convex processes all of whose values are nonempty and
bounded; the converse direction is `ConvexProcess.dom_ofLinearMap` together with
`ConvexProcess.eval_ofLinearMap`. -/
theorem exists_linearMap_of_isBounded (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : U →ₗ[ℝ] X, ∀ u, A.eval u = {T u} := by
  choose T hT using A.exists_eval_eq_singleton hdom hb
  have hmem : ∀ u, (u, T u) ∈ A.graph := by
    intro u
    have h : T u ∈ A.eval u := by rw [hT u]; exact Set.mem_singleton _
    exact h
  have hadd : ∀ u₁ u₂, T (u₁ + u₂) = T u₁ + T u₂ := by
    intro u₁ u₂
    have h := add_mem_graph (hmem u₁) (hmem u₂)
    rw [Prod.mk_add_mk] at h
    have h' : T u₁ + T u₂ ∈ A.eval (u₁ + u₂) := h
    rw [hT (u₁ + u₂), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hT0 : T 0 = 0 := by
    have h0 : (0 : X) ∈ A.eval 0 := A.zero_mem_eval_zero
    rw [hT 0, Set.mem_singleton_iff] at h0
    exact h0.symm
  have hneg : ∀ u, T (-u) = -T u := by
    intro u
    have h := hadd u (-u)
    rw [add_neg_cancel, hT0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hpos : ∀ c : ℝ, 0 < c → ∀ u, T (c • u) = c • T u := by
    intro c hc u
    have h := smul_mem_graph hc.le (hmem u)
    rw [Prod.smul_mk] at h
    have h' : c • T u ∈ A.eval (c • u) := h
    rw [hT (c • u), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hsmul : ∀ (c : ℝ) (u : U), T (c • u) = c • T u := by
    intro c u
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h1 : T ((-c) • u) = (-c) • T u := hpos _ (by linarith) u
      rw [neg_smul, hneg, neg_smul, neg_inj] at h1
      exact h1
    · simp [hT0]
    · exact hpos _ hc u
  exact ⟨{ toFun := T, map_add' := hadd, map_smul' := fun c u => hsmul c u }, hT⟩

end ConvexProcess

end Linear

/-! ### Corollary 39.7.1: closedness of the image -/

section Closedness

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {A : ConvexProcess U X} {C : Set U}

namespace ConvexProcess

/-- **Rockafellar, Corollary 39.7.1**: if `A` is a closed convex process, `C` is a nonempty closed
convex set, and no non-zero vector of `A⁻¹ 0` recedes `C`, then `A C` is closed. In particular this
holds when `C` is bounded, since then `0⁺C = {0}`.

This is exactly **Theorem 9.1** for the projection `(u, x) ↦ x`: `A C` is the image of
`graph A ∩ (C × X)`, whose recession cone is `graph A ∩ (0⁺C × X)` — the graph is its own recession
cone, being a pointed convex cone — and whose intersection with the kernel of the projection is
`{(v, 0) | v ∈ A⁻¹ 0 ∩ 0⁺C}`. Rockafellar instead specializes Theorem 39.7 and separates the
barrier cone of `C` from the range of `A*`; the route through Theorem 9.1 is shorter and needs no
duality. -/
theorem isClosed_image (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty)
    (h : ∀ v : U, (v, (0 : X)) ∈ A.graph → v ∈ recessionCone C → v = 0) :
    IsClosed (A.image C) := by
  have hSconv : Convex ℝ ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    Convex.inter (convex_graph A) (Convex.prod hC convex_univ)
  have hScl : IsClosed ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    hA.inter (hC'.prod isClosed_univ)
  rcases Set.eq_empty_or_nonempty ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) with hSe | hSne
  · have hempty : A.image C = ∅ := by rw [image_eq_image_snd, hSe, Set.image_empty]
    rw [hempty]
    exact isClosed_empty
  rw [image_eq_image_snd]
  refine isClosed_image_of_recessionCone_inter_ker _ hSconv hScl ?_
  rintro ⟨v, y⟩ ⟨hrec, hker⟩
  rw [recessionCone_inter (convex_graph A) hA (Convex.prod hC convex_univ)
    (hC'.prod isClosed_univ) hSne] at hrec
  obtain ⟨hg, hp⟩ := hrec
  rw [recessionCone_coe_pointedCone] at hg
  rw [recessionCone_prod hCne ⟨0, mem_univ 0⟩, recessionCone_univ] at hp
  have hy : y = 0 := by simpa using hker
  subst hy
  have hv : v = 0 := h v hg hp.1
  subst hv
  simp

/-- **Rockafellar, Corollary 39.7.1**, the bounded case: the image of a nonempty compact convex set
under a closed convex process is closed. -/
theorem isClosed_image_of_isBounded (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) := by
  refine isClosed_image hA hC hC' hCne fun v _ hv => ?_
  have h0 : recessionCone C = {0} := recessionCone_eq_zero_of_isBounded hCne hb
  rw [h0] at hv
  simpa using hv

end ConvexProcess

end Closedness

end Tdaf.ConvexAnalysis
