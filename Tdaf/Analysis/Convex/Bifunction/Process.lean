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
* `ConvexProcess.comp`, and the `Add` instance — the product `B A` and the sum `A₁ + A₂`.
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

**The adjoint is the polar of the graph, with a sign flip on one factor.**
`mem_graph_adjointProcess_iff_mem_polarCone` says `(y, v) ∈ graph A*` if and only if
`(-v, y) ∈ (graph A)°` for the product pairing, which is the same sign convention §30 uses for
`adjointBifun`. Everything topological about `A*` then comes from §14 for free:
`isClosed_polarCone` gives Theorem 39.2's first assertion (proved here directly, to avoid
transporting the pairing instance across `LinearMap.flip`), and `polarCone_polarCone` gives
`A** = cl A`.

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
