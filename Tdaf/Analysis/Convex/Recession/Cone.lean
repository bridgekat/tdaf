/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Analysis.Normed.Affine.AsymptoticCone
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Recession cones and lineality spaces

Rockafellar's §8, the half about sets. The *recession cone* `0⁺C` of a set `C` collects the
directions in which `C` recedes: the `y` such that every half-line `{x + a • y | a ≥ 0}` issuing
from a point of `C` stays inside `C`. The *lineality space* is the largest subspace it contains,
`0⁺C ∩ (-0⁺C)`, the directions in which `C` is linear.

## Main definitions

* `recessionCone C` — the recession cone `0⁺C`, as a bare `Set E`.
* `recessionPointedCone C` — the same set bundled as a `PointedCone ℝ E`.
* `linealitySpace C` — the lineality space, as a bare `Set E`.
* `linealitySubmodule C` — the same set bundled as a `Submodule ℝ E`.
* `lineality C` — its dimension, Rockafellar's *lineality of `C`*.

## Main results

* `recessionCone_eq_add_subset` — **Theorem 8.1**: for convex `C`, `0⁺C = {y | C + y ⊆ C}`.
  That `0⁺C` is a convex cone containing the origin is `recessionPointedCone`, and it needs
  no hypothesis on `C` at all.
* `recessionCone_coe_affineSubspace`, `recessionCone_setOf_forall_le` — the recession
  cone of a nonempty affine set is its direction, and that of the solution set of a system of weak
  linear inequalities is the solution set of the associated homogeneous system.
* `eq_add_inter_of_isCompl` — Rockafellar's direct-sum decomposition `C = L + (C ∩ L')`, for
  any complement `L'` of the lineality space `L`.
* `isClosed_recessionCone` — `0⁺C` is closed as soon as `C` is.
* `mem_recessionCone_iff_exists_tendsto` — **Theorem 8.2**: for a nonempty closed convex `C`,
  `0⁺C` consists of the limits of sequences `lᵢ • xᵢ` with `xᵢ ∈ C` and `lᵢ ↓ 0`.
* `mem_recessionCone_of_exists_ray` — **Theorem 8.3**: one half-line in the direction `y`
  inside a closed convex `C` forces all of them.
* `recessionCone_iInter`, `recessionCone_preimage` — **Corollaries 8.3.3 and 8.3.4**.
* `recessionCone_eq_asymptoticCone` — the bridge to Mathlib's `asymptoticCone`.
* `isBounded_iff_recessionCone_eq_zero` — **Theorem 8.4**, with
  `isBounded_inter_of_direction_eq` for **Corollary 8.4.1**.

## Layers

The file is split so that each result sits at the weakest hypothesis that supports it; the layer
names are those of the project plan.

* **Layer A**, `[AddCommGroup E] [Module ℝ E]`, no topology: the definitions, the pointed-cone and
  submodule structures, Theorem 8.1, the affine and linear-inequality examples, and the direct-sum
  decomposition.
* **Layer B**, a real topological vector space: closedness of `0⁺C`, Theorem 8.2, Theorem 8.3 and
  Corollaries 8.3.2–8.3.4, and the `asymptoticCone` bridge. The plan placed closedness of `0⁺C`
  and Theorems 8.2/8.3 in layer D; they do not belong there. See the design note below.
* **Layer B, normed**: the recession cone of a bounded set and of a closed ball.
* **Layer D**, `[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`: Theorem 8.4 and
  Corollary 8.4.1 only. Finite-dimensionality enters exactly once, through local compactness, and
  it is what makes an unbounded closed convex set recede in some direction.

## Design notes

### Why closedness of `0⁺C` is layer B, and needs neither convexity nor nonemptiness

Writing the definition as an intersection,
`0⁺C = ⋂ x ∈ C, ⋂ a ∈ Ici 0, (fun y => x + a • y) ⁻¹' C` (`recessionCone_eq_iInter`, itself
layer A) exhibits `0⁺C` as an intersection of preimages of `C` under continuous maps. So `C`
closed gives `0⁺C` closed in any topological vector space, with no convexity, no nonemptiness and
no local compactness. Rockafellar states the closedness as part of Theorem 8.2 and proves it from
the `cl K` formula, which is why the plan inherited a finite-dimensional hypothesis for it.

Theorem 8.2 itself is also layer B: from `lᵢ • xᵢ → y` one gets
`(1 - a lᵢ) • x + (a lᵢ) • xᵢ ∈ C` for large `i`, and that combination tends to `x + a • y`.
Theorem 8.3 is then a one-line corollary, applying Theorem 8.2 to `lᵢ = (i+1)⁻¹` and
`xᵢ = x + (i+1) • y`. Only Theorem 8.4 is genuinely finite-dimensional.

### Relation to Mathlib's `asymptoticCone`

Mathlib has `asymptoticCone ℝ C`, defined by a filter condition. It is *not* `0⁺C`: it is always
closed, it is empty for `C = ∅`, and `asymptoticCone ℝ (closure C) = asymptoticCone ℝ C`. What it
computes is `0⁺(cl C)` — precisely the "asymptotic cone" terminology Rockafellar mentions and
declines to adopt. `recessionCone_eq_asymptoticCone` records that the two agree for nonempty
closed convex sets, and `recessionCone_closure_eq_asymptoticCone` records the general
identification. A separate definition is still needed: `recessionCone` is purely algebraic,
and `Tdaf/Analysis/Convex/Recession/Function.lean` defines the recession function of `f` as
`ofEpi (0⁺(epi f))` at layer A, where no topology on `E × ℝ` is available.

### What is deliberately absent

*The `cl K` formula* of Theorem 8.2, `cl K = K ∪ {0} × 0⁺C` for the cone `K` generated by
`{1} × C`. In the plan it was the proof route for Theorem 8.2; the direct proof above supersedes
it. Stating it needs a set-level homogenisation `K` that belongs with
`Tdaf/Analysis/Convex/Homogenize.lean` (whose `homCone` is the epigraph analogue), and
nothing in §9 consumes it.

*Corollary 8.3.1*, `0⁺(ri C) = 0⁺(cl C)`, which is stated with relative interiors and rests on
Theorem 6.1. It is `Convex.recessionCone_relint` in
`Tdaf/Analysis/Convex/RelativeInterior.lean`; what is proved here is the layer-B stand-in
`recessionCone_interior_eq_recessionCone_closure`, with `interior` in place of `ri` — the
same substitution `Tdaf/Analysis/Convex/Closure.lean` makes for Theorem 7.5.

*Rockafellar's `rank`*. The direct-sum decomposition `C = L + (C ∩ L')` is here, at layer A and for
an arbitrary complement `L'` of the lineality space `L`, which subsumes the orthogonal complement
`L^⊥` of the book (take `L' = Lᗮ`, using `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`);
no inner product is needed and none is imported. `rank C = dim C - lineality C`, however, needs
`dim C = Module.finrank ℝ (vectorSpan ℝ C)` together with the affine-hull calculus of §6 to be
worth anything, so only `lineality` is defined here.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §8 — from the start
  through Theorem 8.4 and the discussion of lineality spaces.
-/

open Bornology Filter Pointwise Set Topology

namespace Tdaf.ConvexAnalysis

/-! ### Layer A: the definitions and their algebraic structure -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {x y z : E} {a : ℝ}

/-- The recession cone `0⁺C`: the directions in which `C` recedes.

`y ∈ 0⁺C` when every half-line `{x + a • y | a ≥ 0}` issuing from a point `x` of `C` is contained
in `C`. Rockafellar §8 excludes `y = 0`, which has no direction; including it is what makes `0⁺C`
a cone. -/
def recessionCone (C : Set E) : Set E := {y | ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C}

/-- Membership in the recession cone, unfolded. -/
theorem mem_recessionCone : y ∈ recessionCone C ↔ ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C :=
  Iff.rfl

/-- The defining property of a direction of recession. -/
theorem add_smul_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) (ha : 0 ≤ a) :
    x + a • y ∈ C := hy x hx a ha

/-- A direction of recession may be added to any point of `C`. -/
theorem add_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) : x + y ∈ C := by
  simpa using hy x hx 1 zero_le_one

/-- The origin is always a direction of recession. -/
@[simp]
theorem zero_mem_recessionCone (C : Set E) : (0 : E) ∈ recessionCone C := fun x hx _ _ => by
  simpa using hx

/-- The recession cone is closed under nonnegative scalar multiplication. -/
theorem smul_mem_recessionCone (ha : 0 ≤ a) (hy : y ∈ recessionCone C) :
    a • y ∈ recessionCone C := fun x hx b hb => by
  rw [smul_smul]
  exact hy x hx (b * a) (mul_nonneg hb ha)

/-- The recession cone is closed under addition. -/
theorem add_mem_recessionCone (hy : y ∈ recessionCone C) (hz : z ∈ recessionCone C) :
    y + z ∈ recessionCone C := fun x hx a ha => by
  rw [smul_add, ← add_assoc]
  exact hz _ (hy x hx a ha) a ha

/-- **Rockafellar, Theorem 8.1**, the structural half: `0⁺C` is a convex cone containing the
origin, bundled as a Mathlib `PointedCone`.

No hypothesis on `C` is needed. Convexity of `C` enters only in the second half of Theorem 8.1,
`recessionCone_eq_add_subset`. Recording the cone makes the `PointedCone` API — and in
particular `PointedCone.lineal`, which is `linealitySubmodule` — available downstream. -/
def recessionPointedCone (C : Set E) : PointedCone ℝ E where
  carrier := recessionCone C
  zero_mem' := zero_mem_recessionCone C
  add_mem' := add_mem_recessionCone
  smul_mem' c _ hy := smul_mem_recessionCone c.2 hy

/-- The carrier of `recessionPointedCone` is the recession cone. -/
@[simp]
theorem coe_recessionPointedCone (C : Set E) :
    (recessionPointedCone C : Set E) = recessionCone C := rfl

/-- Membership in `recessionPointedCone` is membership in the recession cone. -/
@[simp]
theorem mem_recessionPointedCone : y ∈ recessionPointedCone C ↔ y ∈ recessionCone C := Iff.rfl

/-- The recession cone of any set is convex. -/
theorem convex_recessionCone (C : Set E) : Convex ℝ (recessionCone C) :=
  ((recessionPointedCone C : ConvexCone ℝ E)).convex

/-- Every direction recedes from the empty set, vacuously. -/
@[simp]
theorem recessionCone_empty : recessionCone (∅ : Set E) = univ := by
  ext y; simp [recessionCone]

/-- Every direction recedes from the whole space. -/
@[simp]
theorem recessionCone_univ : recessionCone (univ : Set E) = univ := by
  ext y; simp [recessionCone]

/-- A singleton recedes in no direction. -/
@[simp]
theorem recessionCone_singleton (x : E) : recessionCone ({x} : Set E) = {0} := by
  ext y
  refine ⟨fun hy => ?_, ?_⟩
  · have h : x + (1 : ℝ) • y ∈ ({x} : Set E) := hy x rfl 1 zero_le_one
    rw [one_smul] at h
    simpa using h
  · rintro rfl
    exact zero_mem_recessionCone _

/-- The recession cone as an intersection of preimages of `C`. This is what makes it closed
whenever `C` is; see `isClosed_recessionCone`. For `a > 0` the `a`-th preimage is
`a⁻¹ • (C - x)`, which is the form Rockafellar's argument uses. -/
theorem recessionCone_eq_iInter (C : Set E) :
    recessionCone C = ⋂ x ∈ C, ⋂ a ∈ Ici (0 : ℝ), (fun y => x + a • y) ⁻¹' C := by
  ext y; simp [recessionCone]

/-- Directions of recession of every member of a family recede from the intersection. The reverse
inclusion needs closedness and convexity; it is Corollary 8.3.3, `recessionCone_iInter`. -/
theorem iInter_recessionCone_subset {ι : Sort*} (C : ι → Set E) :
    ⋂ i, recessionCone (C i) ⊆ recessionCone (⋂ i, C i) := by
  intro y hy x hx a ha
  exact mem_iInter.2 fun i => (mem_iInter.1 hy i) x (mem_iInter.1 hx i) a ha

/-- The binary form of `iInter_recessionCone_subset`. -/
theorem inter_recessionCone_subset (C D : Set E) :
    recessionCone C ∩ recessionCone D ⊆ recessionCone (C ∩ D) := by
  rintro y ⟨hyC, hyD⟩ x ⟨hxC, hxD⟩ a ha
  exact ⟨hyC x hxC a ha, hyD x hxD a ha⟩

/-- **Rockafellar, Theorem 8.1**, second half: for a convex set it is enough to test the recession
condition at `a = 1`. -/
theorem mem_recessionCone_iff_forall_add_mem (hC : Convex ℝ C) :
    y ∈ recessionCone C ↔ ∀ x ∈ C, x + y ∈ C := by
  refine ⟨fun hy x hx => add_mem_of_mem_recessionCone hy hx, fun hy x hx a ha => ?_⟩
  have key : ∀ n : ℕ, x + (n : ℝ) • y ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have h := hy _ ih
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_smul, one_smul, ← add_assoc]
      exact h
  obtain ⟨n, hn⟩ := exists_nat_ge a
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hx
  · have hn0 : (0 : ℝ) < n := ha'.trans_le hn
    have hle : a / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hn
    have h := hC hx (key n) (by linarith : (0 : ℝ) ≤ 1 - a / (n : ℝ))
      (by positivity : (0 : ℝ) ≤ a / (n : ℝ)) (by ring)
    have hcancel : a / (n : ℝ) * (n : ℝ) = a := div_mul_cancel₀ a hn0.ne'
    rwa [smul_add, smul_smul, hcancel, ← add_assoc, ← add_smul,
      show 1 - a / (n : ℝ) + a / (n : ℝ) = 1 by ring, one_smul] at h

omit [Module ℝ E] in
/-- Rockafellar's `C + y ⊆ C`, spelled out. -/
theorem add_singleton_subset_iff_forall (C : Set E) (y : E) :
    C + {y} ⊆ C ↔ ∀ x ∈ C, x + y ∈ C := by
  rw [Set.add_singleton, Set.image_subset_iff]
  exact ⟨fun h x hx => h hx, fun h _ hx => h _ hx⟩

/-- **Rockafellar, Theorem 8.1**: the recession cone of a convex set is the set of `y` with
`C + y ⊆ C`. -/
theorem recessionCone_eq_add_subset (hC : Convex ℝ C) :
    recessionCone C = {y | C + {y} ⊆ C} := by
  ext y
  rw [mem_recessionCone_iff_forall_add_mem hC]
  exact (add_singleton_subset_iff_forall C y).symm

/-- The lineality space of `C`: the directions in which `C` is linear. -/
def linealitySpace (C : Set E) : Set E := recessionCone C ∩ (-recessionCone C)

/-- Membership in the lineality space, unfolded. -/
theorem mem_linealitySpace :
    y ∈ linealitySpace C ↔ y ∈ recessionCone C ∧ -y ∈ recessionCone C := by
  simp [linealitySpace]

/-- The lineality space sits inside the recession cone. -/
theorem linealitySpace_subset_recessionCone (C : Set E) :
    linealitySpace C ⊆ recessionCone C := inter_subset_left

/-- **Rockafellar, Theorem 2.7** applied to `0⁺C`: the lineality space is a subspace, bundled as a
`Submodule ℝ E`. It is Mathlib's `PointedCone.lineal` of `recessionPointedCone`. -/
noncomputable def linealitySubmodule (C : Set E) : Submodule ℝ E :=
  (recessionPointedCone C).lineal

/-- The carrier of `linealitySubmodule` is the lineality space. -/
@[simp]
theorem coe_linealitySubmodule (C : Set E) :
    (linealitySubmodule C : Set E) = linealitySpace C := by
  ext y; simp [linealitySubmodule, linealitySpace]

/-- Membership in `linealitySubmodule` is membership in the lineality space. -/
@[simp]
theorem mem_linealitySubmodule : y ∈ linealitySubmodule C ↔ y ∈ linealitySpace C := by
  rw [← SetLike.mem_coe, coe_linealitySubmodule]

/-- The lineality space is a subspace, hence convex. -/
theorem convex_linealitySpace (C : Set E) : Convex ℝ (linealitySpace C) := by
  simpa using (linealitySubmodule C).convex

/-- **Rockafellar, Theorem 2.7**: the lineality space is the largest subspace inside `0⁺C`. -/
theorem linealitySubmodule_isGreatest (C : Set E) :
    IsGreatest {L : Submodule ℝ E | (L : Set E) ⊆ recessionCone C} (linealitySubmodule C) := by
  constructor
  · have hsub : ((linealitySubmodule C : Submodule ℝ E) : Set E) ⊆ recessionCone C := by
      rw [coe_linealitySubmodule]
      exact linealitySpace_subset_recessionCone C
    exact hsub
  · intro L hL y hy
    exact mem_linealitySubmodule.2 (mem_linealitySpace.2 ⟨hL hy, hL (L.neg_mem hy)⟩)

/-- Rockafellar's elementary exercise: the lineality space of a convex set consists of the `y`
with `C + y = C`, in contrast with `C + y ⊆ C` for the recession cone. -/
theorem linealitySpace_eq_add_eq (hC : Convex ℝ C) :
    linealitySpace C = {y | C + {y} = C} := by
  ext y
  rw [mem_linealitySpace, mem_recessionCone_iff_forall_add_mem hC,
    mem_recessionCone_iff_forall_add_mem hC]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine Set.Subset.antisymm ((add_singleton_subset_iff_forall C y).2 h₁) fun x hx => ?_
    exact ⟨x + -y, h₂ x hx, y, rfl, by change x + -y + y = x; abel⟩
  · intro h
    have hsub : C + {y} ⊆ C := h.le
    refine ⟨(add_singleton_subset_iff_forall C y).1 hsub, fun x hx => ?_⟩
    obtain ⟨w, hw, v, hv, hwv⟩ := h.ge hx
    have hwv' : w + v = x := hwv
    rw [Set.mem_singleton_iff] at hv
    have hxw : x + -y = w := by rw [← hwv', hv]; abel
    exact hxw ▸ hw

/-- **Rockafellar's direct-sum decomposition**: if `L'` is any complement of the lineality space
`L` of `C`, then `C = L + (C ∩ L')`. The book states it for `L' = L^⊥` in an inner-product
space; that is the special case `L' = Lᗮ`. -/
theorem eq_add_inter_of_isCompl {L : Submodule ℝ E} (h : IsCompl (linealitySubmodule C) L) :
    C = (linealitySubmodule C : Set E) + (C ∩ (L : Set E)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · have hmem : x ∈ linealitySubmodule C ⊔ L := by rw [h.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hmem
    have hpneg : -p ∈ recessionCone C :=
      (mem_linealitySpace.1 (mem_linealitySubmodule.1 hp)).2
    have hqC : q ∈ C := by
      have hstep := add_mem_of_mem_recessionCone hpneg hx
      simpa [add_comm, add_assoc] using hstep
    exact Set.add_mem_add hp ⟨hqC, hq⟩
  · rintro _ ⟨p, hp, q, ⟨hqC, -⟩, rfl⟩
    have hpC : p ∈ recessionCone C :=
      (mem_linealitySpace.1 (mem_linealitySubmodule.1 hp)).1
    simpa [add_comm] using add_mem_of_mem_recessionCone hpC hqC

/-- Rockafellar's *lineality of `C`*: the dimension of its lineality space. -/
noncomputable def lineality (C : Set E) : ℕ := Module.finrank ℝ (linealitySubmodule C)

end Defs

/-! ### Layer A: affine sets and systems of weak linear inequalities -/

section Examples

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The recession cone of a nonempty affine set is the subspace parallel to it. -/
theorem recessionCone_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    recessionCone (s : Set E) = s.direction := by
  obtain ⟨x, hx⟩ := hs
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · have h : x + (1 : ℝ) • y ∈ s := hy x hx 1 zero_le_one
    rw [one_smul] at h
    simpa using AffineSubspace.vsub_mem_direction h hx
  · have h : a • y ∈ s.direction := s.direction.smul_mem a hy
    simpa [vadd_eq_add, add_comm] using AffineSubspace.vadd_mem_of_mem_direction h hz

/-- The lineality space of a nonempty affine set is the subspace parallel to it. -/
theorem linealitySpace_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    linealitySpace (s : Set E) = s.direction := by
  ext y
  rw [mem_linealitySpace, recessionCone_coe_affineSubspace hs]
  exact ⟨fun h => h.1, fun h => ⟨h, s.direction.neg_mem h⟩⟩

/-- The recession cone of the solution set of a system of weak linear inequalities is the solution
set of the corresponding homogeneous system. -/
theorem recessionCone_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    recessionCone {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, 0 ≤ b i y} := by
  refine Set.Subset.antisymm (fun y hy i => ?_) (fun y hy x hx a ha i => ?_)
  · by_contra hb
    obtain ⟨x, hx⟩ := h
    have hxi : ∀ j, β j ≤ b j x := hx
    have hd : 0 < -(b i y) := by linarith [not_le.1 hb]
    have hnum : (0 : ℝ) ≤ b i x - β i + 1 := by linarith [hxi i]
    have ha : (0 : ℝ) ≤ (b i x - β i + 1) / (-(b i y)) := div_nonneg hnum hd.le
    have hstep : ∀ j, β j ≤ b j (x + ((b i x - β i + 1) / (-(b i y))) • y) := hy x hx _ ha
    have hval := hstep i
    rw [map_add, map_smul, smul_eq_mul] at hval
    have hcancel : (b i x - β i + 1) / (-(b i y)) * (-(b i y)) = b i x - β i + 1 :=
      div_mul_cancel₀ _ hd.ne'
    have hneg : (b i x - β i + 1) / (-(b i y)) * (-(b i y))
        = -((b i x - β i + 1) / (-(b i y)) * b i y) := by ring
    linarith
  · have hxi : ∀ j, β j ≤ b j x := hx
    have hyi : ∀ j, (0 : ℝ) ≤ b j y := hy
    change β i ≤ b i (x + a • y)
    rw [map_add, map_smul, smul_eq_mul]
    have : (0 : ℝ) ≤ a * b i y := mul_nonneg ha (hyi i)
    linarith [hxi i]

/-- The lineality space of the solution set of a system of weak linear inequalities is given by
the corresponding system of equations. -/
theorem linealitySpace_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    linealitySpace {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, b i y = 0} := by
  ext y
  rw [mem_linealitySpace, recessionCone_setOf_forall_le b β h]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    have h₁' : ∀ j, (0 : ℝ) ≤ b j y := h₁
    have h₂' : ∀ j, (0 : ℝ) ≤ b j (-y) := h₂
    have := h₂' i
    rw [map_neg] at this
    linarith [h₁' i]
  · intro hy
    have hy' : ∀ j, b j y = 0 := hy
    exact ⟨fun i => (hy' i).ge, fun i => by rw [map_neg, hy' i]; simp⟩

end Examples

/-! ### Layer A: preimages under a linear map -/

section PreimageDefs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- One inclusion of Corollary 8.3.4, valid with no hypothesis at all. -/
theorem preimage_recessionCone_subset (A : E →ₗ[ℝ] F) (D : Set F) :
    A ⁻¹' recessionCone D ⊆ recessionCone (A ⁻¹' D) := by
  intro y hy x hx a ha
  have h : A x + a • A y ∈ D := hy (A x) hx a ha
  simpa [map_add, map_smul] using h

end PreimageDefs

/-! ### Layer B: closedness, limits, and Theorem 8.3 -/

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C D : Set E} {y : E}

/-- The sequence `(n+1)⁻¹` tends to `0`. Mathlib states this as `1 / (n + 1)`. -/
theorem tendsto_inv_nat_add_one_atTop_nhds_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The recession cone of a closed set is closed.

No convexity and no nonemptiness are needed, and no local compactness: by
`recessionCone_eq_iInter`, `0⁺C` is an intersection of preimages of `C` under the continuous
maps `y ↦ x + a • y`. Rockafellar packages this statement into Theorem 8.2. -/
theorem isClosed_recessionCone (hC : IsClosed C) : IsClosed (recessionCone C) := by
  rw [recessionCone_eq_iInter]
  exact isClosed_biInter fun x _ => isClosed_biInter fun a _ => hC.preimage (by fun_prop)

omit [ContinuousSMul ℝ E] in
/-- Directions of recession survive taking the closure. The reverse inclusion is false: for
`C = {(s, t) | s > 0, t > 0} ∪ {0}` in `ℝ²`, `0⁺(cl C)` is the closed quadrant while `0⁺C` is `C`
itself (Rockafellar's `C₄`). -/
theorem recessionCone_subset_recessionCone_closure (C : Set E) :
    recessionCone C ⊆ recessionCone (closure C) := by
  intro y hy x hx a ha
  have hcont : Continuous fun z : E => z + a • y := by fun_prop
  have himg : (fun z : E => z + a • y) '' closure C ⊆ closure ((fun z : E => z + a • y) '' C) :=
    image_closure_subset_closure_image hcont
  refine closure_mono (fun z hz => ?_) (himg ⟨x, hx, rfl⟩)
  obtain ⟨w, hw, rfl⟩ := hz
  exact hy w hw a ha

/-- The sequence `(n+1)⁻¹ • (x + (n+1) • y)` converges to `y`.

This is the witness for the easy half of Theorem 8.2, and it is what turns Theorem 8.3 into a
corollary of Theorem 8.2. -/
theorem tendsto_inv_smul_ray (x y : E) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y)) atTop (𝓝 y) := by
  have hfun : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y))
      = fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x + y := by
    funext n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) := tendsto_const_nhds
  have hsum := (tendsto_inv_nat_add_one_atTop_nhds_zero.smul_const x).add hconst
  rw [hfun]
  simpa using hsum

/-- **Rockafellar, Theorem 8.2**, the hard half: a limit of `lᵢ • xᵢ` with `xᵢ ∈ C` and `lᵢ ↓ 0` is
a direction of recession of a closed convex `C`.

Finite-dimensionality is not needed: `(1 - a lᵢ) • x + (a lᵢ) • xᵢ` lies in `C` once `a lᵢ ≤ 1`,
and it converges to `x + a • y`. -/
theorem mem_recessionCone_of_tendsto (hC : Convex ℝ C) (hC' : IsClosed C) {l : ℕ → ℝ} {u : ℕ → E}
    (hu : ∀ n, u n ∈ C) (hl : ∀ n, 0 < l n) (hl0 : Tendsto l atTop (𝓝 0))
    (hly : Tendsto (fun n => l n • u n) atTop (𝓝 y)) : y ∈ recessionCone C := by
  intro x hx a ha
  have hal : Tendsto (fun n => a * l n) atTop (𝓝 0) := by simpa using hl0.const_mul a
  have hev : ∀ᶠ n in atTop, a * l n ≤ 1 :=
    (hal.eventually_lt_const one_pos).mono fun n hn => hn.le
  have hmem : ∀ᶠ n in atTop, (1 - a * l n) • x + (a * l n) • u n ∈ C := by
    filter_upwards [hev] with n hn
    exact hC hx (hu n) (by linarith) (mul_nonneg ha (hl n).le) (by ring)
  have h1 : Tendsto (fun n => (1 - a * l n) • x) atTop (𝓝 x) := by
    have hone : Tendsto (fun n => 1 - a * l n) atTop (𝓝 1) := by simpa using hal.const_sub 1
    simpa using hone.smul_const x
  have h2 : Tendsto (fun n => (a * l n) • u n) atTop (𝓝 (a • y)) := by
    simpa [mul_smul] using hly.const_smul a
  exact hC'.mem_of_tendsto (h1.add h2) hmem

/-- **Rockafellar, Theorem 8.2**, the easy half: every direction of recession of a nonempty set is
a limit of `lᵢ • xᵢ` with `xᵢ ∈ C` and `lᵢ ↓ 0`. -/
theorem exists_tendsto_of_mem_recessionCone (hne : C.Nonempty) (hy : y ∈ recessionCone C) :
    ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun n => ((n : ℝ) + 1)⁻¹, fun n => x + ((n : ℝ) + 1) • y,
    fun n => hy x hx _ (by positivity), fun n => by positivity,
    tendsto_inv_nat_add_one_atTop_nhds_zero, tendsto_inv_smul_ray x y⟩

/-- **Rockafellar, Theorem 8.2**: for a nonempty closed convex set, `0⁺C` is exactly the set of
limits of sequences `lᵢ • xᵢ` with `xᵢ ∈ C` and `lᵢ ↓ 0`. -/
theorem mem_recessionCone_iff_exists_tendsto (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) :
    y ∈ recessionCone C ↔ ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) :=
  ⟨exists_tendsto_of_mem_recessionCone hne, fun ⟨_, _, hu, hl, hl0, hly⟩ =>
    mem_recessionCone_of_tendsto hC hC' hu hl hl0 hly⟩

/-- **Rockafellar, Theorem 8.3**: if a closed convex set `C` contains even one half-line in the
direction `y`, then it contains every half-line in that direction issuing from a point of `C`. -/
theorem mem_recessionCone_of_exists_ray (hC : Convex ℝ C) (hC' : IsClosed C)
    (h : ∃ x, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C) : y ∈ recessionCone C := by
  obtain ⟨x, hx⟩ := h
  exact mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹)
    (fun n => hx ((n : ℝ) + 1) (by positivity)) (fun n => by positivity)
    tendsto_inv_nat_add_one_atTop_nhds_zero (tendsto_inv_smul_ray x y)

/-- **Rockafellar, Corollary 8.3.2**: for a closed convex set containing the origin,
`0⁺C = ⋂_{ε > 0} ε • C`. -/
theorem recessionCone_eq_iInter_smul (hC : Convex ℝ C) (hC' : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone C = ⋂ ε ∈ Ioi (0 : ℝ), ε • C := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter₂.2 fun ε hε => ?_) (fun y hy => ?_)
  · have hε' : (0 : ℝ) < ε := hε
    have hmem : ε⁻¹ • y ∈ C := by simpa using hy 0 h0 ε⁻¹ (by positivity)
    simpa [smul_inv_smul₀ hε'.ne'] using Set.smul_mem_smul_set (a := ε) hmem
  · have hu : ∀ n : ℕ, ((n : ℝ) + 1) • y ∈ C := by
      intro n
      have hne : (((n : ℝ) + 1)⁻¹ : ℝ) ≠ 0 := by positivity
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      have hmem : y ∈ ((n : ℝ) + 1)⁻¹ • C := mem_iInter₂.1 hy ((n : ℝ) + 1)⁻¹ hpos
      simpa using (Set.mem_smul_set_iff_inv_smul_mem₀ hne C y).1 hmem
    refine mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹) hu
      (fun n => by positivity) tendsto_inv_nat_add_one_atTop_nhds_zero ?_
    have hconst : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (((n : ℝ) + 1) • y)) = fun _ : ℕ => y := by
      funext n
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [hconst]
    exact tendsto_const_nhds

/-- **Rockafellar, Corollary 8.3.3**: the recession cone of an intersection of closed convex sets
with a common point is the intersection of the recession cones. -/
theorem recessionCone_iInter {ι : Sort*} {C : ι → Set E} (hconv : ∀ i, Convex ℝ (C i))
    (hclosed : ∀ i, IsClosed (C i)) (hne : (⋂ i, C i).Nonempty) :
    recessionCone (⋂ i, C i) = ⋂ i, recessionCone (C i) := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter.2 fun i => ?_)
    (iInter_recessionCone_subset C)
  obtain ⟨x, hx⟩ := hne
  exact mem_recessionCone_of_exists_ray (hconv i) (hclosed i)
    ⟨x, fun a ha => mem_iInter.1 (hy x hx a ha) i⟩

/-- The binary form of **Corollary 8.3.3**. -/
theorem recessionCone_inter (hC : Convex ℝ C) (hC' : IsClosed C) (hD : Convex ℝ D)
    (hD' : IsClosed D) (hne : (C ∩ D).Nonempty) :
    recessionCone (C ∩ D) = recessionCone C ∩ recessionCone D := by
  obtain ⟨x, hxC, hxD⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ⟨?_, ?_⟩) (inter_recessionCone_subset C D)
  · exact mem_recessionCone_of_exists_ray hC hC' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).1⟩
  · exact mem_recessionCone_of_exists_ray hD hD' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).2⟩

/-- The layer-B stand-in for **Corollary 8.3.1**: a convex set with nonempty interior has the same
directions of recession as its interior and as its closure. Rockafellar states this with `ri` in
place of `interior`. -/
theorem recessionCone_interior_eq_recessionCone_closure (hC : Convex ℝ C)
    (hne : (interior C).Nonempty) :
    recessionCone (interior C) = recessionCone (closure C) := by
  refine Set.Subset.antisymm ?_ (fun y hy x hx a ha => ?_)
  · rw [← hC.closure_interior_eq_closure_of_nonempty_interior hne]
    exact recessionCone_subset_recessionCone_closure _
  · have h2 : x + (2 * a) • y ∈ closure C :=
      hy x (subset_closure (interior_subset hx)) (2 * a) (by linarith)
    have hcombo := hC.combo_interior_closure_mem_interior hx h2 (a := (1 : ℝ) / 2)
      (b := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    have hcoef : (1 : ℝ) / 2 * (2 * a) = a := by ring
    have heq : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • (x + (2 * a) • y) = x + a • y := by
      rw [smul_add, smul_smul, hcoef, ← add_assoc, ← add_smul]
      norm_num
    rwa [heq] at hcombo

/-! #### The bridge to Mathlib's `asymptoticCone` -/

/-- Every direction of recession of a nonempty set lies in Mathlib's `asymptoticCone`. -/
theorem recessionCone_subset_asymptoticCone (hne : C.Nonempty) :
    recessionCone C ⊆ asymptoticCone ℝ C := by
  obtain ⟨x, hx⟩ := hne
  intro y hy
  rw [mem_asymptoticCone_iff]
  refine (((tendsto_id (x := atTop (α := ℝ))).atTop_smul_const_tendsto_asymptoticNhds
    y).asymptoticNhds_vadd_const x).frequently (Filter.Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
  simpa [vadd_eq_add, add_comm] using hy x hx c hc

/-- For a closed convex set, Mathlib's `asymptoticCone` is contained in the recession cone. -/
theorem asymptoticCone_subset_recessionCone (hC : Convex ℝ C) (hC' : IsClosed C) :
    asymptoticCone ℝ C ⊆ recessionCone C := fun y hy x hx a ha => by
  simpa [vadd_eq_add, add_comm] using
    hC.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hC' ha hy hx

/-- For a nonempty closed convex set, `0⁺C` is Mathlib's `asymptoticCone ℝ C`. -/
theorem recessionCone_eq_asymptoticCone (hC : Convex ℝ C) (hC' : IsClosed C) (hne : C.Nonempty) :
    recessionCone C = asymptoticCone ℝ C :=
  Set.Subset.antisymm (recessionCone_subset_asymptoticCone hne)
    (asymptoticCone_subset_recessionCone hC hC')

/-- In general Mathlib's `asymptoticCone ℝ C` is the recession cone of the *closure* of `C` — the
"asymptotic cone" of the older literature, which Rockafellar mentions and declines to adopt. -/
theorem recessionCone_closure_eq_asymptoticCone (hC : Convex ℝ C) (hne : C.Nonempty) :
    recessionCone (closure C) = asymptoticCone ℝ C := by
  rw [recessionCone_eq_asymptoticCone hC.closure isClosed_closure hne.closure,
    asymptoticCone_closure]

end Topological

/-! ### Layer B: preimages under a linear map -/

section Preimage

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {D : Set F}

/-- **Rockafellar, Corollary 8.3.4**: `0⁺(A⁻¹ D) = A⁻¹ (0⁺D)` for a closed convex `D` with
nonempty preimage. Continuity of `A` is *not* needed — Theorem 8.3 is applied to `D`, not to
`A ⁻¹' D` — so the domain `E` carries no topology. -/
theorem recessionCone_preimage (A : E →ₗ[ℝ] F) (hD : Convex ℝ D) (hD' : IsClosed D)
    (hne : (A ⁻¹' D).Nonempty) :
    recessionCone (A ⁻¹' D) = A ⁻¹' recessionCone D := by
  obtain ⟨x, hx⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ?_) (preimage_recessionCone_subset A D)
  refine mem_recessionCone_of_exists_ray hD hD' ⟨A x, fun a ha => ?_⟩
  simpa [map_add, map_smul] using hy x hx a ha

end Preimage

/-! ### Layer B, normed: bounded sets and balls -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- The easy half of **Theorem 8.4**: a nonempty bounded set recedes in no direction. Neither
closedness, nor convexity, nor finite-dimensionality is needed. -/
theorem recessionCone_eq_zero_of_isBounded (hne : C.Nonempty) (h : IsBounded C) :
    recessionCone C = {0} := by
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨R, hR⟩ := h.exists_norm_le
  by_contra hy0
  have hyne : y ≠ 0 := by simpa using hy0
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hyne
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hx)
  set a : ℝ := (R + ‖x‖ + 1) / ‖y‖ with hadef
  have ha : 0 ≤ a := by positivity
  have hmem : ‖x + a • y‖ ≤ R := hR _ (hy x hx a ha)
  have hsplit : ‖a • y‖ ≤ ‖x + a • y‖ + ‖x‖ := by
    have hrw : ‖a • y‖ = ‖x + a • y - x‖ := by congr 1; abel
    rw [hrw]
    exact norm_sub_le (x + a • y) x
  have hnorm : ‖a • y‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hadef, div_mul_cancel₀ _ hy'.ne']
  rw [hnorm] at hsplit
  linarith

/-- The recession cone of a closed ball is trivial. -/
theorem recessionCone_closedBall (x : E) {ε : ℝ} (hε : 0 ≤ ε) :
    recessionCone (Metric.closedBall x ε) = {0} :=
  recessionCone_eq_zero_of_isBounded ⟨x, Metric.mem_closedBall_self hε⟩ Metric.isBounded_closedBall

variable {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- The recession cone of `A ⁻¹' (closedBall x ε)` is the kernel of `A`. This is the computation
Theorem 9.1 runs on, and it needs no topology on the domain. -/
theorem recessionCone_preimage_closedBall (A : G →ₗ[ℝ] E) (x : E) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (A ⁻¹' Metric.closedBall x ε).Nonempty) :
    recessionCone (A ⁻¹' Metric.closedBall x ε) = LinearMap.ker A := by
  rw [recessionCone_preimage A (convex_closedBall x ε) Metric.isClosed_closedBall hne,
    recessionCone_closedBall x hε]
  ext y
  simp [LinearMap.mem_ker]

end Normed

/-! ### Layer D: boundedness -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

/-- **Rockafellar, Theorem 8.4**: a nonempty closed convex set is bounded exactly when it recedes
in no direction.

This is the one place in §8 where finite-dimensionality is used; it enters through Mathlib's
`isBounded_iff_asymptoticCone_subset_singleton`, whose proof covers the unit sphere by finitely
many asymptotic neighbourhoods. -/
theorem isBounded_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsBounded C ↔ recessionCone C = {0} := by
  rw [recessionCone_eq_asymptoticCone hC hC' hne, isBounded_iff_asymptoticCone_subset_singleton]
  refine ⟨fun h => Set.Subset.antisymm h ?_, fun h => h.subset⟩
  simpa using zero_mem_asymptoticCone.2 hne

/-- **Theorem 8.4**, contrapositive form: an unbounded closed convex set recedes in some nonzero
direction. -/
theorem exists_ne_zero_mem_recessionCone_of_not_isBounded (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) (hub : ¬ IsBounded C) : ∃ y ∈ recessionCone C, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hub ((isBounded_iff_recessionCone_eq_zero hC hC' hne).2 ?_)
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  simpa using hcon y hy

/-- A nonempty closed convex set is compact exactly when it recedes in no direction. -/
theorem isCompact_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsCompact C ↔ recessionCone C = {0} := by
  rw [← isBounded_iff_recessionCone_eq_zero hC hC' hne]
  exact ⟨fun h => h.isBounded, fun h => Metric.isCompact_of_isClosed_isBounded hC' h⟩

/-- **Rockafellar, Corollary 8.4.1**: if `M ∩ C` is nonempty and bounded for a closed convex `C`
and an affine set `M`, then `N ∩ C` is bounded for every affine set `N` parallel to `M`. -/
theorem isBounded_inter_of_direction_eq (hC : Convex ℝ C) (hC' : IsClosed C)
    {M N : AffineSubspace ℝ E} (hMN : M.direction = N.direction)
    (hM : ((M : Set E) ∩ C).Nonempty) (hb : IsBounded ((M : Set E) ∩ C)) :
    IsBounded ((N : Set E) ∩ C) := by
  rcases Set.eq_empty_or_nonempty ((N : Set E) ∩ C) with h | hN
  · simp [h]
  have hMne : (M : Set E).Nonempty := hM.mono inter_subset_left
  have hNne : (N : Set E).Nonempty := hN.mono inter_subset_left
  have hMcl : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  have hNcl : IsClosed (N : Set E) := N.closed_of_finiteDimensional
  have key : recessionCone ((N : Set E) ∩ C) = recessionCone ((M : Set E) ∩ C) := by
    rw [recessionCone_inter N.convex hNcl hC hC' hN, recessionCone_inter M.convex hMcl hC hC' hM,
      recessionCone_coe_affineSubspace hNne, recessionCone_coe_affineSubspace hMne, hMN]
  rw [isBounded_iff_recessionCone_eq_zero (N.convex.inter hC) (hNcl.inter hC') hN, key]
  exact (isBounded_iff_recessionCone_eq_zero (M.convex.inter hC) (hMcl.inter hC') hM).1 hb

end FiniteDimensional

end Tdaf.ConvexAnalysis
