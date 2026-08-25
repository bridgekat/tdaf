/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Polyhedral.Closedness
import Tdaf.Analysis.Convex.Polyhedral.Simplicial
import Tdaf.Surface.Rockafellar.Part3.Section11
import Tdaf.Surface.Rockafellar.Part3.Section12
import Tdaf.Surface.Rockafellar.Part3.Section16

/-!
# Rockafellar, §20: Some Applications of Polyhedral Convexity

R. T. Rockafellar, *Convex Analysis* (Princeton, 1970), §20, pp. 179–184: the separation theorems,
closure conditions and conjugacy formulas of Parts II and III, refined by assuming *some* of the
convexity polyhedral.

## The asymmetry of Theorem 20.1

Theorem 16.4 makes `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*` exact when the sets `ri (dom fᵢ)` have a common
point. Theorem 20.1 says that for each *polyhedral* `fᵢ` the relative interior may be dropped: only
`dom fᵢ` itself has to take part in the intersection. That asymmetry is the whole point of the
section, and it is the subtlest constraint qualification of Parts I–IV.

In the binary form the surface states, the two halves come from two different backbone lemmas:

* `IsExactSum.of_polyhedral_pair` supplies the case where **both** functions are polyhedral, and
  asks only `x₀ ∈ dom f ∩ dom g`. Its engine is Corollary 19.3.4: `epi f* + epi g*` is polyhedral,
  hence closed, so the infimal convolution's epigraph *is* that sum, with nothing to close.
* `IsExactSum.of_polyhedral` supplies the mixed case, `f` polyhedral and `g` merely proper convex,
  and asks `x₀ ∈ dom f ∩ ri (dom g)`. Its engine is Rockafellar's own reduction — intersect with
  `M = aff (dom g)`, split off `δ(· | M)` with the pair case, re-absorb it using
  `δ(· | M) + g = g` — and the closure step on the way is `conj_add_eq_conj_clFn_add_clFn`, whose
  two segment hypotheses are met on opposite grounds: `f` pays **Corollary 7.5.1** (only
  `x₀ ∈ dom f` is needed, because a proper polyhedral function is already closed) while `g` pays
  **Theorem 7.5** (`x₀ ∈ ri (dom g)`). Those two segment lemmas are exactly where the
  `dom` / `ri dom` asymmetry lives.

`IsExactSum` is the backbone's name for "the infimal convolution of the conjugates is attained
everywhere", i.e. for the conclusion shared by Theorems 16.4 and 20.1; §16 already states the
relative-interior form against the same interface.

**The `m`-ary statements are not an induction over the binary ones.** `IsExactFinsetSum` is the
same conclusion for a finite family, and its consequences — the identity, the attainment, the
properness of the sum — are proved once, for the family. What the book's own proof of
Theorem 20.1 contributes is `IsExactFinsetSum.of_split`: the polyhedral block `∑_{i ≤ k} fᵢ` is a
single polyhedral summand (**Theorem 19.4**, `polyhedralFn_finsetSum`), the rest is a single proper
convex one, the two add exactly by the *binary* Theorem 20.1, and each block adds exactly on its
own. The index set is split membership-wise rather than as `s = t ∪ u`, so no `DecidableEq`
instance reaches any statement.

## Contents

| label | declaration |
|---|---|
| §20 opening, `k = m` | `theorem_20_1_pair_exact`, `theorem_20_1_pair_attained` |
| Theorem 20.1 | `theorem_20_1_exact`, `theorem_20_1_attained`, `theorem_20_1_exact_finset`,
  `theorem_20_1_attained_finset` |
| Corollary 20.1.1 | `corollary_20_1_1`, `corollary_20_1_1_attained`,
  `corollary_20_1_1_finset`, `corollary_20_1_1_attained_finset` |
| Theorem 20.2 | `theorem_20_2` |
| Corollary 20.2.1 | `corollary_20_2_1` |
| Theorem 20.3 | `theorem_20_3` |
| Corollary 20.3.1 | `corollary_20_3_1` |
| Theorem 20.4 | `theorem_20_4` |
| Theorem 20.5 | `theorem_20_5`, `theorem_20_5_polytope` |

## The section's definitions

* `Rockafellar.IsPolyhedral C` — the book's §19 definition, "an intersection of finitely many
  closed half-spaces `{x | ⟨x, bᵢ⟩ ≤ βᵢ}`", quantified over *vectors* as the book quantifies.
  `isPolyhedral_iff_polyhedral` is its bridge to the backbone's `Polyhedral`, which quantifies over
  linear functionals; the translation is `linFn` / `exists_linFn`, exactly as in §11. **This
  definition belongs to §19 by subject**, but §19 does not restate it — it uses the backbone's
  `Polyhedral` directly — so this copy stays where its consumers are.
* `Rockafellar.SeparableProperlyNotContaining C₁ C₂` — "there exists a hyperplane separating `C₁`
  and `C₂` properly and not containing `C₂`", the conclusion of Theorem 20.2. It is built from
  §11's `SeparatesProperlyRn`, so the side convention is §11's: `C₁` lies in `{x | ⟨x, b⟩ ≥ β}`.
  `separableProperlyNotContaining_iff_exists` is the bridge to the backbone's functional form.

**Polyhedral convex *functions* are the backbone's `PolyhedralFn`** (`Polyhedral (epi f)`), used
without a surface copy. The book's definition is the same one, and restating it in vector form
would mean carrying a half-space description of a subset of `ℝⁿ × ℝ`, i.e. a product pairing that
`Tdaf/Surface/Common/Euclidean.lean` supplies only for `Rn m × Rn n`.

## What is not here

* **The opening paragraph's `m`-fold all-polyhedral formula** (book, lines 7003–7028) — *stated*,
  in binary form, as `theorem_20_1_pair_exact` / `theorem_20_1_pair_attained`. It is unnumbered in
  the book, which presents it as the motivating computation for Theorem 20.1; it is the case
  `k = m`, and the backbone's base case.

## Where the book's hypotheses had to change

**Theorem 20.4 needs neither convexity nor non-emptiness of `C`.** Rockafellar assumes `C` is a
non-empty closed bounded convex set; the backbone's `exists_polyhedral_between` uses only that `C`
is closed and bounded, since the argument is a finite subcover of `C` by polyhedral neighbourhoods
and never combines two points of `C` convexly. The surface follows the backbone and records the
difference rather than re-adding hypotheses that go unused.

**Theorem 20.5's proof is not the book's.** Rockafellar's proof (lines 7241–7249) is a two-line
sketch: intersect with a simplex neighbourhood, invoke Theorem 19.1 to write the bounded polyhedral
intersection as a polytope, and then *assert* that Carathéodory's theorem exhibits it as a finite
union of simplices. The backbone's `Polyhedral.locallySimplicial` does not rely on that sketch: it
takes the neighbourhood to be a coordinate cube (`exists_polyhedral_isBounded_mem_nhds`), and it
produces the simplices explicitly, as the convex hulls of the affinely independent subsets of a
generating `Finset` — which is `convexHull_eq_union`, not an appeal to Carathéodory's count.

**Theorem 10.2 does not depend on Theorem 20.5.** The book introduces Theorem 20.5 as the missing
link that makes Theorem 10.2 applicable, and Theorem 10.2's own proof reduces the simplex case to a
vertex by an "intuitively obvious" barycentric step. `Tdaf/Analysis/Convex/Simplicial.lean` proves
upper semicontinuity relative to a simplex *at every point of it*, not only at a vertex, so that
step is never invoked and §10's `theorem_10_2` is unconditional. Theorem 20.5 is therefore what
supplies `LocallySimplicial` *instances*, not what repairs §10.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §20.
-/

open Set Pointwise

namespace Rockafellar

open Tdaf.ConvexAnalysis Tdaf.Surface

variable {n : ℕ}

/-! ### Polyhedral convex sets, in the book's own words

Rockafellar's §19 definition writes each half-space as `{x | ⟨x, bᵢ⟩ ≤ βᵢ}` and quantifies over the
vectors `bᵢ`; the backbone quantifies over linear functionals. In `ℝⁿ` these are the same
quantification, and the round trip is `linFn` / `exists_linFn`. -/

/-- **Rockafellar, §19 (p. 170).** A **polyhedral convex set** in `ℝⁿ` is a set that can be
expressed as the intersection of finitely many closed half-spaces `{x | ⟨x, bᵢ⟩ ≤ βᵢ}`.

This definition is §19's property, repeated here because §20 is written in parallel with §19; every
result in this module is about a polyhedral `C₁`. `isPolyhedral_iff_polyhedral` is the bridge, and
nothing below unfolds the definition. -/
def IsPolyhedral (C : Set (Rn n)) : Prop :=
  ∃ s : Finset (Rn n × ℝ), C = {x | ∀ q ∈ s, pairing n x q.1 ≤ q.2}

/-- **The bridge to the backbone.** Rockafellar's vector-indexed system of half-spaces and the
backbone's functional-indexed one describe the same sets: `linFn` turns a vector into a functional
and `exists_linFn` turns a functional back into a vector, `LinearMap.toContinuousLinearMap` being
the continuity step, which is automatic in finite dimension. -/
theorem isPolyhedral_iff_polyhedral {C : Set (Rn n)} : IsPolyhedral C ↔ Polyhedral C := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s.image fun q => ((linFn q.1 : Rn n →ₗ[ℝ] ℝ), q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change (linFn q.1) x ≤ q.2
      rw [linFn_apply]
      exact hx q hq
    · intro hx q hq
      have hq' : (linFn q.1) x ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [linFn_apply] at hq'
  · rintro ⟨s, rfl⟩
    have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ b : Rn n, ∀ x, pairing n x b = φ x := by
      intro φ
      obtain ⟨b, hb⟩ := exists_linFn (LinearMap.toContinuousLinearMap φ)
      exact ⟨b, fun x => by rw [← linFn_apply, hb]; simp⟩
    choose rep hrep using hrep
    refine ⟨s.image fun q => (rep q.1, q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change pairing n x (rep q.1) ≤ q.2
      rw [hrep]
      exact hx q hq
    · intro hx q hq
      have hq' : pairing n x (rep q.1) ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [hrep] at hq'

/-! ### Separation that does not swallow the second set -/

/-- **Rockafellar, §20 (p. 181).** There exists a hyperplane separating `C₁` and `C₂` properly and
*not containing* `C₂`.

`SeparatesProperlyRn` is §11's, so the side convention is §11's: `C₁` lies in the closed half-space
`{x | ⟨x, b⟩ ≥ β}` and `C₂` in the opposite one. -/
def SeparableProperlyNotContaining (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesProperlyRn b β C₁ C₂ ∧ ¬ C₂ ⊆ {x | pairing n x b = β}

/-- **The bridge to the backbone** for `SeparableProperlyNotContaining`, exactly as §11's
`separableProperly_iff_exists`: the side swap is `SeparatesProperly.symm`, the condition `b ≠ 0` is
`SeparatesProperly.ne_zero`, and "properly" is not an extra demand once `C₂` is known not to lie
inside the hyperplane. -/
theorem separableProperlyNotContaining_iff_exists {C₁ C₂ : Set (Rn n)}
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔
      ∃ (g : Rn n →L[ℝ] ℝ) (c : ℝ), Separates g c C₁ C₂ ∧ ¬ C₂ ⊆ {x | g x = c} := by
  constructor
  · rintro ⟨b, β, ⟨-, hsep⟩, hns⟩
    refine ⟨-linFn b, -β, hsep.toSeparates.symm, fun hcon => hns fun x hx => ?_⟩
    simpa using hcon hx
  · rintro ⟨g, c, hsep, hns⟩
    have hprop : SeparatesProperly g c C₁ C₂ :=
      ⟨hsep, fun hcon => hns fun x hx => hcon (Set.mem_union_right _ hx)⟩
    obtain ⟨b, hb⟩ := exists_linFn (-g)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hprop.ne_zero hne₁ hne₂ hz
    refine ⟨b, -c, ⟨hb0, by rw [hb]; exact hprop.symm⟩, fun hcon => hns fun x hx => ?_⟩
    have h : pairing n x b = -c := hcon hx
    rw [← linFn_apply, hb] at h
    simpa using h

/-! ### Theorem 20.1 and its corollary -/

/-- **Rockafellar, §20 (p. 179)**, the all-polyhedral case `k = m`: if `f` and `g` are proper
polyhedral convex functions whose effective domains meet at all, then `(f + g)* = f* □ g*`. No
relative interior appears anywhere in the hypothesis.

Specialises `IsExactSum.of_polyhedral_pair` and `IsExactSum.conj_add`. Rockafellar presents this in
the unnumbered opening paragraph, as the computation that motivates Theorem 20.1; it is also the
base case of the backbone's proof of Theorem 20.1. -/
theorem theorem_20_1_pair_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : PolyhedralFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ dom g) :
    conj (pairing n) (f + g) = infConv (conj (pairing n) f) (conj (pairing n) g) :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).conj_add

/-- **Rockafellar, §20 (p. 179)**, the all-polyhedral case, attainment: under the same hypothesis
the infimum defining `(f* □ g*)(x*)` is attained for every `x*`.

Specialises `IsExactSum.exists_conj_add_eq`; the attainment is Corollary 19.3.4. -/
theorem theorem_20_1_pair_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : PolyhedralFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ dom g)
    (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      conj (pairing n) f y₁ + conj (pairing n) g y₂ = conj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).exists_conj_add_eq y

/-- **Rockafellar, Theorem 20.1.** Let `f` and `g` be proper convex functions on `ℝⁿ` with `f`
polyhedral, and assume that `dom f ∩ ri (dom g)` is not empty. Then

`(f + g)*(x*) = (f* □ g*)(x*) = inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}`.

Specialises `IsExactSum.of_polyhedral` and `IsExactSum.conj_add`. **The asymmetry is the point**:
the polyhedral summand contributes only a point of `dom f`, the other a point of `ri (dom g)`.
Compare `theorem_16_4_exact`, which asks for a point of `ri (dom f) ∩ ri (dom g)`, and
`theorem_20_1_pair_exact`, which asks for neither relative interior. Which backbone lemma supplies
which half is spelled out in the module docstring. -/
theorem theorem_20_1_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : x₀ ∈ ri (dom g)) :
    conj (pairing n) (f + g) = infConv (conj (pairing n) f) (conj (pairing n) g) :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).conj_add

/-- **Rockafellar, Theorem 20.1**, the attainment clause: under the same qualification, for each
`x*` the infimum `inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}` is attained.

Specialises `IsExactSum.exists_conj_add_eq`. -/
theorem theorem_20_1_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ dom f)
    (hxg : x₀ ∈ ri (dom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      conj (pairing n) f y₁ + conj (pairing n) g y₂ = conj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).exists_conj_add_eq y

section Corollary_20_1_1

variable {f g : Rn n → EReal}

/-- Theorem 20.1 applied to the conjugate functions, which is Rockafellar's one-line proof of
Corollary 20.1.1. Private: the two public statements below are the corollary's two clauses. -/
private theorem isExactSum_conj_of_polyhedral (hf : PolyhedralFn f)
    (hcf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ dom (conj (pairing n) f)) (hxg : x₀ ∈ ri (dom (conj (pairing n) g))) :
    IsExactSum (pairing n) (conj (pairing n) f) (conj (pairing n) g) :=
  IsExactSum.of_polyhedral (B := pairing n) (PolyhedralFn.conj hf) (proper_conj hcf)
    (convexFn_conj _ _) (proper_conj hg) hxf hxg

/-- The infimal convolution is the conjugate of the sum of the conjugates. Both clauses of
Corollary 20.1.1 are read off this identity. -/
private theorem infConv_eq_conj_add_conj (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ dom (conj (pairing n) f))
    (hxg : x₀ ∈ ri (dom (conj (pairing n) g))) :
    infConv f g = conj (pairing n) (conj (pairing n) f + conj (pairing n) g) := by
  have hff : conj (pairing n) (conj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : conj (pairing n) (conj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  rw [(isExactSum_conj_of_polyhedral hf hcf hg hxf hxg).conj_add, hff, hgg]

/-- **Rockafellar, Corollary 20.1.1.** Let `f` and `g` be closed proper convex functions on `ℝⁿ`
with `f` polyhedral, and assume that `dom f* ∩ ri (dom g*)` is not empty. Then `f □ g` is a closed
proper convex function.

Rockafellar's proof verbatim: apply Theorem 20.1 to the conjugate functions. `f*` is polyhedral by
Theorem 19.2 (`PolyhedralFn.conj`), so `(f* + g*)* = f** □ g** = f □ g` by Theorem 12.2, and a
conjugate is closed and convex outright. Properness is `IsExactSum.proper_add` followed by
`proper_conj_of_proper`. -/
theorem corollary_20_1_1 (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ dom (conj (pairing n) f))
    (hxg : x₀ ∈ ri (dom (conj (pairing n) g))) :
    ClosedProperConvexFn (infConv f g) := by
  have hexact := isExactSum_conj_of_polyhedral hf hcf hg hxf hxg
  rw [infConv_eq_conj_add_conj hf hcf hg hxf hxg]
  exact ⟨convexFn_conj _ _, closedFn_conj, proper_conj_of_proper
    (ConvexFn.add (convexFn_conj _ _) (convexFn_conj _ _)
      (proper_conj hcf).ne_bot (proper_conj hg).ne_bot) hexact.proper_add⟩

/-- **Rockafellar, Corollary 20.1.1**, the attainment clause: under the same hypothesis the
infimum in the definition of `(f □ g)(x)` is attained for every `x`.

Specialises `IsExactSum.exists_conj_add_eq` applied to the conjugates, read back through
Theorem 12.2. -/
theorem corollary_20_1_1_attained (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ dom (conj (pairing n) f))
    (hxg : x₀ ∈ ri (dom (conj (pairing n) g))) (x : Rn n) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f x₁ + g x₂ = infConv f g x := by
  have hff : conj (pairing n) (conj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : conj (pairing n) (conj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  obtain ⟨x₁, x₂, hsum, hval⟩ :=
    (isExactSum_conj_of_polyhedral hf hcf hg hxf hxg).exists_conj_add_eq x
  refine ⟨x₁, x₂, hsum, ?_⟩
  rw [infConv_eq_conj_add_conj hf hcf hg hxf hxg, ← hval, hff, hgg]

end Corollary_20_1_1

/-- **Rockafellar, Theorem 20.1** in the book's own `m`-ary form. Let `f₁, …, fₘ` be proper convex
functions on `ℝⁿ` such that `f₁, …, f_k` are polyhedral, and assume that

`dom f₁ ∩ ⋯ ∩ dom f_k ∩ ri (dom f_{k+1}) ∩ ⋯ ∩ ri (dom fₘ)`

is not empty. Then `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*`.

`t` is the book's `{1, …, k}` and `u` its complement; the splitting of the index set is spelled
membership-wise so that no `DecidableEq` instance enters the statement. Specialises
`IsExactFinsetSum.of_polyhedral` and `IsExactFinsetSum.conj_finsetSum`. **The asymmetry is the
point**: each polyhedral summand contributes only a point of `dom fᵢ`, each of the others a point
of `ri (dom fᵢ)`. Compare `theorem_16_4_exact_finset`, which asks for a relative interior point on
every index. -/
theorem theorem_20_1_exact_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ dom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (f i))) :
    conj (pairing n) (∑ i ∈ s, f i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (conj (pairing n) (f i))) :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).conj_finsetSum

/-- **Rockafellar, Theorem 20.1**, the attainment clause for `m` summands: under the same
qualification, for each `x*` the infimum
`inf {f₁*(x₁*) + ⋯ + fₘ*(xₘ*) | x₁* + ⋯ + xₘ* = x*}` is attained.

Specialises `IsExactFinsetSum.exists_conj_finsetSum_eq`. -/
theorem theorem_20_1_attained_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ dom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (f i))) (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, conj (pairing n) (f i) (y' i) = conj (pairing n) (∑ i ∈ s, f i) y :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).exists_conj_finsetSum_eq y

section Corollary_20_1_1_finset

variable {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
variable (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
variable (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hcf : ∀ i ∈ s, ClosedProperConvexFn (f i))
variable {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ dom (conj (pairing n) (f i)))
variable (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (conj (pairing n) (f i))))

include hs hdisj hmem hpoly hcf hxt hxu

/-- Theorem 20.1 applied to the conjugate functions, which is Rockafellar's one-line proof of
Corollary 20.1.1. Private: the two public statements below are the corollary's two clauses. -/
private theorem isExactFinsetSum_conj_of_polyhedral :
    IsExactFinsetSum (pairing n) s fun i => conj (pairing n) (f i) :=
  IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem
    (fun i hi => PolyhedralFn.conj (B := pairing n) (hpoly i hi))
    (fun i _ => convexFn_conj (pairing n) (f i)) (fun i hi => proper_conj (hcf i hi)) hxt hxu

/-- The `m`-fold infimal convolution is the conjugate of the sum of the conjugates. Both clauses
of Corollary 20.1.1 are read off this identity, exactly as in the binary case. -/
private theorem sum_toInfConvFn_eq_conj_finsetSum_conj :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))
      = conj (pairing n) (∑ i ∈ s, conj (pairing n) (f i)) := by
  have hbi : ∀ i ∈ s, conj (pairing n) (conj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  rw [(isExactFinsetSum_conj_of_polyhedral hs hdisj hmem hpoly hcf hxt hxu).conj_finsetSum]
  exact congrArg ofInfConvFn
    (Finset.sum_congr rfl fun i hi => congrArg toInfConvFn (hbi i hi).symm)

/-- **Rockafellar, Corollary 20.1.1** in the book's own `m`-ary form. Let `f₁, …, fₘ` be closed
proper convex functions on `ℝⁿ` such that `f₁, …, f_k` are polyhedral, and assume that

`dom f₁* ∩ ⋯ ∩ dom f_k* ∩ ri (dom f_{k+1}*) ∩ ⋯ ∩ ri (dom fₘ*)`

is not empty. Then `f₁ □ ⋯ □ fₘ` is a closed proper convex function.

Rockafellar's proof verbatim: apply Theorem 20.1 to the conjugates. Each `fᵢ*` is polyhedral for
`i ≤ k` by Theorem 19.2 (`PolyhedralFn.conj`), so `(f₁* + ⋯ + fₘ*)* = f₁** □ ⋯ □ fₘ** =
f₁ □ ⋯ □ fₘ` by Theorem 12.2, and a conjugate is closed and convex outright. Properness is
`IsExactFinsetSum.proper_finsetSum` followed by `proper_conj_of_proper`. -/
theorem corollary_20_1_1_finset :
    ClosedProperConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  have hx₀ : ∀ i ∈ s, x₀ ∈ dom (conj (pairing n) (f i)) := fun i hi =>
    (hmem i).1 hi |>.elim (fun h => hxt i h) fun h => intrinsicInterior_subset (hxu i h)
  obtain ⟨hconvsum, -, -⟩ :=
    properConvexFn_finsetSum (f := fun i => conj (pairing n) (f i))
      (fun i _ => convexFn_conj (pairing n) (f i)) (fun i hi => proper_conj (hcf i hi)) hx₀
  rw [sum_toInfConvFn_eq_conj_finsetSum_conj hs hdisj hmem hpoly hcf hxt hxu]
  exact ⟨convexFn_conj _ _, closedFn_conj, proper_conj_of_proper hconvsum
    (isExactFinsetSum_conj_of_polyhedral hs hdisj hmem hpoly hcf hxt hxu).proper_finsetSum⟩

/-- **Rockafellar, Corollary 20.1.1**, the attainment clause: under the same hypothesis the
infimum in the definition of `(f₁ □ ⋯ □ fₘ)(x)` is attained for every `x`.

Specialises `IsExactFinsetSum.exists_conj_finsetSum_eq` applied to the conjugates, read back
through Theorem 12.2. -/
theorem corollary_20_1_1_attained_finset (x : Rn n) :
    ∃ x' : ι → Rn n, ∑ i ∈ s, x' i = x ∧
      ∑ i ∈ s, f i (x' i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)) x := by
  have hbi : ∀ i ∈ s, conj (pairing n) (conj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  obtain ⟨x', hx', hval⟩ :=
    (isExactFinsetSum_conj_of_polyhedral hs hdisj hmem hpoly hcf hxt hxu).exists_conj_finsetSum_eq
      x
  refine ⟨x', hx', ?_⟩
  rw [sum_toInfConvFn_eq_conj_finsetSum_conj hs hdisj hmem hpoly hcf hxt hxu, ← hval]
  exact Finset.sum_congr rfl fun i hi => congrArg (fun k => k (x' i)) (hbi i hi).symm

end Corollary_20_1_1_finset

/-! ### Theorem 20.2 and its corollary -/

/-- **Rockafellar, Theorem 20.2.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ` such that
`C₁` is polyhedral. In order that there exist a hyperplane separating `C₁` and `C₂` properly and
not containing `C₂`, it is necessary and sufficient that `C₁ ∩ ri C₂ = ∅`.

Specialises `exists_separates_not_subset_iff_disjoint_relint`, through
`separableProperlyNotContaining_iff_exists`. Compare Theorem 11.3, which asks for
`ri C₁ ∩ ri C₂ = ∅` and promises nothing about containment: polyhedrality of `C₁` buys both
improvements at once. Convexity of `C₁` is not a separate hypothesis — it follows from
polyhedrality (`Polyhedral.convex`). -/
theorem theorem_20_2 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔ C₁ ∩ ri C₂ = ∅ := by
  rw [separableProperlyNotContaining_iff_exists hne₁ hne₂,
    exists_separates_not_subset_iff_disjoint_relint (isPolyhedral_iff_polyhedral.1 h₁) h₂ hne₂,
    Set.disjoint_iff_inter_eq_empty]

/-- **Rockafellar, Corollary 20.2.1.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ` such that
`C₁` is polyhedral. In order that `C₁ ∩ ri C₂` be non-empty, it is necessary and sufficient that
every vector `x*` which satisfies `δ*(x* | C₁) ≤ -δ*(-x* | C₂)` also satisfies
`δ*(x* | C₁) = δ*(x* | C₂)`.

Specialises `nonempty_inter_relint_iff_forall_supportFn`. The hypothesis on `x*` says that some
hyperplane orthogonal to `x*` separates the two sets; the conclusion says that every such
hyperplane contains `C₂`. This is Theorem 20.2 read through support functions, and it is the form
Theorem 20.3 applies to the barrier cones. -/
theorem corollary_20_2_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    (C₁ ∩ ri C₂).Nonempty ↔
      ∀ y : Rn n, supportFn (pairing n) C₁ y ≤ -supportFn (pairing n) C₂ (-y) →
        supportFn (pairing n) C₁ y = supportFn (pairing n) C₂ y :=
  nonempty_inter_relint_iff_forall_supportFn (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hne₂

/-! ### Theorem 20.3 and its corollary -/

/-- **Rockafellar, Theorem 20.3.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ` such that
`C₁` is polyhedral and `C₂` is closed. Suppose that every direction of recession of `C₁` whose
opposite is a direction of recession of `C₂` is actually a direction in which `C₂` is linear. Then
`C₁ + C₂` is closed.

Specialises `isClosed_add_of_polyhedral`. "`C₂` is linear in the direction `v`" is `v ∈ 0⁺C₂`
*given* `-v ∈ 0⁺C₂`, which is membership of the lineality space of `C₂`; the backbone states the
hypothesis in that unpacked form. Compare Corollary 9.1.1, which asks in addition that such a `v`
lie in the lineality space of `C₁`: polyhedrality of `C₁` removes that. -/
theorem theorem_20_3 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    IsClosed (C₁ + C₂) :=
  isClosed_add_of_polyhedral (B := pairing n) (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂
    hne₂ hrec

/-- **Rockafellar, Corollary 20.3.1.** Let `C₁` and `C₂` be non-empty convex sets in `ℝⁿ` such that
`C₁` is polyhedral, `C₂` is closed and `C₁ ∩ C₂ = ∅`. Suppose that `C₁` and `C₂` have no common
directions of recession, except for directions in which `C₂` is linear. Then there exists a
hyperplane separating `C₁` and `C₂` strongly.

Specialises `separatesStrongly_of_polyhedral_of_recession`, through §11's
`separableStrongly_iff_exists`. Compare Corollary 11.4.1, which forbids common recession directions
outright, and Corollary 19.3.3, where both sets are polyhedral and no recession hypothesis is
needed at all. -/
theorem corollary_20_3_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty) (hdisj : C₁ ∩ C₂ = ∅)
    (hrec : ∀ v ∈ recessionCone C₁, v ∈ recessionCone C₂ → -v ∈ recessionCone C₂) :
    SeparableStrongly C₁ C₂ := by
  rw [separableStrongly_iff_exists hne₁ hne₂]
  exact separatesStrongly_of_polyhedral_of_recession (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂ hne₂
    (Set.disjoint_iff_inter_eq_empty.2 hdisj) hrec

/-! ### Theorems 20.4 and 20.5 -/

/-- **Rockafellar, Theorem 20.4.** Let `C` be a closed bounded set, and let `D` be any convex set
such that `C ⊆ int D`. Then there exists a polyhedral convex set `P` such that `P ⊆ int D` and
`C ⊆ int P`.

Specialises `exists_polyhedral_between`. Rockafellar covers `C` by simplices whose interiors
contain the points of `C`; the backbone covers it by coordinate cubes instead, which are polyhedral
by inspection, and takes `P` to be the convex hull of the finitely many cubes' vertex sets —
polyhedral by Corollary 19.1.1.

**Rockafellar also assumes `C` non-empty and convex, and neither hypothesis is used**; see the
module docstring. -/
theorem theorem_20_4 {C D : Set (Rn n)} (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C)
    (hD : Convex ℝ D) (hCD : C ⊆ interior D) :
    ∃ P : Set (Rn n), IsPolyhedral P ∧ P ⊆ interior D ∧ C ⊆ interior P := by
  obtain ⟨P, hPpoly, hPD, hCP⟩ := exists_polyhedral_between hCcl hCbdd hD hCD
  exact ⟨P, isPolyhedral_iff_polyhedral.2 hPpoly, hPD, hCP⟩

/-- **Rockafellar, Theorem 20.5.** Every polyhedral convex set is locally simplicial.

Specialises `Polyhedral.locallySimplicial`. The book's proof is a two-line sketch that *asserts*
the triangulation of a bounded polyhedron; the backbone's proof does not rely on it — see the
module docstring, which also records that §10's Theorem 10.2 does not depend on this result. -/
theorem theorem_20_5 {C : Set (Rn n)} (hC : IsPolyhedral C) : LocallySimplicial C :=
  Polyhedral.locallySimplicial (isPolyhedral_iff_polyhedral.1 hC)

/-- **Rockafellar, Theorem 20.5**, second clause: in particular, every polytope is locally
simplicial.

A polytope is the convex hull of a finite set of points, and is polyhedral by Corollary 19.1.1
(`polyhedral_convexHull_finset`). -/
theorem theorem_20_5_polytope (P : Finset (Rn n)) :
    LocallySimplicial (convexHull ℝ (P : Set (Rn n))) :=
  Polyhedral.locallySimplicial (polyhedral_convexHull_finset P)

end Rockafellar
