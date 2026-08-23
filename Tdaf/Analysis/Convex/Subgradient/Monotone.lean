/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Defs

/-!
# Monotonicity of the subdifferential

Rockafellar's §24. The subdifferential of a proper convex function is not merely *monotone* —
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` whenever `yᵢ ∈ ∂f xᵢ` — but **cyclically monotone**: every finite cycle
`(x₀, y₀), (x₁, y₁), …, (x_m, y_m)` in the graph satisfies

```
⟨x₁ - x₀, y₀⟩ + ⟨x₂ - x₁, y₁⟩ + ⋯ + ⟨x₀ - x_m, y_m⟩ ≤ 0.
```

**Theorem 24.8** says this is the whole story: a multivalued mapping is contained in the
subdifferential of a closed proper convex function exactly when it is cyclically monotone, and the
function can be written down — it is the supremum of the telescoping sums above, read as affine
functions of a free endpoint.

## Main definitions

* `chainVal B s l x` — Rockafellar's telescoping sum along the chain that starts at `s`, runs
  through the list `l`, and ends at `x`.
* `IsMonotoneRel B ρ`, `IsCyclicallyMonotone B ρ`, `IsMaximalCyclicallyMonotone B ρ`.
* `cyclicPotential B ρ s` — the function Rockafellar constructs in Theorem 24.8.

## Main results

* `IsCyclicallyMonotone.isMonotoneRel` — cyclic monotonicity implies monotonicity (the case of a
  two-element cycle), and `isMonotoneRel_subgradientRel` is the classical monotonicity of `∂f`.
* `isCyclicallyMonotone_subgradientRel` — **Theorem 24.8**, necessity: `∂f` is cyclically monotone
  for every proper `f`.
* `exists_convexFn_subgradientRel_of_isCyclicallyMonotone`,
  `isCyclicallyMonotone_iff_exists_convexFn` — **Theorem 24.8**, sufficiency and the full
  equivalence.
* `exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone` — **Theorem 24.9**, the half that
  follows from Theorem 24.8: a maximal cyclically monotone mapping *is* a subdifferential.
* `isClosed_subgradientRel` — **Theorem 24.4**: the graph of `∂f` is closed.

## Design notes

**Cycles are lists, not `Fin (m+1)`-indexed families.** Rockafellar writes a cycle as a finite
sequence of pairs; `chainVal` is the same object defined by recursion on a `List (E × F)`, with the
starting pair carried separately so that the recursion step is literally "walk one edge and
recurse". Every proof in the section is then a list induction: the telescoping estimate
`le_of_chain_mem_subgradientRel`, the append lemma `chainVal_append_singleton` that adds the last
edge of the cycle, and the affineness lemma `exists_chainVal_eq` that makes `cyclicPotential` a
supremum of affine functions. A `Fin`-indexed statement would need `Finset.sum_equiv` along
`i ↦ i + 1` for the telescoping and would gain nothing.

**`chainVal B s l x` has the free endpoint last.** That is what makes `cyclicPotential` a supremum
of affine functions of `x` (`exists_chainVal_eq`: `chainVal B s l x = ⟨x, y⟩ - c` for a `(y, c)`
depending only on `s` and `l`), and it makes the cycle condition read
`chainVal B s l s.1 ≤ 0` — "come back to where you started".

**Theorem 24.4 asks for joint continuity of the pairing.** `IsContinuousPairing B` gives continuity
of `⟨·, y⟩` for each fixed `y`, which is not enough to pass to the limit in `⟨z - xᵢ, yᵢ⟩` when both
arguments move. In `ℝⁿ` the hypothesis is automatic; here it is an explicit
`Continuous fun p : E × F => B p.1 p.2`.

## What is not here

**Theorems 24.1, 24.2, 24.3, 24.5, 24.6, 24.7 and the maximality half of 24.9 are not formalised.**
Theorems 24.1–24.3 are the one-dimensional theory (`f'₊` and `f'₋` as nondecreasing functions, and
complete nondecreasing curves), which needs one-sided derivatives on `ℝ` that §23 does not provide.
Theorems 24.5–24.7 are the convergence and boundedness results, which rest on Theorems 10.6–10.9
(the equi-Lipschitz theory, deferred). The remaining half of Theorem 24.9 — that `∂f` is *maximal*
cyclically monotone — needs the uniqueness statement "`∂f ⊆ ∂g` implies `g = f + const`", which
Rockafellar proves from Theorem 23.4, Theorem 23.2 and a one-dimensional argument along segments in
`ri (dom f)`; the one-dimensional argument is the same material as Theorems 24.1–24.3.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24 (Theorems 24.4, 24.8,
  and half of 24.9).
* R. T. Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J.
  Math. **17** (1966) 497–510.
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### Chains and cyclic monotonicity -/

section Chain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Rockafellar's telescoping sum along a finite chain in the graph of a multivalued mapping. The
chain starts at the pair `s = (x₀, y₀)`, runs through `l = [(x₁, y₁), …, (x_m, y_m)]` and ends at
the free point `x`:

```
chainVal B s l x = ⟨x₁ - x₀, y₀⟩ + ⟨x₂ - x₁, y₁⟩ + ⋯ + ⟨x - x_m, y_m⟩.
```

Taking `x = x₀` closes the chain into a cycle. -/
def chainVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : E × F → List (E × F) → E → ℝ
  | s, [], x => B (x - s.1) s.2
  | s, q :: l, x => B (q.1 - s.1) s.2 + chainVal B q l x

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

@[simp] theorem chainVal_nil (s : E × F) (x : E) : chainVal B s [] x = B (x - s.1) s.2 := rfl

@[simp] theorem chainVal_cons (s q : E × F) (l : List (E × F)) (x : E) :
    chainVal B s (q :: l) x = B (q.1 - s.1) s.2 + chainVal B q l x := rfl

/-- Appending one more edge to a chain: the value along `l ++ [q]` ending at `z` is the value along
`l` ending at `q.1`, plus the last edge. This is the step that makes a chain into a longer chain in
the proof of Theorem 24.8. -/
theorem chainVal_append_singleton (s q : E × F) (l : List (E × F)) (z : E) :
    chainVal B s (l ++ [q]) z = chainVal B s l q.1 + B (z - q.1) q.2 := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [List.cons_append, chainVal_cons, ih]; ring

/-- A chain is affine in its free endpoint: `chainVal B s l x = ⟨x, y⟩ - c` for a `(y, c)` that
depends only on the chain. This is why `cyclicPotential` is a supremum of affine functions. -/
theorem exists_chainVal_eq (l : List (E × F)) (s : E × F) :
    ∃ (y : F) (c : ℝ), ∀ x, chainVal B s l x = B x y - c := by
  induction l generalizing s with
  | nil =>
    refine ⟨s.2, B s.1 s.2, fun x => ?_⟩
    rw [chainVal_nil, map_sub, LinearMap.sub_apply]
  | cons q l ih =>
    obtain ⟨y, c, h⟩ := ih q
    refine ⟨y, c - B (q.1 - s.1) s.2, fun x => ?_⟩
    rw [chainVal_cons, h x]
    ring

end Chain

/-! ### Monotone and cyclically monotone multivalued mappings -/

section Monotone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ σ : SetRel E F}

/-- A multivalued mapping is **monotone** when `⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` for all pairs in its
graph. -/
def IsMonotoneRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ p ∈ ρ, ∀ q ∈ ρ, 0 ≤ B (p.1 - q.1) (p.2 - q.2)

/-- A multivalued mapping is **cyclically monotone** when every finite cycle in its graph has
non-positive telescoping sum. Rockafellar's definition, with the cycle written as a starting pair
`s` followed by a list `l`; `chainVal B s l s.1` is the sum around the cycle. -/
def IsCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ s ∈ ρ, ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → chainVal B s l s.1 ≤ 0

/-- A cyclically monotone mapping is **maximal** when no strictly larger cyclically monotone
mapping contains it. Theorem 24.9 identifies these with the subdifferentials. -/
def IsMaximalCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  IsCyclicallyMonotone B ρ ∧ ∀ σ : SetRel E F, IsCyclicallyMonotone B σ → ρ ⊆ σ → σ ⊆ ρ

/-- Cyclic monotonicity passes to sub-mappings. -/
theorem IsCyclicallyMonotone.mono (h : IsCyclicallyMonotone B σ) (hsub : ρ ⊆ σ) :
    IsCyclicallyMonotone B ρ :=
  fun s hs l hl => h s (hsub hs) l fun q hq => hsub (hl q hq)

/-- **Cyclic monotonicity implies monotonicity**: a two-element cycle is exactly the monotonicity
inequality. -/
theorem IsCyclicallyMonotone.isMonotoneRel (h : IsCyclicallyMonotone B ρ) : IsMonotoneRel B ρ := by
  intro p hp q hq
  have hcyc := h p hp [q] (by simpa using hq)
  rw [chainVal_cons, chainVal_nil] at hcyc
  have hexp : B (p.1 - q.1) (p.2 - q.2) = -(B (q.1 - p.1) p.2 + B (p.1 - q.1) q.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp]
  linarith

/-- A one-element mapping is cyclically monotone: every cycle in it has all its edges equal to
zero. Used only to see that a maximal cyclically monotone mapping is nonempty. -/
theorem isCyclicallyMonotone_singleton (p : E × F) : IsCyclicallyMonotone B {p} := by
  have key : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ({p} : Set (E × F))) → chainVal B p l p.1 = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons q l ih =>
      intro hl
      have hq : q = p := hl q (by simp)
      subst hq
      rw [chainVal_cons, ih fun r hr => hl r (by simp [hr])]
      simp
  intro s hs l hl
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact le_of_eq (key l hl)

/-- A maximal cyclically monotone mapping is nonempty: the empty mapping is strictly contained in
the cyclically monotone `{(0, 0)}`. -/
theorem IsMaximalCyclicallyMonotone.nonempty (h : IsMaximalCyclicallyMonotone B ρ) :
    ρ.Nonempty := by
  rcases ρ.eq_empty_or_nonempty with hem | hne
  · have hsub := h.2 {((0 : E), (0 : F))} (isCyclicallyMonotone_singleton _)
      (by rw [hem]; exact Set.empty_subset _)
    rw [hem] at hsub
    exact absurd (hsub rfl) (Set.notMem_empty _)
  · exact hne

end Monotone

/-! ### Theorem 24.8, necessity: `∂f` is cyclically monotone -/

section Necessity

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The telescoping estimate: walking a chain of subgradients from `s` to `x` cannot gain more than
the increase of `f`. Rockafellar's chain of inequalities
`⟨x_{i+1} - x_i, y_i⟩ ≤ f x_{i+1} - f x_i`, summed. -/
theorem le_of_chain_mem_subgradientRel :
    ∀ (l : List (E × F)) (s : E × F), s ∈ subgradientRel B f →
      (∀ q ∈ l, q ∈ subgradientRel B f) →
        ∀ x, f s.1 + ((chainVal B s l x : ℝ) : EReal) ≤ f x := by
  intro l
  induction l with
  | nil => intro s hs _ x; simpa using hs x
  | cons q l ih =>
    intro s hs hl x
    have h₁ : f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) ≤ f q.1 := hs q.1
    have h₂ : f q.1 + ((chainVal B q l x : ℝ) : EReal) ≤ f x :=
      ih q (hl q (by simp)) (fun r hr => hl r (by simp [hr])) x
    calc f s.1 + ((chainVal B s (q :: l) x : ℝ) : EReal)
        = f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) + ((chainVal B q l x : ℝ) : EReal) := by
          rw [chainVal_cons, _root_.EReal.coe_add, add_assoc]
      _ ≤ f q.1 + ((chainVal B q l x : ℝ) : EReal) := add_le_add h₁ (le_refl _)
      _ ≤ f x := h₂

/-- **Rockafellar, Theorem 24.8**, necessity: the graph of `∂f` is cyclically monotone. Convexity
of `f` is not used; properness is, and only to know that `f` is finite at the base point of the
cycle. -/
theorem isCyclicallyMonotone_subgradientRel (hp : Proper f) :
    IsCyclicallyMonotone B (subgradientRel B f) := by
  intro s hs l hl
  have hkey := le_of_chain_mem_subgradientRel l s hs hl s.1
  have hdom : s.1 ∈ dom f := by
    by_contra hcon
    have hmem : s.2 ∈ subgradient B f s.1 := hs
    rw [subgradient_eq_empty_of_notMem_dom hp hcon] at hmem
    exact hmem
  have hcoe : (((f s.1).toReal : ℝ) : EReal) = f s.1 :=
    _root_.EReal.coe_toReal (ne_of_lt hdom) (hp.ne_bot s.1)
  rw [← hcoe, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hkey
  linarith

/-- **The subdifferential is monotone**, the classical inequality
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0`. -/
theorem isMonotoneRel_subgradientRel (hp : Proper f) :
    IsMonotoneRel B (subgradientRel B f) :=
  (isCyclicallyMonotone_subgradientRel hp).isMonotoneRel

end Necessity

/-! ### Theorem 24.8, sufficiency: Rockafellar's potential -/

section Potential

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ : SetRel E F} {s : E × F}

/-- **Rockafellar's potential**, the function built in the proof of Theorem 24.8: the supremum of
the telescoping sums of all finite chains in `ρ` that start at `s` and end at `x`. It is a supremum
of affine functions of `x`, hence a closed convex function, and cyclic monotonicity of `ρ` is
exactly what keeps it from being `+∞` at `s.1`. -/
noncomputable def cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F)
    (x : E) : EReal :=
  ⨆ l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}, ((chainVal B s l x : ℝ) : EReal)

theorem le_cyclicPotential {l : List (E × F)} (hl : ∀ q ∈ l, q ∈ ρ) (s : E × F) (x : E) :
    ((chainVal B s l x : ℝ) : EReal) ≤ cyclicPotential B ρ s x :=
  le_iSup₂ (f := fun l (_ : l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}) =>
    ((chainVal B s l x : ℝ) : EReal)) l hl

theorem cyclicPotential_le {c : EReal} {x : E}
    (h : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → ((chainVal B s l x : ℝ) : EReal) ≤ c) :
    cyclicPotential B ρ s x ≤ c :=
  iSup₂_le h

/-- The potential is convex: it is a supremum of affine functions (Theorem 5.5). -/
theorem convexFn_cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) :
    ConvexFn (cyclicPotential B ρ s) := by
  refine convexFn_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact convexFn_affineFn y c

/-- The potential never takes the value `-∞`: the empty chain already gives it a real lower
bound. -/
theorem cyclicPotential_ne_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) (x : E) :
    cyclicPotential B ρ s x ≠ ⊥ := by
  intro h
  have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s x
  rw [h, le_bot_iff] at hle
  exact _root_.EReal.coe_ne_bot _ hle

/-- **Cyclic monotonicity is exactly what makes the potential finite at its base point**, where it
vanishes. -/
theorem cyclicPotential_eq_zero (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    cyclicPotential B ρ s s.1 = 0 := by
  refine le_antisymm (cyclicPotential_le fun l hl => ?_) ?_
  · exact_mod_cast hρ s hs l hl
  · have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s s.1
    simpa using hle

/-- The potential is proper. -/
theorem proper_cyclicPotential (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    Proper (cyclicPotential B ρ s) := by
  refine ⟨⟨s.1, ?_⟩, cyclicPotential_ne_bot B ρ s⟩
  change cyclicPotential B ρ s s.1 < ⊤
  rw [cyclicPotential_eq_zero hρ hs, ← _root_.EReal.coe_zero]
  exact _root_.EReal.coe_lt_top 0

/-- **Every pair of `ρ` is a subgradient of the potential.** Rockafellar's argument: a chain
ending at `x` followed by the edge `(x, y)` is again a chain, so the supremum defining
`f z` dominates `chainVal … x + ⟨z - x, y⟩` for every chain, hence `f x + ⟨z - x, y⟩ ≤ f z`. -/
theorem mem_subgradient_cyclicPotential {p : E × F} (hp : p ∈ ρ) :
    p.2 ∈ subgradient B (cyclicPotential B ρ s) p.1 := by
  intro z
  have key : cyclicPotential B ρ s p.1
      ≤ cyclicPotential B ρ s z - ((B (z - p.1) p.2 : ℝ) : EReal) := by
    refine cyclicPotential_le fun l hl => ?_
    have hvalid : ∀ q ∈ l ++ [p], q ∈ ρ := by
      intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact hl q h
      · rw [List.mem_singleton.1 h]
        exact hp
    have hle := le_cyclicPotential (B := B) hvalid s z
    rw [chainVal_append_singleton, _root_.EReal.coe_add] at hle
    exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
      (c := cyclicPotential B ρ s z) (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _))).2 hle
  exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
    (c := cyclicPotential B ρ s z) (.inl (_root_.EReal.coe_ne_bot _))
    (.inl (_root_.EReal.coe_ne_top _))).1 key

end Potential

/-! ### Theorem 24.8 and Theorem 24.9 -/

section Main

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  {ρ : SetRel E F}

/-- **Rockafellar, Theorem 24.8**, sufficiency: a nonempty cyclically monotone multivalued mapping
is contained in the subdifferential of a closed proper convex function. -/
theorem exists_convexFn_subgradientRel_of_isCyclicallyMonotone [IsContinuousPairing B]
    (hρ : IsCyclicallyMonotone B ρ) (hne : ρ.Nonempty) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ ⊆ subgradientRel B f := by
  obtain ⟨s, hs⟩ := hne
  refine ⟨cyclicPotential B ρ s, convexFn_cyclicPotential B ρ s, ?_,
    proper_cyclicPotential hρ hs, fun p hp => mem_subgradient_cyclicPotential hp⟩
  refine (closedFn_iff_lowerSemicontinuous (cyclicPotential_ne_bot B ρ s)).2 ?_
  refine lowerSemicontinuous_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact lowerSemicontinuous_affineFn (continuous_pairing B y)

/-- **Rockafellar, Theorem 24.8**: for a nonempty multivalued mapping, being contained in a
subdifferential and being cyclically monotone are the same thing. -/
theorem isCyclicallyMonotone_iff_exists_convexFn [IsContinuousPairing B] (hne : ρ.Nonempty) :
    IsCyclicallyMonotone B ρ ↔
      ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ ⊆ subgradientRel B f :=
  ⟨fun h => exists_convexFn_subgradientRel_of_isCyclicallyMonotone h hne,
    fun ⟨_, _, _, hp, hsub⟩ => (isCyclicallyMonotone_subgradientRel hp).mono hsub⟩

/-- **Rockafellar, Theorem 24.9**, the half that Theorem 24.8 gives at once: a maximal cyclically
monotone multivalued mapping *is* the subdifferential of a closed proper convex function. -/
theorem exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone [IsContinuousPairing B]
    (h : IsMaximalCyclicallyMonotone B ρ) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ = subgradientRel B f := by
  obtain ⟨f, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone h.1 h.nonempty
  exact ⟨f, hconv, hclosed, hproper,
    Subset.antisymm hsub (h.2 _ (isCyclicallyMonotone_subgradientRel hproper) hsub)⟩

end Main

/-! ### Theorem 24.4: the graph of `∂f` is closed -/

section GraphClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Rockafellar, Theorem 24.4**: the graph of `∂f` is a closed subset of `E × F`. Equivalently,
`xᵢ* ∈ ∂f xᵢ`, `xᵢ → x` and `xᵢ* → x*` force `x* ∈ ∂f x`.

Convexity of `f` is not used. Lower semicontinuity is, and so is joint continuity of the pairing:
the subgradient inequality at `xᵢ` involves `⟨z - xᵢ, xᵢ*⟩`, where both arguments move. -/
theorem isClosed_subgradientRel [IsTopologicalAddGroup E]
    (hB : Continuous fun p : E × F => B p.1 p.2) (hp : Proper f)
    (hlsc : LowerSemicontinuous f) : IsClosed (subgradientRel B f) := by
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  have hrw : subgradientRel B f
      = ⋂ z : E, {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z} := by
    ext p
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [hrw]
  refine isClosed_iInter fun z => ?_
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · convert isClosed_univ
    ext p
    simp [hz]
  · set r : ℝ := (f z).toReal with hrdef
    have hrz : ((r : ℝ) : EReal) = f z := _root_.EReal.coe_toReal hz (hp.ne_bot z)
    have hset : {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z}
        = (fun p : E × F => (p.1, r - B (z - p.1) p.2)) ⁻¹' epi f := by
      ext p
      rw [Set.mem_preimage, mem_epi, Set.mem_ofPred_eq, ← hrz, _root_.EReal.coe_sub]
      exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
        (c := ((r : ℝ) : EReal)) (.inl (_root_.EReal.coe_ne_bot _))
        (.inl (_root_.EReal.coe_ne_top _))).symm
    rw [hset]
    refine hepi.preimage (continuous_fst.prodMk ?_)
    exact continuous_const.sub
      (hB.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd))

end GraphClosed

end Tdaf.ConvexAnalysis
