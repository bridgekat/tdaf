/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Calculus
import Tdaf.Analysis.Convex.Subgradient.Convergence
import Tdaf.Analysis.Convex.Subgradient.Gradient

/-!
# A unique subgradient forces differentiability

The converse half of Rockafellar's **Theorem 25.1**: a convex function with exactly one subgradient
at `x` is differentiable at `x`, and that subgradient is the gradient. Together with
`subgradient_eq_singleton_of_hasFDerivAt` this makes Theorem 25.1 an equivalence, and it upgrades
**Corollaries 25.1.2 and 25.1.3** from their subgradient form to the differentiability form the
book states.

## Main results

* `mem_interior_dom_of_subgradient_eq_singleton` — a lone subgradient puts `x` in the *interior*
  of `dom f`.
* `hasGradientAt_evalCLM_of_subgradient_eq_singleton` — **Theorem 25.1**, converse half, for an
  arbitrary compatible pairing.
* `hasGradientAt_iff_subgradient_eq_singleton`,
  `differentiableAtFn_iff_exists_subgradient_eq_singleton` — **Theorem 25.1** in full.
* `hasGradientAt_clFn_iff`, `differentiableAtFn_clFn_iff` — the **remark after Corollary 25.1.1**,
  `∇(cl f) = ∇f`.
* `exists_subgradient_clFn_eq_singleton_iff` — together with `posHomogeneous_clFn` and
  `supportSet_clFn` (`Duality/Support.lean`), what lets the book's reduction to `cl f` be carried
  out.
* `mem_exposedPoints_epi_conj_iff_of_proper`, `mem_exposedPoints_supportSet_iff_of_proper` —
  **Corollaries 25.1.2 and 25.1.3** for an arbitrary compatible pairing, with the `ClosedFn`
  hypothesis of their `Gradient.lean` originals removed.
* `mem_exposedPoints_epi_conj_iff_hasGradientAt` — **Corollary 25.1.2**.
* `mem_exposedPoints_supportSet_iff_hasGradientAt` — **Corollary 25.1.3**.

## Design notes

**The whole difficulty is the interior step.** Once `x` is interior to `dom f`, the directional
derivative `f'(x; ·)` is finite in every direction, hence a finite convex function on the whole
space, hence continuous and closed; Theorem 23.2 — which computes only `cl f'(x; ·)`, as the
support function of `∂f x` — therefore computes `f'(x; ·)` itself, and it is the linear function
`⟨·, y₀⟩`. Theorem 25.2's sufficiency half (`hasGradientAt_of_dirDeriv_eq`) finishes.

Rockafellar's own proof takes the interior step for granted: his Theorem 25.1 says "let `f` be
finite at `x`", and the closure subtlety in Theorem 23.2 is waved through. The step is genuine, and
it is the reason this file exists rather than a dozen lines at the end of `Gradient.lean`:
`∂f x + N_{dom f}(x) ⊆ ∂f x` (`subgradient_add_normalCone_dom_subset`) makes the normal cone
trivial, and a convex set in finite dimensions is a neighbourhood of every point whose normal cone
is trivial (`mem_interior_of_normalCone_eq_zero`, Corollary 11.6.1 read through the pairing).
Theorem 23.4's own interiority clause is no shortcut: `bddAbove_subgradient_iff_mem_interior_dom`
already assumes `x ∈ ri (dom f)`, which is what has to be proved.

**`∇(cl f) = ∇f` is where the closedness of Corollaries 25.1.2 and 25.1.3 goes.** Rockafellar
states both for a merely proper convex `f` and reduces to the closed case by replacing `f` with
`cl f`, on the strength of a one-sentence remark after Corollary 25.1.1 — that `∇f` and `∇(cl f)`
coincide "inasmuch as `f` and `cl f` coincide on `int (dom f)`". That is half the argument: it
gives every gradient of `f` to `cl f`, but the other direction has to know that `cl f` has no
*extra* interior points to be differentiable at, which is `ConvexFn.interior_dom_clFn`
(`RelativeInterior.lean`, beside Corollary 7.4.1) and not the sentence quoted. With that,
`hasGradientAt_clFn_iff` holds and both corollaries carry the book's hypotheses. The corresponding *subgradient* statements in `Gradient.lean` keep their `ClosedFn`,
because `∂f = ∂(cl f)` is false at relative boundary points; only the gradients transfer.

**Why not go through Corollary 24.5.1.** Upper semicontinuity of `∂f` gives the Fréchet estimate
directly — for `y ∈ ∂f z` with `z` near `x`, the two subgradient inequalities sandwich
`0 ≤ f z - f x - ⟨z - x, y₀⟩ ≤ ⟨z - x, y - y₀⟩ ≤ ε ‖z - x‖` — and that is the route
`Saddle/Subgradient.lean` takes for saddle-functions, where no `dirDeriv` API exists. It needs the
same interior step, since Corollary 24.5.1 and Theorem 23.4 both want `x ∈ int (dom f)`, so it
saves nothing here, and it would duplicate Theorem 25.2 rather than use it.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §11 (Corollary 11.6.1);
  §23 (Theorems 23.2, 23.4); §25 (Theorem 25.1, Corollaries 25.1.2 and 25.1.3).
-/

open Set

namespace Tdaf.ConvexAnalysis

/-! ### The interior step -/

section Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

include B in
/-- **A lone subgradient puts `x` in the interior of `dom f`.** This is the step Rockafellar's
Theorem 25.1 passes over: `∂f x = {y₀}` leaves no room for a normal direction to `dom f`
(`normalCone_dom_eq_zero_of_subgradient_eq_singleton`), and in finite dimensions a convex set is a
neighbourhood of every point at which its normal cone is trivial. -/
theorem mem_interior_dom_of_subgradient_eq_singleton [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : Proper f) (h : subgradient B f x = {y₀}) : x ∈ interior (dom f) := by
  have hy₀ : y₀ ∈ subgradient B f x := by rw [h]; rfl
  exact mem_interior_of_normalCone_eq_zero hf.convex_dom (mem_dom_of_mem_subgradient hp hy₀)
    (normalCone_dom_eq_zero_of_subgradient_eq_singleton h)

end Interior

/-! ### Theorem 25.1, converse half -/

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

/-- **At an interior point of `dom f` the directional derivative is its own closure.** It is finite
in every direction there, hence a finite convex function on the whole space, hence continuous by
Corollary 10.1.1 — and a continuous function is closed. This is what removes the `cl` from
Theorem 23.2. -/
theorem closedFn_dirDeriv_of_mem_interior_dom (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) : ClosedFn (dirDeriv f x) := by
  have hri : x ∈ ri (dom f) := Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hx
  have hgp : Proper (dirDeriv f x) := proper_dirDeriv_of_mem_relint_dom hf hp hri
  have hgc : ConvexFn (dirDeriv f x) :=
    convexFn_dirDeriv hf (mem_dom.1 (interior_subset hx)).ne (hp.ne_bot x)
  have hdom : dom (dirDeriv f x) = univ :=
    (dom_dirDeriv_eq_univ_iff_mem_interior_dom hf hp hri).2 hx
  exact (closedFn_iff_lowerSemicontinuous hgp.ne_bot).2
    (hgc.continuous_of_dom_eq_univ hgp hdom).lowerSemicontinuous

/-- **Rockafellar, Theorem 25.1**, converse half: a convex function with a *unique* subgradient at
`x` is differentiable there, and the subgradient is the gradient.

The three steps are the interior step, Theorem 23.2 with its closure removed, and Theorem 25.2's
sufficiency half. Properness is what makes `f x` finite; the book's "let `f` be finite at `x`" is
weaker only in appearance, since at a point where `f = -∞` every element of `F` is a
subgradient. -/
theorem hasGradientAt_evalCLM_of_subgradient_eq_singleton [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : Proper f) (h : subgradient B f x = {y₀}) : HasGradientAt f (evalCLM B y₀) x := by
  have hint := mem_interior_dom_of_subgradient_eq_singleton hf hp h
  have ht : f x ≠ ⊤ := (mem_dom.1 (interior_subset hint)).ne
  have hb : f x ≠ ⊥ := hp.ne_bot x
  have hcl : clFn (dirDeriv f x) = dirDeriv f x := closedFn_dirDeriv_of_mem_interior_dom hf hp hint
  have heq : dirDeriv f x = fun v => ((B v y₀ : ℝ) : EReal) :=
    hcl.symm.trans (clFn_dirDeriv_eq_of_subgradient_eq_singleton hf ht hb h)
  exact hasGradientAt_of_dirDeriv_eq hf ht hb fun v => congrFun heq v

end Converse

/-! ### Theorem 25.1 in full -/

section Full

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- **Rockafellar, Theorem 25.1**, converse half, in the self-pairing of `E` with its continuous
dual: there `evalCLM` is the identity, so the unique subgradient *is* the gradient. -/
theorem hasGradientAt_of_subgradient_eq_singleton (hf : ConvexFn f) (hp : Proper f)
    (h : subgradient (topDualPairing ℝ E).flip f x = {f'}) : HasGradientAt f f' x :=
  hasGradientAt_evalCLM_of_subgradient_eq_singleton (B := (topDualPairing ℝ E).flip) hf hp h

/-- **Rockafellar, Theorem 25.1**, in full: for a proper convex function, having gradient `f'` at
`x` and having `f'` as sole subgradient at `x` are the same thing. -/
theorem hasGradientAt_iff_subgradient_eq_singleton (hf : ConvexFn f) (hp : Proper f) :
    HasGradientAt f f' x ↔ subgradient (topDualPairing ℝ E).flip f x = {f'} :=
  ⟨fun h => h.subgradient_eq hf, hasGradientAt_of_subgradient_eq_singleton hf hp⟩

/-- **Rockafellar, Theorem 25.1**, stated as the book states it: differentiability at `x` is
exactly the subdifferential being a single point. -/
theorem differentiableAtFn_iff_exists_subgradient_eq_singleton (hf : ConvexFn f) (hp : Proper f) :
    DifferentiableAtFn f x ↔
      ∃ y : StrongDual ℝ E, subgradient (topDualPairing ℝ E).flip f x = {y} :=
  exists_congr fun _ => hasGradientAt_iff_subgradient_eq_singleton hf hp

end Full

/-! ### `∇(cl f) = ∇f` -/

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- **`cl f` agrees with `f` on a whole neighbourhood of an interior point of `dom f`.**
`interior (dom f)` is open and sits inside `ri (dom f)`, where Theorem 7.4 makes the two functions
equal pointwise. -/
theorem ConvexFn.clFn_eventuallyEq_of_mem_interior_dom (hf : ConvexFn f)
    (hx : x ∈ interior (dom f)) : clFn f =ᶠ[nhds x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact hf.clFn_eq_of_mem_relint_dom (Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hz)

/-- **Rockafellar's remark after Corollary 25.1.1**: `∇(cl f) = ∇f` for a proper convex `f` —
taking a closure changes no gradient, and creates none.

He asserts it without proof and uses it to state Corollaries 25.1.2 and 25.1.3 for an `f` that
need not be closed. One direction is immediate: a gradient of `f` at `x` puts `x` in
`int (dom f)`, where the two functions agree on a neighbourhood. The other needs
`ConvexFn.interior_dom_clFn`, because what a gradient of `cl f` supplies is a point interior to
`dom (cl f)`, which is the larger domain. -/
theorem hasGradientAt_clFn_iff (hf : ConvexFn f) (hp : Proper f) :
    HasGradientAt (clFn f) f' x ↔ HasGradientAt f f' x := by
  constructor
  · intro h
    have hx : x ∈ interior (dom f) := by
      rw [← hf.interior_dom_clFn hp]
      exact HasGradientAt.mem_interior_dom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.clFn_eventuallyEq_of_mem_interior_dom hx).symm.trans hfg, hd⟩
  · intro h
    have hx : x ∈ interior (dom f) := HasGradientAt.mem_interior_dom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.clFn_eventuallyEq_of_mem_interior_dom hx).trans hfg, hd⟩

/-- **`∇(cl f) = ∇f`**, in the form that names no gradient. -/
theorem differentiableAtFn_clFn_iff (hf : ConvexFn f) (hp : Proper f) :
    DifferentiableAtFn (clFn f) x ↔ DifferentiableAtFn f x :=
  exists_congr fun _ => hasGradientAt_clFn_iff hf hp

end Closure

/-! ### Corollaries 25.1.2 and 25.1.3 without closedness -/

section ClosureExposedEpi

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **A subdifferential that is a single point is unchanged by taking the closure.**
`mem_subgradient_clFn_iff` (Theorem 23.5, `(a) ⟺ (a**)`) gives `∂(cl f) x = ∂f x` wherever
`(cl f) x = f x`; a singleton subdifferential puts `x` in `int (dom f) = int (dom (cl f))`
(`ConvexFn.interior_dom_clFn`), which is inside `ri (dom f)`, where Theorem 7.4 supplies exactly
that hypothesis. Both directions run the same two steps. -/
theorem exists_subgradient_clFn_eq_singleton_iff [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : Proper f) {y : F} :
    (∃ x : E, subgradient B (clFn f) x = {y}) ↔ ∃ x : E, subgradient B f x = {y} := by
  have key : ∀ x : E, x ∈ interior (dom f) → subgradient B (clFn f) x = subgradient B f x :=
    fun x hx => Set.ext fun _ => mem_subgradient_clFn_iff
      (hf.clFn_eq_of_mem_relint_dom (Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hx))
  constructor
  · rintro ⟨x, hx⟩
    have hint : x ∈ interior (dom f) := by
      rw [← hf.interior_dom_clFn hp]
      exact mem_interior_dom_of_subgradient_eq_singleton (convexFn_clFn hf) (hf.proper_clFn hp) hx
    exact ⟨x, (key x hint).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (key x (mem_interior_dom_of_subgradient_eq_singleton hf hp hx)).trans hx⟩

variable [TopologicalSpace F]

/-- **Rockafellar, Corollary 25.1.2** with the book's hypotheses: `f` is merely proper convex.

`mem_exposedPoints_epi_conj_iff` asks for `ClosedFn f`, which the book supplies by replacing `f`
with `cl f` — legitimately, since `(cl f)* = f*` and, by the two lemmas above, `cl f` has exactly
the same points of single-valued subdifferential as `f`. -/
theorem mem_exposedPoints_epi_conj_iff_of_proper [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ConvexFn f) (hp : Proper f) {y : F} {μ : ℝ} :
    (y, μ) ∈ (epi (conj B f)).exposedPoints ℝ ↔
      conj B f y = (μ : EReal) ∧ ∃ x : E, subgradient B f x = {y} := by
  rw [← conj_clFn (B := B) f,
    mem_exposedPoints_epi_conj_iff (convexFn_clFn hf) (hf.proper_clFn hp) (closedFn_clFn f)]
  exact and_congr_right fun _ => exists_subgradient_clFn_eq_singleton_iff hf hp

end ClosureExposedEpi

section ClosureExposedSupport

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : F → EReal}

/-- **Rockafellar, Corollary 25.1.3** with the book's hypotheses: `g` is merely positively
homogeneous proper convex. The book's own proof does not reduce to the closed case here — it
identifies `g*` with an indicator and appeals to Corollary 25.1.2, which by
`mem_exposedPoints_epi_conj_iff_of_proper` no longer needs closedness. The reduction is done
directly instead, on the strength of `posHomogeneous_clFn` and `supportSet_clFn`
(`Duality/Support.lean`) together with `exists_subgradient_clFn_eq_singleton_iff`. -/
theorem mem_exposedPoints_supportSet_iff_of_proper [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (hgh : PosHomogeneous g) (hgc : ConvexFn g) (hgp : Proper g)
    {z : E} :
    z ∈ (supportSet B.flip g).exposedPoints ℝ ↔ ∃ y : F, subgradient B.flip g y = {z} := by
  obtain ⟨w, hw⟩ := hgp.dom_nonempty
  have hne : ∃ y, g y ≠ ⊤ := ⟨w, (mem_dom.1 hw).ne⟩
  have hph := posHomogeneous_clFn (B := B) hgh hgc hne
  rw [← supportSet_clFn (B := B) hgh hgc hne,
    mem_exposedPoints_supportSet_iff (B := B) hph (convexFn_clFn hgc)
    (hgc.proper_clFn hgp) (closedFn_clFn g)]
  exact exists_subgradient_clFn_eq_singleton_iff hgc hgp

end ClosureExposedSupport

/-! ### Corollaries 25.1.2 and 25.1.3 in differentiability form -/

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **Rockafellar, Corollary 25.1.2**: the exposed points of `epi f*` are the points
`(∇f x, f* (∇f x))` at which `f` is differentiable.

`mem_exposedPoints_epi_conj_iff` gives this with "`y` is the only subgradient of `f` at `x`" in
place of "`f` is differentiable at `x` with `∇f x = y`"; Theorem 25.1 identifies the two. That
theorem assumes `f` closed and this one does not, exactly as the book does not: `(cl f)* = f*`
carries the exposed points across, and `hasGradientAt_clFn_iff` carries the gradients back. -/
theorem mem_exposedPoints_epi_conj_iff_hasGradientAt (hf : ConvexFn f) (hp : Proper f)
    {y : StrongDual ℝ E} {μ : ℝ} :
    (y, μ) ∈ (epi (conj (topDualPairing ℝ E).flip f)).exposedPoints ℝ ↔
      conj (topDualPairing ℝ E).flip f y = (μ : EReal) ∧ ∃ x : E, HasGradientAt f y x := by
  rw [mem_exposedPoints_epi_conj_iff_of_proper hf hp]
  exact and_congr_right fun _ =>
    exists_congr fun _ => (hasGradientAt_iff_subgradient_eq_singleton hf hp).symm

/-- **Rockafellar, Corollary 25.1.3**: for a proper convex positively homogeneous `f`, the exposed
points of the closed convex set that `f` supports are exactly its gradients.

The book does not assume `f` closed here either, and its proof does not reduce to the closed case
directly: it identifies `f*` with the indicator of the supported set (Corollary 13.2.1) and applies
Corollary 25.1.2, which by the above no longer needs closedness. The backbone's
`mem_exposedPoints_supportSet_iff` is stated about *subgradients*, where closedness cannot be
dropped, so the reduction is performed here: `cl f` supports the same set — both conjugates are the
same indicator function — and it is positively homogeneous, being a support function. -/
theorem mem_exposedPoints_supportSet_iff_hasGradientAt (hgh : PosHomogeneous f) (hgc : ConvexFn f)
    (hgp : Proper f) {z : StrongDual ℝ E} :
    z ∈ (supportSet (topDualPairing ℝ E).flip f).exposedPoints ℝ ↔
      ∃ y : E, HasGradientAt f z y := by
  rw [mem_exposedPoints_supportSet_iff_of_proper (B := topDualPairing ℝ E) hgh hgc hgp]
  exact exists_congr fun _ => (hasGradientAt_iff_subgradient_eq_singleton hgc hgp).symm

end Exposed

end Tdaf.ConvexAnalysis
