/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Analysis.Convex.Subgradient.Rademacher

/-!
# Convergence of gradients

Rockafellar's **Theorem 25.7**: if convex functions finite and differentiable on an open convex set
converge pointwise there to a function that is also finite and differentiable, then their gradients
converge too — and uniformly on every compact subset. For arbitrary differentiable functions this
is false; convexity is what makes it work, through the upper semicontinuity of the subdifferential
under pointwise convergence (Theorem 24.5).

## Main results

* `dist_le_of_subgradient_subset` — the bookkeeping step: an inclusion `∂p u ⊆ ∂q v + ε B` between
  subdifferentials that are *singletons* is the bound `‖∇p u - ∇q v‖ ≤ ε`.
* `tendsto_of_hasGradientAt` — **Theorem 25.7**, the displayed statement: `∇fᵢ x → ∇f x`.
* `tendstoUniformlyOn_fderiv_toReal` — **Theorem 25.7**, the sentence after it: the convergence is
  uniform on every compact subset.

## Design notes

**The pointwise clause is Theorem 24.5 at a constant sequence.** `∂fᵢ(x) ⊆ ∂f(x) + εB` for large
`i`; both sides are singletons by Theorem 25.1, so the inclusion *is* `‖∇fᵢ x - ∇f x‖ ≤ ε`. No
contradiction argument and no compactness are involved, and — unlike in Rockafellar's proof — no
appeal to Theorem 10.8 either, since Theorem 24.5 has already absorbed it.

**The uniform clause is the same theorem along a subsequence.** Rockafellar reduces to partial
derivatives and argues by contradiction on one coordinate at a time; here the contradiction is run
once, on the norm. If the convergence is not uniform on the compact `S`, there are indices `φ n`
and points `zₙ ∈ S` with `‖∇f(zₙ) - ∇f_{φ n}(zₙ)‖ ≥ ε`; compactness of `S` extracts a convergent
subsequence `zₙ → w ∈ S`, and then Theorem 24.5 along that subsequence and Corollary 24.5.1 at `w`
bound both gradients within `ε/3` of `∇f w`, which the triangle inequality contradicts. Theorem
24.5 is stated for a moving sequence of points exactly so that this works.

**Both clauses are stated for `innerₗ E` internally and for `fderiv` outwardly.** The
subdifferential theory of §24 is available for the inner-product pairing, whose subgradients are
vectors, while a gradient is an element of `StrongDual ℝ E`; `subgradient_innerL_eq_singleton`
translates, and it is an isometry, so `dist_le_of_subgradient_subset` loses nothing.
-/

namespace Tdaf.ConvexAnalysis

open Filter Metric Topology Pointwise

section GradientLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : ℕ → E → EReal} {g : E → EReal} {U : Set E} {x : E}

/-- **An inclusion of singleton subdifferentials is a bound on gradients.** If `a` is the only
subgradient of `p` at `u`, `b` the only one of `q` at `v`, and `∂p u ⊆ ∂q v + ε B`, then
`‖a - b‖ ≤ ε`. The Riesz isomorphism is an isometry, so the `ε` crosses it unchanged. -/
theorem dist_le_of_subgradient_subset {p q : E → EReal} {u v : E} {a b : StrongDual ℝ E} {ε : ℝ}
    (hp : ConvexFn p) (hq : ConvexFn q) (ha : HasGradientAt p a u) (hb : HasGradientAt q b v)
    (hsub : subgradient (innerₗ E) p u ⊆ subgradient (innerₗ E) q v + closedBall (0 : E) ε) :
    dist a b ≤ ε := by
  have hmem : (InnerProductSpace.toDual ℝ E).symm a ∈ subgradient (innerₗ E) p u := by
    rw [subgradient_innerL_eq_singleton hp ha]
    rfl
  have hin := hsub hmem
  rw [subgradient_innerL_eq_singleton hq hb] at hin
  obtain ⟨c, hc, d, hd, hcd⟩ := hin
  rw [Set.mem_singleton_iff] at hc
  subst hc
  rw [mem_closedBall_zero_iff] at hd
  have hdist : dist a b = ‖(InnerProductSpace.toDual ℝ E).symm a
      - (InnerProductSpace.toDual ℝ E).symm b‖ := by
    rw [dist_eq_norm, ← (InnerProductSpace.toDual ℝ E).symm.norm_map (a - b), map_sub]
  rw [hdist, ← hcd, add_sub_cancel_left]
  exact hd

/-- **Rockafellar, Theorem 25.7**: the gradients of convex functions converging pointwise on an
open convex set converge at every point of that set.

Theorem 24.5 at the constant sequence `xᵢ = x`, with both subdifferentials collapsed to singletons
by Theorem 25.1. -/
theorem tendsto_of_hasGradientAt (hU : IsOpen U) (hUc : Convex ℝ U) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i)) (hg : ConvexFn g) (hgp : Proper g)
    (hgU : U ⊆ dom g) (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z))) (hx : x ∈ U)
    {G : ℕ → StrongDual ℝ E} {G' : StrongDual ℝ E} (hG : ∀ i, HasGradientAt (f i) (G i) x)
    (hG' : HasGradientAt g G' x) : Tendsto G atTop (𝓝 G') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_subgradient_subset_add_closedBall hU hUc hf hfp hfU hg hgp hgU hconv hx
    (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ))) (half_pos hε)
  filter_upwards [hev] with i hi
  exact lt_of_le_of_lt (dist_le_of_subgradient_subset (hf i) hg (hG i) hG' hi) (half_lt_self hε)

/-- **Rockafellar, Theorem 25.7**, the uniform clause: on every compact subset of the open set, the
gradients converge uniformly.

Rockafellar argues one partial derivative at a time; the contradiction is run here once, on the
norm. A failure of uniform convergence produces indices `φ n` and points `zₙ` of the compact set
with `‖∇f zₙ - ∇f_{φ n} zₙ‖ ≥ ε`; a convergent subsequence `zₙ → w` turns Theorem 24.5 (along the
subsequence) and Corollary 24.5.1 (at `w`) into two `ε/3` bounds whose triangle inequality
contradicts it. -/
theorem tendstoUniformlyOn_fderiv_toReal (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i))
    (hg : ConvexFn g) (hgp : Proper g) (hgU : U ⊆ dom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hfd : ∀ i, ∀ z ∈ U, DifferentiableAtFn (f i) z) (hgd : ∀ z ∈ U, DifferentiableAtFn g z)
    {S : Set E} (hS : IsCompact S) (hSU : S ⊆ U) :
    TendstoUniformlyOn (fun i => fderiv ℝ fun w => (f i w).toReal)
      (fderiv ℝ fun w => (g w).toReal) atTop S := by
  set Gf : ℕ → E → StrongDual ℝ E := fun i => fderiv ℝ fun w => (f i w).toReal with hGfdef
  set Gg : E → StrongDual ℝ E := fderiv ℝ fun w => (g w).toReal with hGgdef
  have hgradf : ∀ i, ∀ z ∈ U, HasGradientAt (f i) (Gf i z) z := fun i z hz =>
    DifferentiableAtFn.hasGradientAt_fderiv (hfd i z hz)
  have hgradg : ∀ z ∈ U, HasGradientAt g (Gg z) z := fun z hz =>
    DifferentiableAtFn.hasGradientAt_fderiv (hgd z hz)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ i in atTop, ∃ z ∈ S, ε ≤ dist (Gg z) (Gf i z) := by
    refine (Filter.not_eventually.1 hcon).mono fun i hi => ?_
    push Not at hi
    exact hi
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose zs hzsS hzsdist using hφP
  obtain ⟨w, hwS, ψ, hψ, hψlim⟩ := hS.tendsto_subseq hzsS
  have hwU : w ∈ U := hSU hwS
  have hlim : Tendsto (fun n => zs (ψ n)) atTop (𝓝 w) := hψlim
  have hsub : ∀ z ∈ U, Tendsto (fun n => f (φ (ψ n)) z) atTop (𝓝 (g z)) := fun z hz =>
    (hconv z hz).comp (hφ.comp hψ).tendsto_atTop
  have h1 := eventually_subgradient_subset_add_closedBall hU hUc (fun n => hf (φ (ψ n)))
    (fun n => hfp (φ (ψ n))) (fun n => hfU (φ (ψ n))) hg hgp hgU hsub hwU hlim
    (by positivity : (0 : ℝ) < ε / 3)
  have hwint : w ∈ interior (dom g) := interior_maximal hgU hU hwU
  have h2 : ∀ᶠ n in atTop, subgradient (innerₗ E) g (zs (ψ n))
      ⊆ subgradient (innerₗ E) g w + closedBall (0 : E) (ε / 3) :=
    hlim.eventually (eventually_nhds_subgradient_subset_add_closedBall hg hgp hwint
      (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hzU : zs (ψ n) ∈ U := hSU (hzsS (ψ n))
  have hA : dist (Gf (φ (ψ n)) (zs (ψ n))) (Gg w) ≤ ε / 3 :=
    dist_le_of_subgradient_subset (hf _) hg (hgradf _ _ hzU) (hgradg w hwU) hn1
  have hB : dist (Gg (zs (ψ n))) (Gg w) ≤ ε / 3 :=
    dist_le_of_subgradient_subset hg hg (hgradg _ hzU) (hgradg w hwU) hn2
  have hlow := hzsdist (ψ n)
  have htri := dist_triangle (Gg (zs (ψ n))) (Gg w) (Gf (φ (ψ n)) (zs (ψ n)))
  rw [dist_comm (Gg w)] at htri
  linarith

end GradientLimit

end Tdaf.ConvexAnalysis
