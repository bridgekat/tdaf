/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Hom.Basic

/-!
# A Galois connection restricts to an order isomorphism between the closed elements

Mathlib has `GaloisConnection.closureOperator`, `ClosureOperator.Closeds` and `ClosureOperator.gi`,
but not the two-sided statement: the elements of `α` fixed by `u ∘ l` and the elements of `β` fixed
by `l ∘ u` are in order-isomorphic correspondence. `ClosureOperator.gi` is one-sided only.

## Main results

* `GaloisConnection.closedsOrderIso` — the isomorphism.

## Why this is here

Every "the operation is an involution on a characterised class" theorem in convex analysis is an
instance of it. Conjugacy is a bijection between the closed convex functions on the two sides of a
pairing (Rockafellar's Corollary 12.2.1); polarity is one between the closed convex cones
(Theorem 14.1); the gauge and support-function correspondences are two more. Each is currently a
hand-built `Equiv` even though the underlying Galois connection is already recorded, which loses
the order structure — and for an *antitone* connection, the isomorphism is onto the order dual, so
what these correspondences really are is order **anti**-isomorphisms.

Stated for a bare `GaloisConnection` on two `PartialOrder`s: nothing here is about convexity, and
it is an upstreaming candidate.

## Implementation note

`map_rel_iff'` needs the `change` to get past the anonymous-constructor blob — without it the goal
is stated against the structure instance rather than against `l`, and tactics that match on the
relation fail. `show` does the same job and is what the prototype used, but the style linter
reserves `show` for readability, so `change` is the right spelling here.
-/

namespace GaloisConnection

variable {α β : Type*} [PartialOrder α] [PartialOrder β] {l : α → β} {u : β → α}

/-- **A Galois connection restricts to an order isomorphism between the closed elements.**

`{a // u (l a) = a}` and `{b // l (u b) = b}` are the two classes on which the connection's
round trips are the identity, and `l`/`u` exchange them. For an antitone connection — presented
here, as Mathlib presents them, by taking one side to be an `OrderDual` — this reads as an order
anti-isomorphism. -/
def closedsOrderIso (gc : GaloisConnection l u) :
    {a : α // u (l a) = a} ≃o {b : β // l (u b) = b} where
  toFun a := ⟨l a.1, gc.l_u_l_eq_l a.1⟩
  invFun b := ⟨u b.1, gc.u_l_u_eq_u b.1⟩
  left_inv a := Subtype.ext a.2
  right_inv b := Subtype.ext b.2
  map_rel_iff' {a a'} := by
    change l a.1 ≤ l a'.1 ↔ a.1 ≤ a'.1
    refine ⟨fun h => ?_, fun h => gc.monotone_l h⟩
    have := gc.monotone_u h
    rwa [a.2, a'.2] at this

@[simp] theorem closedsOrderIso_apply (gc : GaloisConnection l u) (a : {a : α // u (l a) = a}) :
    (gc.closedsOrderIso a : β) = l a := rfl

@[simp] theorem closedsOrderIso_symm_apply (gc : GaloisConnection l u)
    (b : {b : β // l (u b) = b}) : (gc.closedsOrderIso.symm b : α) = u b := rfl

end GaloisConnection
