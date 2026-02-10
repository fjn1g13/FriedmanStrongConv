/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Int.Basic

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an oriented edge.
This file defines darts and proves some of their basic properties.
-/

universe u v w
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable {G : Graph α β}

/-- A dart is describes a possible direction for a walk starting at one point.
In order to count walks correctly, we adopt the convention that each loop
can be taken in two distinct directions, encoded in orienOfEq. -/
@[ext]
structure Dart where
  fst : α
  snd : α
  edge : β
  isLink : G.IsLink edge fst snd
  orienOfEq : fst = snd -> Bool
  deriving DecidableEq

namespace Dart

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

/-- The reversing operation on darts, which reverses its orientation. -/
def reverse (d : G.Dart) : G.Dart :=
  Dart.mk d.snd d.fst d.edge d.isLink.symm (fun h => (d.orienOfEq h.symm).not)

/-- The start point of the reverse dart is its end point. -/
lemma fst_of_reverse (d : G.Dart) : d.reverse.fst = d.snd := rfl

/-- The end point of the reverse dart is its start point. -/
lemma snd_of_reverse (d : G.Dart) : d.reverse.snd = d.fst := rfl

/-- The edge is unchanged upon reversing the dart. -/
lemma edge_of_reverse (d : G.Dart) : d.reverse.edge = d.edge := rfl

/- The reverse of a dart is distinct from the dart. -/
lemma reverse_neq_self (d : G.Dart) : d.reverse ≠ d := by
  by_cases h : d.fst = d.snd
  · intro hf
    let ho : d.reverse.orienOfEq h.symm = d.orienOfEq h := by congr
    have nho : d.reverse.orienOfEq h.symm ≠ d.orienOfEq h := Bool.eq_not.mp rfl
    exact nho ho
  · intro hf
    have nh : d.reverse.fst = d.snd := rfl
    rw [hf] at nh
    exact h nh

/- The reverse of the reverse of a dart is the dart itself. -/
lemma reverse_of_reverse (d : G.Dart) : d.reverse.reverse = d := by
  rcases d with ⟨fst, snd, edge, isLink, orienOfEq⟩
  unfold reverse
  congr
  change (fun h ↦ !!orienOfEq _) = orienOfEq
  ext
  rw [Bool.not_not]

end Dart

/-- The dartset of a vertex is the set of darts starting at this vertex. -/
def dartSet (x : α) : Set G.Dart := {d | d.fst = x}

/- There exists a dart for any edge. -/
lemma dart_of_edge (e : E(G)) : ∃ d : G.Dart, d.edge = e := by
  have ⟨e, he⟩ := e
  have ⟨x, y, he⟩ := (G.edge_mem_iff_exists_isLink e).mp he
  exists
  {
    fst := x
    snd := y
    edge := e
    isLink := he
    orienOfEq := (fun _ => true)
  }

lemma non_loop_orienOfEq {d : G.Dart} (h : d.fst ≠ d.snd) : (d.orienOfEq ≍ (fun (_:False) => true)) := by
  apply heq_of_eqRec_eq
  . ext hn
    exact False.elim hn
  . rw [eq_false h]

lemma loop_orienOfEq_cases {d : G.Dart} (h : d.fst = d.snd) : (d.orienOfEq ≍ (fun (_:True) => true)) ∨ (d.orienOfEq ≍ (fun (_:True) => false)) := by
  by_cases cc : d.orienOfEq h
  . left
    apply heq_of_eqRec_eq
    . ext k
      rw [<- cc]
      apply congr_heq
      . exact cast_heq ?_ d.orienOfEq -- I don't understand the hole here: if I try to fill it, then checking fails
      . exact proof_irrel_heq k h
    . rw [eq_true h]
  . right
    rw [Bool.bool_iff_false] at cc
    apply heq_of_eqRec_eq
    . ext k
      rw [<- cc]
      apply congr_heq
      . exact cast_heq ?_ d.orienOfEq -- I don't understand the hole here: if I try to fill it, then checking fails
      . exact proof_irrel_heq k h
    . rw [eq_true h]

lemma isLoop_reverse_of_isLoop {d : G.Dart} (h : d.fst = d.snd) : d.reverse.fst = d.reverse.snd := h.symm

-- lemma reverse_loop_orienOfEq {d : G.Dart} (h : d.fst = d.snd) {o : Bool} (ho : d.orienOfEq ≍ (fun (_:True) => o)) : (d.reverse.orienOfEq ≍ (fun (_:True) => !o)) := by
--   apply heq_of_eqRec_eq
--   . ext k
--     unfold Dart.reverse

--   . rw [isLoop_reverse_of_isLoop h]
--     rw [eq_true (Eq.refl d.reverse.snd)]

lemma isLoop_of_same_edge_of_isLoop {d₁ d₂ : G.Dart} (hedge : d₁.edge = d₂.edge) (h₁ : d₁.fst = d₁.snd) : d₂.fst = d₂.snd := by
  rcases IsLink.eq_and_eq_or_eq_and_eq d₁.isLink (hedge ▸ d₂.isLink) with ⟨hff, hss⟩ | ⟨hfs, hsf⟩
  . rw [<- hff, <- hss]
    exact h₁
  . rw [<- hfs, <- hsf]
    exact h₁.symm

lemma isNotLoop_of_same_edge_of_isNotLoop {d₁ d₂ : G.Dart} (hedge : d₁.edge = d₂.edge) (h₁ : d₁.fst ≠ d₁.snd) : d₂.fst ≠ d₂.snd := by
  rcases IsLink.eq_and_eq_or_eq_and_eq d₁.isLink (hedge ▸ d₂.isLink) with ⟨hff, hss⟩ | ⟨hfs, hsf⟩
  . rw [<- hff, <- hss]
    exact h₁
  . rw [<- hfs, <- hsf]
    exact h₁.symm

lemma reverse_orienOfEq_eq_of_ne_of_same_edge {d₁ d₂ : G.Dart} (h : d₁ ≠ d₂) (hedge : d₁.edge = d₂.edge) : d₁.orienOfEq ≍ d₂.reverse.orienOfEq := by
  by_cases h₁ : d₁.fst = d₁.snd
  . have h₂ := isLoop_of_same_edge_of_isLoop hedge h₁
    have hr₂ := isLoop_reverse_of_isLoop h₂
    rcases loop_orienOfEq_cases h₁ with t₁ | f₁ <;> rcases loop_orienOfEq_cases hr₂ with tr₂ | fr₂
    . exact HEq.trans t₁ tr₂.symm
    . -- in theory we can provide that the orienOfEq are the same, and so d1 = d2, and thus a contraduction, but that's going to be a lengthly nightmare
      admit
    . admit
    . exact HEq.trans f₁ fr₂.symm
  . have h₂ := isNotLoop_of_same_edge_of_isNotLoop hedge h₁
    apply HEq.trans
    . exact non_loop_orienOfEq h₁
    . apply HEq.symm
      exact non_loop_orienOfEq h₂.symm


-- lemma loop_orienOfEq_reverse_heq {d₁ d₂ : G.Dart} (h₁ : d₁.fst = d₁.snd) (h₂ : d₂.fst = d₂.snd) : d₁.orienOfEq ≍ d₂.orienOfEq ∨ d₁.orienOfEq ≍ d₂.reverse.orienOfEq := by
--   by_cases eq : d₁ = d₂
--   . left
--     rw [eq]
--   . right
--     apply heq_of_eqRec_eq
--     . ext ht

--       admit
--     . rw [Dart.fst_of_reverse, Dart.snd_of_reverse]
--       rw [h₁, h₂]
--       rw [eq_self _, eq_self _]

-- lemma loop_orienOfEq_heq_or_reverse_heq {d₁ d₂ : G.Dart} (h₁ : d₁.fst = d₁.snd) (h₂ : d₂.fst = d₂.snd) : d₁.orienOfEq ≍ d₂.orienOfEq ∨ d₁.orienOfEq ≍ d₂.reverse.orienOfEq := by
--   apply?
--   apply heq_of_eqRec_eq
--   . ext ht
--     rw [Dart.fst_of_reverse, Dart.snd_of_reverse] at ht


--     admit
--   . rw [Dart.fst_of_reverse, Dart.snd_of_reverse]
--     rw [h₁, h₂]
--     rw [eq_self _, eq_self _]

-- lemma reverse_loop_orienOfEq_eq {d₁ d₂ : G.Dart} (h : d₁.edge = d₂.edge) (h₁ : d₁.fst = d₁.snd) (h₂ : d₂.fst = d₂.snd) : d₁.orienOfEq ≍ d₂.reverse.orienOfEq := by
--   apply heq_of_eqRec_eq
--   . ext ht
--     rw [Dart.fst_of_reverse, Dart.snd_of_reverse] at ht


--     admit
--   . rw [Dart.fst_of_reverse, Dart.snd_of_reverse]
--     rw [h₁, h₂]
--     rw [eq_self _, eq_self _]

lemma non_loop_orienOfEq_eq {d₁ d₂ : G.Dart} (h₁ : d₁.fst ≠ d₁.snd) (h₂ : d₂.fst ≠ d₂.snd) : d₁.orienOfEq ≍ d₂.orienOfEq := by
  apply heq_of_eqRec_eq
  . ext hn
    contradiction
  . rw [eq_false h₁, eq_false h₂]

lemma non_loop_orienOfEq_reverse_eq {d : G.Dart} (h : d.fst ≠ d.snd) : d.orienOfEq ≍ d.reverse.orienOfEq := by
  apply heq_of_eqRec_eq
  . ext hn
    rw [Dart.fst_of_reverse, Dart.snd_of_reverse] at hn
    exfalso
    exact h hn.symm
  . rw [Dart.fst_of_reverse, Dart.snd_of_reverse]
    rw [eq_false h, eq_false h.symm]

/- Two darts are equal or reverse of one another if they have the same edge. -/
lemma edge_dart_eq {d₁ d₂ : G.Dart} (h : d₁.edge = d₂.edge) : d₁ = d₂ ∨ d₁ = d₂.reverse := by
  by_cases eq : d₁ = d₂
  . exact Or.inl eq
  . right
    by_cases isLoop : d₁.fst = d₁.snd
    . rcases IsLink.eq_and_eq_or_eq_and_eq d₁.isLink (h ▸ d₂.isLink) with ⟨hff, hss⟩ | ⟨hfs, hsf⟩
      . apply Dart.ext
        . change d₁.fst = d₂.snd
          rw [isLoop]
          exact hss
        . change d₁.snd = d₂.fst
          rw [<- isLoop]
          exact hff
        . exact h
        . admit
      . apply Dart.ext
        . exact hfs
        . exact hsf
        . exact h
        . admit
    . rcases IsLink.eq_and_eq_or_eq_and_eq d₁.isLink (h ▸ d₂.isLink) with ⟨hff, hss⟩ | ⟨hfs, hsf⟩
      . exfalso
        apply eq
        apply Dart.ext <;> try assumption
        have isLoop₂ := (hff ▸ hss ▸ isLoop)
        exact non_loop_orienOfEq_eq isLoop isLoop₂
      . apply Dart.ext <;> try assumption
        have isLoop₂ := (hfs ▸ hsf ▸ isLoop) -- for some reason I can't inline this... not that I _want_ to inline it, but why can't I?!
        exact non_loop_orienOfEq_eq isLoop isLoop₂

/- Two darts have the same edge if they are equal or reverse of one another. -/
lemma edge_dart_eq' {d₁ d₂ : G.Dart} (h : d₁ = d₂ ∨ d₁ = d₂.reverse) : d₁.edge = d₂.edge := by
  rcases h with eq | rev
  . exact eq ▸ (Eq.refl d₁.edge)
  . exact rev ▸ (Dart.edge_of_reverse d₂)

/- Two darts have the same edge iff they are equal or reverse of one another. -/
lemma edge_dart_eq_iff {d₁ d₂ : G.Dart} : (d₁.edge = d₂.edge) ↔ d₁ = d₂ ∨ d₁ = d₂.reverse := by
  constructor <;> intro lhs
  . exact edge_dart_eq lhs
  . exact edge_dart_eq' lhs

/-- An edge is incident to a vertex iff there is a dart starting at this vertex
carried by this edge.-/
lemma Inc_iff_exists_dart {x : α} {e : β} :
  G.Inc e x ↔ ∃ d : G.Dart, d.fst = x ∧ d.edge = e := by sorry

/-- The IsDartLink relation is the dart version of IsLink, meaning `IsDartLink d x y`
iff `d` is a dart starting at `x` and ending at `y`.-/
def IsDartLink (d : G.Dart) (x y : α) := x = d.fst ∧ y = d.snd
