/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk and Freddie Nash
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
can be taken in two distinct directions, forwards or backwards. -/
inductive Dart
  | Dir : (x y : α) -> (e : β) -> (ne : x ≠ y) -> (h : G.IsLink e x y) -> Dart
  | Fwd : (x : α) -> (e : β) -> (h : G.IsLoopAt e x) -> Dart
  | Bck : (x : α) -> (e : β) -> (h : G.IsLoopAt e x) -> Dart

namespace Dart

/-- The map `fst` extracts the starting point of a dart. -/
def fst (d : G.Dart) : α :=
  match d with
  | .Dir x _ _ _ _ => x
  | .Fwd x _ _ => x
  | .Bck x _ _ => x

/-- The map `snd` extracts the end point of a dart. -/
def snd (d : G.Dart) : α :=
  match d with
  | .Dir _ y _ _ _ => y
  | .Fwd x _ _ => x
  | .Bck x _ _ => x

/-- The map `edge` extracts the edge corresponding to a dart. -/
def edge (d : G.Dart) : β :=
  match d with
  | .Dir _ _ e _ _ => e
  | .Fwd _ e _ => e
  | .Bck _ e _ => e

/-- The map `isBck` extracts indicates whether the edge is an instance of Dart.Bck. -/
def isBck (d : G.Dart) : Bool :=
  match d with
  | .Dir _ _ _ _ _ => false
  | .Fwd _ _ _ => false
  | .Bck _ _ _ => true

/-- `isLink` extracts the link relation from the definition of the dart. -/
lemma isLink (d : G.Dart) : G.IsLink d.edge d.fst d.snd :=
  match d with
  | .Dir _ _ _ _ h => h
  | .Fwd _ _ h => h
  | .Bck _ _ h => h

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

/-- Two darts are equal iff they share their start points, end points and edges.-/
lemma eq_iff {d₁ d₂ : G.Dart} : (d₁ = d₂) ↔ (d₁.fst = d₂.fst ∧ d₁.snd = d₂.snd ∧ d₁.edge = d₂.edge ∧ d₁.isBck = d₂.isBck)
  := by
  constructor
  · intro heq
    rw [heq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rcases d₁ with ⟨x₁, y₁, e₁, ne₁, h₁⟩ | ⟨x₁, e₁, h₁⟩ | ⟨x₁, e₁, h₁⟩
    <;> rcases d₂ with ⟨x₂, y₂, e₂, ne₂, h₂⟩ | ⟨x₂, e₂, h₂⟩ | ⟨x₂, e₂, h₂⟩
    all_goals
      intro ⟨hfst, hsnd, hedge, hbck⟩
      cases hfst
      cases hsnd
      cases hedge
      first | rfl | contradiction

/-- If two darts share their edge and start point then they are equal. -/
lemma fst_edge_unique {d₁ d₂ : G.Dart} (hfst : d₁.fst = d₂.fst) (hedge : d₁.edge = d₂.edge) (hbck : d₁.isBck = d₂.isBck) : d₁ = d₂ := by
  apply eq_iff.mpr
  apply And.intro hfst
  apply And.intro (IsLink.right_unique d₁.isLink (hedge ▸ hfst ▸ d₂.isLink))
  apply And.intro hedge
  exact hbck

/-- If two darts share their edge and end point then they are equal. -/
lemma snd_edge_unique {d₁ d₂ : G.Dart} (hsnd : d₁.snd = d₂.snd) (hedge : d₁.edge = d₂.edge) (hbck : d₁.isBck = d₂.isBck) : d₁ = d₂ := by
  apply eq_iff.mpr
  apply And.intro (IsLink.left_unique d₁.isLink (hedge ▸ hsnd ▸ d₂.isLink))
  apply And.intro hsnd
  apply And.intro hedge
  exact hbck

/-- The reversing operation on darts, which reverses its orientation. -/
def reverse (d : G.Dart) : G.Dart :=
    match d with
  | .Dir x y e ne h => Dir y x e ne.symm h.symm
  | .Fwd x e h => Bck x e h
  | .Bck x e h => Fwd x e h

/-- The start point of the reverse dart is its end point. -/
@[simp]
lemma fst_of_reverse (d : G.Dart) : d.reverse.fst = d.snd := by cases d <;> trivial

/-- The end point of the reverse dart is its start point. -/
@[simp]
lemma snd_of_reverse (d : G.Dart) : d.reverse.snd = d.fst := by cases d <;> trivial

/-- The edge is unchanged upon reversing the dart. -/
@[simp]
lemma edge_of_reverse (d : G.Dart) : d.reverse.edge = d.edge := by cases d <;> trivial

/-- The reverse of a dart is distinct from the dart. -/
lemma reverse_neq_self (d : G.Dart) : d.reverse ≠ d := by
  cases d <;> intro hn <;> cases hn; contradiction

/-- The reverse of the reverse of a dart is the dart itself. -/
@[simp]
lemma reverse_of_reverse (d : G.Dart) : d.reverse.reverse = d := by cases d <;> rfl

end Dart

/-- The dartset of a vertex is the set of darts starting at this vertex. -/
def dartSet (x : α) : Set G.Dart := {d | d.fst = x}

/-- If `e` is an edge linking `x` and `y`, then `e.toDart` is a corresponding dart starting at `x`.-/
def toDart [DecidableEq α] {x y : α} {e : β} (h : G.IsLink e x y) : G.Dart := by
  by_cases eq : x = y
  · have hx : G.IsLink e x x := by rw [eq.symm] at h; exact h
    exact Dart.Fwd x e hx
  . exact Dart.Dir x y e eq h

/-- Two darts are equal or reverse of one another if they have the same edge. -/
lemma eq_or_eq_rev_of_edge_dart_eq {d₁ d₂ : G.Dart} (hedge : d₁.edge = d₂.edge) : d₁ = d₂ ∨ d₁ = d₂.reverse := by
  rcases IsLink.eq_and_eq_or_eq_and_eq d₁.isLink (hedge ▸ d₂.isLink) with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  <;> rcases d₁ with ⟨x₁, y₁, e₁, ne₁, h₁⟩ | ⟨x₁, e₁, h₁⟩ | ⟨x₁, e₁, h₁⟩
  <;> rcases d₂ with ⟨x₂, y₂, e₂, ne₂, h₂⟩ | ⟨x₂, e₂, h₂⟩ | ⟨x₂, e₂, h₂⟩
  all_goals
    cases hedge
    try cases hxx; cases hyy
    try cases hxy; cases hyx
    try left; rfl
    try right; rfl
    try contradiction

/-- Two darts have the same edge iff they are equal or reverse of one another. -/
lemma edge_dart_eq_iff_eq_or_eq_rev {d₁ d₂ : G.Dart} : d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.reverse := by
  constructor
  . exact eq_or_eq_rev_of_edge_dart_eq
  . rintro (rfl | rfl)
    . rfl
    . exact Dart.edge_of_reverse d₂

/-- An edge is incident to a vertex iff there is a dart starting at this vertex
carried by this edge.-/
lemma Inc_iff_exists_dart {x : α} {e : β} :
  G.Inc e x ↔ ∃ d : G.Dart, d.fst = x ∧ d.edge = e := by
  constructor
  . intro ⟨y, he⟩
    by_cases is_loop : x = y
    . exists Dart.Fwd x e (is_loop ▸ he)
    . exists Dart.Dir x y e is_loop he
  . intro ⟨d, ⟨hf, he⟩⟩
    exists d.snd
    exact hf ▸ he ▸ d.isLink

/-- The IsDartLink relation is the dart version of IsLink, meaning `IsDartLink d x y`
iff `d` is a dart starting at `x` and ending at `y`.-/
def IsDartLink (d : G.Dart) (x y : α) := x = d.fst ∧ y = d.snd

-- just playing around
lemma IsDartLink.symm₁ {d : G.Dart} (h : G.IsDartLink d.reverse y x) : G.IsDartLink d x y := by
  rcases h with ⟨hfst, hsnd⟩
  constructor
  . exact Dart.snd_of_reverse d ▸ hsnd
  . exact Dart.fst_of_reverse d ▸ hfst

lemma IsDartLink.symm₂ {d : G.Dart} (h : G.IsDartLink d x y) : G.IsDartLink d.reverse y x := by
  constructor
  · exact Dart.fst_of_reverse d ▸ h.right
  · exact Dart.snd_of_reverse d ▸ h.left

@[simp]
lemma IsDartLink.symm {d : G.Dart} : G.IsDartLink d.reverse y x ↔ G.IsDartLink d x y := by
  constructor <;> intro h
  · exact IsDartLink.symm₁ h
  . exact IsDartLink.symm₂ h
