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
can be taken in two distinct directions, which are encoded in Fwd and Bck
and then surfaced by orienOfEq. -/
inductive Dart
  | Fwd : (x : α) -> (e : β) -> (isLoop : G.IsLoopAt e x) -> Dart
  | Bck : (x : α) -> (e : β) -> (isLoop : G.IsLoopAt e x) -> Dart
  | Dir : (x y : α) -> (e : β) -> (ne : x ≠ y) -> (isLink : G.IsLink e x y) -> Dart

namespace Dart

/- Interface from the structure -/
def fst (d : G.Dart) : α :=
  match d with
  | .Fwd x _ _ => x
  | .Bck x _ _ => x
  | .Dir x _ _ _ _ => x

def snd (d : G.Dart) : α :=
  match d with
  | .Fwd x _ _ => x
  | .Bck x _ _ => x
  | .Dir _ y _ _ _ => y

def edge (d : G.Dart) : β :=
  match d with
  | .Fwd _ e _ => e
  | .Bck _ e _ => e
  | .Dir _ _ e _ _ => e

def isLink (d : G.Dart) : G.IsLink d.edge d.fst d.snd :=
  match d with
  | .Fwd _ _ l => l
  | .Bck _ _ l => l
  | .Dir _ _ _ _ l => l

def orienOfEq (d : G.Dart) (eq : d.fst = d.snd) : Bool :=
  match d with
  | .Fwd _ _ _ => true
  | .Bck _ _ _ => false
  | .Dir x y _ ne _ => by
    change x = y at eq
    exfalso
    exact ne eq

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

/-- The reversing operation on darts, which reverses its orientation. -/
def reverse (d : G.Dart) : G.Dart :=
  match d with
  | .Fwd x e isLoop => Bck x e isLoop
  | .Bck x e isLoop => Fwd x e isLoop
  | .Dir x y e ne isLink => Dir y x e ne.symm isLink.symm

/- The start point of the reverse dart is its end point. -/
lemma fst_of_reverse (d : G.Dart) : d.reverse.fst = d.snd := by
  cases d <;> trivial

/- The end point of the reverse dart is its start point. -/
lemma snd_of_reverse (d : G.Dart) : d.reverse.snd = d.fst := by
  cases d <;> trivial

/- The edge is unchanged upon reversing the dart. -/
lemma edge_of_reverse (d : G.Dart) : d.reverse.edge = d.edge := by
  cases d <;> trivial

/-- The reverse of a dart is distinct from the dart. -/
lemma reverse_neq_self (d : G.Dart) : d.reverse ≠ d := by
  cases d <;> intro hn <;> cases hn; contradiction

/- The reverse of the reverse of a dart is the dart itself. -/
lemma reverse_of_reverse (d : G.Dart) : d.reverse.reverse = d := by
  cases d <;> rfl

end Dart

/-- The dartset of a vertex is the set of darts starting at this vertex. -/
def dartSet (x : α) : Set G.Dart := {d | d.fst = x}

/- There exists a dart for any given edge. -/
lemma dart_of_edge (e : E(G)) : ∃ d : G.Dart, d.edge = e := by
  have ⟨e, he⟩ := e
  have ⟨x, y, isLink⟩ := (G.edge_mem_iff_exists_isLink e).mp he
  by_cases eq : x = y
  . cases eq
    exists Dart.Fwd x e isLink
  . exists Dart.Dir x y e eq isLink

/- Helper properties on Graph.IsLoopAt. -/
private lemma loop_vertex_eq (hx : G.IsLoopAt e x) (hy : G.IsLoopAt e y) : x = y := by
  cases IsLink.left_eq_or_eq hx hy <;> assumption

private lemma loop_vertex_left_eq (hx : G.IsLoopAt e x) (hy : G.IsLink e y z) : x = y := by
  rcases IsLink.eq_and_eq_or_eq_and_eq hx hy with ⟨hxy, hxz⟩ | ⟨hxz, hxy⟩
  . exact hxy
  . exact hxy

private lemma loop_vertex_right_eq (hx : G.IsLoopAt e x) (hy : G.IsLink e y z) : x = z := by
  rcases IsLink.eq_and_eq_or_eq_and_eq hx hy with ⟨hxy, hxz⟩ | ⟨hxz, hxy⟩
  . exact hxz
  . exact hxz

/- Two darts are equal or reverse of one another if they have the same edge. -/
lemma edge_dart_eq {d₁ d₂ : G.Dart} (h : d₁.edge = d₂.edge) : d₁ = d₂ ∨ d₁ = d₂.reverse := by
  by_cases eq : d₁ = d₂
  . exact Or.inl eq
  . right

    -- cross-case analysis: destruct d₁, d₂, and h to get us started
    rcases d₁ with ⟨x₁, e₁, isLoop₁⟩ | ⟨x₁, e₁, isLoop₁⟩ | ⟨x₁, y₁, e₁, ne₁, isLink₁⟩
    all_goals rcases d₂ with ⟨x₂, e₂, isLoop₂⟩ | ⟨x₂, e₂, isLoop₂⟩ | ⟨x₂, y₂, e₂, ne₂, isLink₂⟩
    all_goals cases h

     -- discharge Fwd/Bck, Fwd/Bck cases (4)
    all_goals try
      cases loop_vertex_eq isLoop₁ isLoop₂
      trivial

     -- discharge Fwd/Bck, Dir cases (2)
    all_goals try
      cases loop_vertex_left_eq isLoop₁ isLink₂
      cases loop_vertex_right_eq isLoop₁ isLink₂
      trivial

    -- discharge Dir, Fwd/Bck cases (2)
    all_goals try
      cases loop_vertex_left_eq isLoop₂ isLink₁
      cases loop_vertex_right_eq isLoop₂ isLink₁
      trivial

    -- discharge Dir, Dir case (1)
    rcases IsLink.eq_and_eq_or_eq_and_eq isLink₁ isLink₂ with ⟨hxy, hxz⟩ | ⟨hxz, hxy⟩
    . cases hxy
      cases hxz
      trivial
    . cases hxy
      cases hxz
      trivial

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
  G.Inc e x ↔ ∃ d : G.Dart, d.fst = x ∧ d.edge = e := by
  constructor
  . intro ⟨y, isLink⟩
    by_cases eq : x = y
    . cases eq
      exists Dart.Fwd x e isLink
    . exists Dart.Dir x y e eq isLink
  . intro ⟨d, hfst, hedge⟩
    all_goals cases hfst; cases hedge
    rcases d with ⟨x, e, isLoop⟩ | ⟨x, e, isLoop⟩ | ⟨x, y, e, ne, isLink⟩
    . exists x
    . exists x
    . exists y

/-- The IsDartLink relation is the dart version of IsLink, meaning `IsDartLink d x y`
iff `d` is a dart starting at `x` and ending at `y`.-/
def IsDartLink (d : G.Dart) (x y : α) := x = d.fst ∧ y = d.snd
