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
  | Loop : (x : α) -> (e : β) -> (isLoop : G.IsLoopAt e x) -> (fwd : Bool) -> Dart
  | Dir : (x y : α) -> (e : β) -> (ne : x ≠ y) -> (isLink : G.IsLink e x y) -> Dart

namespace Dart

/- Interface from the structure -/
def fst (d : G.Dart) : α :=
  match d with
  | .Loop x _ _ _ => x
  | .Dir x _ _ _ _ => x

def snd (d : G.Dart) : α :=
  match d with
  | .Loop x _ _ _ => x
  | .Dir _ y _ _ _ => y

def edge (d : G.Dart) : β :=
  match d with
  | .Loop _ e _ _ => e
  | .Dir _ _ e _ _ => e

def isLink (d : G.Dart) : G.IsLink d.edge d.fst d.snd :=
  match d with
  | .Loop _ _ l _ => l
  | .Dir _ _ _ _ l => l

def orienOfEq (d : G.Dart) (eq : d.fst = d.snd) : Bool :=
  match d with
  | .Loop _ _ _ b => b
  | .Dir x y _ ne _ => by
    cases eq
    trivial

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

/-- The reversing operation on darts, which reverses its orientation. -/
def reverse (d : G.Dart) : G.Dart :=
  match d with
  | .Loop x e isLoop dir => Loop x e isLoop (!dir)
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
lemma reverse_neq_self (d : G.Dart) : d.reverse ≠ d :=
  match d with
  | .Loop x e isLoop dir => by
    intro hn
    injection hn with _ _ hdir
    exact (Bool.eq_not_self dir).mp (id (Eq.symm hdir))
  | .Dir x y e ne isLink => by
    intro hn
    cases hn
    exact ne (Eq.refl x)

/- The reverse of the reverse of a dart is the dart itself. -/
lemma reverse_of_reverse (d : G.Dart) : d.reverse.reverse = d := by
  cases d <;> rw [reverse, reverse]; rw [Bool.not_not]

end Dart

/-- The dartset of a vertex is the set of darts starting at this vertex. -/
def dartSet (x : α) : Set G.Dart := {d | d.fst = x}

/- There exists a dart for any given edge. -/
lemma dart_of_edge (e : E(G)) : ∃ d : G.Dart, d.edge = e := by
  have ⟨e, he⟩ := e
  have ⟨x, y, isLink⟩ := (G.edge_mem_iff_exists_isLink e).mp he
  by_cases eq : x = y
  . cases eq
    exists Dart.Loop x e isLink true
  . exists Dart.Dir x y e eq isLink

/- Two darts are equal or reverse of one another if they have the same edge. -/
lemma edge_dart_eq {d₁ d₂ : G.Dart} (h : d₁.edge = d₂.edge) : d₁ = d₂ ∨ d₁ = d₂.reverse := by
  by_cases eq : d₁ = d₂
  . exact Or.inl eq
  . right

    -- cross-case analysis: destruct d₁, d₂, and h to get us started
    rcases d₁ with ⟨x₁, e₁, isLoop₁, fwd₁⟩ | ⟨x₁, y₁, e₁, ne₁, isLink₁⟩
    all_goals rcases d₂ with ⟨x₂, e₂, isLoop₂, fwd₂⟩ | ⟨x₂, y₂, e₂, ne₂, isLink₂⟩
    all_goals cases h

    . rcases IsLink.left_eq_or_eq isLoop₁ isLoop₂ with ⟨hxx⟩ | ⟨hxx⟩
      all_goals
        cases hxx
        congr
        apply Bool.eq_not.mpr
        intro rfl
        apply eq
        rfl
    . rcases IsLink.eq_and_eq_or_eq_and_eq isLoop₁ isLink₂ with ⟨hxx, hxy⟩ | ⟨hxy, hxx⟩
      all_goals
        exfalso
        apply ne₂
        exact (Eq.trans hxx.symm hxy)
    . rcases IsLink.eq_and_eq_or_eq_and_eq isLink₁ isLoop₂ with ⟨hxx, hxy⟩ | ⟨hxx, hxy⟩
      all_goals
        exfalso
        apply ne₁
        exact (Eq.trans hxx hxy.symm)
    . rw [Dart.reverse]
      rcases IsLink.eq_and_eq_or_eq_and_eq isLink₁ isLink₂ with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
      . cases hxx
        cases hyy
        exfalso
        apply eq
        rfl
      . congr

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
  . intro ⟨y, he⟩
    by_cases isLoop : x = y
    . exists Dart.Loop y e (isLoop ▸ he) true
      exact And.intro isLoop.symm rfl
    . exists Dart.Dir x y e isLoop he
  . intro ⟨d, ⟨h₁, h₂⟩⟩
    unfold Graph.Inc
    exists d.snd
    rw [<- h₁, <- h₂]
    exact Dart.isLink d

/-- The IsDartLink relation is the dart version of IsLink, meaning `IsDartLink d x y`
iff `d` is a dart starting at `x` and ending at `y`.-/
def IsDartLink (d : G.Dart) (x y : α) := x = d.fst ∧ y = d.snd

lemma IsLink_edge_of_IsDartLink {d : G.Dart} {x y : α} (h : IsDartLink d x y) : G.IsLink d.edge x y := by
  rcases h with ⟨rfl, rfl⟩ -- this is fun: you can drop rfl in to immediately destruct it
  exact Dart.isLink d
