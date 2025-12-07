/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walks.Basic
import FriedmanStrongConv.Graph.Walks.Operations

variable {α β : Type*} {x y z u v w : α} {e f : β}
variable (G : Graph α β)

namespace Graph

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (x y : α) : Prop := Nonempty (G.Walk x y)

variable {G}

theorem reachable_iff_nonempty_univ {x y : α} :
    G.Reachable x y ↔ (Set.univ : Set (G.Walk x y)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {x y : α} :
  ¬G.Reachable x y ↔ IsEmpty (G.Walk x y) := not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {x y : α} (h : G.Reachable x y)
    (hp : G.Walk x y → p) : p :=
  Nonempty.elim h hp

protected theorem Walk.reachable {G : Graph α β} {x y : α} (p : G.Walk x y) :
  G.Reachable x y := ⟨p⟩

protected theorem Adj.reachable {x y : α} (h : G.Adj x y) : G.Reachable x y :=
  h.toWalk.reachable

@[refl]
protected theorem Reachable.refl (x : α) : G.Reachable x x := ⟨Walk.nil⟩

@[simp] protected theorem Reachable.rfl {x : α} : G.Reachable x x := Reachable.refl _

@[symm]
protected theorem Reachable.symm {x y : α} (hxy : G.Reachable x y) : G.Reachable y x :=
  hxy.elim fun p => ⟨p.reverse⟩

theorem reachable_comm {x y : α} : G.Reachable x y ↔ G.Reachable y x :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
protected theorem Reachable.trans {x y z : α} (hxy : G.Reachable x y) (hyz : G.Reachable y z) :
    G.Reachable x z :=
  hxy.elim fun pxy => hyz.elim fun pyz => ⟨pxy.append pyz⟩

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (Reachable.refl (G := G)) (Reachable.symm (G := G)) (Reachable.trans (G := G))

def Connected (U : Set α) := U ⊆ V(G) ∧ ∀x y, x ∈ U ∧ y ∈ U -> G.Reachable x y

theorem singleton_connected (xinVG : x ∈ V(G)) : Connected G {x} := by
  constructor
  . exact Set.singleton_subset_iff.mpr xinVG
  . intro y z ⟨hy, hz⟩
    cases hy
    cases hz
    exact Reachable.refl x

def Disconnected (U : Set α) := ¬Connected G U

def ConnectedComponent (U : Set α) := U ≠ ∅ ∧ Connected G U ∧ ∀U', U ⊂ U' -> Disconnected G U'

-- shows that, if y is reachable from x, then either x = y or they are both in V(G)
lemma eq_or_inVG_of_reachable (hxy : G.Reachable x y) : x = y ∨ (x ∈ V(G) ∧ y ∈ V(G)) := by
  induction hxy.some
  . left
    rfl
  . rename_i x y z e h p p_ih
    right
    rcases p_ih ⟨p⟩ with yeqz | ⟨yinVG, zinVG⟩
    . have xinVG := h.left_mem
      have yinVG := h.right_mem
      rw [<- yeqz]
      exact ⟨xinVG, yinVG⟩
    . have xinVG := h.left_mem
      exact ⟨xinVG, zinVG⟩

lemma not_reachable_of_different_or_ninVG (h : ¬(x = y ∨ (x ∈ V(G) ∧ y ∈ V(G)))) : ¬G.Reachable x y := by
  intro hxy
  apply h
  rcases eq_or_inVG_of_reachable G hxy with xeqy | inVG
  exact Or.inl xeqy
  exact Or.inr inVG

-- gets a set that is the ConnectedComponent of G in which x ∈ V(G) resides
def cc (x : α) : Set α := { y | G.Reachable x y }

-- x is in its ConnectedComponent
lemma mem_cc (x : α) : x ∈ (cc G x) := Reachable.refl x

-- x's connected component is actually a ConnectedComponent
lemma connected_component_cc (xinVG : x ∈ V(G)) : ConnectedComponent G (cc G x) := by
  have xinU := mem_cc G x
  repeat any_goals constructor
  . exact ne_of_mem_of_not_mem' xinU id
  . intro y yinU
    rcases eq_or_inVG_of_reachable G yinU with xeqy | ⟨xinVG, yinVG⟩
    . rw [<- xeqy]
      exact xinVG
    . exact yinVG
  . intro y z ⟨yinU, zinU⟩
    apply Reachable.trans (y := x)
    exact Reachable.symm yinU
    exact zinU
  . intro U' hUU'
    have ⟨y, yinU', yninU⟩ := Set.exists_of_ssubset hUU'
    have xinU' : x ∈ U' := Set.mem_of_subset_of_mem hUU'.subset xinU
    intro hU'
    unfold Connected at hU'
    have hxy := hU'.right x y ⟨xinU', yinU'⟩
    have yinU : y ∈ (cc G x) := hxy
    exact yninU yinU

-- I don't like this definition: I'm pretty sure it only goes one-way
theorem cc_equivalence_class₁ : ∀x, x ∈ V(G) -> ∃U, x ∈ U ∧ ConnectedComponent G U ∧ ∀y, G.Reachable x y <-> y ∈ U := by
  intro x xinVG
  exists cc G x
  apply And.intro (mem_cc G x)
  apply And.intro (connected_component_cc G xinVG)
  intro y
  exact Eq.to_iff rfl

-- if U is connected, and there is some x reachable from y, the U ∪ {y} is also connected
-- TODO: probably want a version that takes two arbitrary sets U and U' rather than one set U and a singleton { y }
lemma including_connected {U : Set α} (hU : Connected G U) (xinU : x ∈ U) (hxy : G.Reachable x y) : Connected G (U ∪ { y }) := by
  rcases eq_or_inVG_of_reachable G hxy with xeqy | ⟨xinVG, yinVG⟩
  . have h : U ∪ { y } = U := by
      rw [<- xeqy]
      apply Set.union_eq_left.mpr
      exact Set.singleton_subset_iff.mpr xinU
    rw [h]
    exact hU
  . constructor
    . apply Set.union_subset
      . exact hU.left
      . exact Set.singleton_subset_iff.mpr yinVG
    . intro x' y' ⟨x'inUy, y'inUy⟩
      rcases x'inUy with x'inU | x'eqY
      . rcases y'inUy with y'inU | y'eqY
        . exact hU.right x' y' ⟨x'inU, y'inU⟩
        . apply Reachable.trans (y := x)
          . exact hU.right x' x ⟨x'inU, xinU⟩
          . cases y'eqY
            exact hxy
      . rcases y'inUy with y'inU | y'eqY
        . apply Reachable.trans (y := x)
          . cases x'eqY
            exact hxy.symm
          . exact hU.right x y' ⟨xinU, y'inU⟩
        . cases x'eqY
          cases y'eqY
          exact Reachable.refl y

-- if x ∈ Connected U is reachable from y ∈ Connected U', then U ∪ U' is connected
lemma union_connected_of_reachable {U U' : Set α} (hU : Connected G U) (hU' : Connected G U') (xinU : x ∈ U) (yinU' : y ∈ U') (hxy : G.Reachable x y) : Connected G (U ∪ U') := by
  unfold Connected
  constructor
  . have UsubsetVG := hU.left
    have U'subsetVG := hU'.left
    exact Set.union_subset UsubsetVG U'subsetVG
  . intro z w ⟨zinUnion, winUnion⟩
    rcases zinUnion with zinU | zinU' <;> rcases winUnion with winU | winU'
    . exact hU.right z w ⟨zinU, winU⟩
    . apply Reachable.trans (y := x)
      exact hU.right z x ⟨zinU, xinU⟩
      apply Reachable.trans (y := y)
      exact hxy
      exact hU'.right y w ⟨yinU', winU'⟩
    . apply Reachable.trans (y := y)
      exact hU'.right z y ⟨zinU', yinU'⟩
      apply Reachable.trans (y := x)
      exact hxy.symm
      exact hU.right x w ⟨xinU, winU⟩
    . exact hU'.right z w ⟨zinU', winU'⟩

-- now let's prove this special case much more easily...
lemma including_connected₂ {U : Set α} (hU : Connected G U) (xinU : x ∈ U) (hxy : G.Reachable x y) : Connected G (U ∪ { y }) := by
  rcases eq_or_inVG_of_reachable G hxy with xeqy | ⟨xinVG, yinVG⟩
  . rw [<- xeqy]
    have xinVG := hU.left xinU
    exact union_connected_of_reachable G hU (singleton_connected G xinVG) xinU rfl (Reachable.refl x)
  . exact union_connected_of_reachable G hU (singleton_connected G yinVG) xinU rfl hxy

theorem mem_connected_component_of_mem_reachable {U : Set α} (hU : ConnectedComponent G U) (xinU : x ∈ U) (hxy : G.Reachable x y) : y ∈ U := by
  rcases Classical.em (y ∈ U) with yinU | yninU
  . exact yinU
  . exfalso
    have union_connected := including_connected G hU.right.left xinU hxy
    have singleton_not_subset : ¬{ y } ⊆ U := fun hn => yninU (hn rfl)
    have union_strict_superset : (U ∪ { y }) ⊃ U := Set.ssubset_union_left_iff.mpr singleton_not_subset
    have union_disconnected := hU.right.right (U ∪ { y }) union_strict_superset
    exact union_disconnected union_connected

theorem connected_components_eq_or_disjoint : ∀U U', ConnectedComponent G U -> ConnectedComponent G U' -> U = U' ∨ U ∩ U' = ∅ := by
  intro U U' hU hU'
  let ⟨x, xinU⟩ := Set.nonempty_iff_ne_empty.mpr hU.left
  rcases Classical.em (x ∈ U') with xinU' | xninU'
  . left
    funext y
    ext
    constructor
    . intro yinU
      have hxy := hU.right.left.right x y ⟨xinU, yinU⟩
      exact mem_connected_component_of_mem_reachable G hU' xinU' hxy
    . intro yinU'
      have hxy := hU'.right.left.right x y ⟨xinU', yinU'⟩
      exact mem_connected_component_of_mem_reachable G hU xinU hxy
  . right
    -- prove that U' ∪ x is Disconnected... then what?
    have singleton_not_subset : ¬{ x } ⊆ U' := fun hn => xninU' (hn rfl)
    have union_strict_superset : (U' ∪ { x }) ⊃ U' := Set.ssubset_union_left_iff.mpr singleton_not_subset
    have union_disconnected : Disconnected G (U' ∪ { x }) := hU'.right.right (U' ∪ { x }) union_strict_superset
    -- I have no idea where to go with this...
    -- I guess we do a proof by contradiction
    apply Classical.byContradiction
    intro hn
    rw [Set.eq_empty_iff_forall_notMem] at hn
    have ⟨z, ⟨zinU, zinU'⟩⟩ : ∃z, z ∈ U ∧ z ∈ U' := Classical.not_forall_not.mp hn
    -- we now have x in U but not in U', and z in both U and U'
    -- this means z is reachable from x...
    -- which means U' ∪ {x} is connected...
    -- which contradicts what we already know
    have hxz := hU.right.left.right x z ⟨xinU, zinU⟩
    have union_connected : Connected G (U' ∪ { x }) := including_connected G hU'.right.left zinU' hxz.symm
    exact union_disconnected union_connected

-- this is a bit boring... feel like it should say a bit more about cc
theorem mem_cc_of_reachable (hxy : G.Reachable x y) : y ∈ (G.cc x) := hxy

-- if x is in a ConnectedComponent U, then U is cc G x
theorem eq_cc_of_mem {U : Set α} (hU : ConnectedComponent G U) (xinU : x ∈ U) : U = cc G x := by
  have hcc := connected_component_cc G (hU.right.left.left xinU)
  rcases connected_components_eq_or_disjoint G U (cc G x) hU hcc with Ueqcc | disjoint
  . exact Ueqcc
  . exfalso
    have xincc := mem_cc G x
    rw [Set.eq_empty_iff_forall_notMem] at disjoint
    apply disjoint x
    constructor
    . exact xinU
    . exact xincc

-- I don't like this definition either... but it might go both ways
-- still feel like we need prove that the connected components are disjoint? (done above)
theorem cc_equivalence_class : ∀x U, ConnectedComponent G U -> (x ∈ U <-> (∀y, G.Reachable x y -> y ∈ U)) := by
  intro x U hU
  constructor
  . intro xinU y hxy
    exact mem_connected_component_of_mem_reachable G hU xinU hxy
  . intro lhs
    apply lhs
    exact Reachable.refl x
