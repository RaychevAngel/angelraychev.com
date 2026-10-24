import SmallBudgetEightWitness

/-! The retained five-vertex, 12-arrow witness; every winning-region step is
checked against the actual graph, including all cop replies. -/
namespace Delivery.FiveVertexWitness12
open FiniteGame Extremal SparseSupport

def edge (s t : Fin 5) : Prop := (s.val,t.val)∈[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0),(3,1),(4,0)]
instance (s t : Fin 5) : Decidable (edge s t) := inferInstanceAs (Decidable (_∈_))
instance (s t : Fin 5) : Decidable (Legal edge s t) := inferInstanceAs (Decidable (_∨_))
def code (t r c : Fin 5) : Nat := [1, 1, 1, 1, 1, 0, 0, 0, 4, 4, 2, 2, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 4, 1, 1, 1, 1, 1, 0, 0, 0, 0, 4, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4, 4, 0, 4, 0, 4, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 0, 2, 2, 1, 1, 1, 1, 1, 0, 4, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 0, 2, 2, 4, 4, 4, 0, 4, 1, 1, 1, 1, 1][t.val*25+r.val*5+c.val]?.getD 0
def move (t r c : Fin 5) : Fin 5 :=
  ⟨[0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 1, 1, 1, 1, 0, 0, 0, 0, 3, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0, 4, 4, 1, 0, 1, 0, 1, 4, 4, 4, 4, 4][t.val*25+r.val*5+c.val]?.getD 0 % 5, Nat.mod_lt _ (by decide)⟩
def region (t r c : Fin 5) : Prop := 0<code t r c
instance (t r c : Fin 5) : Decidable (region t r c) := inferInstanceAs (Decidable (_<_))
def rank (t r c : Fin 5) : Nat := code t r c-1

theorem valid (t r c : Fin 5) (inside : region t r c) (nonterminal : r≠t) (safe : r≠c) :
    Legal edge r (move t r c) ∧ (move t r c=t ∨
      (move t r c≠c ∧ ∀d,Legal edge c d →
        move t r c≠d ∧ region t (move t r c) d ∧ rank t (move t r c) d<rank t r c)) := by
  revert t r c
  decide +kernel

def certificate (t : Fin 5) : WinningRegion edge t :=
  ⟨region t,rank t,move t,valid t⟩

def counted (s t : Fin 5) : Prop := (s.val,t.val)∈[(3,2),(3,4)]
instance (s t : Fin 5) : Decidable (counted s t) := inferInstanceAs (Decidable (_∈_))
theorem starts (s t c : Fin 5) (pair : counted s t) (initial : c≠s) : region t s c := by
  revert s t c
  decide +kernel

theorem lower : 2≤score edge := by
  have valid (s t : Fin 5) (pair : counted s t) : Indirect edge s t := by
    have facts : ∀s t : Fin 5,counted s t→s≠t∧¬edge s t := by decide +kernel
    refine ⟨(facts s t pair).1,(facts s t pair).2,?_⟩
    intro c initial
    exact ⟨_,winningRegion_winning (certificate t) s c (starts s t c pair initial) (Ne.symm initial)⟩
  have bound := arcs_mono valid
  have count : arcCount counted=2 := by rw [arcCount_eq]; decide +kernel
  change arcCount counted≤score edge at bound
  omega

theorem loopless : Loopless edge := by unfold Loopless; decide +kernel
theorem arrows : arcCount edge=12 := by rw [arcCount_eq]; decide +kernel
#print axioms lower
end Delivery.FiveVertexWitness12
