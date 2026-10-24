import SmallBudgetEightWitness

/-! The retained 6-vertex, 10-arrow witness; every winning-region step is
checked against the actual graph, including all cop replies. -/
namespace Delivery.SmallBudgetTenWitness
open FiniteGame Extremal SparseSupport

def edge (s t : Fin 6) : Prop := (s.val,t.val)∈[(1,3),(2,3),(2,4),(3,0),(3,1),(4,2),(4,5),(5,0),(5,1),(5,4)]
instance (s t : Fin 6) : Decidable (edge s t) := inferInstanceAs (Decidable (_∈_))
instance (s t : Fin 6) : Decidable (Legal edge s t) := inferInstanceAs (Decidable (_∨_))
def code (t r c : Fin 6) : Nat := [1, 1, 1, 1, 1, 1, 4, 0, 0, 0, 4, 4, 4, 6, 0, 6, 4, 4, 2, 2, 2, 0, 2, 2, 4, 4, 4, 4, 0, 8, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 4, 6, 0, 6, 4, 4, 2, 2, 2, 0, 2, 2, 4, 4, 4, 4, 0, 8, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 2, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 8, 4, 0, 4, 4, 6, 4, 6, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 2, 1, 1, 1, 1, 1, 1][t.val*36+r.val*6+c.val]?.getD 0
def move (t r c : Fin 6) : Fin 6 :=
  ⟨[0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 3, 4, 0, 4, 3, 3, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 3, 4, 0, 4, 3, 3, 1, 1, 1, 0, 1, 1, 5, 5, 5, 5, 0, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 2, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 5, 2, 0, 2, 1, 4, 1, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5][t.val*36+r.val*6+c.val]?.getD 0 % 6, Nat.mod_lt _ (by decide)⟩
def region (t r c : Fin 6) : Prop := 0<code t r c
instance (t r c : Fin 6) : Decidable (region t r c) := inferInstanceAs (Decidable (_<_))
def rank (t r c : Fin 6) : Nat := code t r c-1

theorem valid (t r c : Fin 6) (inside : region t r c) (nonterminal : r≠t) (safe : r≠c) :
    Legal edge r (move t r c) ∧ (move t r c=t ∨
      (move t r c≠c ∧ ∀d,Legal edge c d →
        move t r c≠d ∧ region t (move t r c) d ∧ rank t (move t r c) d<rank t r c)) := by
  revert t r c
  decide +kernel

def certificate (t : Fin 6) : WinningRegion edge t :=
  ⟨region t,rank t,move t,valid t⟩

def counted (s t : Fin 6) : Prop := (s.val,t.val)∈[(2,0),(2,1),(4,0),(4,1),(4,3),(5,3)]
instance (s t : Fin 6) : Decidable (counted s t) := inferInstanceAs (Decidable (_∈_))
theorem starts (s t c : Fin 6) (pair : counted s t) (initial : c≠s) : region t s c := by
  revert s t c
  decide +kernel

theorem counted_pairs : 6≤score edge := by
  have valid (s t : Fin 6) (pair : counted s t) : Indirect edge s t := by
    have facts : ∀s t : Fin 6,counted s t→s≠t∧¬edge s t := by decide +kernel
    refine ⟨(facts s t pair).1,(facts s t pair).2,?_⟩
    intro c initial
    exact ⟨_,winningRegion_winning (certificate t) s c (starts s t c pair initial) (Ne.symm initial)⟩
  have bound := arcs_mono valid
  have count : arcCount counted=6 := by rw [arcCount_eq]; decide +kernel
  change arcCount counted≤score edge at bound
  omega

theorem loopless : Loopless edge := by unfold Loopless; decide +kernel
theorem arrows : arcCount edge=10 := by rw [arcCount_eq]; decide +kernel
#print axioms counted_pairs
end Delivery.SmallBudgetTenWitness
