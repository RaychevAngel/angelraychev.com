import SmallBudgetSix

/-! Literal eight-arrow, four-pair witness retained in solver-enumeration-n6.json. -/
namespace Delivery.SmallBudgetEightWitness
open FiniteGame Extremal SparseSupport

def edge (s t : Fin 6) : Prop :=
  ((s=2 ∨ s=3) ∧ (t=0 ∨ t=1)) ∨ (s=4 ∧ (t=2 ∨ t=5)) ∨ (s=5 ∧ (t=3 ∨ t=4))
instance (s t : Fin 6) : Decidable (edge s t) := inferInstanceAs (Decidable (_∨_))
instance (s t : Fin 6) : Decidable (Legal edge s t) := inferInstanceAs (Decidable (_∨_))

theorem loopless : Loopless edge := by unfold Loopless; decide +kernel
theorem arrows : arcCount edge=8 := by rw [arcCount_eq]; decide +kernel

def counted (s t : Fin 6) : Prop := (s=4 ∨ s=5) ∧ (t=0 ∨ t=1)
instance (s t : Fin 6) : Decidable (counted s t) := inferInstanceAs (Decidable (_∧_))

theorem witnesses (s t c : Fin 6) (pair : counted s t) (initial : c≠s) :
    ∃a,edge s a ∧ a≠c ∧ ∀d,Legal edge c d → a≠d ∧
      (edge a t ∨ ∃b,edge a b ∧ edge b t ∧ ¬Legal edge d b) := by
  revert s t c
  decide +kernel

theorem wins (s t : Fin 6) (pair : counted s t) : Guaranteed edge s t := by
  intro c initial
  obtain ⟨a,first,safe,next⟩ := witnesses s t c pair initial
  refine ⟨3,Winning.step (Ne.symm initial) (Or.inr first) safe (fun d hd => (next d hd).1) ?_⟩
  intro d hd
  obtain ⟨distinct,direct|⟨b,move,last,avoid⟩⟩ := next d hd
  · exact Winning.finish distinct (Or.inr direct)
  · exact DenseCounting.safe_intermediate_winning distinct move last avoid

theorem four_pairs : 4≤score edge := by
  have valid (s t : Fin 6) (pair : counted s t) : Indirect edge s t := by
    have facts : ∀s t : Fin 6,counted s t→s≠t∧¬edge s t := by decide +kernel
    exact ⟨(facts s t pair).1,(facts s t pair).2,wins s t pair⟩
  have bound := arcs_mono valid
  have count : arcCount counted=4 := by rw [arcCount_eq]; decide +kernel
  change arcCount counted≤score edge at bound
  omega

#print axioms four_pairs
end Delivery.SmallBudgetEightWitness
