import FiniteExclusionScore
import GraphRelabeling
import FiniteExclusionNine2x2x2x3
import FiniteExclusionNine2x2x5
import FiniteExclusionNine2x3x4
import FiniteExclusionNine2x7
import FiniteExclusionNine3x3x3
import FiniteExclusionNine3x6
import FiniteExclusionNine4x5
import FiniteExclusionNine9

/-! Complete kernel-checked second-permutation exclusions for the eight
canonical first-factor types at order nine. Arbitrary regular-graph
factorization and cycle normalization are deliberately not assumed here. -/
namespace Delivery.FiniteExclusion.Nine
open FiniteGame Extremal

inductive CycleType
  | c2223 | c225 | c234 | c27 | c333 | c36 | c45 | c9
  deriving DecidableEq, Repr

def first : CycleType → Assignment 9
  | .c2223 => Cycle2x2x2x3.a
  | .c225 => Cycle2x2x5.a
  | .c234 => Cycle2x3x4.a
  | .c27 => Cycle2x7.a
  | .c333 => Cycle3x3x3.a
  | .c36 => Cycle3x6.a
  | .c45 => Cycle4x5.a
  | .c9 => Cycle9.a

theorem first_loopless (cycle : CycleType) : ∀ i, first cycle i ≠ i := by
  cases cycle <;> decide +kernel

theorem first_injective (cycle : CycleType) :
    ∀ i j, first cycle i = first cycle j → i = j := by
  cases cycle <;> decide +kernel

theorem blocked (cycle : CycleType) (b : Assignment 9) (valid : Valid (first cycle) b) :
    Blocked (first cycle) b := by
  cases cycle with
  | c2223 => exact Cycle2x2x2x3.every_second_factor_blocked b valid
  | c225 => exact Cycle2x2x5.every_second_factor_blocked b valid
  | c234 => exact Cycle2x3x4.every_second_factor_blocked b valid
  | c27 => exact Cycle2x7.every_second_factor_blocked b valid
  | c333 => exact Cycle3x3x3.every_second_factor_blocked b valid
  | c36 => exact Cycle3x6.every_second_factor_blocked b valid
  | c45 => exact Cycle4x5.every_second_factor_blocked b valid
  | c9 => exact Cycle9.every_second_factor_blocked b valid

theorem upper (cycle : CycleType) (b : Assignment 9) (valid : Valid (first cycle) b) :
    score (edgeOf (first cycle) b) ≤ 53 :=
  nine_factor_upper (first cycle) b (first_loopless cycle) valid (blocked cycle b valid)


theorem exact_budget (cycle : CycleType) (b : Assignment 9)
    (valid : Valid (first cycle) b) :
    Loopless (edgeOf (first cycle) b) ∧ arcCount (edgeOf (first cycle) b) = 18 ∧
      missingCount (edgeOf (first cycle) b) = 54 :=
  ⟨factor_loopless _ _ (first_loopless cycle) valid, nine_factor_arcs _ _ valid,
    nine_factor_missing _ _ (first_loopless cycle) valid⟩

/-- The exact proved family includes every valid second factor, not only the
535 leaves that required a non-camping losing certificate. -/
def Represented (E : Graph (Fin 9)) : Prop :=
  ∃ cycle b, Valid (first cycle) b ∧ E = edgeOf (first cycle) b

theorem represented_upper (E : Graph (Fin 9)) (represented : Represented E) :
    score E ≤ 53 := by
  obtain ⟨cycle,b,valid,rfl⟩ := represented
  exact upper cycle b valid

/-- Relabeling transport is unconditional once an explicit representation
is given. It does not assert that every regular graph has such a representation. -/
theorem relabeled_upper (E : Graph (Fin 9)) (cycle : CycleType)
    (b : Assignment 9) (valid : Valid (first cycle) b)
    (iso : GraphRelabeling.Iso E (edgeOf (first cycle) b)) : score E ≤ 53 := by
  rw [GraphRelabeling.score_eq iso]
  exact upper cycle b valid

#print axioms blocked
#print axioms upper
#print axioms exact_budget
#print axioms represented_upper
#print axioms relabeled_upper
end Delivery.FiniteExclusion.Nine
