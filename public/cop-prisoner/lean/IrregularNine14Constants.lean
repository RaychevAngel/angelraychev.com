import IrregularNine14Base
import RowPrefixCampingNine

namespace Delivery.IrregularNine14
open RowPrefix

def leftConstant (profile : Fin 11) : Nat := match profile.val with
| 0 => 28
| 1 => 28
| 2 => 29
| 3 => 28
| 4 => 28
| 5 => 29
| 6 => 30
| 7 => 31
| 8 => 28
| 9 => 32
| _ => 29

theorem constants (profile : Fin 11) :
    eligibleCount (D profile) (R profile) + lowSum (D profile) + lowSum (R profile) = leftConstant profile ∧
    degreeSum (D profile) = 14 := by
  revert profile
  decide +kernel

#print axioms constants
end Delivery.IrregularNine14
