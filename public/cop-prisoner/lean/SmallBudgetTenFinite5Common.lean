import SmallRowPrefixDegreeCheck
import SmallRowPrefixFastRouting
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
5 vertices with 10 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetTenFinite5
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e : Nat) : Rows 5 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16]
  | 2 => [3,5,9,17,6,10,18,12,20,24]
  | 3 => [7,11,19,13,21,25,14,22,26,28]
  | 4 => [15,23,27,29,30]
  | 5 => [31]
  | _ => []

theorem cover (d : Fin 6) : RowCover 5 d.val (choices d.val) := by
  revert d
  decide +kernel

#print axioms cover
end Delivery.SmallBudgetTenFinite5
