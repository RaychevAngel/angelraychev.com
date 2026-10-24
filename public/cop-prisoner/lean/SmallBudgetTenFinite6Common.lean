import SmallRowPrefixDegreeCheck
import SmallRowPrefixFastRouting
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
6 vertices with 10 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetTenFinite6
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f : Nat) : Rows 6 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32]
  | 2 => [3,5,9,17,33,6,10,18,34,12,20,36,24,40,48]
  | 3 => [7,11,19,35,13,21,37,25,41,49,14,22,38,26,42,50,28,44,52,56]
  | 4 => [15,23,39,27,43,51,29,45,53,57,30,46,54,58,60]
  | 5 => [31,47,55,59,61,62]
  | 6 => [63]
  | _ => []

theorem cover (d : Fin 7) : RowCover 6 d.val (choices d.val) := by
  revert d
  decide +kernel

#print axioms cover
end Delivery.SmallBudgetTenFinite6
