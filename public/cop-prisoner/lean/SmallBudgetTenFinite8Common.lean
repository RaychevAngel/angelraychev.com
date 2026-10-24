import SmallRowPrefixDegreeCheck
import SmallRowPrefixFastRouting
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
8 vertices with 10 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetTenFinite8
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g h : Nat) : Rows 8 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64,128]
  | 2 => [3,5,9,17,33,65,129,6,10,18,34,66,130,12,20,36,68,132,24,40,72,136,48,80,144,96,160,192]
  | 3 => [7,11,19,35,67,131,13,21,37,69,133,25,41,73,137,49,81,145,97,161,193,14,22,38,70,134,26,42,74,138,50,82,146,98,162,194,28,44,76,140,52,84,148,100,164,196,56,88,152,104,168,200,112,176,208,224]
  | 4 => [15,23,39,71,135,27,43,75,139,51,83,147,99,163,195,29,45,77,141,53,85,149,101,165,197,57,89,153,105,169,201,113,177,209,225,30,46,78,142,54,86,150,102,166,198,58,90,154,106,170,202,114,178,210,226,60,92,156,108,172,204,116,180,212,228,120,184,216,232,240]
  | 5 => [31,47,79,143,55,87,151,103,167,199,59,91,155,107,171,203,115,179,211,227,61,93,157,109,173,205,117,181,213,229,121,185,217,233,241,62,94,158,110,174,206,118,182,214,230,122,186,218,234,242,124,188,220,236,244,248]
  | 6 => [63,95,159,111,175,207,119,183,215,231,123,187,219,235,243,125,189,221,237,245,249,126,190,222,238,246,250,252]
  | 7 => [127,191,223,239,247,251,253,254]
  | 8 => [255]
  | _ => []

theorem cover (d : Fin 9) : RowCover 8 d.val (choices d.val) := by
  revert d
  decide +kernel

#print axioms cover
end Delivery.SmallBudgetTenFinite8
