import RowPrefixBooleanNine

namespace Delivery.IrregularNine14
open FiniteGame Extremal RowPrefix

def rows (a b c d e f g h i : Nat) : Rows 9 := fun v =>
  match v.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
  | 5 => f | 6 => g | 7 => h | _ => i

def D (profile : Fin 11) : Fin 9 → Nat :=
  match profile.val with
  | 0 => rows 3 2 2 2 1 1 1 1 1
  | 1 => rows 3 2 2 2 1 1 1 1 1
  | 2 => rows 3 2 2 2 1 1 1 1 1
  | 3 => rows 2 2 2 2 2 1 1 1 1
  | 4 => rows 2 2 2 2 2 1 1 1 1
  | 5 => rows 2 2 2 2 2 1 1 1 1
  | 6 => rows 2 2 2 2 2 1 1 1 1
  | 7 => rows 2 2 2 2 2 1 1 1 1
  | 8 => rows 2 2 2 2 2 1 1 1 1
  | 9 => rows 2 2 2 2 2 1 1 1 1
  | _ => rows 2 2 2 2 2 1 1 1 1

def R (profile : Fin 11) : Fin 9 → Nat :=
  match profile.val with
  | 0 => rows 2 1 1 1 2 2 2 2 1
  | 1 => rows 1 2 1 1 2 2 2 2 1
  | 2 => rows 1 1 1 1 2 2 2 2 2
  | 3 => rows 3 1 1 1 1 2 2 2 1
  | 4 => rows 2 2 2 2 2 1 1 1 1
  | 5 => rows 2 2 2 2 1 2 1 1 1
  | 6 => rows 2 2 2 1 1 2 2 1 1
  | 7 => rows 2 2 1 1 1 2 2 2 1
  | 8 => rows 2 1 1 1 1 3 2 2 1
  | 9 => rows 2 1 1 1 1 2 2 2 2
  | _ => rows 1 1 1 1 1 3 2 2 2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def choices (d : Nat) : List Nat :=
  match d with
  | 1 => [1,2,4,8,16,32,64,128,256]
  | 2 => [3,5,9,17,33,65,129,257,6,10,18,34,66,130,258,12,20,36,68,132,260,24,40,72,136,264,48,80,144,272,96,160,288,192,320,384]
  | 3 => [7,11,19,35,67,131,259,13,21,37,69,133,261,25,41,73,137,265,49,81,145,273,97,161,289,193,321,385,14,22,38,70,134,262,26,42,74,138,266,50,82,146,274,98,162,290,194,322,386,28,44,76,140,268,52,84,148,276,100,164,292,196,324,388,56,88,152,280,104,168,296,200,328,392,112,176,304,208,336,400,224,352,416,448]
  | _ => []

theorem cover_one : RowCover 9 1 (choices 1) := by decide +kernel
theorem cover_two : RowCover 9 2 (choices 2) := by decide +kernel
theorem cover_three : RowCover 9 3 (choices 3) := by decide +kernel

theorem degree_cases (profile : Fin 11) (s : Fin 9) :
    D profile s=1 ∨ D profile s=2 ∨ D profile s=3 := by
  revert profile s
  decide +kernel

theorem complete (profile : Fin 11) (s : Fin 9) : RowCover 9 (D profile s) (choices (D profile s)) := by
  rcases degree_cases profile s with h | h | h
  · rw [h]; exact cover_one
  · rw [h]; exact cover_two
  · rw [h]; exact cover_three

#print axioms complete
end Delivery.IrregularNine14
