import RowPrefixBoolean

namespace Delivery.IrregularTen14
open FiniteGame Extremal RowPrefix

def D (s : Fin 10) : Nat := if s.val < 4 then 2 else 1
def R (t : Fin 10) : Nat := if 4 ≤ t.val ∧ t.val < 8 then 2 else 1

def rows (a b c d e f g h i j : Nat) : Rows 10 := fun v =>
  match v.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
  | 5 => f | 6 => g | 7 => h | 8 => i | _ => j

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def choices (d : Nat) : List Nat :=
  if d = 2 then [3,5,9,17,33,65,129,257,513,6,10,18,34,66,130,258,514,12,20,36,68,132,260,516,24,40,72,136,264,520,48,80,144,272,528,96,160,288,544,192,320,576,384,640,768] else [1,2,4,8,16,32,64,128,256,512]

theorem cover_one : RowCover 10 1 (choices 1) := by decide +kernel
theorem cover_two : RowCover 10 2 (choices 2) := by decide +kernel
theorem complete (s : Fin 10) : RowCover 10 (D s) (choices (D s)) := by
  unfold D
  split
  · exact cover_two
  · exact cover_one

#print axioms complete
end Delivery.IrregularTen14
