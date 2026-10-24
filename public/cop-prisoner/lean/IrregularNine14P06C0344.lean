import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0101

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r20640 : Route 9 := (fun mask => (mask,id))

def c20640 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20640 : Upper (D 6) (R 6) [34,68,160,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17,320,8] 13 (by decide) (choices 1) [1,2,4] r20640 c20640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6092
  · exact u6093
  · exact u6094

def b20641 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 164 26 81 33 332 396 268), lower := (rows 35 70 164 26 81 33 64 128 256), losses := [] }

theorem u20641 : Upper (D 6) (R 6) [34,68,160,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20642 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 26 81 36 329 393 265), lower := (rows 35 70 164 26 81 36 64 128 256), losses := [] }

theorem u20642 : Upper (D 6) (R 6) [34,68,160,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20643 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 164 26 81 40 325 389 261), lower := (rows 35 70 164 26 81 40 64 128 256), losses := [] }

theorem u20643 : Upper (D 6) (R 6) [34,68,160,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20643 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20644 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 26 81 288 77 141 269), lower := (rows 35 70 164 26 81 288 64 128 256), losses := [] }

theorem u20644 : Upper (D 6) (R 6) [34,68,160,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20644 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20645 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 70 164 26 273 33 76 204 332), lower := (rows 35 70 164 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 68 164 508 305 33 64 128 256) }] }

theorem u20645 : Upper (D 6) (R 6) [34,68,160,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20646 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 26 273 36 73 201 329), lower := (rows 35 70 164 26 273 36 64 128 256), losses := [] }

theorem u20646 : Upper (D 6) (R 6) [34,68,160,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20647 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 164 26 273 40 69 197 325), lower := (rows 35 70 164 26 273 40 64 128 256), losses := [] }

theorem u20647 : Upper (D 6) (R 6) [34,68,160,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20647 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20648 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 26 273 96 77 141 269), lower := (rows 35 70 164 26 273 96 64 128 256), losses := [] }

theorem u20648 : Upper (D 6) (R 6) [34,68,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20649 : Route 9 := (fun mask => (mask,id))

def c20649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20649 : Upper (D 6) (R 6) [34,68,160,18,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,18,260,1] 13 (by decide) (choices 1) [1,8] r20649 c20649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6095
  · exact u6096

def b20650 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 164 26 276 40 65 193 321), lower := (rows 35 70 164 26 276 40 64 128 256), losses := [] }

theorem u20650 : Upper (D 6) (R 6) [34,68,160,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20650 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20651 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 26 276 96 73 137 265), lower := (rows 35 70 164 26 276 96 64 128 256), losses := [] }

theorem u20651 : Upper (D 6) (R 6) [34,68,160,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20652 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 70 164 26 280 33 69 197 325), lower := (rows 35 70 164 26 280 33 64 128 256), losses := [] }

theorem u20652 : Upper (D 6) (R 6) [34,68,160,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20653 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 26 280 36 65 193 321), lower := (rows 35 70 164 26 280 36 64 128 256), losses := [] }

theorem u20653 : Upper (D 6) (R 6) [34,68,160,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20654 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 26 280 96 69 133 261), lower := (rows 35 70 164 26 280 96 64 128 256), losses := [] }

theorem u20654 : Upper (D 6) (R 6) [34,68,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20655 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 164 26 336 33 77 141 269), lower := (rows 35 70 164 26 336 33 64 128 256), losses := [] }

theorem u20655 : Upper (D 6) (R 6) [34,68,160,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20656 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 26 336 36 73 137 265), lower := (rows 35 70 164 26 336 36 64 128 256), losses := [] }

theorem u20656 : Upper (D 6) (R 6) [34,68,160,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20657 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 164 26 336 40 69 133 261), lower := (rows 35 70 164 26 336 40 64 128 256), losses := [] }

theorem u20657 : Upper (D 6) (R 6) [34,68,160,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20657 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20658 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 322, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 70 164 28 81 33 330 394 266), lower := (rows 35 70 164 28 81 33 64 128 256), losses := [] }

theorem u20658 : Upper (D 6) (R 6) [34,68,160,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20659 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 28 81 34 329 393 265), lower := (rows 35 70 164 28 81 34 64 128 256), losses := [] }

theorem u20659 : Upper (D 6) (R 6) [34,68,160,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20660 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 28 81 40 323 387 259), lower := (rows 35 70 164 28 81 40 64 128 256), losses := [] }

theorem u20660 : Upper (D 6) (R 6) [34,68,160,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20660 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20661 : Route 9 := (fun mask => (mask,id))

def c20661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20661 : Upper (D 6) (R 6) [34,68,160,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,65,256] 13 (by decide) (choices 1) [1,2,8] r20661 c20661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6097
  · exact u6098
  · exact u6099

def b20662 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 164 28 273 33 74 202 330), lower := (rows 35 70 164 28 273 33 64 128 256), losses := [] }

theorem u20662 : Upper (D 6) (R 6) [34,68,160,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20663 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 28 273 34 73 201 329), lower := (rows 35 70 164 28 273 34 64 128 256), losses := [] }

theorem u20663 : Upper (D 6) (R 6) [34,68,160,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20664 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 28 273 40 67 195 323), lower := (rows 35 70 164 28 273 40 64 128 256), losses := [] }

theorem u20664 : Upper (D 6) (R 6) [34,68,160,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20664 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20665 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 28 273 96 75 139 267), lower := (rows 35 70 164 28 273 96 64 128 256), losses := [] }

theorem u20665 : Upper (D 6) (R 6) [34,68,160,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20666 : Route 9 := (fun mask => (mask,id))

def c20666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20666 : Upper (D 6) (R 6) [34,68,160,20,258,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,258,1] 13 (by decide) (choices 1) [1,8] r20666 c20666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6100
  · exact u6101

def b20667 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 28 274 40 65 193 321), lower := (rows 35 70 164 28 274 40 64 128 256), losses := [] }

theorem u20667 : Upper (D 6) (R 6) [34,68,160,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20667 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20668 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 28 274 96 73 137 265), lower := (rows 35 70 164 28 274 96 64 128 256), losses := [] }

theorem u20668 : Upper (D 6) (R 6) [34,68,160,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20669 : Route 9 := (fun mask => (mask,id))

def c20669 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20669 : Upper (D 6) (R 6) [34,68,160,20,264,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,264,1] 13 (by decide) (choices 1) [1,2] r20669 c20669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6102
  · exact u6103

def b20670 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 28 280 34 65 193 321), lower := (rows 35 70 164 28 280 34 64 128 256), losses := [] }

theorem u20670 : Upper (D 6) (R 6) [34,68,160,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20671 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 164 28 280 96 67 131 259), lower := (rows 35 70 164 28 280 96 64 128 256), losses := [] }

theorem u20671 : Upper (D 6) (R 6) [34,68,160,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20672 : Route 9 := (fun mask => (mask,id))

def c20672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20672 : Upper (D 6) (R 6) [34,68,160,20,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,20,320,1] 13 (by decide) (choices 1) [1,2,8] r20672 c20672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6104
  · exact u6105
  · exact u6106

def b20673 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 28 336 34 73 137 265), lower := (rows 35 70 164 28 336 34 64 128 256), losses := [] }

theorem u20673 : Upper (D 6) (R 6) [34,68,160,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20674 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 70 164 28 336 40 67 131 259), lower := (rows 35 70 164 28 336 40 64 128 256), losses := [] }

theorem u20674 : Upper (D 6) (R 6) [34,68,160,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20674 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20675 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 73 273 34 92 156 284), lower := (rows 35 70 164 73 273 34 64 128 256), losses := [] }

theorem u20675 : Upper (D 6) (R 6) [34,68,160,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20676 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 73 273 36 90 154 282), lower := (rows 35 70 164 73 273 36 64 128 256), losses := [] }

theorem u20676 : Upper (D 6) (R 6) [34,68,160,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20677 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 273 40 86 150 278), lower := (rows 35 70 164 73 273 40 64 128 256), losses := [] }

theorem u20677 : Upper (D 6) (R 6) [34,68,160,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20677 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20678 : Route 9 := (fun mask => (mask,id))

def c20678 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20678 : Upper (D 6) (R 6) [34,68,160,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,257,16] 13 (by decide) (choices 1) [2,4,8] r20678 c20678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6107
  · exact u6108
  · exact u6109

def b20679 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 164 73 274 33 92 156 284), lower := (rows 35 70 164 73 274 33 64 128 256), losses := [] }

theorem u20679 : Upper (D 6) (R 6) [34,68,160,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20680 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 73 274 36 89 153 281), lower := (rows 35 70 164 73 274 36 64 128 256), losses := [] }

theorem u20680 : Upper (D 6) (R 6) [34,68,160,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20681 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 274 40 85 149 277), lower := (rows 35 70 164 73 274 40 64 128 256), losses := [] }

theorem u20681 : Upper (D 6) (R 6) [34,68,160,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20681 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20682 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 73 274 48 77 141 269), lower := (rows 35 70 164 73 274 48 64 128 256), losses := [] }

theorem u20682 : Upper (D 6) (R 6) [34,68,160,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20682 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20683 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 164 73 276 33 90 154 282), lower := (rows 35 70 164 73 276 33 64 128 256), losses := [] }

theorem u20683 : Upper (D 6) (R 6) [34,68,160,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20684 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 73 276 34 89 153 281), lower := (rows 35 70 164 73 276 34 64 128 256), losses := [] }

theorem u20684 : Upper (D 6) (R 6) [34,68,160,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20685 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 276 40 83 147 275), lower := (rows 35 70 164 73 276 40 64 128 256), losses := [] }

theorem u20685 : Upper (D 6) (R 6) [34,68,160,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20685 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20686 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 164 73 276 48 75 139 267), lower := (rows 35 70 164 73 276 48 64 128 256), losses := [] }

theorem u20686 : Upper (D 6) (R 6) [34,68,160,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20686 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20687 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 164 73 280 33 86 150 278), lower := (rows 35 70 164 73 280 33 64 128 256), losses := [] }

theorem u20687 : Upper (D 6) (R 6) [34,68,160,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20688 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 73 280 34 85 149 277), lower := (rows 35 70 164 73 280 34 64 128 256), losses := [] }

theorem u20688 : Upper (D 6) (R 6) [34,68,160,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20689 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 73 280 36 83 147 275), lower := (rows 35 70 164 73 280 36 64 128 256), losses := [] }

theorem u20689 : Upper (D 6) (R 6) [34,68,160,65,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20690 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 73 280 48 71 135 263), lower := (rows 35 70 164 73 280 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 13 8 24 56 0 129 257), good := (rows 423 6 164 445 316 48 0 128 256) }] }

theorem u20690 : Upper (D 6) (R 6) [34,68,160,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20690 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20691 : Route 9 := (fun mask => (mask,id))

def c20691 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20691 : Upper (D 6) (R 6) [34,68,160,80,257,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257,1] 13 (by decide) (choices 1) [2,4,8] r20691 c20691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6110
  · exact u6111
  · exact u6112

def b20692 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 88 273 34 77 141 269), lower := (rows 35 70 164 88 273 34 64 128 256), losses := [] }

theorem u20692 : Upper (D 6) (R 6) [34,68,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20693 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 88 273 36 75 139 267), lower := (rows 35 70 164 88 273 36 64 128 256), losses := [] }

theorem u20693 : Upper (D 6) (R 6) [34,68,160,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20694 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 88 273 40 71 135 263), lower := (rows 35 70 164 88 273 40 64 128 256), losses := [] }

theorem u20694 : Upper (D 6) (R 6) [34,68,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20694 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20695 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 164 88 274 33 77 141 269), lower := (rows 35 70 164 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 136 264), good := (rows 35 39 164 445 307 33 0 128 256) }] }

theorem u20695 : Upper (D 6) (R 6) [34,68,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20696 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 70 164 88 274 36 73 137 265), lower := (rows 35 70 164 88 274 36 64 128 256), losses := [] }

theorem u20696 : Upper (D 6) (R 6) [34,68,160,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20697 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 164 88 274 40 69 133 261), lower := (rows 35 70 164 88 274 40 64 128 256), losses := [] }

theorem u20697 : Upper (D 6) (R 6) [34,68,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20697 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20698 : Route 9 := (fun mask => (mask,id))

def c20698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20698 : Upper (D 6) (R 6) [34,68,160,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,260,1] 13 (by decide) (choices 1) [1,2,8] r20698 c20698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6113
  · exact u6114
  · exact u6115

def b20699 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 164 88 276 34 73 137 265), lower := (rows 35 70 164 88 276 34 64 128 256), losses := [] }

theorem u20699 : Upper (D 6) (R 6) [34,68,160,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20699
end Delivery.IrregularNine14.P06
