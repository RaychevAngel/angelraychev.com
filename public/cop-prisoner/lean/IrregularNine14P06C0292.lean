import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0080
import IrregularNine14P06C0081

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17520 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 84 44 274 96 69 133 261), lower := (rows 11 162 84 44 274 96 64 128 256), losses := [] }

theorem u17520 : Upper (D 6) (R 6) [10,160,80,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17521 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 73 52 33 326 390 262), lower := (rows 11 162 84 73 52 33 64 128 256), losses := [] }

theorem u17521 : Upper (D 6) (R 6) [10,160,80,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17522 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 73 52 34 325 389 261), lower := (rows 11 162 84 73 52 34 64 128 256), losses := [] }

theorem u17522 : Upper (D 6) (R 6) [10,160,80,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17523 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 73 52 36 323 387 259), lower := (rows 11 162 84 73 52 36 64 128 256), losses := [] }

theorem u17523 : Upper (D 6) (R 6) [10,160,80,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17524 : Route 9 := (fun mask => (mask,id))

def c17524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17524 : Upper (D 6) (R 6) [10,160,80,65,36,256] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,36,256] 13 (by decide) (choices 1) [1,2,4] r17524 c17524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4823
  · exact u4824
  · exact u4825

def b17525 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 73 274 33 100 164 292), lower := (rows 11 162 84 73 274 33 64 128 256), losses := [] }

theorem u17525 : Upper (D 6) (R 6) [10,160,80,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17526 : Route 9 := (fun mask => (mask,id))

def c17526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17526 : Upper (D 6) (R 6) [10,160,80,65,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,258,4] 13 (by decide) (choices 1) [1,4,32] r17526 c17526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4826
  · exact u4827
  · exact u4828

def b17527 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 73 276 33 102 166 294), lower := (rows 11 162 84 73 276 33 64 128 256), losses := [] }

theorem u17527 : Upper (D 6) (R 6) [10,160,80,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17528 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 73 276 34 101 165 293), lower := (rows 11 162 84 73 276 34 64 128 256), losses := [] }

theorem u17528 : Upper (D 6) (R 6) [10,160,80,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17529 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 73 276 36 99 163 291), lower := (rows 11 162 84 73 276 36 64 128 256), losses := [] }

theorem u17529 : Upper (D 6) (R 6) [10,160,80,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17530 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 73 304 33 70 134 262), lower := (rows 11 162 84 73 304 33 64 128 256), losses := [] }

theorem u17530 : Upper (D 6) (R 6) [10,160,80,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17531 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 73 304 34 69 133 261), lower := (rows 11 162 84 73 304 34 64 128 256), losses := [] }

theorem u17531 : Upper (D 6) (R 6) [10,160,80,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17532 : Route 9 := (fun mask => (mask,id))

def c17532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17532 : Upper (D 6) (R 6) [10,160,80,65,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,65,288,4] 13 (by decide) (choices 1) [1,2,4] r17532 c17532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4829
  · exact u4830
  · exact u4831

def b17533 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 84 104 22 33 325 389 261), lower := (rows 11 162 84 104 22 33 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 12 16 53 64 128 256), good := (rows 43 162 121 104 59 33 64 128 256) }] }

theorem u17533 : Upper (D 6) (R 6) [10,160,80,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17534 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 104 22 36 321 385 257), lower := (rows 11 162 84 104 22 36 64 128 256), losses := [] }

theorem u17534 : Upper (D 6) (R 6) [10,160,80,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17535 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 84 104 22 288 69 133 261), lower := (rows 11 162 84 104 22 288 64 128 256), losses := [] }

theorem u17535 : Upper (D 6) (R 6) [10,160,80,96,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17535 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17536 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 84 104 273 33 70 134 262), lower := (rows 11 162 84 104 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 49 64 128 256), good := (rows 41 160 124 104 305 33 64 128 256) }] }

theorem u17536 : Upper (D 6) (R 6) [10,160,80,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17537 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 104 273 34 69 133 261), lower := (rows 11 162 84 104 273 34 64 128 256), losses := [] }

theorem u17537 : Upper (D 6) (R 6) [10,160,80,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17538 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 84 104 273 36 71 135 263), lower := (rows 11 162 84 104 273 36 64 128 256), losses := [] }

theorem u17538 : Upper (D 6) (R 6) [10,160,80,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17539 : Route 9 := (fun mask => (mask,id))

def c17539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17539 : Upper (D 6) (R 6) [10,160,80,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,258,1] 13 (by decide) (choices 1) [1,4] r17539 c17539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4832
  · exact u4833

def b17540 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 84 104 274 36 69 133 261), lower := (rows 11 162 84 104 274 36 64 128 256), losses := [] }

theorem u17540 : Upper (D 6) (R 6) [10,160,80,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17541 : Route 9 := (fun mask => (mask,id))

def c17541 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17541 : Upper (D 6) (R 6) [10,160,80,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,96,260,1] 13 (by decide) (choices 1) [1,2,4] r17541 c17541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4834
  · exact u4835
  · exact u4836

def b17542 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 104 276 34 69 133 261), lower := (rows 11 162 84 104 276 34 64 128 256), losses := [] }

theorem u17542 : Upper (D 6) (R 6) [10,160,80,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17543 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 104 276 36 67 131 259), lower := (rows 11 162 84 104 276 36 64 128 256), losses := [] }

theorem u17543 : Upper (D 6) (R 6) [10,160,80,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17544 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 265 21 34 100 228 356), lower := (rows 11 162 84 265 21 34 64 128 256), losses := [] }

theorem u17544 : Upper (D 6) (R 6) [10,160,80,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17545 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 265 21 36 98 226 354), lower := (rows 11 162 84 265 21 36 64 128 256), losses := [] }

theorem u17545 : Upper (D 6) (R 6) [10,160,80,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17546 : Route 9 := (fun mask => (mask,id))

def c17546 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17546 : Upper (D 6) (R 6) [10,160,80,257,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,5,64] 13 (by decide) (choices 1) [2,4,32] r17546 c17546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4837
  · exact u4838
  · exact u4839

def b17547 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 265 22 33 100 228 356), lower := (rows 11 162 84 265 22 33 64 128 256), losses := [] }

theorem u17547 : Upper (D 6) (R 6) [10,160,80,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17548 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 265 22 36 97 225 353), lower := (rows 11 162 84 265 22 36 64 128 256), losses := [] }

theorem u17548 : Upper (D 6) (R 6) [10,160,80,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17549 : Route 9 := (fun mask => (mask,id))

def c17549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17549 : Upper (D 6) (R 6) [10,160,80,257,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,6,64] 13 (by decide) (choices 1) [1,4,32] r17549 c17549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4840
  · exact u4841
  · exact u4842

def b17550 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 84 265 49 34 68 196 324), lower := (rows 11 162 84 265 49 34 64 128 256), losses := [] }

theorem u17550 : Upper (D 6) (R 6) [10,160,80,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17551 : Route 9 := (fun mask => (mask,id))

def c17551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17551 : Upper (D 6) (R 6) [10,160,80,257,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,33,4] 13 (by decide) (choices 1) [2,4] r17551 c17551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4843
  · exact u4844

def r17552 : Route 9 := (fun mask => (mask,id))

def c17552 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17552 : Upper (D 6) (R 6) [10,160,80,257,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,257,33,64] 13 (by decide) (choices 1) [2,4] r17552 c17552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4845
  · exact u4846

def b17553 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 265 52 33 70 198 326), lower := (rows 11 162 84 265 52 33 64 128 256), losses := [] }

theorem u17553 : Upper (D 6) (R 6) [10,160,80,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17554 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 265 52 34 69 197 325), lower := (rows 11 162 84 265 52 34 64 128 256), losses := [] }

theorem u17554 : Upper (D 6) (R 6) [10,160,80,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17555 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 265 52 36 67 195 323), lower := (rows 11 162 84 265 52 36 64 128 256), losses := [] }

theorem u17555 : Upper (D 6) (R 6) [10,160,80,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17556 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 265 52 96 71 135 263), lower := (rows 11 162 84 265 52 96 64 128 256), losses := [] }

theorem u17556 : Upper (D 6) (R 6) [10,160,80,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17557 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 5, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 84 268 21 33 98 226 354), lower := (rows 11 162 84 268 21 33 64 128 256), losses := [] }

theorem u17557 : Upper (D 6) (R 6) [10,160,80,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17558 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 268 21 34 97 225 353), lower := (rows 11 162 84 268 21 34 64 128 256), losses := [] }

theorem u17558 : Upper (D 6) (R 6) [10,160,80,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17559 : Route 9 := (fun mask => (mask,id))

def c17559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17559 : Upper (D 6) (R 6) [10,160,80,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,5,64] 13 (by decide) (choices 1) [1,2,32] r17559 c17559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4847
  · exact u4848
  · exact u4849

def r17560 : Route 9 := (fun mask => (mask,id))

def c17560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17560 : Upper (D 6) (R 6) [10,160,80,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,6,1] 13 (by decide) (choices 1) [1,32] r17560 c17560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4850
  · exact u4851

def r17561 : Route 9 := (fun mask => (mask,id))

def c17561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17561 : Upper (D 6) (R 6) [10,160,80,260,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,6,64] 13 (by decide) (choices 1) [1,32] r17561 c17561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4852
  · exact u4853

def b17562 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 84 268 49 33 70 198 326), lower := (rows 11 162 84 268 49 33 64 128 256), losses := [] }

theorem u17562 : Upper (D 6) (R 6) [10,160,80,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17563 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 84 268 49 34 69 197 325), lower := (rows 11 162 84 268 49 34 64 128 256), losses := [] }

theorem u17563 : Upper (D 6) (R 6) [10,160,80,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17564 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(2,5),(4,1)], upper := (rows 11 162 84 268 49 36 67 195 323), lower := (rows 11 162 84 268 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 64 128 256), good := (rows 57 160 116 300 49 36 64 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 459 130 92 268 477 4 64 128 256) }] }

theorem u17564 : Upper (D 6) (R 6) [10,160,80,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17565 : Route 9 := (fun mask => (mask,id))

def c17565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17565 : Upper (D 6) (R 6) [10,160,80,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,33,64] 13 (by decide) (choices 1) [1,2,4] r17565 c17565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4854
  · exact u4855
  · exact u4856

def r17566 : Route 9 := (fun mask => (mask,id))

def c17566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17566 : Upper (D 6) (R 6) [10,160,80,260,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260,36,1] 13 (by decide) (choices 1) [1,2] r17566 c17566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4857
  · exact u4858

def b17567 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 268 52 34 65 193 321), lower := (rows 11 162 84 268 52 34 64 128 256), losses := [] }

theorem u17567 : Upper (D 6) (R 6) [10,160,80,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17568 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 268 52 96 67 131 259), lower := (rows 11 162 84 268 52 96 64 128 256), losses := [] }

theorem u17568 : Upper (D 6) (R 6) [10,160,80,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17569 : Route 9 := (fun mask => (mask,id))

def c17569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17569 : Upper (D 6) (R 6) [10,160,80,288,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,5,1] 13 (by decide) (choices 1) [2,4] r17569 c17569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4859
  · exact u4860

def b17570 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 296 21 34 69 197 325), lower := (rows 11 162 84 296 21 34 64 128 256), losses := [] }

theorem u17570 : Upper (D 6) (R 6) [10,160,80,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17571 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 296 21 36 67 195 323), lower := (rows 11 162 84 296 21 36 64 128 256), losses := [] }

theorem u17571 : Upper (D 6) (R 6) [10,160,80,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17572 : Route 9 := (fun mask => (mask,id))

def c17572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17572 : Upper (D 6) (R 6) [10,160,80,288,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,5,64] 13 (by decide) (choices 1) [1,2,4] r17572 c17572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4861
  · exact u4862
  · exact u4863

def r17573 : Route 9 := (fun mask => (mask,id))

def c17573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17573 : Upper (D 6) (R 6) [10,160,80,288,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,6,1] 13 (by decide) (choices 1) [1,4] r17573 c17573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4864
  · exact u4865

def b17574 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 296 22 36 65 193 321), lower := (rows 11 162 84 296 22 36 64 128 256), losses := [] }

theorem u17574 : Upper (D 6) (R 6) [10,160,80,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17575 : Route 9 := (fun mask => (mask,id))

def c17575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17575 : Upper (D 6) (R 6) [10,160,80,288,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,6,64] 13 (by decide) (choices 1) [1,4] r17575 c17575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4866
  · exact u4867

def r17576 : Route 9 := (fun mask => (mask,id))

def c17576 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17576 : Upper (D 6) (R 6) [10,160,80,320,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,5,1] 13 (by decide) (choices 1) [2,4,32] r17576 c17576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4868
  · exact u4869
  · exact u4870

def b17577 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 328 21 34 101 165 293), lower := (rows 11 162 84 328 21 34 64 128 256), losses := [] }

theorem u17577 : Upper (D 6) (R 6) [10,160,80,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17578 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 328 21 36 99 163 291), lower := (rows 11 162 84 328 21 36 64 128 256), losses := [] }

theorem u17578 : Upper (D 6) (R 6) [10,160,80,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17579 : Route 9 := (fun mask => (mask,id))

def c17579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17579 : Upper (D 6) (R 6) [10,160,80,320,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,6,1] 13 (by decide) (choices 1) [1,4,32] r17579 c17579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4871
  · exact u4872
  · exact u4873

#print axioms u17579
end Delivery.IrregularNine14.P06
