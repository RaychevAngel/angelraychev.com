import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0041

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12660 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 268 81 36 98 226 354), lower := (rows 11 35 148 268 81 36 64 128 256), losses := [] }

theorem u12660 : Upper (D 6) (R 6) [10,33,144,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12661 : Route 9 := (fun mask => (mask,id))

def c12661 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12661 : Upper (D 6) (R 6) [10,33,144,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,65,64] 13 (by decide) (choices 1) [2,4,32] r12661 c12661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2493
  · exact u2494
  · exact u2495

def b12662 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 268 82 33 100 228 356), lower := (rows 11 35 148 268 82 33 64 128 256), losses := [] }

theorem u12662 : Upper (D 6) (R 6) [10,33,144,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12663 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 268 82 36 97 225 353), lower := (rows 11 35 148 268 82 36 64 128 256), losses := [] }

theorem u12663 : Upper (D 6) (R 6) [10,33,144,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12664 : Route 9 := (fun mask => (mask,id))

def c12664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12664 : Upper (D 6) (R 6) [10,33,144,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,66,64] 13 (by decide) (choices 1) [1,4,32] r12664 c12664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2496
  · exact u2497
  · exact u2498

def b12665 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 268 84 33 98 226 354), lower := (rows 11 35 148 268 84 33 64 128 256), losses := [] }

theorem u12665 : Upper (D 6) (R 6) [10,33,144,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12666 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 268 84 34 97 225 353), lower := (rows 11 35 148 268 84 34 64 128 256), losses := [] }

theorem u12666 : Upper (D 6) (R 6) [10,33,144,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12667 : Route 9 := (fun mask => (mask,id))

def c12667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12667 : Upper (D 6) (R 6) [10,33,144,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,68,64] 13 (by decide) (choices 1) [1,2,32] r12667 c12667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2499
  · exact u2500
  · exact u2501

def b12668 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 268 112 33 70 198 326), lower := (rows 11 35 148 268 112 33 64 128 256), losses := [] }

theorem u12668 : Upper (D 6) (R 6) [10,33,144,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12669 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 268 112 34 69 197 325), lower := (rows 11 35 148 268 112 34 64 128 256), losses := [] }

theorem u12669 : Upper (D 6) (R 6) [10,33,144,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12670 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 268 112 36 67 195 323), lower := (rows 11 35 148 268 112 36 64 128 256), losses := [] }

theorem u12670 : Upper (D 6) (R 6) [10,33,144,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12671 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 148 268 112 96 71 135 263), lower := (rows 11 35 148 268 112 96 64 128 256), losses := [] }

theorem u12671 : Upper (D 6) (R 6) [10,33,144,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12672 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 21 34 100 228 356), lower := (rows 11 35 148 328 21 34 64 128 256), losses := [] }

theorem u12672 : Upper (D 6) (R 6) [10,33,144,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12673 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 328 21 36 98 226 354), lower := (rows 11 35 148 328 21 36 64 128 256), losses := [] }

theorem u12673 : Upper (D 6) (R 6) [10,33,144,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12674 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 328 21 96 102 166 294), lower := (rows 11 35 148 328 21 96 64 128 256), losses := [] }

theorem u12674 : Upper (D 6) (R 6) [10,33,144,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12675 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 22 33 100 228 356), lower := (rows 11 35 148 328 22 33 64 128 256), losses := [] }

theorem u12675 : Upper (D 6) (R 6) [10,33,144,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12676 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 328 22 36 97 225 353), lower := (rows 11 35 148 328 22 36 64 128 256), losses := [] }

theorem u12676 : Upper (D 6) (R 6) [10,33,144,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12677 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 328 22 96 101 165 293), lower := (rows 11 35 148 328 22 96 64 128 256), losses := [] }

theorem u12677 : Upper (D 6) (R 6) [10,33,144,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12678 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 52 33 70 198 326), lower := (rows 11 35 148 328 52 33 64 128 256), losses := [] }

theorem u12678 : Upper (D 6) (R 6) [10,33,144,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12679 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 52 34 69 197 325), lower := (rows 11 35 148 328 52 34 64 128 256), losses := [] }

theorem u12679 : Upper (D 6) (R 6) [10,33,144,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12680 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 148 328 52 36 67 195 323), lower := (rows 11 35 148 328 52 36 64 128 256), losses := [] }

theorem u12680 : Upper (D 6) (R 6) [10,33,144,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12681 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 328 52 96 71 135 263), lower := (rows 11 35 148 328 52 96 64 128 256), losses := [] }

theorem u12681 : Upper (D 6) (R 6) [10,33,144,320,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12682 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 328 81 34 100 164 292), lower := (rows 11 35 148 328 81 34 64 128 256), losses := [] }

theorem u12682 : Upper (D 6) (R 6) [10,33,144,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12683 : Route 9 := (fun mask => (mask,id))

def c12683 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12683 : Upper (D 6) (R 6) [10,33,144,320,65,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,65,4] 13 (by decide) (choices 1) [2,4,32] r12683 c12683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2502
  · exact u2503
  · exact u2504

def b12684 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 328 82 33 100 164 292), lower := (rows 11 35 148 328 82 33 64 128 256), losses := [] }

theorem u12684 : Upper (D 6) (R 6) [10,33,144,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12685 : Route 9 := (fun mask => (mask,id))

def c12685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12685 : Upper (D 6) (R 6) [10,33,144,320,66,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,66,4] 13 (by decide) (choices 1) [1,4,32] r12685 c12685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2505
  · exact u2506
  · exact u2507

def b12686 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 84 33 102 166 294), lower := (rows 11 35 148 328 84 33 64 128 256), losses := [] }

theorem u12686 : Upper (D 6) (R 6) [10,33,144,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12687 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 328 84 34 101 165 293), lower := (rows 11 35 148 328 84 34 64 128 256), losses := [] }

theorem u12687 : Upper (D 6) (R 6) [10,33,144,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12688 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 328 84 36 99 163 291), lower := (rows 11 35 148 328 84 36 64 128 256), losses := [] }

theorem u12688 : Upper (D 6) (R 6) [10,33,144,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12689 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 328 112 33 70 134 262), lower := (rows 11 35 148 328 112 33 64 128 256), losses := [] }

theorem u12689 : Upper (D 6) (R 6) [10,33,144,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12690 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 328 112 34 69 133 261), lower := (rows 11 35 148 328 112 34 64 128 256), losses := [] }

theorem u12690 : Upper (D 6) (R 6) [10,33,144,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12691 : Route 9 := (fun mask => (mask,id))

def c12691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12691 : Upper (D 6) (R 6) [10,33,144,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,320,96,4] 13 (by decide) (choices 1) [1,2,4] r12691 c12691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2508
  · exact u2509
  · exact u2510

def b12692 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 25 84 34 324 452 324), lower := (rows 11 35 164 25 84 34 64 128 256), losses := [] }

theorem u12692 : Upper (D 6) (R 6) [10,33,160,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12693 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 25 84 36 322 450 322), lower := (rows 11 35 164 25 84 36 64 128 256), losses := [] }

theorem u12693 : Upper (D 6) (R 6) [10,33,160,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12694 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 164 25 84 96 326 390 262), lower := (rows 11 35 164 25 84 96 64 128 256), losses := [] }

theorem u12694 : Upper (D 6) (R 6) [10,33,160,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12695 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 164 25 84 288 70 198 326), lower := (rows 11 35 164 25 84 288 64 128 256), losses := [] }

theorem u12695 : Upper (D 6) (R 6) [10,33,160,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12695 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12696 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 25 276 34 68 196 324), lower := (rows 11 35 164 25 276 34 64 128 256), losses := [] }

theorem u12696 : Upper (D 6) (R 6) [10,33,160,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12697 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 164 25 276 36 66 194 322), lower := (rows 11 35 164 25 276 36 64 128 256), losses := [] }

theorem u12697 : Upper (D 6) (R 6) [10,33,160,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12698 : Route 9 := (fun mask => (mask,id))

def c12698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12698 : Upper (D 6) (R 6) [10,33,160,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,17,260,64] 13 (by decide) (choices 1) [2,4] r12698 c12698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2511
  · exact u2512

def b12699 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 25 336 34 68 196 324), lower := (rows 11 35 164 25 336 34 64 128 256), losses := [] }

theorem u12699 : Upper (D 6) (R 6) [10,33,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12700 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 25 336 36 70 198 326), lower := (rows 11 35 164 25 336 36 64 128 256), losses := [] }

theorem u12700 : Upper (D 6) (R 6) [10,33,160,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12701 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 164 25 336 96 70 134 262), lower := (rows 11 35 164 25 336 96 64 128 256), losses := [] }

theorem u12701 : Upper (D 6) (R 6) [10,33,160,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12702 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 81 34 324 452 324), lower := (rows 11 35 164 28 81 34 64 128 256), losses := [] }

theorem u12702 : Upper (D 6) (R 6) [10,33,160,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12703 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 28 81 36 322 450 322), lower := (rows 11 35 164 28 81 36 64 128 256), losses := [] }

theorem u12703 : Upper (D 6) (R 6) [10,33,160,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12704 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 1, region := 388, targets := 64 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 35 164 28 81 96 326 390 262), lower := (rows 11 35 164 28 81 96 64 128 256), losses := [] }

theorem u12704 : Upper (D 6) (R 6) [10,33,160,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12705 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 164 28 81 288 70 198 326), lower := (rows 11 35 164 28 81 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 164 60 508 288 64 128 288) }] }

theorem u12705 : Upper (D 6) (R 6) [10,33,160,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12705 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12706 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 82 33 324 452 324), lower := (rows 11 35 164 28 82 33 64 128 256), losses := [] }

theorem u12706 : Upper (D 6) (R 6) [10,33,160,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12707 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 28 82 36 321 449 321), lower := (rows 11 35 164 28 82 36 64 128 256), losses := [] }

theorem u12707 : Upper (D 6) (R 6) [10,33,160,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12708 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 35 164 28 82 96 325 389 261), lower := (rows 11 35 164 28 82 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 115 67 131 259), good := (rows 493 485 164 60 508 96 96 128 256) }] }

theorem u12708 : Upper (D 6) (R 6) [10,33,160,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12709 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 164 28 82 288 69 197 325), lower := (rows 11 35 164 28 82 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 493 485 164 60 508 288 64 128 288) }] }

theorem u12709 : Upper (D 6) (R 6) [10,33,160,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12709 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12710 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 273 34 68 196 324), lower := (rows 11 35 164 28 273 34 64 128 256), losses := [] }

theorem u12710 : Upper (D 6) (R 6) [10,33,160,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12711 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 28 273 36 66 194 322), lower := (rows 11 35 164 28 273 36 64 128 256), losses := [] }

theorem u12711 : Upper (D 6) (R 6) [10,33,160,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12712 : Route 9 := (fun mask => (mask,id))

def c12712 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12712 : Upper (D 6) (R 6) [10,33,160,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,257,64] 13 (by decide) (choices 1) [2,4] r12712 c12712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2513
  · exact u2514

def b12713 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 274 33 68 196 324), lower := (rows 11 35 164 28 274 33 64 128 256), losses := [] }

theorem u12713 : Upper (D 6) (R 6) [10,33,160,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12714 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 28 274 36 65 193 321), lower := (rows 11 35 164 28 274 36 64 128 256), losses := [] }

theorem u12714 : Upper (D 6) (R 6) [10,33,160,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12715 : Route 9 := (fun mask => (mask,id))

def c12715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12715 : Upper (D 6) (R 6) [10,33,160,20,258,64] 13 := by
  apply FastRouting.sound _ _ [10,33,160,20,258,64] 13 (by decide) (choices 1) [1,4] r12715 c12715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2515
  · exact u2516

def b12716 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 336 33 70 198 326), lower := (rows 11 35 164 28 336 33 64 128 256), losses := [] }

theorem u12716 : Upper (D 6) (R 6) [10,33,160,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12717 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 28 336 34 69 197 325), lower := (rows 11 35 164 28 336 34 64 128 256), losses := [] }

theorem u12717 : Upper (D 6) (R 6) [10,33,160,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12718 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 28 336 36 67 195 323), lower := (rows 11 35 164 28 336 36 64 128 256), losses := [] }

theorem u12718 : Upper (D 6) (R 6) [10,33,160,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12719 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 132, targets := 64 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 11 35 164 28 336 96 71 135 263), lower := (rows 11 35 164 28 336 96 64 128 256), losses := [{ target := 2, region := (rows 9 10 0 8 16 112 64 128 256), good := (rows 11 35 160 59 368 96 96 128 256) }] }

theorem u12719 : Upper (D 6) (R 6) [10,33,160,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12719
end Delivery.IrregularNine14.P06
