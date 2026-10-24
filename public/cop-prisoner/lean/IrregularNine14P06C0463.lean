import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0148
import IrregularNine14P06C0149

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27780 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 392 50 101 69 197 325), lower := (rows 7 11 52 392 50 32 64 128 256), losses := [] }

theorem u27780 : Upper (D 6) (R 6) [6,9,48,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27781 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 20, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 52 392 52 99 67 195 323), lower := (rows 7 11 52 392 52 32 64 128 256), losses := [] }

theorem u27781 : Upper (D 6) (R 6) [6,9,48,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27782 : Route 9 := (fun mask => (mask,id))

def c27782 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27782 : Upper (D 6) (R 6) [6,9,48,384,65] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384,65] 13 (by decide) (choices 1) [2,4,64] r27782 c27782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8891
  · exact u8892
  · exact u8893

def r27783 : Route 9 := (fun mask => (mask,id))

def c27783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27783 : Upper (D 6) (R 6) [6,9,48,384,66] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384,66] 13 (by decide) (choices 1) [1,4,64] r27783 c27783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8894
  · exact u8895
  · exact u8896

def r27784 : Route 9 := (fun mask => (mask,id))

def c27784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27784 : Upper (D 6) (R 6) [6,9,48,384,68] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384,68] 13 (by decide) (choices 1) [1,2,64] r27784 c27784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8897
  · exact u8898
  · exact u8899

def b27785 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 52 392 112 103 71 199 327), lower := (rows 7 11 52 392 112 32 64 128 256), losses := [] }

theorem u27785 : Upper (D 6) (R 6) [6,9,48,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27786 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 26 21 480 480 480 480), lower := (rows 7 11 100 26 21 32 64 128 256), losses := [] }

theorem u27786 : Upper (D 6) (R 6) [6,9,96,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27787 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 100 26 49 484 452 452 452), lower := (rows 7 11 100 26 49 32 64 128 256), losses := [] }

theorem u27787 : Upper (D 6) (R 6) [6,9,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27788 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 26 52 481 449 449 449), lower := (rows 7 11 100 26 52 32 64 128 256), losses := [] }

theorem u27788 : Upper (D 6) (R 6) [6,9,96,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27789 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 16, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 11 100 26 112 421 453 389 389), lower := (rows 7 11 100 26 112 32 64 128 256), losses := [] }

theorem u27789 : Upper (D 6) (R 6) [6,9,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27790 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 100 26 145 356 356 484 356), lower := (rows 7 11 100 26 145 32 64 128 256), losses := [] }

theorem u27790 : Upper (D 6) (R 6) [6,9,96,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27791 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 26 148 353 353 481 353), lower := (rows 7 11 100 26 148 32 64 128 256), losses := [] }

theorem u27791 : Upper (D 6) (R 6) [6,9,96,18,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27792 : Route 9 := (fun mask => (mask,id))

def c27792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27792 : Upper (D 6) (R 6) [6,9,96,18,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,18,160] 13 (by decide) (choices 1) [1,4,64,256] r27792 c27792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8900
  · exact u8901
  · exact u8902
  · exact u8903

def r27793 : Route 9 := (fun mask => (mask,id))

def c27793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27793 : Upper (D 6) (R 6) [6,9,96,18,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,18,384] 13 (by decide) (choices 1) [1,4,64] r27793 c27793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8904
  · exact u8905
  · exact u8906

def b27794 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 19 484 452 452 452), lower := (rows 7 11 100 56 19 32 64 128 256), losses := [] }

theorem u27794 : Upper (D 6) (R 6) [6,9,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27795 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 21 482 450 450 450), lower := (rows 7 11 100 56 21 32 64 128 256), losses := [] }

theorem u27795 : Upper (D 6) (R 6) [6,9,96,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27796 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 56 22 481 449 449 449), lower := (rows 7 11 100 56 22 32 64 128 256), losses := [] }

theorem u27796 : Upper (D 6) (R 6) [6,9,96,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27797 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 100 56 81 422 454 390 390), lower := (rows 7 11 100 56 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 100 60 508 32 64 128 256) }] }

theorem u27797 : Upper (D 6) (R 6) [6,9,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27798 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 100 56 82 421 453 389 389), lower := (rows 7 11 100 56 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 35 67 131 259), good := (rows 485 493 100 60 508 32 64 128 256) }] }

theorem u27798 : Upper (D 6) (R 6) [6,9,96,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27799 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 100 56 84 419 451 387 387), lower := (rows 7 11 100 56 84 32 64 128 256), losses := [] }

theorem u27799 : Upper (D 6) (R 6) [6,9,96,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27800 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 356, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 11 100 56 145 358 326 454 326), lower := (rows 7 11 100 56 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 100 60 508 32 64 128 256) }] }

theorem u27800 : Upper (D 6) (R 6) [6,9,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27801 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 11 100 56 146 357 325 453 325), lower := (rows 7 11 100 56 146 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 35 67 131 259), good := (rows 485 493 100 60 508 32 64 128 256) }] }

theorem u27801 : Upper (D 6) (R 6) [6,9,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27802 : Route 9 := (fun mask => (mask,id))

def c27802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27802 : Upper (D 6) (R 6) [6,9,96,48,132] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,132] 13 (by decide) (choices 1) [1,2,64,256] r27802 c27802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8907
  · exact u8908
  · exact u8909
  · exact u8910

def r27803 : Route 9 := (fun mask => (mask,id))

def c27803 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27803 : Upper (D 6) (R 6) [6,9,96,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,192] 13 (by decide) (choices 1) [1,2,4,256] r27803 c27803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8911
  · exact u8912
  · exact u8913
  · exact u8914

def r27804 : Route 9 := (fun mask => (mask,id))

def c27804 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27804 : Upper (D 6) (R 6) [6,9,96,48,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,384] 13 (by decide) (choices 1) [1,2,4,64] r27804 c27804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8915
  · exact u8916
  · exact u8917
  · exact u8918

def b27805 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 100 138 21 368 368 496 368), lower := (rows 7 11 100 138 21 32 64 128 256), losses := [] }

theorem u27805 : Upper (D 6) (R 6) [6,9,96,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27806 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 4, region := 324, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 138 49 372 340 468 340), lower := (rows 7 11 100 138 49 32 64 128 256), losses := [] }

theorem u27806 : Upper (D 6) (R 6) [6,9,96,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27807 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 100 138 52 369 337 465 337), lower := (rows 7 11 100 138 52 32 64 128 256), losses := [] }

theorem u27807 : Upper (D 6) (R 6) [6,9,96,130,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27808 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 16, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 11 100 138 112 309 341 405 277), lower := (rows 7 11 100 138 112 32 64 128 256), losses := [] }

theorem u27808 : Upper (D 6) (R 6) [6,9,96,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27809 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 11 100 138 273 116 116 244 372), lower := (rows 7 11 100 138 273 32 64 128 256), losses := [] }

theorem u27809 : Upper (D 6) (R 6) [6,9,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27810 : Route 9 := (fun mask => (mask,id))

def c27810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27810 : Upper (D 6) (R 6) [6,9,96,130,260] 13 := by
  apply FastRouting.sound _ _ [6,9,96,130,260] 13 (by decide) (choices 1) [1,16,64] r27810 c27810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8919
  · exact u8920
  · exact u8921

def r27811 : Route 9 := (fun mask => (mask,id))

def c27811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27811 : Upper (D 6) (R 6) [6,9,96,130,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,130,288] 13 (by decide) (choices 1) [1,4,16,64] r27811 c27811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8922
  · exact u8923
  · exact u8924
  · exact u8925

def b27812 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 152 19 356 356 484 356), lower := (rows 7 11 100 152 19 32 64 128 256), losses := [] }

theorem u27812 : Upper (D 6) (R 6) [6,9,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27813 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 100 152 21 354 354 482 354), lower := (rows 7 11 100 152 21 32 64 128 256), losses := [] }

theorem u27813 : Upper (D 6) (R 6) [6,9,96,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27814 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 100 152 22 353 353 481 353), lower := (rows 7 11 100 152 22 32 64 128 256), losses := [] }

theorem u27814 : Upper (D 6) (R 6) [6,9,96,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27815 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 7 11 100 152 49 358 326 454 326), lower := (rows 7 11 100 152 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 35 67 131 259), good := (rows 486 494 100 156 508 32 64 128 256) },{ target := 5, region := (rows 1 18 4 24 16 0 65 129 257), good := (rows 455 459 68 154 475 0 64 128 256) }] }

theorem u27815 : Upper (D 6) (R 6) [6,9,96,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27816 : Route 9 := (fun mask => (mask,id))

def c27816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u27816 : Upper (D 6) (R 6) [6,9,96,144,34] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,34] 13 (by decide) (choices 1) [1,4,64,256] r27816 c27816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8926
  · exact u8927
  · exact u8928
  · exact u8929

def b27817 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 100 152 52 355 323 451 323), lower := (rows 7 11 100 152 52 32 64 128 256), losses := [] }

theorem u27817 : Upper (D 6) (R 6) [6,9,96,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27818 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 11 100 152 112 295 327 391 263), lower := (rows 7 11 100 152 112 32 64 128 256), losses := [] }

theorem u27818 : Upper (D 6) (R 6) [6,9,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27819 : Route 9 := (fun mask => (mask,id))

def c27819 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27819 : Upper (D 6) (R 6) [6,9,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257] 13 (by decide) (choices 1) [2,4,64] r27819 c27819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8930
  · exact u8931
  · exact u8932

def r27820 : Route 9 := (fun mask => (mask,id))

def c27820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27820 : Upper (D 6) (R 6) [6,9,96,144,258] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,258] 13 (by decide) (choices 1) [1,4,64] r27820 c27820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8933
  · exact u8934
  · exact u8935

def r27821 : Route 9 := (fun mask => (mask,id))

def c27821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27821 : Upper (D 6) (R 6) [6,9,96,144,260] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,260] 13 (by decide) (choices 1) [1,2,64] r27821 c27821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8936
  · exact u8937
  · exact u8938

def r27822 : Route 9 := (fun mask => (mask,id))

def c27822 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27822 : Upper (D 6) (R 6) [6,9,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288] 13 (by decide) (choices 1) [1,2,4,64] r27822 c27822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8939
  · exact u8940
  · exact u8941
  · exact u8942

def b27823 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 168 19 372 340 468 340), lower := (rows 7 11 100 168 19 32 64 128 256), losses := [] }

theorem u27823 : Upper (D 6) (R 6) [6,9,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27824 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 490, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 100 168 21 370 338 466 338), lower := (rows 7 11 100 168 21 32 64 128 256), losses := [] }

theorem u27824 : Upper (D 6) (R 6) [6,9,96,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27825 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 11 100 168 22 369 337 465 337), lower := (rows 7 11 100 168 22 32 64 128 256), losses := [] }

theorem u27825 : Upper (D 6) (R 6) [6,9,96,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27826 : Route 9 := (fun mask => (mask,id))

def c27826 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27826 : Upper (D 6) (R 6) [6,9,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,65] 13 (by decide) (choices 1) [2,4,16,256] r27826 c27826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8943
  · exact u8944
  · exact u8945
  · exact u8946

def r27827 : Route 9 := (fun mask => (mask,id))

def c27827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u27827 : Upper (D 6) (R 6) [6,9,96,160,66] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,66] 13 (by decide) (choices 1) [1,4,16,256] r27827 c27827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8947
  · exact u8948
  · exact u8949
  · exact u8950

def b27828 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 11 100 168 84 307 339 403 275), lower := (rows 7 11 100 168 84 32 64 128 256), losses := [] }

theorem u27828 : Upper (D 6) (R 6) [6,9,96,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27828 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27829 : Route 9 := (fun mask => (mask,id))

def c27829 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27829 : Upper (D 6) (R 6) [6,9,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257] 13 (by decide) (choices 1) [2,4,16,64] r27829 c27829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8951
  · exact u8952
  · exact u8953
  · exact u8954

def r27830 : Route 9 := (fun mask => (mask,id))

def c27830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27830 : Upper (D 6) (R 6) [6,9,96,160,258] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,258] 13 (by decide) (choices 1) [1,4,16,64] r27830 c27830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8955
  · exact u8956
  · exact u8957
  · exact u8958

def r27831 : Route 9 := (fun mask => (mask,id))

def c27831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27831 : Upper (D 6) (R 6) [6,9,96,160,260] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,260] 13 (by decide) (choices 1) [1,2,16,64] r27831 c27831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8959
  · exact u8960
  · exact u8961
  · exact u8962

def r27832 : Route 9 := (fun mask => (mask,id))

def c27832 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27832 : Upper (D 6) (R 6) [6,9,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320] 13 (by decide) (choices 1) [1,2,4,16] r27832 c27832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8963
  · exact u8964
  · exact u8965
  · exact u8966

def b27833 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 392 19 116 116 244 372), lower := (rows 7 11 100 392 19 32 64 128 256), losses := [] }

theorem u27833 : Upper (D 6) (R 6) [6,9,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27834 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 11 100 392 21 114 114 242 370), lower := (rows 7 11 100 392 21 32 64 128 256), losses := [] }

theorem u27834 : Upper (D 6) (R 6) [6,9,96,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27835 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 11 100 392 22 113 113 241 369), lower := (rows 7 11 100 392 22 32 64 128 256), losses := [] }

theorem u27835 : Upper (D 6) (R 6) [6,9,96,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27836 : Route 9 := (fun mask => (mask,id))

def c27836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27836 : Upper (D 6) (R 6) [6,9,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,33] 13 (by decide) (choices 1) [2,4,16,64] r27836 c27836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8967
  · exact u8968
  · exact u8969
  · exact u8970

def r27837 : Route 9 := (fun mask => (mask,id))

def c27837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27837 : Upper (D 6) (R 6) [6,9,96,384,34] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,34] 13 (by decide) (choices 1) [1,4,16,64] r27837 c27837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8971
  · exact u8972
  · exact u8973
  · exact u8974

def b27838 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 11 100 392 52 115 83 211 339), lower := (rows 7 11 100 392 52 32 64 128 256), losses := [] }

theorem u27838 : Upper (D 6) (R 6) [6,9,96,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27839 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 11 100 392 112 55 87 151 279), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u27839 : Upper (D 6) (R 6) [6,9,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27839
end Delivery.IrregularNine14.P06
