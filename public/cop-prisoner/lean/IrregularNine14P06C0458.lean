import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0144
import IrregularNine14P06C0145

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27480 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 292 11 28 96 83 147 275), lower := (rows 97 134 292 11 28 96 64 128 256), losses := [] }

theorem u27480 : Upper (D 6) (R 6) [96,132,288,3,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27481 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 97 134 292 11 82 33 92 156 284), lower := (rows 97 134 292 11 82 33 64 128 256), losses := [] }

theorem u27481 : Upper (D 6) (R 6) [96,132,288,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27482 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 134 292 11 82 36 89 153 281), lower := (rows 97 134 292 11 82 36 64 128 256), losses := [] }

theorem u27482 : Upper (D 6) (R 6) [96,132,288,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27483 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 97 134 292 11 82 40 85 149 277), lower := (rows 97 134 292 11 82 40 64 128 256), losses := [] }

theorem u27483 : Upper (D 6) (R 6) [96,132,288,3,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27483 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27484 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 82 48 77 141 269), lower := (rows 97 134 292 11 82 48 64 128 256), losses := [] }

theorem u27484 : Upper (D 6) (R 6) [96,132,288,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27484 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27485 : Route 9 := (fun mask => (mask,id))

def c27485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27485 : Upper (D 6) (R 6) [96,132,288,3,68,1] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,68,1] 13 (by decide) (choices 1) [2,8,16] r27485 c27485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8687
  · exact u8688
  · exact u8689

def r27486 : Route 9 := (fun mask => (mask,id))

def c27486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27486 : Upper (D 6) (R 6) [96,132,288,3,68,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,68,2] 13 (by decide) (choices 1) [1,8,16] r27486 c27486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8690
  · exact u8691
  · exact u8692

def r27487 : Route 9 := (fun mask => (mask,id))

def c27487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27487 : Upper (D 6) (R 6) [96,132,288,3,68,8] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,68,8] 13 (by decide) (choices 1) [1,2,16] r27487 c27487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8693
  · exact u8694
  · exact u8695

def b27488 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 84 48 75 139 267), lower := (rows 97 134 292 11 84 48 64 128 256), losses := [] }

theorem u27488 : Upper (D 6) (R 6) [96,132,288,3,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27488 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27489 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2),(1,6)], upper := (rows 97 134 292 11 88 33 86 150 278), lower := (rows 97 134 292 11 88 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 20 8 16 41 0 144 272), good := (rows 33 134 292 43 446 33 0 128 256) }] }

theorem u27489 : Upper (D 6) (R 6) [96,132,288,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27490 : Route 9 := (fun mask => (mask,id))

def c27490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27490 : Upper (D 6) (R 6) [96,132,288,3,72,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,72,2] 13 (by decide) (choices 1) [1,4,16] r27490 c27490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8696
  · exact u8697
  · exact u8698

def b27491 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 134 292 11 88 36 83 147 275), lower := (rows 97 134 292 11 88 36 64 128 256), losses := [] }

theorem u27491 : Upper (D 6) (R 6) [96,132,288,3,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27492 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 11 88 48 71 135 263), lower := (rows 97 134 292 11 88 48 64 128 256), losses := [] }

theorem u27492 : Upper (D 6) (R 6) [96,132,288,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27492 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27493 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 134 292 13 82 33 90 154 282), lower := (rows 97 134 292 13 82 33 64 128 256), losses := [] }

theorem u27493 : Upper (D 6) (R 6) [96,132,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27494 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 97 134 292 13 82 34 89 153 281), lower := (rows 97 134 292 13 82 34 64 128 256), losses := [] }

theorem u27494 : Upper (D 6) (R 6) [96,132,288,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27495 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 97 134 292 13 82 40 83 147 275), lower := (rows 97 134 292 13 82 40 64 128 256), losses := [] }

theorem u27495 : Upper (D 6) (R 6) [96,132,288,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27495 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27496 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 13 82 48 75 139 267), lower := (rows 97 134 292 13 82 48 64 128 256), losses := [] }

theorem u27496 : Upper (D 6) (R 6) [96,132,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27496 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27497 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 97 134 292 13 88 33 82 146 274), lower := (rows 97 134 292 13 88 33 64 128 256), losses := [] }

theorem u27497 : Upper (D 6) (R 6) [96,132,288,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27498 : Route 9 := (fun mask => (mask,id))

def c27498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27498 : Upper (D 6) (R 6) [96,132,288,5,72,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,5,72,2] 13 (by decide) (choices 1) [1,2,16] r27498 c27498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8699
  · exact u8700
  · exact u8701

def b27499 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 13 88 48 67 131 259), lower := (rows 97 134 292 13 88 48 64 128 256), losses := [] }

theorem u27499 : Upper (D 6) (R 6) [96,132,288,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27499 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27500 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 134 292 25 26 33 70 198 326), lower := (rows 97 134 292 25 26 33 64 128 256), losses := [] }

theorem u27500 : Upper (D 6) (R 6) [96,132,288,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27501 : Route 9 := (fun mask => (mask,id))

def c27501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27501 : Upper (D 6) (R 6) [96,132,288,17,10,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,10,2] 13 (by decide) (choices 1) [1,4] r27501 c27501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8702
  · exact u8703

def b27502 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 134 292 25 26 36 67 195 323), lower := (rows 97 134 292 25 26 36 64 128 256), losses := [] }

theorem u27502 : Upper (D 6) (R 6) [96,132,288,17,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27503 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 292 25 26 96 71 135 263), lower := (rows 97 134 292 25 26 96 64 128 256), losses := [] }

theorem u27503 : Upper (D 6) (R 6) [96,132,288,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27504 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 1 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 97 134 292 25 28 33 66 194 322), lower := (rows 97 134 292 25 28 33 64 128 256), losses := [] }

theorem u27504 : Upper (D 6) (R 6) [96,132,288,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27505 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 97 134 292 25 28 34 67 195 323), lower := (rows 97 134 292 25 28 34 64 128 256), losses := [{ target := 2, region := (rows 39 2 0 24 16 34 98 162 290), good := (rows 481 483 481 25 25 483 64 128 256) },{ target := 5, region := (rows 1 18 4 8 16 0 72 136 264), good := (rows 65 134 260 475 478 2 64 128 256) }] }

theorem u27505 : Upper (D 6) (R 6) [96,132,288,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27506 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 134 292 25 28 96 67 131 259), lower := (rows 97 134 292 25 28 96 64 128 256), losses := [] }

theorem u27506 : Upper (D 6) (R 6) [96,132,288,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27507 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 292 25 82 33 78 142 270), lower := (rows 97 134 292 25 82 33 64 128 256), losses := [] }

theorem u27507 : Upper (D 6) (R 6) [96,132,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27508 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 97 134 292 25 82 34 77 141 269), lower := (rows 97 134 292 25 82 34 64 128 256), losses := [] }

theorem u27508 : Upper (D 6) (R 6) [96,132,288,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27509 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 134 292 25 82 36 75 139 267), lower := (rows 97 134 292 25 82 36 64 128 256), losses := [] }

theorem u27509 : Upper (D 6) (R 6) [96,132,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27510 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 134 292 25 82 40 71 135 263), lower := (rows 97 134 292 25 82 40 64 128 256), losses := [] }

theorem u27510 : Upper (D 6) (R 6) [96,132,288,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27510 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27511 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 97 134 292 25 84 33 74 138 266), lower := (rows 97 134 292 25 84 33 64 128 256), losses := [] }

theorem u27511 : Upper (D 6) (R 6) [96,132,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27512 : Route 9 := (fun mask => (mask,id))

def c27512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27512 : Upper (D 6) (R 6) [96,132,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,68,2] 13 (by decide) (choices 1) [1,2,8] r27512 c27512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8704
  · exact u8705
  · exact u8706

def b27513 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 97 134 292 25 84 40 67 131 259), lower := (rows 97 134 292 25 84 40 64 128 256), losses := [] }

theorem u27513 : Upper (D 6) (R 6) [96,132,288,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27513 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27514 : Route 9 := (fun mask => (mask,id))

def c27514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27514 : Upper (D 6) (R 6) [96,132,288,18,68,1] 13 := by
  apply FastRouting.sound _ _ [96,132,288,18,68,1] 13 (by decide) (choices 1) [1,2,8] r27514 c27514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8707
  · exact u8708
  · exact u8709

def r27515 : Route 9 := (fun mask => (mask,id))

def c27515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27515 : Upper (D 6) (R 6) [96,132,288,18,68,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,18,68,2] 13 (by decide) (choices 1) [1,8] r27515 c27515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8710
  · exact u8711

def b27516 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 26 84 40 67 131 259), lower := (rows 97 134 292 26 84 40 64 128 256), losses := [] }

theorem u27516 : Upper (D 6) (R 6) [96,132,288,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27516 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27517 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 134 292 26 88 33 71 135 263), lower := (rows 97 134 292 26 88 33 64 128 256), losses := [] }

theorem u27517 : Upper (D 6) (R 6) [96,132,288,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27518 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 5, region := 325, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 97 134 292 26 88 34 69 133 261), lower := (rows 97 134 292 26 88 34 64 128 256), losses := [] }

theorem u27518 : Upper (D 6) (R 6) [96,132,288,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27519 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 134 292 26 88 36 67 131 259), lower := (rows 97 134 292 26 88 36 64 128 256), losses := [] }

theorem u27519 : Upper (D 6) (R 6) [96,132,288,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27520 : Route 9 := (fun mask => (mask,id))

def c27520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27520 : Upper (D 6) (R 6) [96,132,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [96,132,288,20,66,1] 13 (by decide) (choices 1) [1,2,8] r27520 c27520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8712
  · exact u8713
  · exact u8714

def r27521 : Route 9 := (fun mask => (mask,id))

def c27521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27521 : Upper (D 6) (R 6) [96,132,288,20,66,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,20,66,2] 13 (by decide) (choices 1) [1,8] r27521 c27521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8715
  · exact u8716

def b27522 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 134 292 28 82 40 67 131 259), lower := (rows 97 134 292 28 82 40 64 128 256), losses := [] }

theorem u27522 : Upper (D 6) (R 6) [96,132,288,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27522 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27523 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 276 11 21 34 100 228 356), lower := (rows 97 138 276 11 21 34 64 128 256), losses := [] }

theorem u27523 : Upper (D 6) (R 6) [96,136,272,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27524 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 11 21 96 102 166 294), lower := (rows 97 138 276 11 21 96 64 128 256), losses := [] }

theorem u27524 : Upper (D 6) (R 6) [96,136,272,3,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27525 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 357, targets := 2 },{ cop := 6, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 97 138 276 11 22 33 100 228 356), lower := (rows 97 138 276 11 22 33 64 128 256), losses := [] }

theorem u27525 : Upper (D 6) (R 6) [96,136,272,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27526 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 97 138 276 11 22 36 97 225 353), lower := (rows 97 138 276 11 22 36 64 128 256), losses := [] }

theorem u27526 : Upper (D 6) (R 6) [96,136,272,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27527 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 11 22 96 101 165 293), lower := (rows 97 138 276 11 22 96 64 128 256), losses := [] }

theorem u27527 : Upper (D 6) (R 6) [96,136,272,3,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27528 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 97 138 276 11 50 33 68 196 324), lower := (rows 97 138 276 11 50 33 64 128 256), losses := [] }

theorem u27528 : Upper (D 6) (R 6) [96,136,272,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27529 : Route 9 := (fun mask => (mask,id))

def c27529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27529 : Upper (D 6) (R 6) [96,136,272,3,34,4] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,34,4] 13 (by decide) (choices 1) [1,4] r27529 c27529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8717
  · exact u8718

def b27530 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 11 50 96 69 133 261), lower := (rows 97 138 276 11 50 96 64 128 256), losses := [] }

theorem u27530 : Upper (D 6) (R 6) [96,136,272,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27531 : Route 9 := (fun mask => (mask,id))

def c27531 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27531 : Upper (D 6) (R 6) [96,136,272,3,36,1] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,36,1] 13 (by decide) (choices 1) [2,4] r27531 c27531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8719
  · exact u8720

def b27532 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 341, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 138 276 11 52 34 69 197 325), lower := (rows 97 138 276 11 52 34 64 128 256), losses := [] }

theorem u27532 : Upper (D 6) (R 6) [96,136,272,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27533 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 138 276 11 52 36 67 195 323), lower := (rows 97 138 276 11 52 36 64 128 256), losses := [] }

theorem u27533 : Upper (D 6) (R 6) [96,136,272,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27534 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 11 52 96 71 135 263), lower := (rows 97 138 276 11 52 96 64 128 256), losses := [] }

theorem u27534 : Upper (D 6) (R 6) [96,136,272,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27535 : Route 9 := (fun mask => (mask,id))

def c27535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27535 : Upper (D 6) (R 6) [96,136,272,5,3,2] 13 := by
  apply FastRouting.sound _ _ [96,136,272,5,3,2] 13 (by decide) (choices 1) [4,32] r27535 c27535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8721
  · exact u8722

def b27536 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 13 19 96 102 166 294), lower := (rows 97 138 276 13 19 96 64 128 256), losses := [] }

theorem u27536 : Upper (D 6) (R 6) [96,136,272,5,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27537 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 138 276 13 22 33 98 226 354), lower := (rows 97 138 276 13 22 33 64 128 256), losses := [] }

theorem u27537 : Upper (D 6) (R 6) [96,136,272,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27538 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 5, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 138 276 13 22 34 97 225 353), lower := (rows 97 138 276 13 22 34 64 128 256), losses := [] }

theorem u27538 : Upper (D 6) (R 6) [96,136,272,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27539 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 138 276 13 22 96 99 163 291), lower := (rows 97 138 276 13 22 96 64 128 256), losses := [] }

theorem u27539 : Upper (D 6) (R 6) [96,136,272,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27539
end Delivery.IrregularNine14.P06
