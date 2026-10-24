import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0125
import IrregularNine14P06C0126

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24480 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 324 44 21 33 82 210 338), lower := (rows 35 138 324 44 21 33 64 128 256), losses := [] }

theorem u24480 : Upper (D 6) (R 6) [34,136,320,36,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24481 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 44 21 34 81 209 337), lower := (rows 35 138 324 44 21 34 64 128 256), losses := [] }

theorem u24481 : Upper (D 6) (R 6) [34,136,320,36,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24482 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 324 44 21 48 67 195 323), lower := (rows 35 138 324 44 21 48 64 128 256), losses := [] }

theorem u24482 : Upper (D 6) (R 6) [34,136,320,36,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24482 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24483 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 147, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 138 324 44 21 96 83 147 275), lower := (rows 35 138 324 44 21 96 64 128 256), losses := [] }

theorem u24483 : Upper (D 6) (R 6) [34,136,320,36,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24484 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 324 44 81 33 86 150 278), lower := (rows 35 138 324 44 81 33 64 128 256), losses := [] }

theorem u24484 : Upper (D 6) (R 6) [34,136,320,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24485 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 44 81 34 85 149 277), lower := (rows 35 138 324 44 81 34 64 128 256), losses := [] }

theorem u24485 : Upper (D 6) (R 6) [34,136,320,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24486 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 324 44 81 36 83 147 275), lower := (rows 35 138 324 44 81 36 64 128 256), losses := [] }

theorem u24486 : Upper (D 6) (R 6) [34,136,320,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24487 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 324 44 81 48 71 135 263), lower := (rows 35 138 324 44 81 48 64 128 256), losses := [] }

theorem u24487 : Upper (D 6) (R 6) [34,136,320,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24487 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24488 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 324 44 82 33 85 149 277), lower := (rows 35 138 324 44 82 33 64 128 256), losses := [] }

theorem u24488 : Upper (D 6) (R 6) [34,136,320,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24489 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 324 44 82 36 81 145 273), lower := (rows 35 138 324 44 82 36 64 128 256), losses := [] }

theorem u24489 : Upper (D 6) (R 6) [34,136,320,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24490 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 324 44 82 48 69 133 261), lower := (rows 35 138 324 44 82 48 64 128 256), losses := [] }

theorem u24490 : Upper (D 6) (R 6) [34,136,320,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24490 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24491 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 324 56 21 33 70 198 326), lower := (rows 35 138 324 56 21 33 64 128 256), losses := [] }

theorem u24491 : Upper (D 6) (R 6) [34,136,320,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24492 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 56 21 34 69 197 325), lower := (rows 35 138 324 56 21 34 64 128 256), losses := [] }

theorem u24492 : Upper (D 6) (R 6) [34,136,320,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24493 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 324 56 21 36 67 195 323), lower := (rows 35 138 324 56 21 36 64 128 256), losses := [] }

theorem u24493 : Upper (D 6) (R 6) [34,136,320,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24494 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 324 56 21 96 71 135 263), lower := (rows 35 138 324 56 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 138 356 56 60 96 96 128 256) }] }

theorem u24494 : Upper (D 6) (R 6) [34,136,320,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24495 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 324 56 81 33 70 134 262), lower := (rows 35 138 324 56 81 33 64 128 256), losses := [] }

theorem u24495 : Upper (D 6) (R 6) [34,136,320,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24496 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 56 81 34 69 133 261), lower := (rows 35 138 324 56 81 34 64 128 256), losses := [] }

theorem u24496 : Upper (D 6) (R 6) [34,136,320,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24497 : Route 9 := (fun mask => (mask,id))

def c24497 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24497 : Upper (D 6) (R 6) [34,136,320,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,48,65,4] 13 (by decide) (choices 1) [1,2,4] r24497 c24497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7546
  · exact u7547
  · exact u7548

def b24498 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 73 21 34 116 180 308), lower := (rows 35 138 324 73 21 34 64 128 256), losses := [] }

theorem u24498 : Upper (D 6) (R 6) [34,136,320,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24499 : Route 9 := (fun mask => (mask,id))

def c24499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24499 : Upper (D 6) (R 6) [34,136,320,65,5,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65,5,4] 13 (by decide) (choices 1) [2,16,32] r24499 c24499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7549
  · exact u7550
  · exact u7551

def b24500 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 324 73 21 48 102 166 294), lower := (rows 35 138 324 73 21 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 29 8 16 48 65 129 257), good := (rows 486 142 324 462 500 52 64 128 256) }] }

theorem u24500 : Upper (D 6) (R 6) [34,136,320,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24500 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24501 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 73 22 33 116 180 308), lower := (rows 35 138 324 73 22 33 64 128 256), losses := [] }

theorem u24501 : Upper (D 6) (R 6) [34,136,320,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24502 : Route 9 := (fun mask => (mask,id))

def c24502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24502 : Upper (D 6) (R 6) [34,136,320,65,6,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65,6,4] 13 (by decide) (choices 1) [1,16,32] r24502 c24502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7552
  · exact u7553
  · exact u7554

def b24503 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 324 73 22 48 101 165 293), lower := (rows 35 138 324 73 22 48 64 128 256), losses := [] }

theorem u24503 : Upper (D 6) (R 6) [34,136,320,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24503 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24504 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 324 73 52 33 86 150 278), lower := (rows 35 138 324 73 52 33 64 128 256), losses := [] }

theorem u24504 : Upper (D 6) (R 6) [34,136,320,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24505 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 73 52 34 85 149 277), lower := (rows 35 138 324 73 52 34 64 128 256), losses := [] }

theorem u24505 : Upper (D 6) (R 6) [34,136,320,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24506 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 138 324 73 52 36 83 147 275), lower := (rows 35 138 324 73 52 36 64 128 256), losses := [] }

theorem u24506 : Upper (D 6) (R 6) [34,136,320,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24507 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 73 52 48 71 135 263), lower := (rows 35 138 324 73 52 48 64 128 256), losses := [] }

theorem u24507 : Upper (D 6) (R 6) [34,136,320,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24507 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24508 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 74 21 33 116 180 308), lower := (rows 35 138 324 74 21 33 64 128 256), losses := [] }

theorem u24508 : Upper (D 6) (R 6) [34,136,320,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24509 : Route 9 := (fun mask => (mask,id))

def c24509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24509 : Upper (D 6) (R 6) [34,136,320,66,5,4] 13 := by
  apply FastRouting.sound _ _ [34,136,320,66,5,4] 13 (by decide) (choices 1) [1,16,32] r24509 c24509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7555
  · exact u7556
  · exact u7557

def b24510 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 324 74 21 48 101 165 293), lower := (rows 35 138 324 74 21 48 64 128 256), losses := [] }

theorem u24510 : Upper (D 6) (R 6) [34,136,320,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24510 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24511 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 324 74 52 33 85 149 277), lower := (rows 35 138 324 74 52 33 64 128 256), losses := [] }

theorem u24511 : Upper (D 6) (R 6) [34,136,320,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24512 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 138 324 74 52 36 81 145 273), lower := (rows 35 138 324 74 52 36 64 128 256), losses := [] }

theorem u24512 : Upper (D 6) (R 6) [34,136,320,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24513 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 324 74 52 48 69 133 261), lower := (rows 35 138 324 74 52 48 64 128 256), losses := [] }

theorem u24513 : Upper (D 6) (R 6) [34,136,320,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24513 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24514 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 324 88 21 33 102 166 294), lower := (rows 35 138 324 88 21 33 64 128 256), losses := [] }

theorem u24514 : Upper (D 6) (R 6) [34,136,320,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24515 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 88 21 34 101 165 293), lower := (rows 35 138 324 88 21 34 64 128 256), losses := [] }

theorem u24515 : Upper (D 6) (R 6) [34,136,320,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24516 : PairBound 9 := { available := 35, camps := [], pairs := [(0,6),(1,2),(3,2)], upper := (rows 35 138 324 88 21 36 99 163 291), lower := (rows 35 138 324 88 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 65 129 257), good := (rows 483 138 320 90 475 32 64 128 256) },{ target := 6, region := (rows 9 10 4 8 16 52 0 137 265), good := (rows 419 395 292 443 437 36 0 128 256) }] }

theorem u24516 : Upper (D 6) (R 6) [34,136,320,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24517 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 138 324 88 52 33 71 135 263), lower := (rows 35 138 324 88 52 33 64 128 256), losses := [] }

theorem u24517 : Upper (D 6) (R 6) [34,136,320,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24518 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 88 52 34 69 133 261), lower := (rows 35 138 324 88 52 34 64 128 256), losses := [] }

theorem u24518 : Upper (D 6) (R 6) [34,136,320,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24519 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 138 324 88 52 36 67 131 259), lower := (rows 35 138 324 88 52 36 64 128 256), losses := [] }

theorem u24519 : Upper (D 6) (R 6) [34,136,320,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24520 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 324 104 21 33 86 150 278), lower := (rows 35 138 324 104 21 33 64 128 256), losses := [] }

theorem u24520 : Upper (D 6) (R 6) [34,136,320,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24521 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 324 104 21 34 85 149 277), lower := (rows 35 138 324 104 21 34 64 128 256), losses := [] }

theorem u24521 : Upper (D 6) (R 6) [34,136,320,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24522 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 324 104 21 36 83 147 275), lower := (rows 35 138 324 104 21 36 64 128 256), losses := [] }

theorem u24522 : Upper (D 6) (R 6) [34,136,320,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24523 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 324 104 21 48 71 135 263), lower := (rows 35 138 324 104 21 48 64 128 256), losses := [] }

theorem u24523 : Upper (D 6) (R 6) [34,136,320,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24523 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24524 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 25 84 33 326 390 262), lower := (rows 35 194 44 25 84 33 64 128 256), losses := [] }

theorem u24524 : Upper (D 6) (R 6) [34,192,40,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24525 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 25 84 34 325 389 261), lower := (rows 35 194 44 25 84 34 64 128 256), losses := [] }

theorem u24525 : Upper (D 6) (R 6) [34,192,40,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24526 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 25 84 36 323 387 259), lower := (rows 35 194 44 25 84 36 64 128 256), losses := [] }

theorem u24526 : Upper (D 6) (R 6) [34,192,40,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24527 : Route 9 := (fun mask => (mask,id))

def c24527 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24527 : Upper (D 6) (R 6) [34,192,40,17,68,256] 13 := by
  apply FastRouting.sound _ _ [34,192,40,17,68,256] 13 (by decide) (choices 1) [1,2,4] r24527 c24527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7558
  · exact u7559
  · exact u7560

def b24528 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 25 274 33 68 196 324), lower := (rows 35 194 44 25 274 33 64 128 256), losses := [] }

theorem u24528 : Upper (D 6) (R 6) [34,192,40,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24529 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 194 44 25 274 36 69 197 325), lower := (rows 35 194 44 25 274 36 64 128 256), losses := [] }

theorem u24529 : Upper (D 6) (R 6) [34,192,40,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24530 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 25 274 96 69 133 261), lower := (rows 35 194 44 25 274 96 64 128 256), losses := [] }

theorem u24530 : Upper (D 6) (R 6) [34,192,40,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24531 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 25 276 33 70 198 326), lower := (rows 35 194 44 25 276 33 64 128 256), losses := [] }

theorem u24531 : Upper (D 6) (R 6) [34,192,40,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24532 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 25 276 34 69 197 325), lower := (rows 35 194 44 25 276 34 64 128 256), losses := [] }

theorem u24532 : Upper (D 6) (R 6) [34,192,40,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24533 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 25 276 36 67 195 323), lower := (rows 35 194 44 25 276 36 64 128 256), losses := [] }

theorem u24533 : Upper (D 6) (R 6) [34,192,40,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24534 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 44 25 276 96 71 135 263), lower := (rows 35 194 44 25 276 96 64 128 256), losses := [] }

theorem u24534 : Upper (D 6) (R 6) [34,192,40,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24535 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 44 25 336 33 70 134 262), lower := (rows 35 194 44 25 336 33 64 128 256), losses := [] }

theorem u24535 : Upper (D 6) (R 6) [34,192,40,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24536 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 44 25 336 34 69 133 261), lower := (rows 35 194 44 25 336 34 64 128 256), losses := [] }

theorem u24536 : Upper (D 6) (R 6) [34,192,40,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24537 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 25 336 36 71 135 263), lower := (rows 35 194 44 25 336 36 64 128 256), losses := [] }

theorem u24537 : Upper (D 6) (R 6) [34,192,40,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24538 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 44 26 81 33 324 388 260), lower := (rows 35 194 44 26 81 33 64 128 256), losses := [] }

theorem u24538 : Upper (D 6) (R 6) [34,192,40,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24539 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 194 44 26 81 36 325 389 261), lower := (rows 35 194 44 26 81 36 64 128 256), losses := [] }

theorem u24539 : Upper (D 6) (R 6) [34,192,40,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24539
end Delivery.IrregularNine14.P06
