import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0380
import IrregularNine14P06C0381
import IrregularNine14P06C0382

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37500 : Route 9 := (fun mask => (mask,id))

def c37500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37500 : Upper (D 6) (R 6) [34,129,320,18,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,65] 13 (by decide) (choices 1) [4,8] r37500 c37500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22807
  · exact u22808

def b37501 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 26 84 45 109 173 301), lower := (rows 35 131 324 26 84 32 64 128 256), losses := [] }

theorem u37501 : Upper (D 6) (R 6) [34,129,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37502 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 131 324 26 88 37 101 165 293), lower := (rows 35 131 324 26 88 32 64 128 256), losses := [] }

theorem u37502 : Upper (D 6) (R 6) [34,129,320,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37503 : Route 9 := (fun mask => (mask,id))

def c37503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37503 : Upper (D 6) (R 6) [34,129,320,18,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,96] 13 (by decide) (choices 1) [1,4,8] r37503 c37503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22809
  · exact u22810
  · exact u22811

def b37504 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 324 28 28 99 99 227 355), lower := (rows 35 131 324 28 28 32 64 128 256), losses := [] }

theorem u37504 : Upper (D 6) (R 6) [34,129,320,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37505 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 324 28 49 110 78 206 334), lower := (rows 35 131 324 28 49 32 64 128 256), losses := [] }

theorem u37505 : Upper (D 6) (R 6) [34,129,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37506 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 324 28 50 109 77 205 333), lower := (rows 35 131 324 28 50 32 64 128 256), losses := [] }

theorem u37506 : Upper (D 6) (R 6) [34,129,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37507 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 324 28 52 107 75 203 331), lower := (rows 35 131 324 28 52 32 64 128 256), losses := [] }

theorem u37507 : Upper (D 6) (R 6) [34,129,320,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37508 : Route 9 := (fun mask => (mask,id))

def c37508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37508 : Upper (D 6) (R 6) [34,129,320,20,40] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,40] 13 (by decide) (choices 1) [1,2,4,64] r37508 c37508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22812
  · exact u22813
  · exact u22814
  · exact u22815

def r37509 : Route 9 := (fun mask => (mask,id))

def c37509 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37509 : Upper (D 6) (R 6) [34,129,320,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,65] 13 (by decide) (choices 1) [2,4,8] r37509 c37509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22816
  · exact u22817
  · exact u22818

def r37510 : Route 9 := (fun mask => (mask,id))

def c37510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37510 : Upper (D 6) (R 6) [34,129,320,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,66] 13 (by decide) (choices 1) [1,4,8] r37510 c37510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22819
  · exact u22820
  · exact u22821

def b37511 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 324 28 84 43 107 171 299), lower := (rows 35 131 324 28 84 32 64 128 256), losses := [] }

theorem u37511 : Upper (D 6) (R 6) [34,129,320,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37512 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 324 28 88 39 103 167 295), lower := (rows 35 131 324 28 88 32 64 128 256), losses := [] }

theorem u37512 : Upper (D 6) (R 6) [34,129,320,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37513 : Route 9 := (fun mask => (mask,id))

def c37513 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37513 : Upper (D 6) (R 6) [34,129,320,20,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20,96] 13 (by decide) (choices 1) [1,2,4,8] r37513 c37513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22822
  · exact u22823
  · exact u22824
  · exact u22825

def b37514 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 324 41 82 60 92 156 284), lower := (rows 35 131 324 41 82 32 64 128 256), losses := [] }

theorem u37514 : Upper (D 6) (R 6) [34,129,320,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37515 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 324 41 88 54 86 150 278), lower := (rows 35 131 324 41 88 32 64 128 256), losses := [] }

theorem u37515 : Upper (D 6) (R 6) [34,129,320,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37516 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 324 42 81 60 92 156 284), lower := (rows 35 131 324 42 81 32 64 128 256), losses := [] }

theorem u37516 : Upper (D 6) (R 6) [34,129,320,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37517 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 324 42 88 53 85 149 277), lower := (rows 35 131 324 42 88 32 64 128 256), losses := [] }

theorem u37517 : Upper (D 6) (R 6) [34,129,320,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37518 : Route 9 := (fun mask => (mask,id))

def c37518 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37518 : Upper (D 6) (R 6) [34,129,320,36,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,36,65] 13 (by decide) (choices 1) [2,4,8,16] r37518 c37518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22826
  · exact u22827
  · exact u22828
  · exact u22829

def r37519 : Route 9 := (fun mask => (mask,id))

def c37519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37519 : Upper (D 6) (R 6) [34,129,320,36,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,36,66] 13 (by decide) (choices 1) [1,4,8,16] r37519 c37519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22830
  · exact u22831
  · exact u22832
  · exact u22833

def b37520 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 44 84 59 91 155 283), lower := (rows 35 131 324 44 84 32 64 128 256), losses := [] }

theorem u37520 : Upper (D 6) (R 6) [34,129,320,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37521 : Route 9 := (fun mask => (mask,id))

def c37521 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37521 : Upper (D 6) (R 6) [34,129,320,36,72] 13 := by
  apply FastRouting.sound _ _ [34,129,320,36,72] 13 (by decide) (choices 1) [1,2,4,16] r37521 c37521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22834
  · exact u22835
  · exact u22836
  · exact u22837

def r37522 : Route 9 := (fun mask => (mask,id))

def c37522 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37522 : Upper (D 6) (R 6) [34,129,320,48,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,48,65] 13 (by decide) (choices 1) [2,4,8] r37522 c37522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22838
  · exact u22839
  · exact u22840

def r37523 : Route 9 := (fun mask => (mask,id))

def c37523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37523 : Upper (D 6) (R 6) [34,129,320,48,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,48,66] 13 (by decide) (choices 1) [1,4,8] r37523 c37523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22841
  · exact u22842
  · exact u22843

def b37524 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 56 84 47 79 143 271), lower := (rows 35 131 324 56 84 32 64 128 256), losses := [] }

theorem u37524 : Upper (D 6) (R 6) [34,129,320,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37525 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 131 324 56 88 39 71 135 263), lower := (rows 35 131 324 56 88 32 64 128 256), losses := [] }

theorem u37525 : Upper (D 6) (R 6) [34,129,320,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37526 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 25 19 356 324 452 324), lower := (rows 35 134 44 25 19 32 64 128 256), losses := [] }

theorem u37526 : Upper (D 6) (R 6) [34,132,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37527 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 134 44 25 21 354 322 450 322), lower := (rows 35 134 44 25 21 32 64 128 256), losses := [] }

theorem u37527 : Upper (D 6) (R 6) [34,132,40,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37528 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 44 25 22 353 321 449 321), lower := (rows 35 134 44 25 22 32 64 128 256), losses := [] }

theorem u37528 : Upper (D 6) (R 6) [34,132,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37529 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 44 25 81 358 326 454 326), lower := (rows 35 134 44 25 81 32 64 128 256), losses := [] }

theorem u37529 : Upper (D 6) (R 6) [34,132,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37530 : Route 9 := (fun mask => (mask,id))

def c37530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37530 : Upper (D 6) (R 6) [34,132,40,17,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,66] 13 (by decide) (choices 1) [1,4,64,256] r37530 c37530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22844
  · exact u22845
  · exact u22846
  · exact u22847

def r37531 : Route 9 := (fun mask => (mask,id))

def c37531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37531 : Upper (D 6) (R 6) [34,132,40,17,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,68] 13 (by decide) (choices 1) [1,2,64,256] r37531 c37531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22848
  · exact u22849
  · exact u22850
  · exact u22851

def b37532 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 134 44 25 273 102 70 198 326), lower := (rows 35 134 44 25 273 32 64 128 256), losses := [] }

theorem u37532 : Upper (D 6) (R 6) [34,132,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37533 : Route 9 := (fun mask => (mask,id))

def c37533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37533 : Upper (D 6) (R 6) [34,132,40,17,258] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,258] 13 (by decide) (choices 1) [1,4,64] r37533 c37533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22852
  · exact u22853
  · exact u22854

def r37534 : Route 9 := (fun mask => (mask,id))

def c37534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37534 : Upper (D 6) (R 6) [34,132,40,17,260] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,260] 13 (by decide) (choices 1) [1,2,64] r37534 c37534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22855
  · exact u22856
  · exact u22857

def r37535 : Route 9 := (fun mask => (mask,id))

def c37535 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37535 : Upper (D 6) (R 6) [34,132,40,17,320] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17,320] 13 (by decide) (choices 1) [1,2,4,64] r37535 c37535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22858
  · exact u22859
  · exact u22860
  · exact u22861

def b37536 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 44 26 21 353 321 449 321), lower := (rows 35 134 44 26 21 32 64 128 256), losses := [] }

theorem u37536 : Upper (D 6) (R 6) [34,132,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37537 : Route 9 := (fun mask => (mask,id))

def c37537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37537 : Upper (D 6) (R 6) [34,132,40,18,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,65] 13 (by decide) (choices 1) [1,4,64,256] r37537 c37537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22862
  · exact u22863
  · exact u22864
  · exact u22865

def r37538 : Route 9 := (fun mask => (mask,id))

def c37538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37538 : Upper (D 6) (R 6) [34,132,40,18,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,68] 13 (by decide) (choices 1) [1,64,256] r37538 c37538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22866
  · exact u22867
  · exact u22868

def r37539 : Route 9 := (fun mask => (mask,id))

def c37539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37539 : Upper (D 6) (R 6) [34,132,40,18,257] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,257] 13 (by decide) (choices 1) [1,4,64] r37539 c37539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22869
  · exact u22870
  · exact u22871

def r37540 : Route 9 := (fun mask => (mask,id))

def c37540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37540 : Upper (D 6) (R 6) [34,132,40,18,260] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,260] 13 (by decide) (choices 1) [1,64] r37540 c37540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22872
  · exact u22873

def r37541 : Route 9 := (fun mask => (mask,id))

def c37541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37541 : Upper (D 6) (R 6) [34,132,40,18,320] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,320] 13 (by decide) (choices 1) [1,4,64] r37541 c37541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22874
  · exact u22875
  · exact u22876

def b37542 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 44 73 19 372 340 468 340), lower := (rows 35 134 44 73 19 32 64 128 256), losses := [] }

theorem u37542 : Upper (D 6) (R 6) [34,132,40,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37543 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 35 134 44 73 21 370 338 466 338), lower := (rows 35 134 44 73 21 32 64 128 256), losses := [] }

theorem u37543 : Upper (D 6) (R 6) [34,132,40,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37544 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 44 73 22 369 337 465 337), lower := (rows 35 134 44 73 22 32 64 128 256), losses := [] }

theorem u37544 : Upper (D 6) (R 6) [34,132,40,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37545 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 134 44 73 81 310 342 406 278), lower := (rows 35 134 44 73 81 32 64 128 256), losses := [] }

theorem u37545 : Upper (D 6) (R 6) [34,132,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37546 : Route 9 := (fun mask => (mask,id))

def c37546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37546 : Upper (D 6) (R 6) [34,132,40,65,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,66] 13 (by decide) (choices 1) [1,4,16,256] r37546 c37546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22877
  · exact u22878
  · exact u22879
  · exact u22880

def r37547 : Route 9 := (fun mask => (mask,id))

def c37547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37547 : Upper (D 6) (R 6) [34,132,40,65,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,68] 13 (by decide) (choices 1) [1,2,16,256] r37547 c37547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22881
  · exact u22882
  · exact u22883
  · exact u22884

def r37548 : Route 9 := (fun mask => (mask,id))

def c37548 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37548 : Upper (D 6) (R 6) [34,132,40,65,257] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,257] 13 (by decide) (choices 1) [2,4,16,64] r37548 c37548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22885
  · exact u22886
  · exact u22887
  · exact u22888

def r37549 : Route 9 := (fun mask => (mask,id))

def c37549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37549 : Upper (D 6) (R 6) [34,132,40,65,258] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,258] 13 (by decide) (choices 1) [1,4,16,64] r37549 c37549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22889
  · exact u22890
  · exact u22891
  · exact u22892

def r37550 : Route 9 := (fun mask => (mask,id))

def c37550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37550 : Upper (D 6) (R 6) [34,132,40,65,260] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,260] 13 (by decide) (choices 1) [1,2,16,64] r37550 c37550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22893
  · exact u22894
  · exact u22895
  · exact u22896

def r37551 : Route 9 := (fun mask => (mask,id))

def c37551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37551 : Upper (D 6) (R 6) [34,132,40,65,320] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,320] 13 (by decide) (choices 1) [1,2,4,16] r37551 c37551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22897
  · exact u22898
  · exact u22899
  · exact u22900

def r37552 : Route 9 := (fun mask => (mask,id))

def c37552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37552 : Upper (D 6) (R 6) [34,132,40,66,5] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,5] 13 (by decide) (choices 1) [1,16,64,256] r37552 c37552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22901
  · exact u22902
  · exact u22903
  · exact u22904

def r37553 : Route 9 := (fun mask => (mask,id))

def c37553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37553 : Upper (D 6) (R 6) [34,132,40,66,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,65] 13 (by decide) (choices 1) [1,4,16,256] r37553 c37553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22905
  · exact u22906
  · exact u22907
  · exact u22908

def r37554 : Route 9 := (fun mask => (mask,id))

def c37554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37554 : Upper (D 6) (R 6) [34,132,40,66,68] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,68] 13 (by decide) (choices 1) [1,16,256] r37554 c37554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22909
  · exact u22910
  · exact u22911

def r37555 : Route 9 := (fun mask => (mask,id))

def c37555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37555 : Upper (D 6) (R 6) [34,132,40,66,257] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,257] 13 (by decide) (choices 1) [1,4,16,64] r37555 c37555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22912
  · exact u22913
  · exact u22914
  · exact u22915

def r37556 : Route 9 := (fun mask => (mask,id))

def c37556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37556 : Upper (D 6) (R 6) [34,132,40,66,260] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,260] 13 (by decide) (choices 1) [1,16,64] r37556 c37556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22916
  · exact u22917
  · exact u22918

def r37557 : Route 9 := (fun mask => (mask,id))

def c37557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37557 : Upper (D 6) (R 6) [34,132,40,66,320] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,320] 13 (by decide) (choices 1) [1,4,16] r37557 c37557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22919
  · exact u22920
  · exact u22921

def b37558 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 44 88 19 357 325 453 325), lower := (rows 35 134 44 88 19 32 64 128 256), losses := [] }

theorem u37558 : Upper (D 6) (R 6) [34,132,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37559 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(1,5),(3,5)], upper := (rows 35 134 44 88 21 355 323 451 323), lower := (rows 35 134 44 88 21 32 64 128 256), losses := [] }

theorem u37559 : Upper (D 6) (R 6) [34,132,40,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37559
end Delivery.IrregularNine14.P06
