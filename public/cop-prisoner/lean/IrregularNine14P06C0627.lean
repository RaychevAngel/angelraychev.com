import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0383
import IrregularNine14P06C0384
import IrregularNine14P06C0385

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37620 : Route 9 := (fun mask => (mask,id))

def c37620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37620 : Upper (D 6) (R 6) [34,132,72,18,257] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,257] 13 (by decide) (choices 1) [1,4,64] r37620 c37620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23020
  · exact u23021
  · exact u23022

def r37621 : Route 9 := (fun mask => (mask,id))

def c37621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37621 : Upper (D 6) (R 6) [34,132,72,18,260] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,260] 13 (by decide) (choices 1) [1,64] r37621 c37621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23023
  · exact u23024

def r37622 : Route 9 := (fun mask => (mask,id))

def c37622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37622 : Upper (D 6) (R 6) [34,132,72,18,288] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,288] 13 (by decide) (choices 1) [1,4,64] r37622 c37622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23025
  · exact u23026
  · exact u23027

def r37623 : Route 9 := (fun mask => (mask,id))

def c37623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37623 : Upper (D 6) (R 6) [34,132,72,18,320] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,320] 13 (by decide) (choices 1) [1,4] r37623 c37623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23028
  · exact u23029

def b37624 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 76 28 19 353 353 481 353), lower := (rows 35 134 76 28 19 32 64 128 256), losses := [] }

theorem u37624 : Upper (D 6) (R 6) [34,132,72,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37625 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 76 28 49 355 323 451 323), lower := (rows 35 134 76 28 49 32 64 128 256), losses := [] }

theorem u37625 : Upper (D 6) (R 6) [34,132,72,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37626 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 76 28 50 353 321 449 321), lower := (rows 35 134 76 28 50 32 64 128 256), losses := [] }

theorem u37626 : Upper (D 6) (R 6) [34,132,72,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37627 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 28 81 291 355 419 291), lower := (rows 35 134 76 28 81 32 64 128 256), losses := [] }

theorem u37627 : Upper (D 6) (R 6) [34,132,72,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37628 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 28 82 289 353 417 289), lower := (rows 35 134 76 28 82 32 64 128 256), losses := [] }

theorem u37628 : Upper (D 6) (R 6) [34,132,72,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37629 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 28 112 291 323 387 259), lower := (rows 35 134 76 28 112 32 64 128 256), losses := [] }

theorem u37629 : Upper (D 6) (R 6) [34,132,72,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37630 : Route 9 := (fun mask => (mask,id))

def c37630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37630 : Upper (D 6) (R 6) [34,132,72,20,257] 13 := by
  apply FastRouting.sound _ _ [34,132,72,20,257] 13 (by decide) (choices 1) [1,2,64] r37630 c37630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23030
  · exact u23031
  · exact u23032

def r37631 : Route 9 := (fun mask => (mask,id))

def c37631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37631 : Upper (D 6) (R 6) [34,132,72,20,258] 13 := by
  apply FastRouting.sound _ _ [34,132,72,20,258] 13 (by decide) (choices 1) [1,64] r37631 c37631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23033
  · exact u23034

def r37632 : Route 9 := (fun mask => (mask,id))

def c37632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37632 : Upper (D 6) (R 6) [34,132,72,20,288] 13 := by
  apply FastRouting.sound _ _ [34,132,72,20,288] 13 (by decide) (choices 1) [1,2,64] r37632 c37632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23035
  · exact u23036
  · exact u23037

def b37633 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 28 336 35 99 163 291), lower := (rows 35 134 76 28 336 32 64 128 256), losses := [] }

theorem u37633 : Upper (D 6) (R 6) [34,132,72,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37634 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 134 76 56 19 357 325 453 325), lower := (rows 35 134 76 56 19 32 64 128 256), losses := [] }

theorem u37634 : Upper (D 6) (R 6) [34,132,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37635 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 35 134 76 56 21 355 323 451 323), lower := (rows 35 134 76 56 21 32 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 35 67 131 259), good := (rows 483 483 72 56 505 32 64 128 256) }] }

theorem u37635 : Upper (D 6) (R 6) [34,132,72,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37636 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 56 22 353 321 449 321), lower := (rows 35 134 76 56 22 32 64 128 256), losses := [] }

theorem u37636 : Upper (D 6) (R 6) [34,132,72,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37637 : Route 9 := (fun mask => (mask,id))

def c37637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37637 : Upper (D 6) (R 6) [34,132,72,48,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,65] 13 (by decide) (choices 1) [1,2,4,256] r37637 c37637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23038
  · exact u23039
  · exact u23040
  · exact u23041

def b37638 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 56 82 293 325 389 261), lower := (rows 35 134 76 56 82 32 64 128 256), losses := [{ target := 6, region := (rows 23 6 4 24 16 38 0 134 262), good := (rows 419 423 431 57 443 32 0 128 256) }] }

theorem u37638 : Upper (D 6) (R 6) [34,132,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37639 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 56 84 291 323 387 259), lower := (rows 35 134 76 56 84 32 64 128 256), losses := [] }

theorem u37639 : Upper (D 6) (R 6) [34,132,72,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37640 : Route 9 := (fun mask => (mask,id))

def c37640 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37640 : Upper (D 6) (R 6) [34,132,72,48,257] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,257] 13 (by decide) (choices 1) [1,2,4,64] r37640 c37640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23042
  · exact u23043
  · exact u23044
  · exact u23045

def r37641 : Route 9 := (fun mask => (mask,id))

def c37641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37641 : Upper (D 6) (R 6) [34,132,72,48,258] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,258] 13 (by decide) (choices 1) [1,4,64] r37641 c37641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23046
  · exact u23047
  · exact u23048

def r37642 : Route 9 := (fun mask => (mask,id))

def c37642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37642 : Upper (D 6) (R 6) [34,132,72,48,260] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,260] 13 (by decide) (choices 1) [1,2,64] r37642 c37642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23049
  · exact u23050
  · exact u23051

def r37643 : Route 9 := (fun mask => (mask,id))

def c37643 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37643 : Upper (D 6) (R 6) [34,132,72,48,320] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,320] 13 (by decide) (choices 1) [1,2,4] r37643 c37643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23052
  · exact u23053
  · exact u23054

def b37644 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 76 265 19 116 116 244 372), lower := (rows 35 134 76 265 19 32 64 128 256), losses := [] }

theorem u37644 : Upper (D 6) (R 6) [34,132,72,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37645 : Route 9 := (fun mask => (mask,id))

def c37645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37645 : Upper (D 6) (R 6) [34,132,72,257,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,5] 13 (by decide) (choices 1) [2,16,64] r37645 c37645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23055
  · exact u23056
  · exact u23057

def b37646 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 265 22 113 113 241 369), lower := (rows 35 134 76 265 22 32 64 128 256), losses := [] }

theorem u37646 : Upper (D 6) (R 6) [34,132,72,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37647 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 76 265 49 118 86 214 342), lower := (rows 35 134 76 265 49 32 64 128 256), losses := [] }

theorem u37647 : Upper (D 6) (R 6) [34,132,72,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37648 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 265 50 117 85 213 341), lower := (rows 35 134 76 265 50 32 64 128 256), losses := [] }

theorem u37648 : Upper (D 6) (R 6) [34,132,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37649 : Route 9 := (fun mask => (mask,id))

def c37649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37649 : Upper (D 6) (R 6) [34,132,72,257,36] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,36] 13 (by decide) (choices 1) [1,2,16,64] r37649 c37649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23058
  · exact u23059
  · exact u23060
  · exact u23061

def r37650 : Route 9 := (fun mask => (mask,id))

def c37650 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37650 : Upper (D 6) (R 6) [34,132,72,257,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,65] 13 (by decide) (choices 1) [2,4,16] r37650 c37650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23062
  · exact u23063
  · exact u23064

def r37651 : Route 9 := (fun mask => (mask,id))

def c37651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37651 : Upper (D 6) (R 6) [34,132,72,257,66] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,66] 13 (by decide) (choices 1) [1,4,16] r37651 c37651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23065
  · exact u23066
  · exact u23067

def b37652 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 265 84 51 115 179 307), lower := (rows 35 134 76 265 84 32 64 128 256), losses := [] }

theorem u37652 : Upper (D 6) (R 6) [34,132,72,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37653 : Route 9 := (fun mask => (mask,id))

def c37653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37653 : Upper (D 6) (R 6) [34,132,72,257,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,96] 13 (by decide) (choices 1) [1,2,4,16] r37653 c37653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23068
  · exact u23069
  · exact u23070
  · exact u23071

def r37654 : Route 9 := (fun mask => (mask,id))

def c37654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37654 : Upper (D 6) (R 6) [34,132,72,258,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258,5] 13 (by decide) (choices 1) [1,16,64] r37654 c37654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23072
  · exact u23073
  · exact u23074

def b37655 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 76 266 49 117 85 213 341), lower := (rows 35 134 76 266 49 32 64 128 256), losses := [] }

theorem u37655 : Upper (D 6) (R 6) [34,132,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37656 : Route 9 := (fun mask => (mask,id))

def c37656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37656 : Upper (D 6) (R 6) [34,132,72,258,36] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258,36] 13 (by decide) (choices 1) [1,16,64] r37656 c37656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23075
  · exact u23076
  · exact u23077

def r37657 : Route 9 := (fun mask => (mask,id))

def c37657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37657 : Upper (D 6) (R 6) [34,132,72,258,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258,65] 13 (by decide) (choices 1) [1,4,16] r37657 c37657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23078
  · exact u23079
  · exact u23080

def b37658 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 266 84 49 113 177 305), lower := (rows 35 134 76 266 84 32 64 128 256), losses := [] }

theorem u37658 : Upper (D 6) (R 6) [34,132,72,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37659 : Route 9 := (fun mask => (mask,id))

def c37659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37659 : Upper (D 6) (R 6) [34,132,72,258,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258,96] 13 (by decide) (choices 1) [1,4,16] r37659 c37659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23081
  · exact u23082
  · exact u23083

def b37660 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 134 76 268 19 113 113 241 369), lower := (rows 35 134 76 268 19 32 64 128 256), losses := [] }

theorem u37660 : Upper (D 6) (R 6) [34,132,72,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37661 : PairBound 9 := { available := 83, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 134 76 268 49 115 83 211 339), lower := (rows 35 134 76 268 49 32 64 128 256), losses := [] }

theorem u37661 : Upper (D 6) (R 6) [34,132,72,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37662 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 76 268 50 113 81 209 337), lower := (rows 35 134 76 268 50 32 64 128 256), losses := [] }

theorem u37662 : Upper (D 6) (R 6) [34,132,72,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37663 : Route 9 := (fun mask => (mask,id))

def c37663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37663 : Upper (D 6) (R 6) [34,132,72,260,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,260,65] 13 (by decide) (choices 1) [1,2,16] r37663 c37663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23084
  · exact u23085
  · exact u23086

def b37664 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 268 82 49 113 177 305), lower := (rows 35 134 76 268 82 32 64 128 256), losses := [] }

theorem u37664 : Upper (D 6) (R 6) [34,132,72,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37665 : Route 9 := (fun mask => (mask,id))

def c37665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37665 : Upper (D 6) (R 6) [34,132,72,260,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,260,96] 13 (by decide) (choices 1) [1,2,16] r37665 c37665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23087
  · exact u23088
  · exact u23089

def b37666 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 76 280 19 101 101 229 357), lower := (rows 35 134 76 280 19 32 64 128 256), losses := [] }

theorem u37666 : Upper (D 6) (R 6) [34,132,72,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37667 : Route 9 := (fun mask => (mask,id))

def c37667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37667 : Upper (D 6) (R 6) [34,132,72,272,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,272,5] 13 (by decide) (choices 1) [1,2,64] r37667 c37667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23090
  · exact u23091
  · exact u23092

def b37668 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 280 22 97 97 225 353), lower := (rows 35 134 76 280 22 32 64 128 256), losses := [] }

theorem u37668 : Upper (D 6) (R 6) [34,132,72,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37669 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 134 76 280 49 103 71 199 327), lower := (rows 35 134 76 280 49 32 64 128 256), losses := [] }

theorem u37669 : Upper (D 6) (R 6) [34,132,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37670 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 280 50 101 69 197 325), lower := (rows 35 134 76 280 50 32 64 128 256), losses := [] }

theorem u37670 : Upper (D 6) (R 6) [34,132,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37671 : Route 9 := (fun mask => (mask,id))

def c37671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37671 : Upper (D 6) (R 6) [34,132,72,272,36] 13 := by
  apply FastRouting.sound _ _ [34,132,72,272,36] 13 (by decide) (choices 1) [1,2,64] r37671 c37671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23093
  · exact u23094
  · exact u23095

def r37672 : Route 9 := (fun mask => (mask,id))

def c37672 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37672 : Upper (D 6) (R 6) [34,132,72,272,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,272,65] 13 (by decide) (choices 1) [1,2,4] r37672 c37672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23096
  · exact u23097
  · exact u23098

def b37673 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 280 82 37 101 165 293), lower := (rows 35 134 76 280 82 32 64 128 256), losses := [{ target := 6, region := (rows 23 6 4 24 16 38 0 134 262), good := (rows 419 423 431 281 443 32 0 128 256) }] }

theorem u37673 : Upper (D 6) (R 6) [34,132,72,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37674 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 134 76 280 84 35 99 163 291), lower := (rows 35 134 76 280 84 32 64 128 256), losses := [] }

theorem u37674 : Upper (D 6) (R 6) [34,132,72,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37675 : Route 9 := (fun mask => (mask,id))

def c37675 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37675 : Upper (D 6) (R 6) [34,132,72,272,96] 13 := by
  apply FastRouting.sound _ _ [34,132,72,272,96] 13 (by decide) (choices 1) [1,2,4] r37675 c37675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23099
  · exact u23100
  · exact u23101

def b37676 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 134 76 296 19 117 85 213 341), lower := (rows 35 134 76 296 19 32 64 128 256), losses := [] }

theorem u37676 : Upper (D 6) (R 6) [34,132,72,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37677 : Route 9 := (fun mask => (mask,id))

def c37677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37677 : Upper (D 6) (R 6) [34,132,72,288,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,5] 13 (by decide) (choices 1) [1,2,16,64] r37677 c37677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23102
  · exact u23103
  · exact u23104
  · exact u23105

def b37678 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 134 76 296 22 113 81 209 337), lower := (rows 35 134 76 296 22 32 64 128 256), losses := [] }

theorem u37678 : Upper (D 6) (R 6) [34,132,72,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37679 : Route 9 := (fun mask => (mask,id))

def c37679 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37679 : Upper (D 6) (R 6) [34,132,72,288,65] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288,65] 13 (by decide) (choices 1) [1,2,4,16] r37679 c37679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23106
  · exact u23107
  · exact u23108
  · exact u23109

#print axioms u37679
end Delivery.IrregularNine14.P06
