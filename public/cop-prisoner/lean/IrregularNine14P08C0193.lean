import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0059

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11580 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 28 41 49 484 452 452 452), lower := (rows 67 162 28 41 49 32 64 128 256), losses := [] }

theorem u11580 : Upper (D 8) (R 8) [66,160,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11581 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 28 41 52 481 449 449 449), lower := (rows 67 162 28 41 52 32 64 128 256), losses := [] }

theorem u11581 : Upper (D 8) (R 8) [66,160,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11582 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 41 81 420 484 420 420), lower := (rows 67 162 28 41 81 32 64 128 256), losses := [] }

theorem u11582 : Upper (D 8) (R 8) [66,160,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11583 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 41 84 417 481 417 417), lower := (rows 67 162 28 41 84 32 64 128 256), losses := [] }

theorem u11583 : Upper (D 8) (R 8) [66,160,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11584 : Route 9 := (fun mask => (mask,id))

def c11584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u11584 : Upper (D 8) (R 8) [66,160,24,33,96] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,96] 13 (by decide) (choices 1) [1,4,128,256] r11584 c11584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3565
  · exact u3566
  · exact u3567
  · exact u3568

def b11585 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 41 145 356 356 484 356), lower := (rows 67 162 28 41 145 32 64 128 256), losses := [] }

theorem u11585 : Upper (D 8) (R 8) [66,160,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11586 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 41 148 353 353 481 353), lower := (rows 67 162 28 41 148 32 64 128 256), losses := [] }

theorem u11586 : Upper (D 8) (R 8) [66,160,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11587 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 28 41 176 357 325 453 325), lower := (rows 67 162 28 41 176 32 64 128 256), losses := [] }

theorem u11587 : Upper (D 8) (R 8) [66,160,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11588 : Route 9 := (fun mask => (mask,id))

def c11588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11588 : Upper (D 8) (R 8) [66,160,24,33,192] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,192] 13 (by decide) (choices 1) [1,4,256] r11588 c11588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3569
  · exact u3570
  · exact u3571

def b11589 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 273 228 228 228 484), lower := (rows 67 162 28 41 273 32 64 128 256), losses := [] }

theorem u11589 : Upper (D 8) (R 8) [66,160,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11590 : Route 9 := (fun mask => (mask,id))

def c11590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11590 : Upper (D 8) (R 8) [66,160,24,33,260] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,260] 13 (by decide) (choices 1) [1,64,128] r11590 c11590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3572
  · exact u3573
  · exact u3574

def r11591 : Route 9 := (fun mask => (mask,id))

def c11591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11591 : Upper (D 8) (R 8) [66,160,24,33,288] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,288] 13 (by decide) (choices 1) [1,4,64,128] r11591 c11591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3575
  · exact u3576
  · exact u3577
  · exact u3578

def r11592 : Route 9 := (fun mask => (mask,id))

def c11592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11592 : Upper (D 8) (R 8) [66,160,24,33,320] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,320] 13 (by decide) (choices 1) [1,4,128] r11592 c11592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3579
  · exact u3580
  · exact u3581

def r11593 : Route 9 := (fun mask => (mask,id))

def c11593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11593 : Upper (D 8) (R 8) [66,160,24,33,384] 13 := by
  apply FastRouting.sound _ _ [66,160,24,33,384] 13 (by decide) (choices 1) [1,4,64] r11593 c11593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3582
  · exact u3583
  · exact u3584

def b11594 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 44 81 417 481 417 417), lower := (rows 67 162 28 44 81 32 64 128 256), losses := [] }

theorem u11594 : Upper (D 8) (R 8) [66,160,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11595 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 28 44 112 417 449 385 385), lower := (rows 67 162 28 44 112 32 64 128 256), losses := [] }

theorem u11595 : Upper (D 8) (R 8) [66,160,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11596 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 44 145 353 353 481 353), lower := (rows 67 162 28 44 145 32 64 128 256), losses := [] }

theorem u11596 : Upper (D 8) (R 8) [66,160,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11597 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 28, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 28 44 176 353 321 449 321), lower := (rows 67 162 28 44 176 32 64 128 256), losses := [] }

theorem u11597 : Upper (D 8) (R 8) [66,160,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11598 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 44 208 289 353 417 289), lower := (rows 67 162 28 44 208 32 64 128 256), losses := [] }

theorem u11598 : Upper (D 8) (R 8) [66,160,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11599 : Route 9 := (fun mask => (mask,id))

def c11599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11599 : Upper (D 8) (R 8) [66,160,24,36,257] 13 := by
  apply FastRouting.sound _ _ [66,160,24,36,257] 13 (by decide) (choices 1) [1,64,128] r11599 c11599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3585
  · exact u3586
  · exact u3587

def b11600 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 162 28 44 304 225 193 193 449), lower := (rows 67 162 28 44 304 32 64 128 256), losses := [] }

theorem u11600 : Upper (D 8) (R 8) [66,160,24,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11601 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 44 336 161 225 161 417), lower := (rows 67 162 28 44 336 32 64 128 256), losses := [] }

theorem u11601 : Upper (D 8) (R 8) [66,160,24,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11602 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 44 400 97 97 225 353), lower := (rows 67 162 28 44 400 32 64 128 256), losses := [] }

theorem u11602 : Upper (D 8) (R 8) [66,160,24,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11603 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 73 273 164 228 164 420), lower := (rows 67 162 28 73 273 32 64 128 256), losses := [] }

theorem u11603 : Upper (D 8) (R 8) [66,160,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11604 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 73 276 161 225 161 417), lower := (rows 67 162 28 73 276 32 64 128 256), losses := [] }

theorem u11604 : Upper (D 8) (R 8) [66,160,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11605 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 73 304 165 229 165 421), lower := (rows 67 162 28 73 304 32 64 128 256), losses := [] }

theorem u11605 : Upper (D 8) (R 8) [66,160,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11606 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 73 400 37 101 165 293), lower := (rows 67 162 28 73 400 32 64 128 256), losses := [] }

theorem u11606 : Upper (D 8) (R 8) [66,160,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11607 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 76 273 161 225 161 417), lower := (rows 67 162 28 76 273 32 64 128 256), losses := [] }

theorem u11607 : Upper (D 8) (R 8) [66,160,24,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11608 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 76 304 161 225 161 417), lower := (rows 67 162 28 76 304 32 64 128 256), losses := [] }

theorem u11608 : Upper (D 8) (R 8) [66,160,24,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11609 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 76 400 33 97 161 289), lower := (rows 67 162 28 76 400 32 64 128 256), losses := [] }

theorem u11609 : Upper (D 8) (R 8) [66,160,24,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11610 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 104 145 293 357 421 293), lower := (rows 67 162 28 104 145 32 64 128 256), losses := [] }

theorem u11610 : Upper (D 8) (R 8) [66,160,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11611 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 104 148 289 353 417 289), lower := (rows 67 162 28 104 148 32 64 128 256), losses := [] }

theorem u11611 : Upper (D 8) (R 8) [66,160,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11612 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 28 104 176 293 325 389 261), lower := (rows 67 162 28 104 176 32 64 128 256), losses := [] }

theorem u11612 : Upper (D 8) (R 8) [66,160,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11613 : Route 9 := (fun mask => (mask,id))

def c11613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11613 : Upper (D 8) (R 8) [66,160,24,96,257] 13 := by
  apply FastRouting.sound _ _ [66,160,24,96,257] 13 (by decide) (choices 1) [1,4,128] r11613 c11613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3588
  · exact u3589
  · exact u3590

def b11614 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 104 276 161 225 161 417), lower := (rows 67 162 28 104 276 32 64 128 256), losses := [] }

theorem u11614 : Upper (D 8) (R 8) [66,160,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11615 : Route 9 := (fun mask => (mask,id))

def c11615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11615 : Upper (D 8) (R 8) [66,160,24,96,288] 13 := by
  apply FastRouting.sound _ _ [66,160,24,96,288] 13 (by decide) (choices 1) [1,4,128] r11615 c11615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3591
  · exact u3592
  · exact u3593

def r11616 : Route 9 := (fun mask => (mask,id))

def c11616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11616 : Upper (D 8) (R 8) [66,160,24,96,384] 13 := by
  apply FastRouting.sound _ _ [66,160,24,96,384] 13 (by decide) (choices 1) [1,4] r11616 c11616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3594
  · exact u3595

def b11617 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 137 273 100 100 228 356), lower := (rows 67 162 28 137 273 32 64 128 256), losses := [] }

theorem u11617 : Upper (D 8) (R 8) [66,160,24,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11618 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 137 276 97 97 225 353), lower := (rows 67 162 28 137 276 32 64 128 256), losses := [] }

theorem u11618 : Upper (D 8) (R 8) [66,160,24,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11619 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 137 304 101 101 229 357), lower := (rows 67 162 28 137 304 32 64 128 256), losses := [] }

theorem u11619 : Upper (D 8) (R 8) [66,160,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11620 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 137 336 37 101 165 293), lower := (rows 67 162 28 137 336 32 64 128 256), losses := [] }

theorem u11620 : Upper (D 8) (R 8) [66,160,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11621 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 140 273 97 97 225 353), lower := (rows 67 162 28 140 273 32 64 128 256), losses := [] }

theorem u11621 : Upper (D 8) (R 8) [66,160,24,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11622 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 140 304 97 97 225 353), lower := (rows 67 162 28 140 304 32 64 128 256), losses := [] }

theorem u11622 : Upper (D 8) (R 8) [66,160,24,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11623 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 140 336 33 97 161 289), lower := (rows 67 162 28 140 336 32 64 128 256), losses := [] }

theorem u11623 : Upper (D 8) (R 8) [66,160,24,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11624 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 28 168 273 101 101 229 357), lower := (rows 67 162 28 168 273 32 64 128 256), losses := [] }

theorem u11624 : Upper (D 8) (R 8) [66,160,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11625 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 28 168 276 97 97 225 353), lower := (rows 67 162 28 168 276 32 64 128 256), losses := [] }

theorem u11625 : Upper (D 8) (R 8) [66,160,24,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11626 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 28 168 304 101 69 197 325), lower := (rows 67 162 28 168 304 32 64 128 256), losses := [] }

theorem u11626 : Upper (D 8) (R 8) [66,160,24,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11627 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 28 168 336 37 101 165 293), lower := (rows 67 162 28 168 336 32 64 128 256), losses := [] }

theorem u11627 : Upper (D 8) (R 8) [66,160,24,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11628 : Route 9 := (fun mask => (mask,id))

def c11628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11628 : Upper (D 8) (R 8) [66,160,24,192,257] 13 := by
  apply FastRouting.sound _ _ [66,160,24,192,257] 13 (by decide) (choices 1) [1,4] r11628 c11628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3596
  · exact u3597

def b11629 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 200 276 33 97 161 289), lower := (rows 67 162 28 200 276 32 64 128 256), losses := [] }

theorem u11629 : Upper (D 8) (R 8) [66,160,24,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11630 : Route 9 := (fun mask => (mask,id))

def c11630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11630 : Upper (D 8) (R 8) [66,160,24,192,288] 13 := by
  apply FastRouting.sound _ _ [66,160,24,192,288] 13 (by decide) (choices 1) [1,4] r11630 c11630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3598
  · exact u3599

def b11631 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 84 440 472 408 408), lower := (rows 67 162 37 41 84 32 64 128 256), losses := [] }

theorem u11631 : Upper (D 8) (R 8) [66,160,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11632 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 148 376 344 472 344), lower := (rows 67 162 37 41 148 32 64 128 256), losses := [] }

theorem u11632 : Upper (D 8) (R 8) [66,160,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11633 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 208 316 348 412 284), lower := (rows 67 162 37 41 208 32 64 128 256), losses := [] }

theorem u11633 : Upper (D 8) (R 8) [66,160,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11634 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 276 248 216 216 472), lower := (rows 67 162 37 41 276 32 64 128 256), losses := [] }

theorem u11634 : Upper (D 8) (R 8) [66,160,33,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11635 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 336 188 220 156 412), lower := (rows 67 162 37 41 336 32 64 128 256), losses := [] }

theorem u11635 : Upper (D 8) (R 8) [66,160,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11636 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 162 37 41 400 124 92 220 348), lower := (rows 67 162 37 41 400 32 64 128 256), losses := [] }

theorem u11636 : Upper (D 8) (R 8) [66,160,33,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11637 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 88 433 465 401 401), lower := (rows 67 162 37 44 88 32 64 128 256), losses := [] }

theorem u11637 : Upper (D 8) (R 8) [66,160,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11638 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 152 369 337 465 337), lower := (rows 67 162 37 44 152 32 64 128 256), losses := [] }

theorem u11638 : Upper (D 8) (R 8) [66,160,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11639 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 37 44 208 313 345 409 281), lower := (rows 67 162 37 44 208 32 64 128 256), losses := [] }

theorem u11639 : Upper (D 8) (R 8) [66,160,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11639
end Delivery.IrregularNine14.P08
