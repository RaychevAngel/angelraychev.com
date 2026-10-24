import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0069

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12660 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 146 480 480 480 480), lower := (rows 97 7 28 41 146 32 64 128 256), losses := [] }

theorem u12660 : Upper (D 8) (R 8) [96,5,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12661 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 176 482 450 450 450), lower := (rows 97 7 28 41 176 32 64 128 256), losses := [] }

theorem u12661 : Upper (D 8) (R 8) [96,5,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12662 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 274 224 224 224 480), lower := (rows 97 7 28 41 274 32 64 128 256), losses := [] }

theorem u12662 : Upper (D 8) (R 8) [96,5,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12663 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 304 226 194 194 450), lower := (rows 97 7 28 41 304 32 64 128 256), losses := [] }

theorem u12663 : Upper (D 8) (R 8) [96,5,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12664 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 41 400 226 226 226 482), lower := (rows 97 7 28 41 400 32 64 128 256), losses := [] }

theorem u12664 : Upper (D 8) (R 8) [96,5,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12665 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 28 42 81 416 480 416 416), lower := (rows 97 7 28 42 81 32 64 128 256), losses := [] }

theorem u12665 : Upper (D 8) (R 8) [96,5,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12666 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 28 42 112 417 449 385 385), lower := (rows 97 7 28 42 112 32 64 128 256), losses := [] }

theorem u12666 : Upper (D 8) (R 8) [96,5,24,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12667 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 488, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 42 145 480 480 480 480), lower := (rows 97 7 28 42 145 32 64 128 256), losses := [] }

theorem u12667 : Upper (D 8) (R 8) [96,5,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12668 : Route 9 := (fun mask => (mask,id))

def c12668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u12668 : Upper (D 8) (R 8) [96,5,24,34,160] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,160] 13 (by decide) (choices 1) [1,64,128,256] r12668 c12668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4177
  · exact u4178
  · exact u4179
  · exact u4180

def b12669 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 42 208 417 481 417 417), lower := (rows 97 7 28 42 208 32 64 128 256), losses := [] }

theorem u12669 : Upper (D 8) (R 8) [96,5,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12670 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 42 273 224 224 224 480), lower := (rows 97 7 28 42 273 32 64 128 256), losses := [] }

theorem u12670 : Upper (D 8) (R 8) [96,5,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12671 : Route 9 := (fun mask => (mask,id))

def c12671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12671 : Upper (D 8) (R 8) [96,5,24,34,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,288] 13 (by decide) (choices 1) [1,64,128] r12671 c12671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4181
  · exact u4182
  · exact u4183

def b12672 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 42 336 161 225 161 417), lower := (rows 97 7 28 42 336 32 64 128 256), losses := [] }

theorem u12672 : Upper (D 8) (R 8) [96,5,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12673 : Route 9 := (fun mask => (mask,id))

def c12673 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12673 : Upper (D 8) (R 8) [96,5,24,34,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,384] 13 (by decide) (choices 1) [1,64,128] r12673 c12673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4184
  · exact u4185
  · exact u4186

def b12674 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 146 416 480 416 416), lower := (rows 97 7 28 73 146 32 64 128 256), losses := [] }

theorem u12674 : Upper (D 8) (R 8) [96,5,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12675 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 176 418 482 418 418), lower := (rows 97 7 28 73 176 32 64 128 256), losses := [] }

theorem u12675 : Upper (D 8) (R 8) [96,5,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12676 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 274 160 224 160 416), lower := (rows 97 7 28 73 274 32 64 128 256), losses := [] }

theorem u12676 : Upper (D 8) (R 8) [96,5,24,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12677 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 304 162 226 162 418), lower := (rows 97 7 28 73 304 32 64 128 256), losses := [] }

theorem u12677 : Upper (D 8) (R 8) [96,5,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12678 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 73 400 162 226 162 418), lower := (rows 97 7 28 73 400 32 64 128 256), losses := [] }

theorem u12678 : Upper (D 8) (R 8) [96,5,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12679 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 145 416 480 416 416), lower := (rows 97 7 28 74 145 32 64 128 256), losses := [] }

theorem u12679 : Upper (D 8) (R 8) [96,5,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12680 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 176 417 481 417 417), lower := (rows 97 7 28 74 176 32 64 128 256), losses := [] }

theorem u12680 : Upper (D 8) (R 8) [96,5,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12681 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 273 160 224 160 416), lower := (rows 97 7 28 74 273 32 64 128 256), losses := [] }

theorem u12681 : Upper (D 8) (R 8) [96,5,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12682 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 304 161 225 161 417), lower := (rows 97 7 28 74 304 32 64 128 256), losses := [] }

theorem u12682 : Upper (D 8) (R 8) [96,5,24,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12683 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 74 400 161 225 161 417), lower := (rows 97 7 28 74 400 32 64 128 256), losses := [] }

theorem u12683 : Upper (D 8) (R 8) [96,5,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12684 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 146 417 481 417 417), lower := (rows 97 7 28 104 146 32 64 128 256), losses := [] }

theorem u12684 : Upper (D 8) (R 8) [96,5,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12685 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 176 419 451 387 387), lower := (rows 97 7 28 104 176 32 64 128 256), losses := [] }

theorem u12685 : Upper (D 8) (R 8) [96,5,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12686 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 274 161 225 161 417), lower := (rows 97 7 28 104 274 32 64 128 256), losses := [] }

theorem u12686 : Upper (D 8) (R 8) [96,5,24,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12687 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 304 163 195 131 387), lower := (rows 97 7 28 104 304 32 64 128 256), losses := [] }

theorem u12687 : Upper (D 8) (R 8) [96,5,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12688 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 400 163 227 163 419), lower := (rows 97 7 28 104 400 32 64 128 256), losses := [] }

theorem u12688 : Upper (D 8) (R 8) [96,5,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12689 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 137 146 352 352 480 352), lower := (rows 97 7 28 137 146 32 64 128 256), losses := [] }

theorem u12689 : Upper (D 8) (R 8) [96,5,24,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12690 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 176 354 354 482 354), lower := (rows 97 7 28 137 176 32 64 128 256), losses := [] }

theorem u12690 : Upper (D 8) (R 8) [96,5,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12691 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 208 290 354 418 290), lower := (rows 97 7 28 137 208 32 64 128 256), losses := [] }

theorem u12691 : Upper (D 8) (R 8) [96,5,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12692 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 137 274 224 224 224 480), lower := (rows 97 7 28 137 274 32 64 128 256), losses := [] }

theorem u12692 : Upper (D 8) (R 8) [96,5,24,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12693 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 137 304 226 226 226 482), lower := (rows 97 7 28 137 304 32 64 128 256), losses := [] }

theorem u12693 : Upper (D 8) (R 8) [96,5,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12694 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 28 137 336 162 226 162 418), lower := (rows 97 7 28 137 336 32 64 128 256), losses := [] }

theorem u12694 : Upper (D 8) (R 8) [96,5,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12695 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 400 98 98 226 354), lower := (rows 97 7 28 137 400 32 64 128 256), losses := [] }

theorem u12695 : Upper (D 8) (R 8) [96,5,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12696 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 176 353 353 481 353), lower := (rows 97 7 28 138 176 32 64 128 256), losses := [] }

theorem u12696 : Upper (D 8) (R 8) [96,5,24,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12697 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 208 289 353 417 289), lower := (rows 97 7 28 138 208 32 64 128 256), losses := [] }

theorem u12697 : Upper (D 8) (R 8) [96,5,24,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12698 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 138 273 224 224 224 480), lower := (rows 97 7 28 138 273 32 64 128 256), losses := [] }

theorem u12698 : Upper (D 8) (R 8) [96,5,24,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12699 : Route 9 := (fun mask => (mask,id))

def c12699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12699 : Upper (D 8) (R 8) [96,5,24,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,288] 13 (by decide) (choices 1) [1,64,128] r12699 c12699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4187
  · exact u4188
  · exact u4189

def b12700 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 138 336 161 225 161 417), lower := (rows 97 7 28 138 336 32 64 128 256), losses := [] }

theorem u12700 : Upper (D 8) (R 8) [96,5,24,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12701 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 400 97 97 225 353), lower := (rows 97 7 28 138 400 32 64 128 256), losses := [] }

theorem u12701 : Upper (D 8) (R 8) [96,5,24,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12702 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 28 168 176 355 323 451 323), lower := (rows 97 7 28 168 176 32 64 128 256), losses := [] }

theorem u12702 : Upper (D 8) (R 8) [96,5,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12703 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 208 291 355 419 291), lower := (rows 97 7 28 168 208 32 64 128 256), losses := [] }

theorem u12703 : Upper (D 8) (R 8) [96,5,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12704 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 168 273 226 226 226 482), lower := (rows 97 7 28 168 273 32 64 128 256), losses := [] }

theorem u12704 : Upper (D 8) (R 8) [96,5,24,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12705 : Route 9 := (fun mask => (mask,id))

def c12705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12705 : Upper (D 8) (R 8) [96,5,24,160,258] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,258] 13 (by decide) (choices 1) [1,64,128] r12705 c12705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4190
  · exact u4191
  · exact u4192

def r12706 : Route 9 := (fun mask => (mask,id))

def c12706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12706 : Upper (D 8) (R 8) [96,5,24,160,288] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,288] 13 (by decide) (choices 1) [1,2,64,128] r12706 c12706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4193
  · exact u4194
  · exact u4195
  · exact u4196

def b12707 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 28 168 336 163 227 163 419), lower := (rows 97 7 28 168 336 32 64 128 256), losses := [] }

theorem u12707 : Upper (D 8) (R 8) [96,5,24,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12708 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 168 400 99 99 227 355), lower := (rows 97 7 28 168 400 32 64 128 256), losses := [] }

theorem u12708 : Upper (D 8) (R 8) [96,5,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12709 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 200 273 162 226 162 418), lower := (rows 97 7 28 200 273 32 64 128 256), losses := [] }

theorem u12709 : Upper (D 8) (R 8) [96,5,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12710 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 200 274 161 225 161 417), lower := (rows 97 7 28 200 274 32 64 128 256), losses := [] }

theorem u12710 : Upper (D 8) (R 8) [96,5,24,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12711 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 28 200 304 163 227 163 419), lower := (rows 97 7 28 200 304 32 64 128 256), losses := [] }

theorem u12711 : Upper (D 8) (R 8) [96,5,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12712 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 200 400 35 99 163 291), lower := (rows 97 7 28 200 400 32 64 128 256), losses := [] }

theorem u12712 : Upper (D 8) (R 8) [96,5,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12713 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 56 480 448 448 448), lower := (rows 97 7 37 26 56 32 64 128 256), losses := [] }

theorem u12713 : Upper (D 8) (R 8) [96,5,33,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12714 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 152 480 480 480 480), lower := (rows 97 7 37 26 152 32 64 128 256), losses := [] }

theorem u12714 : Upper (D 8) (R 8) [96,5,33,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12715 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 176 488 456 456 456), lower := (rows 97 7 37 26 176 32 64 128 256), losses := [] }

theorem u12715 : Upper (D 8) (R 8) [96,5,33,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12716 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 208 424 488 424 424), lower := (rows 97 7 37 26 208 32 64 128 256), losses := [] }

theorem u12716 : Upper (D 8) (R 8) [96,5,33,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12717 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 280 224 224 224 480), lower := (rows 97 7 37 26 280 32 64 128 256), losses := [] }

theorem u12717 : Upper (D 8) (R 8) [96,5,33,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12718 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 304 232 200 200 456), lower := (rows 97 7 37 26 304 32 64 128 256), losses := [] }

theorem u12718 : Upper (D 8) (R 8) [96,5,33,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12719 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 336 168 232 168 424), lower := (rows 97 7 37 26 336 32 64 128 256), losses := [] }

theorem u12719 : Upper (D 8) (R 8) [96,5,33,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12719
end Delivery.IrregularNine14.P08
