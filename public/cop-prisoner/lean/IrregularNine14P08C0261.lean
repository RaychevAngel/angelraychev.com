import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0091

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15660 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 73 400 35 99 163 291), lower := (rows 193 14 52 73 400 32 64 128 256), losses := [] }

theorem u15660 : Upper (D 8) (R 8) [192,12,48,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15661 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 52 74 273 161 225 161 417), lower := (rows 193 14 52 74 273 32 64 128 256), losses := [] }

theorem u15661 : Upper (D 8) (R 8) [192,12,48,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15662 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 52 74 400 33 97 161 289), lower := (rows 193 14 52 74 400 32 64 128 256), losses := [] }

theorem u15662 : Upper (D 8) (R 8) [192,12,48,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15663 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 104 49 419 451 387 387), lower := (rows 193 14 52 104 49 32 64 128 256), losses := [] }

theorem u15663 : Upper (D 8) (R 8) [192,12,48,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15664 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 52 104 50 417 449 385 385), lower := (rows 193 14 52 104 50 32 64 128 256), losses := [] }

theorem u15664 : Upper (D 8) (R 8) [192,12,48,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15665 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 52 104 145 291 355 419 291), lower := (rows 193 14 52 104 145 32 64 128 256), losses := [] }

theorem u15665 : Upper (D 8) (R 8) [192,12,48,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15666 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 296, targets := 128 }], pairs := [(3,7)], upper := (rows 193 14 52 104 146 289 353 417 289), lower := (rows 193 14 52 104 146 32 64 128 256), losses := [] }

theorem u15666 : Upper (D 8) (R 8) [192,12,48,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15666 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15667 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 104 176 291 323 387 259), lower := (rows 193 14 52 104 176 32 64 128 256), losses := [] }

theorem u15667 : Upper (D 8) (R 8) [192,12,48,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15668 : Route 9 := (fun mask => (mask,id))

def c15668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15668 : Upper (D 8) (R 8) [192,12,48,96,257] 13 := by
  apply FastRouting.sound _ _ [192,12,48,96,257] 13 (by decide) (choices 1) [1,2,128] r15668 c15668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5497
  · exact u5498
  · exact u5499

def r15669 : Route 9 := (fun mask => (mask,id))

def c15669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15669 : Upper (D 8) (R 8) [192,12,48,96,258] 13 := by
  apply FastRouting.sound _ _ [192,12,48,96,258] 13 (by decide) (choices 1) [1,128] r15669 c15669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5500
  · exact u5501

def b15670 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 104 304 163 195 131 387), lower := (rows 193 14 52 104 304 32 64 128 256), losses := [] }

theorem u15670 : Upper (D 8) (R 8) [192,12,48,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15671 : Route 9 := (fun mask => (mask,id))

def c15671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15671 : Upper (D 8) (R 8) [192,12,48,96,384] 13 := by
  apply FastRouting.sound _ _ [192,12,48,96,384] 13 (by decide) (choices 1) [1,2] r15671 c15671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5502
  · exact u5503

def b15672 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 52 200 273 35 99 163 291), lower := (rows 193 14 52 200 273 32 64 128 256), losses := [] }

theorem u15672 : Upper (D 8) (R 8) [192,12,48,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15673 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 52 200 274 33 97 161 289), lower := (rows 193 14 52 200 274 32 64 128 256), losses := [] }

theorem u15673 : Upper (D 8) (R 8) [192,12,48,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15674 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 265 49 226 226 226 482), lower := (rows 193 14 52 265 49 32 64 128 256), losses := [] }

theorem u15674 : Upper (D 8) (R 8) [192,12,48,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15675 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 265 50 225 225 225 481), lower := (rows 193 14 52 265 50 32 64 128 256), losses := [] }

theorem u15675 : Upper (D 8) (R 8) [192,12,48,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15676 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 265 81 162 226 162 418), lower := (rows 193 14 52 265 81 32 64 128 256), losses := [] }

theorem u15676 : Upper (D 8) (R 8) [192,12,48,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15677 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 52 265 82 161 225 161 417), lower := (rows 193 14 52 265 82 32 64 128 256), losses := [] }

theorem u15677 : Upper (D 8) (R 8) [192,12,48,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15678 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 265 112 163 227 163 419), lower := (rows 193 14 52 265 112 32 64 128 256), losses := [] }

theorem u15678 : Upper (D 8) (R 8) [192,12,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15679 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 52 265 208 35 99 163 291), lower := (rows 193 14 52 265 208 32 64 128 256), losses := [] }

theorem u15679 : Upper (D 8) (R 8) [192,12,48,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15680 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 266 49 225 225 225 481), lower := (rows 193 14 52 266 49 32 64 128 256), losses := [] }

theorem u15680 : Upper (D 8) (R 8) [192,12,48,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15681 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 266 81 161 225 161 417), lower := (rows 193 14 52 266 81 32 64 128 256), losses := [] }

theorem u15681 : Upper (D 8) (R 8) [192,12,48,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15682 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 266 112 161 225 161 417), lower := (rows 193 14 52 266 112 32 64 128 256), losses := [] }

theorem u15682 : Upper (D 8) (R 8) [192,12,48,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15683 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 52 266 208 33 97 161 289), lower := (rows 193 14 52 266 208 32 64 128 256), losses := [] }

theorem u15683 : Upper (D 8) (R 8) [192,12,48,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15684 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 296 49 227 195 195 451), lower := (rows 193 14 52 296 49 32 64 128 256), losses := [] }

theorem u15684 : Upper (D 8) (R 8) [192,12,48,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15685 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 52 296 50 225 193 193 449), lower := (rows 193 14 52 296 50 32 64 128 256), losses := [] }

theorem u15685 : Upper (D 8) (R 8) [192,12,48,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15686 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 52 296 81 163 227 163 419), lower := (rows 193 14 52 296 81 32 64 128 256), losses := [] }

theorem u15686 : Upper (D 8) (R 8) [192,12,48,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15687 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 296, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 52 296 82 161 225 161 417), lower := (rows 193 14 52 296 82 32 64 128 256), losses := [] }

theorem u15687 : Upper (D 8) (R 8) [192,12,48,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15688 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 296 112 163 195 131 387), lower := (rows 193 14 52 296 112 32 64 128 256), losses := [] }

theorem u15688 : Upper (D 8) (R 8) [192,12,48,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15689 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 52 296 208 35 99 163 291), lower := (rows 193 14 52 296 208 32 64 128 256), losses := [] }

theorem u15689 : Upper (D 8) (R 8) [192,12,48,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15690 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 328 49 163 227 163 419), lower := (rows 193 14 52 328 49 32 64 128 256), losses := [] }

theorem u15690 : Upper (D 8) (R 8) [192,12,48,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15691 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 328 50 161 225 161 417), lower := (rows 193 14 52 328 50 32 64 128 256), losses := [] }

theorem u15691 : Upper (D 8) (R 8) [192,12,48,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15692 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 52 328 145 35 99 163 291), lower := (rows 193 14 52 328 145 32 64 128 256), losses := [] }

theorem u15692 : Upper (D 8) (R 8) [192,12,48,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15693 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 128 }], pairs := [(3,7)], upper := (rows 193 14 52 328 146 33 97 161 289), lower := (rows 193 14 52 328 146 32 64 128 256), losses := [] }

theorem u15693 : Upper (D 8) (R 8) [192,12,48,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15694 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 52 328 176 35 99 163 291), lower := (rows 193 14 52 328 176 32 64 128 256), losses := [] }

theorem u15694 : Upper (D 8) (R 8) [192,12,48,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15695 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 152 49 290 354 418 290), lower := (rows 193 14 69 152 49 32 64 128 256), losses := [] }

theorem u15695 : Upper (D 8) (R 8) [192,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15696 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 152 273 34 98 162 290), lower := (rows 193 14 69 152 273 32 64 128 256), losses := [] }

theorem u15696 : Upper (D 8) (R 8) [192,12,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15697 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 152 304 35 99 163 291), lower := (rows 193 14 69 152 304 32 64 128 256), losses := [] }

theorem u15697 : Upper (D 8) (R 8) [192,12,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15698 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 49 306 370 434 306), lower := (rows 193 14 69 168 49 32 64 128 256), losses := [] }

theorem u15698 : Upper (D 8) (R 8) [192,12,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15699 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 50 305 369 433 305), lower := (rows 193 14 69 168 50 32 64 128 256), losses := [] }

theorem u15699 : Upper (D 8) (R 8) [192,12,65,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15700 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 273 50 114 178 306), lower := (rows 193 14 69 168 273 32 64 128 256), losses := [] }

theorem u15700 : Upper (D 8) (R 8) [192,12,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15701 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 274 49 113 177 305), lower := (rows 193 14 69 168 274 32 64 128 256), losses := [] }

theorem u15701 : Upper (D 8) (R 8) [192,12,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15702 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 168 304 51 115 179 307), lower := (rows 193 14 69 168 304 32 64 128 256), losses := [] }

theorem u15702 : Upper (D 8) (R 8) [192,12,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15703 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 265 50 176 240 176 432), lower := (rows 193 14 69 265 50 32 64 128 256), losses := [] }

theorem u15703 : Upper (D 8) (R 8) [192,12,65,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15704 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 265 146 48 112 176 304), lower := (rows 193 14 69 265 146 32 64 128 256), losses := [] }

theorem u15704 : Upper (D 8) (R 8) [192,12,65,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15705 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 265 176 50 114 178 306), lower := (rows 193 14 69 265 176 32 64 128 256), losses := [] }

theorem u15705 : Upper (D 8) (R 8) [192,12,65,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15706 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 266 49 176 240 176 432), lower := (rows 193 14 69 266 49 32 64 128 256), losses := [] }

theorem u15706 : Upper (D 8) (R 8) [192,12,65,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15707 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 266 176 49 113 177 305), lower := (rows 193 14 69 266 176 32 64 128 256), losses := [] }

theorem u15707 : Upper (D 8) (R 8) [192,12,65,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15708 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 280 49 162 226 162 418), lower := (rows 193 14 69 280 49 32 64 128 256), losses := [] }

theorem u15708 : Upper (D 8) (R 8) [192,12,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15709 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 280 50 161 225 161 417), lower := (rows 193 14 69 280 50 32 64 128 256), losses := [] }

theorem u15709 : Upper (D 8) (R 8) [192,12,65,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15710 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 280 176 35 99 163 291), lower := (rows 193 14 69 280 176 32 64 128 256), losses := [] }

theorem u15710 : Upper (D 8) (R 8) [192,12,65,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15711 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 296 49 178 242 178 434), lower := (rows 193 14 69 296 49 32 64 128 256), losses := [] }

theorem u15711 : Upper (D 8) (R 8) [192,12,65,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15712 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 296 50 177 241 177 433), lower := (rows 193 14 69 296 50 32 64 128 256), losses := [] }

theorem u15712 : Upper (D 8) (R 8) [192,12,65,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15713 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 296 146 49 113 177 305), lower := (rows 193 14 69 296 146 32 64 128 256), losses := [] }

theorem u15713 : Upper (D 8) (R 8) [192,12,65,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15714 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 296 176 51 115 179 307), lower := (rows 193 14 69 296 176 32 64 128 256), losses := [] }

theorem u15714 : Upper (D 8) (R 8) [192,12,65,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15715 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 392 49 50 114 178 306), lower := (rows 193 14 69 392 49 32 64 128 256), losses := [] }

theorem u15715 : Upper (D 8) (R 8) [192,12,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15716 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 69 392 50 49 113 177 305), lower := (rows 193 14 69 392 50 32 64 128 256), losses := [] }

theorem u15716 : Upper (D 8) (R 8) [192,12,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15717 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 152 49 289 353 417 289), lower := (rows 193 14 70 152 49 32 64 128 256), losses := [] }

theorem u15717 : Upper (D 8) (R 8) [192,12,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15718 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 152 273 33 97 161 289), lower := (rows 193 14 70 152 273 32 64 128 256), losses := [] }

theorem u15718 : Upper (D 8) (R 8) [192,12,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15719 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 70 152 304 33 97 161 289), lower := (rows 193 14 70 152 304 32 64 128 256), losses := [] }

theorem u15719 : Upper (D 8) (R 8) [192,12,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15719
end Delivery.IrregularNine14.P08
