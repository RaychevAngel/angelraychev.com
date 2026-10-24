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

def b12600 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 176 417 481 417 417), lower := (rows 97 7 14 88 176 32 64 128 256), losses := [] }

theorem u12600 : Upper (D 8) (R 8) [96,5,10,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12601 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 273 160 224 160 416), lower := (rows 97 7 14 88 273 32 64 128 256), losses := [] }

theorem u12601 : Upper (D 8) (R 8) [96,5,10,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12602 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 304 161 225 161 417), lower := (rows 97 7 14 88 304 32 64 128 256), losses := [] }

theorem u12602 : Upper (D 8) (R 8) [96,5,10,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12603 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 400 161 225 161 417), lower := (rows 97 7 14 88 400 32 64 128 256), losses := [] }

theorem u12603 : Upper (D 8) (R 8) [96,5,10,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12604 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 176 433 465 401 401), lower := (rows 97 7 14 104 176 32 64 128 256), losses := [] }

theorem u12604 : Upper (D 8) (R 8) [96,5,10,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12605 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 304 177 209 145 401), lower := (rows 97 7 14 104 304 32 64 128 256), losses := [] }

theorem u12605 : Upper (D 8) (R 8) [96,5,10,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12606 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 400 177 241 177 433), lower := (rows 97 7 14 104 400 32 64 128 256), losses := [] }

theorem u12606 : Upper (D 8) (R 8) [96,5,10,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12607 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 176 368 368 496 368), lower := (rows 97 7 14 137 176 32 64 128 256), losses := [] }

theorem u12607 : Upper (D 8) (R 8) [96,5,10,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12608 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 208 304 368 432 304), lower := (rows 97 7 14 137 208 32 64 128 256), losses := [] }

theorem u12608 : Upper (D 8) (R 8) [96,5,10,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12609 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 304 240 240 240 496), lower := (rows 97 7 14 137 304 32 64 128 256), losses := [] }

theorem u12609 : Upper (D 8) (R 8) [96,5,10,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12610 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 336 176 240 176 432), lower := (rows 97 7 14 137 336 32 64 128 256), losses := [] }

theorem u12610 : Upper (D 8) (R 8) [96,5,10,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12611 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 400 112 112 240 368), lower := (rows 97 7 14 137 400 32 64 128 256), losses := [] }

theorem u12611 : Upper (D 8) (R 8) [96,5,10,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12612 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 152 49 480 480 480 480), lower := (rows 97 7 14 152 49 32 64 128 256), losses := [] }

theorem u12612 : Upper (D 8) (R 8) [96,5,10,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12613 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 152 81 416 480 416 416), lower := (rows 97 7 14 152 81 32 64 128 256), losses := [] }

theorem u12613 : Upper (D 8) (R 8) [96,5,10,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12614 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 152 112 417 481 417 417), lower := (rows 97 7 14 152 112 32 64 128 256), losses := [] }

theorem u12614 : Upper (D 8) (R 8) [96,5,10,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12615 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 152 145 352 352 480 352), lower := (rows 97 7 14 152 145 32 64 128 256), losses := [] }

theorem u12615 : Upper (D 8) (R 8) [96,5,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12616 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 176 353 353 481 353), lower := (rows 97 7 14 152 176 32 64 128 256), losses := [] }

theorem u12616 : Upper (D 8) (R 8) [96,5,10,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12617 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 208 289 353 417 289), lower := (rows 97 7 14 152 208 32 64 128 256), losses := [] }

theorem u12617 : Upper (D 8) (R 8) [96,5,10,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12618 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 152 273 224 224 224 480), lower := (rows 97 7 14 152 273 32 64 128 256), losses := [] }

theorem u12618 : Upper (D 8) (R 8) [96,5,10,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12619 : Route 9 := (fun mask => (mask,id))

def c12619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12619 : Upper (D 8) (R 8) [96,5,10,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,288] 13 (by decide) (choices 1) [1,64,128] r12619 c12619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4153
  · exact u4154
  · exact u4155

def r12620 : Route 9 := (fun mask => (mask,id))

def c12620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12620 : Upper (D 8) (R 8) [96,5,10,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,320] 13 (by decide) (choices 1) [1,128] r12620 c12620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4156
  · exact u4157

def b12621 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 400 97 97 225 353), lower := (rows 97 7 14 152 400 32 64 128 256), losses := [] }

theorem u12621 : Upper (D 8) (R 8) [96,5,10,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12622 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 168 49 496 464 464 464), lower := (rows 97 7 14 168 49 32 64 128 256), losses := [] }

theorem u12622 : Upper (D 8) (R 8) [96,5,10,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12623 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 168 81 432 496 432 432), lower := (rows 97 7 14 168 81 32 64 128 256), losses := [] }

theorem u12623 : Upper (D 8) (R 8) [96,5,10,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12624 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 168 112 433 465 401 401), lower := (rows 97 7 14 168 112 32 64 128 256), losses := [] }

theorem u12624 : Upper (D 8) (R 8) [96,5,10,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12625 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 168 145 368 368 496 368), lower := (rows 97 7 14 168 145 32 64 128 256), losses := [] }

theorem u12625 : Upper (D 8) (R 8) [96,5,10,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12626 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 168 176 369 337 465 337), lower := (rows 97 7 14 168 176 32 64 128 256), losses := [] }

theorem u12626 : Upper (D 8) (R 8) [96,5,10,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12627 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 168 208 305 369 433 305), lower := (rows 97 7 14 168 208 32 64 128 256), losses := [] }

theorem u12627 : Upper (D 8) (R 8) [96,5,10,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12628 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 168 273 240 240 240 496), lower := (rows 97 7 14 168 273 32 64 128 256), losses := [] }

theorem u12628 : Upper (D 8) (R 8) [96,5,10,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12629 : Route 9 := (fun mask => (mask,id))

def c12629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12629 : Upper (D 8) (R 8) [96,5,10,160,288] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,288] 13 (by decide) (choices 1) [1,16,64,128] r12629 c12629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4158
  · exact u4159
  · exact u4160
  · exact u4161

def r12630 : Route 9 := (fun mask => (mask,id))

def c12630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12630 : Upper (D 8) (R 8) [96,5,10,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,320] 13 (by decide) (choices 1) [1,16,128] r12630 c12630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4162
  · exact u4163
  · exact u4164

def b12631 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 168 400 113 113 241 369), lower := (rows 97 7 14 168 400 32 64 128 256), losses := [] }

theorem u12631 : Upper (D 8) (R 8) [96,5,10,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12632 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 145 304 368 432 304), lower := (rows 97 7 14 200 145 32 64 128 256), losses := [] }

theorem u12632 : Upper (D 8) (R 8) [96,5,10,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12633 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 176 305 369 433 305), lower := (rows 97 7 14 200 176 32 64 128 256), losses := [] }

theorem u12633 : Upper (D 8) (R 8) [96,5,10,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12634 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 273 176 240 176 432), lower := (rows 97 7 14 200 273 32 64 128 256), losses := [] }

theorem u12634 : Upper (D 8) (R 8) [96,5,10,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12635 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 304 177 241 177 433), lower := (rows 97 7 14 200 304 32 64 128 256), losses := [] }

theorem u12635 : Upper (D 8) (R 8) [96,5,10,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12636 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 200 400 49 113 177 305), lower := (rows 97 7 14 200 400 32 64 128 256), losses := [] }

theorem u12636 : Upper (D 8) (R 8) [96,5,10,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12637 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 176 240 240 240 496), lower := (rows 97 7 14 265 176 32 64 128 256), losses := [] }

theorem u12637 : Upper (D 8) (R 8) [96,5,10,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12638 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 208 176 240 176 432), lower := (rows 97 7 14 265 208 32 64 128 256), losses := [] }

theorem u12638 : Upper (D 8) (R 8) [96,5,10,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12639 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 280 49 224 224 224 480), lower := (rows 97 7 14 280 49 32 64 128 256), losses := [] }

theorem u12639 : Upper (D 8) (R 8) [96,5,10,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12640 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 280 81 160 224 160 416), lower := (rows 97 7 14 280 81 32 64 128 256), losses := [] }

theorem u12640 : Upper (D 8) (R 8) [96,5,10,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12641 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 280 112 161 225 161 417), lower := (rows 97 7 14 280 112 32 64 128 256), losses := [] }

theorem u12641 : Upper (D 8) (R 8) [96,5,10,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12642 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 280 145 224 224 224 480), lower := (rows 97 7 14 280 145 32 64 128 256), losses := [] }

theorem u12642 : Upper (D 8) (R 8) [96,5,10,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12643 : Route 9 := (fun mask => (mask,id))

def c12643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12643 : Upper (D 8) (R 8) [96,5,10,272,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272,160] 13 (by decide) (choices 1) [1,64,128] r12643 c12643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4165
  · exact u4166
  · exact u4167

def r12644 : Route 9 := (fun mask => (mask,id))

def c12644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12644 : Upper (D 8) (R 8) [96,5,10,272,192] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272,192] 13 (by decide) (choices 1) [1,128] r12644 c12644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4168
  · exact u4169

def b12645 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 296 49 240 208 208 464), lower := (rows 97 7 14 296 49 32 64 128 256), losses := [] }

theorem u12645 : Upper (D 8) (R 8) [96,5,10,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12646 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 296 81 176 240 176 432), lower := (rows 97 7 14 296 81 32 64 128 256), losses := [] }

theorem u12646 : Upper (D 8) (R 8) [96,5,10,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12647 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 296 112 177 209 145 401), lower := (rows 97 7 14 296 112 32 64 128 256), losses := [] }

theorem u12647 : Upper (D 8) (R 8) [96,5,10,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12648 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 296 145 240 240 240 496), lower := (rows 97 7 14 296 145 32 64 128 256), losses := [] }

theorem u12648 : Upper (D 8) (R 8) [96,5,10,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12649 : Route 9 := (fun mask => (mask,id))

def c12649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12649 : Upper (D 8) (R 8) [96,5,10,288,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,288,160] 13 (by decide) (choices 1) [1,16,64,128] r12649 c12649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4170
  · exact u4171
  · exact u4172
  · exact u4173

def r12650 : Route 9 := (fun mask => (mask,id))

def c12650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12650 : Upper (D 8) (R 8) [96,5,10,288,192] 13 := by
  apply FastRouting.sound _ _ [96,5,10,288,192] 13 (by decide) (choices 1) [1,16,128] r12650 c12650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4174
  · exact u4175
  · exact u4176

def b12651 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 328 145 176 240 176 432), lower := (rows 97 7 14 328 145 32 64 128 256), losses := [] }

theorem u12651 : Upper (D 8) (R 8) [96,5,10,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12652 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 328 176 177 241 177 433), lower := (rows 97 7 14 328 176 32 64 128 256), losses := [] }

theorem u12652 : Upper (D 8) (R 8) [96,5,10,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12653 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 392 49 240 240 240 496), lower := (rows 97 7 14 392 49 32 64 128 256), losses := [] }

theorem u12653 : Upper (D 8) (R 8) [96,5,10,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12654 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 392 81 176 240 176 432), lower := (rows 97 7 14 392 81 32 64 128 256), losses := [] }

theorem u12654 : Upper (D 8) (R 8) [96,5,10,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12655 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 14 392 112 177 241 177 433), lower := (rows 97 7 14 392 112 32 64 128 256), losses := [] }

theorem u12655 : Upper (D 8) (R 8) [96,5,10,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12656 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 392 145 112 112 240 368), lower := (rows 97 7 14 392 145 32 64 128 256), losses := [] }

theorem u12656 : Upper (D 8) (R 8) [96,5,10,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12657 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 392 176 113 113 241 369), lower := (rows 97 7 14 392 176 32 64 128 256), losses := [] }

theorem u12657 : Upper (D 8) (R 8) [96,5,10,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12658 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 392 208 49 113 177 305), lower := (rows 97 7 14 392 208 32 64 128 256), losses := [] }

theorem u12658 : Upper (D 8) (R 8) [96,5,10,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12659 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 41 50 480 448 448 448), lower := (rows 97 7 28 41 50 32 64 128 256), losses := [] }

theorem u12659 : Upper (D 8) (R 8) [96,5,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12659
end Delivery.IrregularNine14.P08
