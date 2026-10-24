import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0099
import IrregularNine14P08C0100

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16620 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 25 112 168 232 168 424), lower := (rows 259 70 37 25 112 32 64 128 256), losses := [] }

theorem u16620 : Upper (D 8) (R 8) [258,68,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16621 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 25 152 224 224 224 480), lower := (rows 259 70 37 25 152 32 64 128 256), losses := [] }

theorem u16621 : Upper (D 8) (R 8) [258,68,33,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16622 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 25 176 232 232 232 488), lower := (rows 259 70 37 25 176 32 64 128 256), losses := [] }

theorem u16622 : Upper (D 8) (R 8) [258,68,33,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16623 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 25 208 168 232 168 424), lower := (rows 259 70 37 25 208 32 64 128 256), losses := [] }

theorem u16623 : Upper (D 8) (R 8) [258,68,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16624 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 56 240 208 208 464), lower := (rows 259 70 37 41 56 32 64 128 256), losses := [] }

theorem u16624 : Upper (D 8) (R 8) [258,68,33,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16625 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 88 176 240 176 432), lower := (rows 259 70 37 41 88 32 64 128 256), losses := [] }

theorem u16625 : Upper (D 8) (R 8) [258,68,33,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16626 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 112 184 216 152 408), lower := (rows 259 70 37 41 112 32 64 128 256), losses := [] }

theorem u16626 : Upper (D 8) (R 8) [258,68,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16627 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 152 240 240 240 496), lower := (rows 259 70 37 41 152 32 64 128 256), losses := [] }

theorem u16627 : Upper (D 8) (R 8) [258,68,33,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16628 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 176 248 216 216 472), lower := (rows 259 70 37 41 176 32 64 128 256), losses := [] }

theorem u16628 : Upper (D 8) (R 8) [258,68,33,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16629 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 41 208 184 248 184 440), lower := (rows 259 70 37 41 208 32 64 128 256), losses := [] }

theorem u16629 : Upper (D 8) (R 8) [258,68,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16630 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 56 56 225 193 193 449), lower := (rows 259 70 37 56 56 32 64 128 256), losses := [] }

theorem u16630 : Upper (D 8) (R 8) [258,68,33,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16631 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 37 56 81 168 232 168 424), lower := (rows 259 70 37 56 81 32 64 128 256), losses := [] }

theorem u16631 : Upper (D 8) (R 8) [258,68,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16632 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 37 56 88 161 225 161 417), lower := (rows 259 70 37 56 88 32 64 128 256), losses := [] }

theorem u16632 : Upper (D 8) (R 8) [258,68,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16633 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 56 112 169 201 137 393), lower := (rows 259 70 37 56 112 32 64 128 256), losses := [] }

theorem u16633 : Upper (D 8) (R 8) [258,68,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16634 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 56 145 232 232 232 488), lower := (rows 259 70 37 56 145 32 64 128 256), losses := [] }

theorem u16634 : Upper (D 8) (R 8) [258,68,33,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16635 : Route 9 := (fun mask => (mask,id))

def c16635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16635 : Upper (D 8) (R 8) [258,68,33,48,136] 13 := by
  apply FastRouting.sound _ _ [258,68,33,48,136] 13 (by decide) (choices 1) [1,64,128] r16635 c16635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5997
  · exact u5998
  · exact u5999

def b16636 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 56 176 233 201 201 457), lower := (rows 259 70 37 56 176 32 64 128 256), losses := [] }

theorem u16636 : Upper (D 8) (R 8) [258,68,33,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16637 : Route 9 := (fun mask => (mask,id))

def c16637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16637 : Upper (D 8) (R 8) [258,68,33,48,192] 13 := by
  apply FastRouting.sound _ _ [258,68,33,48,192] 13 (by decide) (choices 1) [1,8,128] r16637 c16637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6000
  · exact u6001
  · exact u6002

def b16638 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 37 73 152 176 240 176 432), lower := (rows 259 70 37 73 152 32 64 128 256), losses := [] }

theorem u16638 : Upper (D 8) (R 8) [258,68,33,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16639 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 37 73 176 184 248 184 440), lower := (rows 259 70 37 73 176 32 64 128 256), losses := [] }

theorem u16639 : Upper (D 8) (R 8) [258,68,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16640 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 88 145 168 232 168 424), lower := (rows 259 70 37 88 145 32 64 128 256), losses := [] }

theorem u16640 : Upper (D 8) (R 8) [258,68,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16641 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 37 88 152 161 225 161 417), lower := (rows 259 70 37 88 152 32 64 128 256), losses := [] }

theorem u16641 : Upper (D 8) (R 8) [258,68,33,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16642 : Route 9 := (fun mask => (mask,id))

def c16642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16642 : Upper (D 8) (R 8) [258,68,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,68,33,80,160] 13 (by decide) (choices 1) [1,8,128] r16642 c16642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6003
  · exact u6004
  · exact u6005

def b16643 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 104 145 184 248 184 440), lower := (rows 259 70 37 104 145 32 64 128 256), losses := [] }

theorem u16643 : Upper (D 8) (R 8) [258,68,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16644 : Route 9 := (fun mask => (mask,id))

def c16644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16644 : Upper (D 8) (R 8) [258,68,33,96,136] 13 := by
  apply FastRouting.sound _ _ [258,68,33,96,136] 13 (by decide) (choices 1) [1,16,128] r16644 c16644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6006
  · exact u6007
  · exact u6008

def r16645 : Route 9 := (fun mask => (mask,id))

def c16645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16645 : Upper (D 8) (R 8) [258,68,33,96,160] 13 := by
  apply FastRouting.sound _ _ [258,68,33,96,160] 13 (by decide) (choices 1) [1,8,16,128] r16645 c16645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6009
  · exact u6010
  · exact u6011
  · exact u6012

def b16646 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 137 152 112 112 240 368), lower := (rows 259 70 37 137 152 32 64 128 256), losses := [] }

theorem u16646 : Upper (D 8) (R 8) [258,68,33,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16647 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 137 176 120 120 248 376), lower := (rows 259 70 37 137 176 32 64 128 256), losses := [] }

theorem u16647 : Upper (D 8) (R 8) [258,68,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16648 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 137 208 56 120 184 312), lower := (rows 259 70 37 137 208 32 64 128 256), losses := [] }

theorem u16648 : Upper (D 8) (R 8) [258,68,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16649 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 152 152 97 97 225 353), lower := (rows 259 70 37 152 152 32 64 128 256), losses := [] }

theorem u16649 : Upper (D 8) (R 8) [258,68,33,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16650 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 152 176 105 105 233 361), lower := (rows 259 70 37 152 176 32 64 128 256), losses := [] }

theorem u16650 : Upper (D 8) (R 8) [258,68,33,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16651 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 37 152 208 41 105 169 297), lower := (rows 259 70 37 152 208 32 64 128 256), losses := [] }

theorem u16651 : Upper (D 8) (R 8) [258,68,33,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16652 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 37 168 176 121 89 217 345), lower := (rows 259 70 37 168 176 32 64 128 256), losses := [] }

theorem u16652 : Upper (D 8) (R 8) [258,68,33,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16653 : Route 9 := (fun mask => (mask,id))

def c16653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16653 : Upper (D 8) (R 8) [258,68,33,160,192] 13 := by
  apply FastRouting.sound _ _ [258,68,33,160,192] 13 (by decide) (choices 1) [1,8,16] r16653 c16653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6013
  · exact u6014
  · exact u6015

def b16654 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 44 25 49 224 224 224 480), lower := (rows 259 70 44 25 49 32 64 128 256), losses := [] }

theorem u16654 : Upper (D 8) (R 8) [258,68,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16655 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 25 81 160 224 160 416), lower := (rows 259 70 44 25 81 32 64 128 256), losses := [] }

theorem u16655 : Upper (D 8) (R 8) [258,68,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16656 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 25 112 161 225 161 417), lower := (rows 259 70 44 25 112 32 64 128 256), losses := [] }

theorem u16656 : Upper (D 8) (R 8) [258,68,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16657 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 44 25 145 224 224 224 480), lower := (rows 259 70 44 25 145 32 64 128 256), losses := [] }

theorem u16657 : Upper (D 8) (R 8) [258,68,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16658 : Route 9 := (fun mask => (mask,id))

def c16658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16658 : Upper (D 8) (R 8) [258,68,40,17,160] 13 := by
  apply FastRouting.sound _ _ [258,68,40,17,160] 13 (by decide) (choices 1) [1,64,128] r16658 c16658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6016
  · exact u6017
  · exact u6018

def b16659 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 25 208 161 225 161 417), lower := (rows 259 70 44 25 208 32 64 128 256), losses := [] }

theorem u16659 : Upper (D 8) (R 8) [258,68,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16659 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16660 : Route 9 := (fun mask => (mask,id))

def c16660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16660 : Upper (D 8) (R 8) [258,68,40,129,33] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129,33] 13 (by decide) (choices 1) [16,64,128] r16660 c16660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6019
  · exact u6020
  · exact u6021

def b16661 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 44 137 81 176 240 176 432), lower := (rows 259 70 44 137 81 32 64 128 256), losses := [] }

theorem u16661 : Upper (D 8) (R 8) [258,68,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16662 : Route 9 := (fun mask => (mask,id))

def c16662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16662 : Upper (D 8) (R 8) [258,68,40,129,96] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129,96] 13 (by decide) (choices 1) [1,16,128] r16662 c16662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6022
  · exact u6023
  · exact u6024

def b16663 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 70 44 137 145 112 112 240 368), lower := (rows 259 70 44 137 145 32 64 128 256), losses := [] }

theorem u16663 : Upper (D 8) (R 8) [258,68,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16664 : Route 9 := (fun mask => (mask,id))

def c16664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16664 : Upper (D 8) (R 8) [258,68,40,129,160] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129,160] 13 (by decide) (choices 1) [1,16,64] r16664 c16664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6025
  · exact u6026
  · exact u6027

def r16665 : Route 9 := (fun mask => (mask,id))

def c16665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16665 : Upper (D 8) (R 8) [258,68,40,129,192] 13 := by
  apply FastRouting.sound _ _ [258,68,40,129,192] 13 (by decide) (choices 1) [1,16] r16665 c16665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6028
  · exact u6029

def r16666 : Route 9 := (fun mask => (mask,id))

def c16666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16666 : Upper (D 8) (R 8) [258,68,40,144,33] 13 := by
  apply FastRouting.sound _ _ [258,68,40,144,33] 13 (by decide) (choices 1) [1,64,128] r16666 c16666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6030
  · exact u6031
  · exact u6032

def b16667 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 44 152 81 161 225 161 417), lower := (rows 259 70 44 152 81 32 64 128 256), losses := [] }

theorem u16667 : Upper (D 8) (R 8) [258,68,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16668 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 44 152 112 161 225 161 417), lower := (rows 259 70 44 152 112 32 64 128 256), losses := [] }

theorem u16668 : Upper (D 8) (R 8) [258,68,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16669 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 152 145 97 97 225 353), lower := (rows 259 70 44 152 145 32 64 128 256), losses := [] }

theorem u16669 : Upper (D 8) (R 8) [258,68,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16670 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 44 152 176 97 97 225 353), lower := (rows 259 70 44 152 176 32 64 128 256), losses := [] }

theorem u16670 : Upper (D 8) (R 8) [258,68,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16671 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 152 208 33 97 161 289), lower := (rows 259 70 44 152 208 32 64 128 256), losses := [] }

theorem u16671 : Upper (D 8) (R 8) [258,68,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16672 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 133 25 56 224 224 224 480), lower := (rows 259 70 133 25 56 32 64 128 256), losses := [] }

theorem u16672 : Upper (D 8) (R 8) [258,68,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16673 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 133 25 88 160 224 160 416), lower := (rows 259 70 133 25 88 32 64 128 256), losses := [] }

theorem u16673 : Upper (D 8) (R 8) [258,68,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16674 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 25 112 168 232 168 424), lower := (rows 259 70 133 25 112 32 64 128 256), losses := [] }

theorem u16674 : Upper (D 8) (R 8) [258,68,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16675 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 70 133 25 152 96 96 224 352), lower := (rows 259 70 133 25 152 32 64 128 256), losses := [] }

theorem u16675 : Upper (D 8) (R 8) [258,68,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16676 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 25 176 104 104 232 360), lower := (rows 259 70 133 25 176 32 64 128 256), losses := [] }

theorem u16676 : Upper (D 8) (R 8) [258,68,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16677 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 25 208 40 104 168 296), lower := (rows 259 70 133 25 208 32 64 128 256), losses := [] }

theorem u16677 : Upper (D 8) (R 8) [258,68,129,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16678 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 259 70 133 41 56 240 240 240 496), lower := (rows 259 70 133 41 56 32 64 128 256), losses := [] }

theorem u16678 : Upper (D 8) (R 8) [258,68,129,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16679 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 133 41 88 176 240 176 432), lower := (rows 259 70 133 41 88 32 64 128 256), losses := [] }

theorem u16679 : Upper (D 8) (R 8) [258,68,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16679
end Delivery.IrregularNine14.P08
