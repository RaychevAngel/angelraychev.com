import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0099

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16560 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 112 181 213 149 405), lower := (rows 259 67 44 168 112 32 64 128 256), losses := [] }

theorem u16560 : Upper (D 8) (R 8) [258,65,40,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16561 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 148 113 113 241 369), lower := (rows 259 67 44 168 148 32 64 128 256), losses := [] }

theorem u16561 : Upper (D 8) (R 8) [258,65,40,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16562 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 176 117 85 213 341), lower := (rows 259 67 44 168 176 32 64 128 256), losses := [] }

theorem u16562 : Upper (D 8) (R 8) [258,65,40,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16563 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 208 53 117 181 309), lower := (rows 259 67 44 168 208 32 64 128 256), losses := [] }

theorem u16563 : Upper (D 8) (R 8) [258,65,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16564 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 200 145 52 116 180 308), lower := (rows 259 67 44 200 145 32 64 128 256), losses := [] }

theorem u16564 : Upper (D 8) (R 8) [258,65,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16565 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 200 148 49 113 177 305), lower := (rows 259 67 44 200 148 32 64 128 256), losses := [] }

theorem u16565 : Upper (D 8) (R 8) [258,65,40,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16566 : Route 9 := (fun mask => (mask,id))

def c16566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16566 : Upper (D 8) (R 8) [258,65,40,192,160] 13 := by
  apply FastRouting.sound _ _ [258,65,40,192,160] 13 (by decide) (choices 1) [1,4,16] r16566 c16566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5983
  · exact u5984
  · exact u5985

def b16567 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 69 140 176 56 120 184 312), lower := (rows 259 67 69 140 176 32 64 128 256), losses := [] }

theorem u16567 : Upper (D 8) (R 8) [258,65,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16568 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 76 137 148 48 112 176 304), lower := (rows 259 67 76 137 148 32 64 128 256), losses := [] }

theorem u16568 : Upper (D 8) (R 8) [258,65,72,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16569 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 76 137 176 52 116 180 308), lower := (rows 259 67 76 137 176 32 64 128 256), losses := [] }

theorem u16569 : Upper (D 8) (R 8) [258,65,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16570 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 76 140 176 49 113 177 305), lower := (rows 259 67 76 140 176 32 64 128 256), losses := [] }

theorem u16570 : Upper (D 8) (R 8) [258,65,72,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16571 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 76 152 145 36 100 164 292), lower := (rows 259 67 76 152 145 32 64 128 256), losses := [] }

theorem u16571 : Upper (D 8) (R 8) [258,65,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16572 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 76 152 148 33 97 161 289), lower := (rows 259 67 76 152 148 32 64 128 256), losses := [] }

theorem u16572 : Upper (D 8) (R 8) [258,65,72,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16573 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 76 152 176 37 101 165 293), lower := (rows 259 67 76 152 176 32 64 128 256), losses := [] }

theorem u16573 : Upper (D 8) (R 8) [258,65,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16574 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 76 168 145 52 116 180 308), lower := (rows 259 67 76 168 145 32 64 128 256), losses := [] }

theorem u16574 : Upper (D 8) (R 8) [258,65,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16575 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 76 168 148 49 113 177 305), lower := (rows 259 67 76 168 148 32 64 128 256), losses := [] }

theorem u16575 : Upper (D 8) (R 8) [258,65,72,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16576 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 67 76 168 176 53 117 181 309), lower := (rows 259 67 76 168 176 32 64 128 256), losses := [] }

theorem u16576 : Upper (D 8) (R 8) [258,65,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16577 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 100 137 148 56 120 184 312), lower := (rows 259 67 100 137 148 32 64 128 256), losses := [] }

theorem u16577 : Upper (D 8) (R 8) [258,65,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16578 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 100 137 152 52 116 180 308), lower := (rows 259 67 100 137 152 32 64 128 256), losses := [] }

theorem u16578 : Upper (D 8) (R 8) [258,65,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16579 : PairBound 9 := { available := 60, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 100 137 176 60 124 188 316), lower := (rows 259 67 100 137 176 32 64 128 256), losses := [] }

theorem u16579 : Upper (D 8) (R 8) [258,65,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16580 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 67 100 140 152 49 113 177 305), lower := (rows 259 67 100 140 152 32 64 128 256), losses := [] }

theorem u16580 : Upper (D 8) (R 8) [258,65,96,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16581 : Route 9 := (fun mask => (mask,id))

def c16581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16581 : Upper (D 8) (R 8) [258,65,96,132,160] 13 := by
  apply FastRouting.sound _ _ [258,65,96,132,160] 13 (by decide) (choices 1) [1,8,16] r16581 c16581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5986
  · exact u5987
  · exact u5988

def b16582 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 100 152 152 37 101 165 293), lower := (rows 259 67 100 152 152 32 64 128 256), losses := [] }

theorem u16582 : Upper (D 8) (R 8) [258,65,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16583 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 100 152 176 45 109 173 301), lower := (rows 259 67 100 152 176 32 64 128 256), losses := [] }

theorem u16583 : Upper (D 8) (R 8) [258,65,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16584 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 67 100 168 176 61 93 157 285), lower := (rows 259 67 100 168 176 32 64 128 256), losses := [] }

theorem u16584 : Upper (D 8) (R 8) [258,65,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16585 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 13 56 49 224 224 224 480), lower := (rows 259 70 13 56 49 32 64 128 256), losses := [] }

theorem u16585 : Upper (D 8) (R 8) [258,68,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16586 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 13 56 81 160 224 160 416), lower := (rows 259 70 13 56 81 32 64 128 256), losses := [] }

theorem u16586 : Upper (D 8) (R 8) [258,68,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16587 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 56 112 161 225 161 417), lower := (rows 259 70 13 56 112 32 64 128 256), losses := [] }

theorem u16587 : Upper (D 8) (R 8) [258,68,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16588 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 13 56 145 224 224 224 480), lower := (rows 259 70 13 56 145 32 64 128 256), losses := [] }

theorem u16588 : Upper (D 8) (R 8) [258,68,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16589 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 56 176 225 225 225 481), lower := (rows 259 70 13 56 176 32 64 128 256), losses := [] }

theorem u16589 : Upper (D 8) (R 8) [258,68,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16590 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 13 56 208 161 225 161 417), lower := (rows 259 70 13 56 208 32 64 128 256), losses := [] }

theorem u16590 : Upper (D 8) (R 8) [258,68,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16591 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 13 152 49 224 224 224 480), lower := (rows 259 70 13 152 49 32 64 128 256), losses := [] }

theorem u16591 : Upper (D 8) (R 8) [258,68,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16592 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 13 152 81 160 224 160 416), lower := (rows 259 70 13 152 81 32 64 128 256), losses := [] }

theorem u16592 : Upper (D 8) (R 8) [258,68,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16593 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 13 152 112 161 225 161 417), lower := (rows 259 70 13 152 112 32 64 128 256), losses := [] }

theorem u16593 : Upper (D 8) (R 8) [258,68,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16594 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 13 152 145 96 96 224 352), lower := (rows 259 70 13 152 145 32 64 128 256), losses := [] }

theorem u16594 : Upper (D 8) (R 8) [258,68,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16595 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 13 152 176 97 97 225 353), lower := (rows 259 70 13 152 176 32 64 128 256), losses := [] }

theorem u16595 : Upper (D 8) (R 8) [258,68,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16596 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 13 152 208 33 97 161 289), lower := (rows 259 70 13 152 208 32 64 128 256), losses := [] }

theorem u16596 : Upper (D 8) (R 8) [258,68,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16597 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 168 49 240 240 240 496), lower := (rows 259 70 13 168 49 32 64 128 256), losses := [] }

theorem u16597 : Upper (D 8) (R 8) [258,68,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16598 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 13 168 81 176 240 176 432), lower := (rows 259 70 13 168 81 32 64 128 256), losses := [] }

theorem u16598 : Upper (D 8) (R 8) [258,68,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16599 : Route 9 := (fun mask => (mask,id))

def c16599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16599 : Upper (D 8) (R 8) [258,68,9,160,96] 13 := by
  apply FastRouting.sound _ _ [258,68,9,160,96] 13 (by decide) (choices 1) [1,16,128] r16599 c16599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5989
  · exact u5990
  · exact u5991

def b16600 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 13 168 145 112 112 240 368), lower := (rows 259 70 13 168 145 32 64 128 256), losses := [] }

theorem u16600 : Upper (D 8) (R 8) [258,68,9,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16601 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 13 168 176 113 113 241 369), lower := (rows 259 70 13 168 176 32 64 128 256), losses := [] }

theorem u16601 : Upper (D 8) (R 8) [258,68,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16602 : Route 9 := (fun mask => (mask,id))

def c16602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16602 : Upper (D 8) (R 8) [258,68,9,160,192] 13 := by
  apply FastRouting.sound _ _ [258,68,9,160,192] 13 (by decide) (choices 1) [1,16] r16602 c16602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5992
  · exact u5993

def b16603 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 259 70 28 41 49 224 224 224 480), lower := (rows 259 70 28 41 49 32 64 128 256), losses := [] }

theorem u16603 : Upper (D 8) (R 8) [258,68,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16604 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 41 81 160 224 160 416), lower := (rows 259 70 28 41 81 32 64 128 256), losses := [] }

theorem u16604 : Upper (D 8) (R 8) [258,68,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16605 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 41 112 161 225 161 417), lower := (rows 259 70 28 41 112 32 64 128 256), losses := [] }

theorem u16605 : Upper (D 8) (R 8) [258,68,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16606 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 28 41 145 224 224 224 480), lower := (rows 259 70 28 41 145 32 64 128 256), losses := [] }

theorem u16606 : Upper (D 8) (R 8) [258,68,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16607 : Route 9 := (fun mask => (mask,id))

def c16607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16607 : Upper (D 8) (R 8) [258,68,24,33,160] 13 := by
  apply FastRouting.sound _ _ [258,68,24,33,160] 13 (by decide) (choices 1) [1,64,128] r16607 c16607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5994
  · exact u5995
  · exact u5996

def b16608 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 41 208 161 225 161 417), lower := (rows 259 70 28 41 208 32 64 128 256), losses := [] }

theorem u16608 : Upper (D 8) (R 8) [258,68,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16609 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 73 145 160 224 160 416), lower := (rows 259 70 28 73 145 32 64 128 256), losses := [] }

theorem u16609 : Upper (D 8) (R 8) [258,68,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16610 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 73 176 161 225 161 417), lower := (rows 259 70 28 73 176 32 64 128 256), losses := [] }

theorem u16610 : Upper (D 8) (R 8) [258,68,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16611 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 104 145 161 225 161 417), lower := (rows 259 70 28 104 145 32 64 128 256), losses := [] }

theorem u16611 : Upper (D 8) (R 8) [258,68,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16612 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 104 176 161 225 161 417), lower := (rows 259 70 28 104 176 32 64 128 256), losses := [] }

theorem u16612 : Upper (D 8) (R 8) [258,68,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16613 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 70 28 137 145 96 96 224 352), lower := (rows 259 70 28 137 145 32 64 128 256), losses := [] }

theorem u16613 : Upper (D 8) (R 8) [258,68,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16614 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 28 137 176 97 97 225 353), lower := (rows 259 70 28 137 176 32 64 128 256), losses := [] }

theorem u16614 : Upper (D 8) (R 8) [258,68,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16615 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 137 208 33 97 161 289), lower := (rows 259 70 28 137 208 32 64 128 256), losses := [] }

theorem u16615 : Upper (D 8) (R 8) [258,68,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16616 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 28 168 176 97 97 225 353), lower := (rows 259 70 28 168 176 32 64 128 256), losses := [] }

theorem u16616 : Upper (D 8) (R 8) [258,68,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16617 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 28 168 208 33 97 161 289), lower := (rows 259 70 28 168 208 32 64 128 256), losses := [] }

theorem u16617 : Upper (D 8) (R 8) [258,68,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16618 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 259 70 37 25 56 224 224 224 480), lower := (rows 259 70 37 25 56 32 64 128 256), losses := [] }

theorem u16618 : Upper (D 8) (R 8) [258,68,33,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16619 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 37 25 88 160 224 160 416), lower := (rows 259 70 37 25 88 32 64 128 256), losses := [] }

theorem u16619 : Upper (D 8) (R 8) [258,68,33,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16619
end Delivery.IrregularNine14.P08
