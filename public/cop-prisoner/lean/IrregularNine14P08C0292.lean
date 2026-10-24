import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0107
import IrregularNine14P08C0108

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17520 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 69 168 49 242 210 210 466), lower := (rows 289 14 69 168 49 32 64 128 256), losses := [] }

theorem u17520 : Upper (D 8) (R 8) [288,12,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17521 : Route 9 := (fun mask => (mask,id))

def c17521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17521 : Upper (D 8) (R 8) [288,12,65,160,34] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,34] 13 (by decide) (choices 1) [1,16,64,128] r17521 c17521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6470
  · exact u6471
  · exact u6472
  · exact u6473

def b17522 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 168 81 178 242 178 434), lower := (rows 289 14 69 168 81 32 64 128 256), losses := [] }

theorem u17522 : Upper (D 8) (R 8) [288,12,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17523 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 82 177 241 177 433), lower := (rows 289 14 69 168 82 32 64 128 256), losses := [] }

theorem u17523 : Upper (D 8) (R 8) [288,12,65,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17524 : Route 9 := (fun mask => (mask,id))

def c17524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17524 : Upper (D 8) (R 8) [288,12,65,160,96] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,96] 13 (by decide) (choices 1) [1,2,16,128] r17524 c17524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6474
  · exact u6475
  · exact u6476
  · exact u6477

def r17525 : Route 9 := (fun mask => (mask,id))

def c17525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17525 : Upper (D 8) (R 8) [288,12,65,160,129] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,129] 13 (by decide) (choices 1) [2,16,64] r17525 c17525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6478
  · exact u6479
  · exact u6480

def b17526 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 146 113 113 241 369), lower := (rows 289 14 69 168 146 32 64 128 256), losses := [] }

theorem u17526 : Upper (D 8) (R 8) [288,12,65,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17527 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 69 168 176 115 83 211 339), lower := (rows 289 14 69 168 176 32 64 128 256), losses := [] }

theorem u17527 : Upper (D 8) (R 8) [288,12,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17528 : Route 9 := (fun mask => (mask,id))

def c17528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17528 : Upper (D 8) (R 8) [288,12,65,160,192] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,192] 13 (by decide) (choices 1) [1,2,16] r17528 c17528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6481
  · exact u6482
  · exact u6483

def b17529 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 50 177 241 177 433), lower := (rows 289 14 69 200 50 32 64 128 256), losses := [] }

theorem u17529 : Upper (D 8) (R 8) [288,12,65,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17530 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 145 50 114 178 306), lower := (rows 289 14 69 200 145 32 64 128 256), losses := [] }

theorem u17530 : Upper (D 8) (R 8) [288,12,65,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17531 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 146 49 113 177 305), lower := (rows 289 14 69 200 146 32 64 128 256), losses := [] }

theorem u17531 : Upper (D 8) (R 8) [288,12,65,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17532 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 176 51 115 179 307), lower := (rows 289 14 69 200 176 32 64 128 256), losses := [] }

theorem u17532 : Upper (D 8) (R 8) [288,12,65,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17533 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 88 145 161 225 161 417), lower := (rows 289 14 70 88 145 32 64 128 256), losses := [] }

theorem u17533 : Upper (D 8) (R 8) [288,12,66,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17534 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 88 176 161 225 161 417), lower := (rows 289 14 70 88 176 32 64 128 256), losses := [] }

theorem u17534 : Upper (D 8) (R 8) [288,12,66,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17535 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 104 145 177 241 177 433), lower := (rows 289 14 70 104 145 32 64 128 256), losses := [] }

theorem u17535 : Upper (D 8) (R 8) [288,12,66,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17536 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 104 176 177 209 145 401), lower := (rows 289 14 70 104 176 32 64 128 256), losses := [] }

theorem u17536 : Upper (D 8) (R 8) [288,12,66,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17537 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 70 152 49 225 225 225 481), lower := (rows 289 14 70 152 49 32 64 128 256), losses := [] }

theorem u17537 : Upper (D 8) (R 8) [288,12,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17538 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 152 81 161 225 161 417), lower := (rows 289 14 70 152 81 32 64 128 256), losses := [] }

theorem u17538 : Upper (D 8) (R 8) [288,12,66,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17539 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 152 112 161 225 161 417), lower := (rows 289 14 70 152 112 32 64 128 256), losses := [] }

theorem u17539 : Upper (D 8) (R 8) [288,12,66,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17540 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 70 152 145 97 97 225 353), lower := (rows 289 14 70 152 145 32 64 128 256), losses := [] }

theorem u17540 : Upper (D 8) (R 8) [288,12,66,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17541 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 70 152 176 97 97 225 353), lower := (rows 289 14 70 152 176 32 64 128 256), losses := [] }

theorem u17541 : Upper (D 8) (R 8) [288,12,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17542 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 152 208 33 97 161 289), lower := (rows 289 14 70 152 208 32 64 128 256), losses := [] }

theorem u17542 : Upper (D 8) (R 8) [288,12,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17543 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 70 168 49 241 209 209 465), lower := (rows 289 14 70 168 49 32 64 128 256), losses := [] }

theorem u17543 : Upper (D 8) (R 8) [288,12,66,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17544 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 168 81 177 241 177 433), lower := (rows 289 14 70 168 81 32 64 128 256), losses := [] }

theorem u17544 : Upper (D 8) (R 8) [288,12,66,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17545 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 168 112 177 209 145 401), lower := (rows 289 14 70 168 112 32 64 128 256), losses := [] }

theorem u17545 : Upper (D 8) (R 8) [288,12,66,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17546 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 70 168 145 113 113 241 369), lower := (rows 289 14 70 168 145 32 64 128 256), losses := [] }

theorem u17546 : Upper (D 8) (R 8) [288,12,66,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17547 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 70 168 176 113 81 209 337), lower := (rows 289 14 70 168 176 32 64 128 256), losses := [] }

theorem u17547 : Upper (D 8) (R 8) [288,12,66,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17548 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 168 208 49 113 177 305), lower := (rows 289 14 70 168 208 32 64 128 256), losses := [] }

theorem u17548 : Upper (D 8) (R 8) [288,12,66,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17549 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 200 145 49 113 177 305), lower := (rows 289 14 70 200 145 32 64 128 256), losses := [] }

theorem u17549 : Upper (D 8) (R 8) [288,12,66,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17550 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 200 176 49 113 177 305), lower := (rows 289 14 70 200 176 32 64 128 256), losses := [] }

theorem u17550 : Upper (D 8) (R 8) [288,12,66,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17551 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 84 104 50 161 193 129 385), lower := (rows 289 14 84 104 50 32 64 128 256), losses := [] }

theorem u17551 : Upper (D 8) (R 8) [288,12,80,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17552 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 145 163 227 163 419), lower := (rows 289 14 84 104 145 32 64 128 256), losses := [] }

theorem u17552 : Upper (D 8) (R 8) [288,12,80,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17553 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 146 161 225 161 417), lower := (rows 289 14 84 104 146 32 64 128 256), losses := [] }

theorem u17553 : Upper (D 8) (R 8) [288,12,80,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17554 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 176 163 195 131 387), lower := (rows 289 14 84 104 176 32 64 128 256), losses := [] }

theorem u17554 : Upper (D 8) (R 8) [288,12,80,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17555 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 84 168 49 227 195 195 451), lower := (rows 289 14 84 168 49 32 64 128 256), losses := [] }

theorem u17555 : Upper (D 8) (R 8) [288,12,80,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17556 : Route 9 := (fun mask => (mask,id))

def c17556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17556 : Upper (D 8) (R 8) [288,12,80,160,34] 13 := by
  apply FastRouting.sound _ _ [288,12,80,160,34] 13 (by decide) (choices 1) [1,64,128] r17556 c17556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6484
  · exact u6485
  · exact u6486

def b17557 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 81 163 227 163 419), lower := (rows 289 14 84 168 81 32 64 128 256), losses := [] }

theorem u17557 : Upper (D 8) (R 8) [288,12,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17558 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 82 161 225 161 417), lower := (rows 289 14 84 168 82 32 64 128 256), losses := [] }

theorem u17558 : Upper (D 8) (R 8) [288,12,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17559 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 112 163 195 131 387), lower := (rows 289 14 84 168 112 32 64 128 256), losses := [] }

theorem u17559 : Upper (D 8) (R 8) [288,12,80,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17560 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 84 168 145 99 99 227 355), lower := (rows 289 14 84 168 145 32 64 128 256), losses := [] }

theorem u17560 : Upper (D 8) (R 8) [288,12,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17561 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 84 168 146 97 97 225 353), lower := (rows 289 14 84 168 146 32 64 128 256), losses := [] }

theorem u17561 : Upper (D 8) (R 8) [288,12,80,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17562 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 84 168 176 99 67 195 323), lower := (rows 289 14 84 168 176 32 64 128 256), losses := [] }

theorem u17562 : Upper (D 8) (R 8) [288,12,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17563 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 208 35 99 163 291), lower := (rows 289 14 84 168 208 32 64 128 256), losses := [] }

theorem u17563 : Upper (D 8) (R 8) [288,12,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17564 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 50 161 225 161 417), lower := (rows 289 14 84 200 50 32 64 128 256), losses := [] }

theorem u17564 : Upper (D 8) (R 8) [288,12,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17565 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 145 35 99 163 291), lower := (rows 289 14 84 200 145 32 64 128 256), losses := [] }

theorem u17565 : Upper (D 8) (R 8) [288,12,80,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17566 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 84 200 146 33 97 161 289), lower := (rows 289 14 84 200 146 32 64 128 256), losses := [] }

theorem u17566 : Upper (D 8) (R 8) [288,12,80,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17567 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 176 35 99 163 291), lower := (rows 289 14 84 200 176 32 64 128 256), losses := [] }

theorem u17567 : Upper (D 8) (R 8) [288,12,80,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17568 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 100 104 145 179 211 147 403), lower := (rows 289 14 100 104 145 32 64 128 256), losses := [] }

theorem u17568 : Upper (D 8) (R 8) [288,12,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17569 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 100 104 146 177 209 145 401), lower := (rows 289 14 100 104 146 32 64 128 256), losses := [] }

theorem u17569 : Upper (D 8) (R 8) [288,12,96,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17570 : Route 9 := (fun mask => (mask,id))

def c17570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17570 : Upper (D 8) (R 8) [288,12,96,160,65] 13 := by
  apply FastRouting.sound _ _ [288,12,96,160,65] 13 (by decide) (choices 1) [1,2,16,128] r17570 c17570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6487
  · exact u6488
  · exact u6489
  · exact u6490

def b17571 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 168 82 177 209 145 401), lower := (rows 289 14 100 168 82 32 64 128 256), losses := [] }

theorem u17571 : Upper (D 8) (R 8) [288,12,96,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17572 : Route 9 := (fun mask => (mask,id))

def c17572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17572 : Upper (D 8) (R 8) [288,12,96,160,192] 13 := by
  apply FastRouting.sound _ _ [288,12,96,160,192] 13 (by decide) (choices 1) [1,2,16] r17572 c17572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6491
  · exact u6492
  · exact u6493

def b17573 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 50 177 209 145 401), lower := (rows 289 14 100 200 50 32 64 128 256), losses := [] }

theorem u17573 : Upper (D 8) (R 8) [288,12,96,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17574 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 145 51 115 179 307), lower := (rows 289 14 100 200 145 32 64 128 256), losses := [] }

theorem u17574 : Upper (D 8) (R 8) [288,12,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17575 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 146 49 113 177 305), lower := (rows 289 14 100 200 146 32 64 128 256), losses := [] }

theorem u17575 : Upper (D 8) (R 8) [288,12,96,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17576 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 176 51 83 147 275), lower := (rows 289 14 100 200 176 32 64 128 256), losses := [] }

theorem u17576 : Upper (D 8) (R 8) [288,12,96,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17577 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 196 200 50 49 113 177 305), lower := (rows 289 14 196 200 50 32 64 128 256), losses := [] }

theorem u17577 : Upper (D 8) (R 8) [288,12,192,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17578 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 73 84 184 216 152 408), lower := (rows 289 35 38 73 84 32 64 128 256), losses := [] }

theorem u17578 : Upper (D 8) (R 8) [288,33,34,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17579 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 38 73 148 248 216 216 472), lower := (rows 289 35 38 73 148 32 64 128 256), losses := [] }

theorem u17579 : Upper (D 8) (R 8) [288,33,34,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17579
end Delivery.IrregularNine14.P08
