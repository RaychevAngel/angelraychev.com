import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0063

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16560 : Route 9 := (fun mask => (mask,id))

def c16560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16560 : Upper (D 7) (R 7) [12,96,3,160,258,16] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,258,16] 13 (by decide) (choices 1) [1,128] r16560 c16560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3785
  · exact u3786

def b16561 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 168 274 96 209 145 401), lower := (rows 13 98 7 168 274 96 64 128 256), losses := [] }

theorem u16561 : Upper (D 7) (R 7) [12,96,3,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16562 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 7 168 274 160 81 209 337), lower := (rows 13 98 7 168 274 160 64 128 256), losses := [] }

theorem u16562 : Upper (D 7) (R 7) [12,96,3,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16563 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 168 336 33 210 146 402), lower := (rows 13 98 7 168 336 33 64 128 256), losses := [] }

theorem u16563 : Upper (D 7) (R 7) [12,96,3,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16564 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 7 168 336 34 209 145 401), lower := (rows 13 98 7 168 336 34 64 128 256), losses := [] }

theorem u16564 : Upper (D 7) (R 7) [12,96,3,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16565 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 168 336 48 195 131 387), lower := (rows 13 98 7 168 336 48 64 128 256), losses := [] }

theorem u16565 : Upper (D 7) (R 7) [12,96,3,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16566 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 7 168 336 160 83 147 275), lower := (rows 13 98 7 168 336 160 64 128 256), losses := [] }

theorem u16566 : Upper (D 7) (R 7) [12,96,3,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16567 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 168 400 33 82 210 338), lower := (rows 13 98 7 168 400 33 64 128 256), losses := [] }

theorem u16567 : Upper (D 7) (R 7) [12,96,3,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16568 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 7 168 400 34 81 209 337), lower := (rows 13 98 7 168 400 34 64 128 256), losses := [] }

theorem u16568 : Upper (D 7) (R 7) [12,96,3,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16569 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 400 48 67 195 323), lower := (rows 13 98 7 168 400 48 64 128 256), losses := [] }

theorem u16569 : Upper (D 7) (R 7) [12,96,3,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16569 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16570 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 168 400 96 83 147 275), lower := (rows 13 98 7 168 400 96 64 128 256), losses := [] }

theorem u16570 : Upper (D 7) (R 7) [12,96,3,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16571 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 13 98 7 265 146 48 224 224 480), lower := (rows 13 98 7 265 146 48 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 48 114 178 306), good := (rows 13 480 461 265 496 496 64 128 256) }] }

theorem u16571 : Upper (D 7) (R 7) [12,96,3,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16571 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16572 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 265 146 96 240 176 432), lower := (rows 13 98 7 265 146 96 64 128 256), losses := [] }

theorem u16572 : Upper (D 7) (R 7) [12,96,3,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16573_16 : Upper (D 7) (R 7) [12,96,3,257,130,128,16] 13 :=
  permutation_upper _ _ _ [12,96,3,257,130,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3787

theorem m16573_32 : Upper (D 7) (R 7) [12,96,3,257,130,128,32] 13 :=
  permutation_upper _ _ _ [12,96,3,257,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3788

def r16573 : Route 9 := (fun mask => (mask,id))

def c16573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16573 : Upper (D 7) (R 7) [12,96,3,257,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,257,130,128] 13 (by decide) (choices 1) [16,32] r16573 c16573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16573_16
  · exact m16573_32

def b16574 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 265 176 34 208 208 464), lower := (rows 13 98 7 265 176 34 64 128 256), losses := [] }

theorem u16574 : Upper (D 7) (R 7) [12,96,3,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16575 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 265 176 48 194 194 450), lower := (rows 13 98 7 265 176 48 64 128 256), losses := [] }

theorem u16575 : Upper (D 7) (R 7) [12,96,3,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16575 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16576 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 265 176 96 210 146 402), lower := (rows 13 98 7 265 176 96 64 128 256), losses := [] }

theorem u16576 : Upper (D 7) (R 7) [12,96,3,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16577 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 265 176 160 82 210 338), lower := (rows 13 98 7 265 176 160 64 128 256), losses := [] }

theorem u16577 : Upper (D 7) (R 7) [12,96,3,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16578 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 98 7 280 49 34 192 192 448), lower := (rows 13 98 7 280 49 34 64 128 256), losses := [] }

theorem u16578 : Upper (D 7) (R 7) [12,96,3,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16579 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 49 96 194 130 386), lower := (rows 13 98 7 280 49 96 64 128 256), losses := [] }

theorem u16579 : Upper (D 7) (R 7) [12,96,3,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16580 : Route 9 := (fun mask => (mask,id))

def c16580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16580 : Upper (D 7) (R 7) [12,96,3,272,33,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,33,128] 13 (by decide) (choices 1) [2,128] r16580 c16580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3789
  · exact u3790

def b16581 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 13 98 7 280 145 34 224 224 480), lower := (rows 13 98 7 280 145 34 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 98 162 290), good := (rows 29 480 477 280 145 480 64 128 256) }] }

theorem u16581 : Upper (D 7) (R 7) [12,96,3,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16582 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 145 96 226 162 418), lower := (rows 13 98 7 280 145 96 64 128 256), losses := [] }

theorem u16582 : Upper (D 7) (R 7) [12,96,3,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16583_2 : Upper (D 7) (R 7) [12,96,3,272,129,128,2] 13 :=
  permutation_upper _ _ _ [12,96,3,272,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3791

theorem m16583_32 : Upper (D 7) (R 7) [12,96,3,272,129,128,32] 13 :=
  permutation_upper _ _ _ [12,96,3,272,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3792

def r16583 : Route 9 := (fun mask => (mask,id))

def c16583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16583 : Upper (D 7) (R 7) [12,96,3,272,129,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,129,128] 13 (by decide) (choices 1) [2,32] r16583 c16583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16583_2
  · exact m16583_32

def b16584 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 7 280 146 33 224 224 480), lower := (rows 13 98 7 280 146 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 493 480 485 280 472 481 64 128 256) }] }

theorem u16584 : Upper (D 7) (R 7) [12,96,3,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16585 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 146 96 225 161 417), lower := (rows 13 98 7 280 146 96 64 128 256), losses := [] }

theorem u16585 : Upper (D 7) (R 7) [12,96,3,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16586_1 : Upper (D 7) (R 7) [12,96,3,272,130,128,1] 13 :=
  permutation_upper _ _ _ [12,96,3,272,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3793

theorem m16586_32 : Upper (D 7) (R 7) [12,96,3,272,130,128,32] 13 :=
  permutation_upper _ _ _ [12,96,3,272,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3794

def r16586 : Route 9 := (fun mask => (mask,id))

def c16586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16586 : Upper (D 7) (R 7) [12,96,3,272,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,130,128] 13 (by decide) (choices 1) [1,32] r16586 c16586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16586_1
  · exact m16586_32

def r16587 : Route 9 := (fun mask => (mask,id))

def c16587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16587 : Upper (D 7) (R 7) [12,96,3,272,160,1] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,160,1] 13 (by decide) (choices 1) [2,128] r16587 c16587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3795
  · exact u3796

def r16588 : Route 9 := (fun mask => (mask,id))

def c16588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16588 : Upper (D 7) (R 7) [12,96,3,272,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,160,2] 13 (by decide) (choices 1) [1,128] r16588 c16588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3797
  · exact u3798

def b16589 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 176 96 195 131 387), lower := (rows 13 98 7 280 176 96 64 128 256), losses := [] }

theorem u16589 : Upper (D 7) (R 7) [12,96,3,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16590 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 280 176 160 67 195 323), lower := (rows 13 98 7 280 176 160 64 128 256), losses := [] }

theorem u16590 : Upper (D 7) (R 7) [12,96,3,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16591 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 296 81 34 208 144 400), lower := (rows 13 98 7 296 81 34 64 128 256), losses := [] }

theorem u16591 : Upper (D 7) (R 7) [12,96,3,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16592 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 296 81 48 194 130 386), lower := (rows 13 98 7 296 81 48 64 128 256), losses := [] }

theorem u16592 : Upper (D 7) (R 7) [12,96,3,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16592 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16593 : Route 9 := (fun mask => (mask,id))

def c16593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16593 : Upper (D 7) (R 7) [12,96,3,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,65,128] 13 (by decide) (choices 1) [2,16,128] r16593 c16593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3799
  · exact u3800
  · exact u3801

def b16594 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 296 145 34 208 208 464), lower := (rows 13 98 7 296 145 34 64 128 256), losses := [] }

theorem u16594 : Upper (D 7) (R 7) [12,96,3,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16595 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 98 7 296 145 48 194 194 450), lower := (rows 13 98 7 296 145 48 64 128 256), losses := [] }

theorem u16595 : Upper (D 7) (R 7) [12,96,3,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16595 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16596 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 296 145 96 210 146 402), lower := (rows 13 98 7 296 145 96 64 128 256), losses := [] }

theorem u16596 : Upper (D 7) (R 7) [12,96,3,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16597 : Route 9 := (fun mask => (mask,id))

def c16597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16597 : Upper (D 7) (R 7) [12,96,3,288,129,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,129,128] 13 (by decide) (choices 1) [2,16] r16597 c16597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3802
  · exact u3803

def b16598 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 296 146 33 208 208 464), lower := (rows 13 98 7 296 146 33 64 128 256), losses := [] }

theorem u16598 : Upper (D 7) (R 7) [12,96,3,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16599 : Route 9 := (fun mask => (mask,id))

def c16599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16599 : Upper (D 7) (R 7) [12,96,3,288,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,130,16] 13 (by decide) (choices 1) [1,128] r16599 c16599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3804
  · exact u3805

def b16600 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 296 146 96 209 145 401), lower := (rows 13 98 7 296 146 96 64 128 256), losses := [] }

theorem u16600 : Upper (D 7) (R 7) [12,96,3,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16601 : Route 9 := (fun mask => (mask,id))

def c16601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16601 : Upper (D 7) (R 7) [12,96,3,288,130,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,130,128] 13 (by decide) (choices 1) [1,16] r16601 c16601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3806
  · exact u3807

def b16602 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 296 208 33 210 146 402), lower := (rows 13 98 7 296 208 33 64 128 256), losses := [] }

theorem u16602 : Upper (D 7) (R 7) [12,96,3,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16603 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 7 296 208 34 209 145 401), lower := (rows 13 98 7 296 208 34 64 128 256), losses := [] }

theorem u16603 : Upper (D 7) (R 7) [12,96,3,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16604 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 296 208 48 195 131 387), lower := (rows 13 98 7 296 208 48 64 128 256), losses := [] }

theorem u16604 : Upper (D 7) (R 7) [12,96,3,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16604 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16605 : Route 9 := (fun mask => (mask,id))

def c16605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16605 : Upper (D 7) (R 7) [12,96,3,288,192,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,192,128] 13 (by decide) (choices 1) [1,2,16] r16605 c16605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3808
  · exact u3809
  · exact u3810

def b16606 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 98 7 392 49 34 208 208 464), lower := (rows 13 98 7 392 49 34 64 128 256), losses := [] }

theorem u16606 : Upper (D 7) (R 7) [12,96,3,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16607 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 13 98 7 392 49 48 194 194 450), lower := (rows 13 98 7 392 49 48 64 128 256), losses := [] }

theorem u16607 : Upper (D 7) (R 7) [12,96,3,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16608 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 392 49 96 210 146 402), lower := (rows 13 98 7 392 49 96 64 128 256), losses := [] }

theorem u16608 : Upper (D 7) (R 7) [12,96,3,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16609 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 70, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 392 49 160 82 210 338), lower := (rows 13 98 7 392 49 160 64 128 256), losses := [] }

theorem u16609 : Upper (D 7) (R 7) [12,96,3,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16610 : Route 9 := (fun mask => (mask,id))

def c16610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16610 : Upper (D 7) (R 7) [12,96,3,384,130,1] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,130,1] 13 (by decide) (choices 1) [16,32] r16610 c16610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3811
  · exact u3812

theorem m16611_1 : Upper (D 7) (R 7) [12,96,3,384,130,16,1] 13 :=
  permutation_upper _ _ _ [12,96,3,384,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3811

def r16611 : Route 9 := (fun mask => (mask,id))

def c16611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16611 : Upper (D 7) (R 7) [12,96,3,384,130,16] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,130,16] 13 (by decide) (choices 1) [1,32] r16611 c16611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16611_1
  · exact u3813

def b16612 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 392 146 96 113 177 305), lower := (rows 13 98 7 392 146 96 64 128 256), losses := [] }

theorem u16612 : Upper (D 7) (R 7) [12,96,3,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16613 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 7 392 176 33 82 210 338), lower := (rows 13 98 7 392 176 33 64 128 256), losses := [] }

theorem u16613 : Upper (D 7) (R 7) [12,96,3,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16614 : Route 9 := (fun mask => (mask,id))

def c16614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16614 : Upper (D 7) (R 7) [12,96,3,384,160,2] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,160,2] 13 (by decide) (choices 1) [1,16] r16614 c16614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3814
  · exact u3815

def b16615 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 392 176 48 67 195 323), lower := (rows 13 98 7 392 176 48 64 128 256), losses := [] }

theorem u16615 : Upper (D 7) (R 7) [12,96,3,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16615 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16616 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 392 176 96 83 147 275), lower := (rows 13 98 7 392 176 96 64 128 256), losses := [] }

theorem u16616 : Upper (D 7) (R 7) [12,96,3,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16617 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 21 41 146 34 448 448 448), lower := (rows 13 98 21 41 146 34 64 128 256), losses := [] }

theorem u16617 : Upper (D 7) (R 7) [12,96,17,33,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16618 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 41 146 96 450 386 386), lower := (rows 13 98 21 41 146 96 64 128 256), losses := [] }

theorem u16618 : Upper (D 7) (R 7) [12,96,17,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16619 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 98 21 41 146 160 322 450 322), lower := (rows 13 98 21 41 146 160 64 128 256), losses := [] }

theorem u16619 : Upper (D 7) (R 7) [12,96,17,33,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16619
end Delivery.IrregularNine14.P07
