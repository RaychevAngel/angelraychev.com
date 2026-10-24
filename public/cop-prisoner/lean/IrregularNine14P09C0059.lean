import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0010
import IrregularNine14P09C0011

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3540 : Route 9 := (fun mask => (mask,id))

def c3540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3540 : Upper (D 9) (R 9) [6,96,384,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,256] 13 (by decide) (choices 1) [1,8] r3540 c3540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u634
  · exact u635

def r3541 : Route 9 := (fun mask => (mask,id))

def c3541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3541 : Upper (D 9) (R 9) [6,96,384,160,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160,320,1] 13 (by decide) (choices 1) [1,8,16] r3541 c3541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u636
  · exact u637
  · exact u638

def b3542 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 98 388 168 336 40 81 145 273), lower := (rows 7 98 388 168 336 40 64 128 256), losses := [] }

theorem u3542 : Upper (D 9) (R 9) [6,96,384,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3542 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 7 98 388 168 336 48 73 137 265), lower := (rows 7 98 388 168 336 48 64 128 256), losses := [] }

theorem u3543 : Upper (D 9) (R 9) [6,96,384,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3543 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,6),(2,0),(3,5),(4,0),(4,6)], upper := (rows 35 7 28 73 176 96 448 384 384), lower := (rows 35 7 28 73 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 49 32 0 511 511), good := (rows 435 407 414 415 432 432 384 384 384) }] }

theorem u3544 : Upper (D 9) (R 9) [34,5,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(3,7)], upper := (rows 35 7 28 73 176 160 320 448 320), lower := (rows 35 7 28 73 176 160 64 128 256), losses := [] }

theorem u3545 : Upper (D 9) (R 9) [34,5,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3546 : Route 9 := (fun mask => (mask,id))

def c3546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3546 : Upper (D 9) (R 9) [34,5,24,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,160,256] 13 (by decide) (choices 1) [128,256] r3546 c3546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u639
  · exact u640

def b3547 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 28 73 208 160 352 416 288), lower := (rows 35 7 28 73 208 160 64 128 256), losses := [] }

theorem u3547 : Upper (D 9) (R 9) [34,5,24,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3547 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3548 : Route 9 := (fun mask => (mask,id))

def c3548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3548 : Upper (D 9) (R 9) [34,5,24,65,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,192,256] 13 (by decide) (choices 1) [32,128,256] r3548 c3548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u641
  · exact u642
  · exact u643

def b3549 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,6),(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 7 28 73 400 96 480 416 416), lower := (rows 35 7 28 73 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 59 32 0 161 289), good := (rows 435 407 30 415 400 432 0 128 256) }] }

theorem u3549 : Upper (D 9) (R 9) [34,5,24,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3549 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(3,7),(4,0)], upper := (rows 35 7 28 73 400 160 352 480 352), lower := (rows 35 7 28 73 400 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 176 0 128 256), good := (rows 35 7 63 9 432 160 0 160 256) }] }

theorem u3550 : Upper (D 9) (R 9) [34,5,24,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 28 104 208 33 448 384 384), lower := (rows 35 7 28 104 208 33 64 128 256), losses := [] }

theorem u3551 : Upper (D 9) (R 9) [34,5,24,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 28 104 208 160 321 385 257), lower := (rows 35 7 28 104 208 160 64 128 256), losses := [] }

theorem u3552 : Upper (D 9) (R 9) [34,5,24,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3552 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3553 : Route 9 := (fun mask => (mask,id))

def c3553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3553 : Upper (D 9) (R 9) [34,5,24,96,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,192,256] 13 (by decide) (choices 1) [1,128,256] r3553 c3553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u644
  · exact u645
  · exact u646

def b3554 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 28 104 400 33 448 448 448), lower := (rows 35 7 28 104 400 33 64 128 256), losses := [] }

theorem u3554 : Upper (D 9) (R 9) [34,5,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 35 7 28 104 400 96 449 385 385), lower := (rows 35 7 28 104 400 96 64 128 256), losses := [] }

theorem u3555 : Upper (D 9) (R 9) [34,5,24,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(3,7),(4,5)], upper := (rows 35 7 28 104 400 160 321 449 321), lower := (rows 35 7 28 104 400 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 176 0 128 256), good := (rows 35 7 63 40 432 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 16 176 64 128 0), good := (rows 35 7 63 104 176 160 64 160 0) }] }

theorem u3556 : Upper (D 9) (R 9) [34,5,24,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3556 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 7 28 200 336 33 480 416 416), lower := (rows 35 7 28 200 336 33 64 128 256), losses := [] }

theorem u3557 : Upper (D 9) (R 9) [34,5,24,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3557 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3558 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(4,7)], upper := (rows 35 7 28 200 336 160 353 417 289), lower := (rows 35 7 28 200 336 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 7 63 232 80 160 64 160 0) }] }

theorem u3558 : Upper (D 9) (R 9) [34,5,24,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3558 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3559 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 25 176 96 448 384 384), lower := (rows 35 7 76 25 176 96 64 128 256), losses := [] }

theorem u3559 : Upper (D 9) (R 9) [34,5,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 3, region := 324, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(3,7)], upper := (rows 35 7 76 25 176 160 320 448 320), lower := (rows 35 7 76 25 176 160 64 128 256), losses := [] }

theorem u3560 : Upper (D 9) (R 9) [34,5,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3560 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3561 : Route 9 := (fun mask => (mask,id))

def c3561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3561 : Upper (D 9) (R 9) [34,5,72,17,160,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,160,256] 13 (by decide) (choices 1) [128,256] r3561 c3561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u647
  · exact u648

def b3562 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 25 208 160 352 416 288), lower := (rows 35 7 76 25 208 160 64 128 256), losses := [] }

theorem u3562 : Upper (D 9) (R 9) [34,5,72,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3562 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3563 : Route 9 := (fun mask => (mask,id))

def c3563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3563 : Upper (D 9) (R 9) [34,5,72,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,192,256] 13 (by decide) (choices 1) [32,128,256] r3563 c3563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u649
  · exact u650
  · exact u651

def b3564 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 25 400 96 480 416 416), lower := (rows 35 7 76 25 400 96 64 128 256), losses := [] }

theorem u3564 : Upper (D 9) (R 9) [34,5,72,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3564 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3565 : Route 9 := (fun mask => (mask,id))

def c3565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3565 : Upper (D 9) (R 9) [34,5,72,17,384,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,384,128] 13 (by decide) (choices 1) [32,256] r3565 c3565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u652
  · exact u653

def b3566 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 56 145 96 448 384 384), lower := (rows 35 7 76 56 145 96 64 128 256), losses := [] }

theorem u3566 : Upper (D 9) (R 9) [34,5,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 364, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(3,0)], upper := (rows 35 7 76 56 145 160 320 448 320), lower := (rows 35 7 76 56 145 160 64 128 256), losses := [] }

theorem u3567 : Upper (D 9) (R 9) [34,5,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3568 : Route 9 := (fun mask => (mask,id))

def c3568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3568 : Upper (D 9) (R 9) [34,5,72,48,129,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,129,256] 13 (by decide) (choices 1) [128,256] r3568 c3568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u654
  · exact u655

def b3569 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 7 76 56 208 33 448 384 384), lower := (rows 35 7 76 56 208 33 64 128 256), losses := [] }

theorem u3569 : Upper (D 9) (R 9) [34,5,72,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 56 208 160 321 385 257), lower := (rows 35 7 76 56 208 160 64 128 256), losses := [] }

theorem u3570 : Upper (D 9) (R 9) [34,5,72,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3570 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3571 : Route 9 := (fun mask => (mask,id))

def c3571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3571 : Upper (D 9) (R 9) [34,5,72,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,48,192,256] 13 (by decide) (choices 1) [1,128,256] r3571 c3571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u656
  · exact u657
  · exact u658

def b3572 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 56 400 33 448 448 448), lower := (rows 35 7 76 56 400 33 64 128 256), losses := [] }

theorem u3572 : Upper (D 9) (R 9) [34,5,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3572 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 56 400 96 449 385 385), lower := (rows 35 7 76 56 400 96 64 128 256), losses := [] }

theorem u3573 : Upper (D 9) (R 9) [34,5,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3573 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 35 7 76 56 400 160 321 449 321), lower := (rows 35 7 76 56 400 160 64 128 256), losses := [] }

theorem u3574 : Upper (D 9) (R 9) [34,5,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3574 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 7 76 137 112 48 448 384 384), lower := (rows 35 7 76 137 112 48 64 128 256), losses := [] }

theorem u3575 : Upper (D 9) (R 9) [34,5,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3575 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,7)], upper := (rows 35 7 76 137 112 160 336 400 272), lower := (rows 35 7 76 137 112 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 184 0 144 272), good := (rows 35 7 47 169 432 160 0 160 256) }] }

theorem u3576 : Upper (D 9) (R 9) [34,5,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3576 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3577 : Route 9 := (fun mask => (mask,id))

def c3577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3577 : Upper (D 9) (R 9) [34,5,72,129,96,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,96,256] 13 (by decide) (choices 1) [16,128,256] r3577 c3577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u659
  · exact u660
  · exact u661

def b3578 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 324, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(3,5)], upper := (rows 35 7 76 137 176 48 320 448 320), lower := (rows 35 7 76 137 176 48 64 128 256), losses := [] }

theorem u3578 : Upper (D 9) (R 9) [34,5,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3578 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3579 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 137 176 96 336 400 272), lower := (rows 35 7 76 137 176 96 64 128 256), losses := [] }

theorem u3579 : Upper (D 9) (R 9) [34,5,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3580 : Route 9 := (fun mask => (mask,id))

def c3580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3580 : Upper (D 9) (R 9) [34,5,72,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,160,256] 13 (by decide) (choices 1) [16,256] r3580 c3580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u662
  · exact u663

def b3581 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 7 76 137 208 48 352 416 288), lower := (rows 35 7 76 137 208 48 64 128 256), losses := [] }

theorem u3581 : Upper (D 9) (R 9) [34,5,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3581 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3582 : Route 9 := (fun mask => (mask,id))

def c3582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3582 : Upper (D 9) (R 9) [34,5,72,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,192,256] 13 (by decide) (choices 1) [16,32,256] r3582 c3582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u664
  · exact u665
  · exact u666

def b3583 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 324, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(3,5)], upper := (rows 35 7 76 137 304 48 448 448 448), lower := (rows 35 7 76 137 304 48 64 128 256), losses := [] }

theorem u3583 : Upper (D 9) (R 9) [34,5,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3583 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3584 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 137 304 96 464 400 400), lower := (rows 35 7 76 137 304 96 64 128 256), losses := [] }

theorem u3584 : Upper (D 9) (R 9) [34,5,72,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,7)], upper := (rows 35 7 76 137 304 160 336 464 336), lower := (rows 35 7 76 137 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 35 7 47 169 304 160 0 160 256) }] }

theorem u3585 : Upper (D 9) (R 9) [34,5,72,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3585 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 35 7 76 137 304 288 208 208 464), lower := (rows 35 7 76 137 304 288 64 128 256), losses := [] }

theorem u3586 : Upper (D 9) (R 9) [34,5,72,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3586 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3587 : Route 9 := (fun mask => (mask,id))

def c3587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3587 : Upper (D 9) (R 9) [34,5,72,129,320,16] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,320,16] 13 (by decide) (choices 1) [32,128,256] r3587 c3587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u667
  · exact u668
  · exact u669

def b3588 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,7)], upper := (rows 35 7 76 137 336 160 368 432 304), lower := (rows 35 7 76 137 336 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 184 0 144 272), good := (rows 35 7 47 169 432 160 0 160 256) }] }

theorem u3588 : Upper (D 9) (R 9) [34,5,72,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3588 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3589 : Route 9 := (fun mask => (mask,id))

def c3589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3589 : Upper (D 9) (R 9) [34,5,72,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,320,256] 13 (by decide) (choices 1) [16,32,128] r3589 c3589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u670
  · exact u671
  · exact u672

def b3590 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(1,7),(2,0),(2,7),(4,0)], upper := (rows 35 7 76 137 400 48 352 480 352), lower := (rows 35 7 76 137 400 48 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 48 113 0 305), good := (rows 355 327 78 335 368 368 64 0 256) }] }

theorem u3590 : Upper (D 9) (R 9) [34,5,72,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3590 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 137 400 96 368 432 304), lower := (rows 35 7 76 137 400 96 64 128 256), losses := [] }

theorem u3591 : Upper (D 9) (R 9) [34,5,72,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3591 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3592 : Route 9 := (fun mask => (mask,id))

def c3592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3592 : Upper (D 9) (R 9) [34,5,72,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,384,256] 13 (by decide) (choices 1) [16,32] r3592 c3592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u673
  · exact u674

def b3593 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 7 76 152 112 33 448 384 384), lower := (rows 35 7 76 152 112 33 64 128 256), losses := [] }

theorem u3593 : Upper (D 9) (R 9) [34,5,72,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3593 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3594 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(4,0),(4,7)], upper := (rows 35 7 76 152 112 160 321 385 257), lower := (rows 35 7 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 22 124 184 112 160 64 160 256) },{ target := 8, region := (rows 5 6 4 8 20 168 64 128 0), good := (rows 35 23 127 184 112 160 64 160 0) }] }

theorem u3594 : Upper (D 9) (R 9) [34,5,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3594 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3595 : Route 9 := (fun mask => (mask,id))

def c3595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3595 : Upper (D 9) (R 9) [34,5,72,144,96,256] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,96,256] 13 (by decide) (choices 1) [1,128,256] r3595 c3595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u675
  · exact u676
  · exact u677

def b3596 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 35 7 76 152 273 96 480 416 416), lower := (rows 35 7 76 152 273 96 64 128 256), losses := [] }

theorem u3596 : Upper (D 9) (R 9) [34,5,72,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3596 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,7)], upper := (rows 35 7 76 152 273 160 352 480 352), lower := (rows 35 7 76 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 35 7 47 184 273 160 0 160 256) }] }

theorem u3597 : Upper (D 9) (R 9) [34,5,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3597 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(1,8),(2,0),(2,8),(3,0),(3,8)], upper := (rows 35 7 76 152 273 288 224 224 480), lower := (rows 35 7 76 152 273 288 64 128 256), losses := [{ target := 8, region := (rows 1 18 20 24 16 32 97 161 0), good := (rows 227 199 76 158 223 224 64 128 0) }] }

theorem u3598 : Upper (D 9) (R 9) [34,5,72,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3598 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3599 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 76 152 304 33 448 448 448), lower := (rows 35 7 76 152 304 33 64 128 256), losses := [] }

theorem u3599 : Upper (D 9) (R 9) [34,5,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3599 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P09
