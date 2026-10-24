import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0460
import IrregularNine14P06C0461
import IrregularNine14P06C0462
import IrregularNine14P06C0463

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40560 : Route 9 := (fun mask => (mask,id))

def c40560 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40560 : Upper (D 6) (R 6) [96,136,288,80,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80,6] 13 (by decide) (choices 1) [1,2,4] r40560 c40560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27641
  · exact u27642
  · exact u27643

def b40561 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 16, targets := 68 },{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 97 162 324 11 19 60 92 156 284), lower := (rows 97 162 324 11 19 32 64 128 256), losses := [] }

theorem u40561 : Upper (D 6) (R 6) [96,160,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40562 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 340, targets := 32 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 97 162 324 11 21 62 94 158 286), lower := (rows 97 162 324 11 21 32 64 128 256), losses := [] }

theorem u40562 : Upper (D 6) (R 6) [96,160,320,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40563 : Route 9 := (fun mask => (mask,id))

def c40563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40563 : Upper (D 6) (R 6) [96,160,320,3,6] 13 := by
  apply FastRouting.sound _ _ [96,160,320,3,6] 13 (by decide) (choices 1) [1,4,8,16] r40563 c40563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27644
  · exact u27645
  · exact u27646
  · exact u27647

def b40564 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 162 324 11 25 54 86 150 278), lower := (rows 97 162 324 11 25 32 64 128 256), losses := [] }

theorem u40564 : Upper (D 6) (R 6) [96,160,320,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40565 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 162 324 11 26 53 85 149 277), lower := (rows 97 162 324 11 26 32 64 128 256), losses := [] }

theorem u40565 : Upper (D 6) (R 6) [96,160,320,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40566 : Route 9 := (fun mask => (mask,id))

def c40566 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40566 : Upper (D 6) (R 6) [96,160,320,3,12] 13 := by
  apply FastRouting.sound _ _ [96,160,320,3,12] 13 (by decide) (choices 1) [1,2,4,16] r40566 c40566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27648
  · exact u27649
  · exact u27650
  · exact u27651

def b40567 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 162 324 14 22 57 89 153 281), lower := (rows 97 162 324 14 22 32 64 128 256), losses := [] }

theorem u40567 : Upper (D 6) (R 6) [96,160,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40568 : Route 9 := (fun mask => (mask,id))

def c40568 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40568 : Upper (D 6) (R 6) [96,160,320,6,9] 13 := by
  apply FastRouting.sound _ _ [96,160,320,6,9] 13 (by decide) (choices 1) [1,2,4,16] r40568 c40568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27652
  · exact u27653
  · exact u27654
  · exact u27655

def b40569 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 97 162 324 14 26 53 85 149 277), lower := (rows 97 162 324 14 26 32 64 128 256), losses := [] }

theorem u40569 : Upper (D 6) (R 6) [96,160,320,6,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40570 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 162 324 25 25 38 70 134 262), lower := (rows 97 162 324 25 25 32 64 128 256), losses := [] }

theorem u40570 : Upper (D 6) (R 6) [96,160,320,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40571 : Route 9 := (fun mask => (mask,id))

def c40571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40571 : Upper (D 6) (R 6) [96,160,320,17,10] 13 := by
  apply FastRouting.sound _ _ [96,160,320,17,10] 13 (by decide) (choices 1) [1,2,4] r40571 c40571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27656
  · exact u27657
  · exact u27658

def b40572 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 162 324 26 26 37 69 133 261), lower := (rows 97 162 324 26 26 32 64 128 256), losses := [] }

theorem u40572 : Upper (D 6) (R 6) [96,160,320,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40573 : Route 9 := (fun mask => (mask,id))

def c40573 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40573 : Upper (D 6) (R 6) [96,160,320,18,12] 13 := by
  apply FastRouting.sound _ _ [96,160,320,18,12] 13 (by decide) (choices 1) [1,2,4] r40573 c40573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27659
  · exact u27660
  · exact u27661

def b40574 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 15, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 14 496 480 480 480 480), lower := (rows 7 11 21 14 16 32 64 128 256), losses := [] }

theorem u40574 : Upper (D 6) (R 6) [6,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40575 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 42 500 484 484 484 484), lower := (rows 7 11 21 42 16 32 64 128 256), losses := [] }

theorem u40575 : Upper (D 6) (R 6) [6,9,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40576 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 44 498 482 482 482 482), lower := (rows 7 11 21 44 16 32 64 128 256), losses := [] }

theorem u40576 : Upper (D 6) (R 6) [6,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40577_6 : Upper (D 6) (R 6) [6,9,17,96,6] 13 :=
  permutation_upper _ _ _ [6,9,17,6,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27662

theorem m40577_34 : Upper (D 6) (R 6) [6,9,17,96,34] 13 :=
  permutation_upper _ _ _ [6,9,17,36,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27669

theorem m40577_36 : Upper (D 6) (R 6) [6,9,17,96,36] 13 :=
  permutation_upper _ _ _ [6,9,17,34,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27665

def r40577 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40577 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40577 : Upper (D 6) (R 6) [6,9,17,96] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96] 13 (by decide) (choices 2) [6,34,36,96,130,132,160,384] r40577 c40577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40577_6
  · exact m40577_34
  · exact m40577_36
  · exact u27673
  · exact u27674
  · exact u27675
  · exact u27676
  · exact u27677

def b40578 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 21 138 372 356 356 484 356), lower := (rows 7 11 21 138 16 32 64 128 256), losses := [] }

theorem u40578 : Upper (D 6) (R 6) [6,9,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40579 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 21 140 370 354 354 482 354), lower := (rows 7 11 21 140 16 32 64 128 256), losses := [] }

theorem u40579 : Upper (D 6) (R 6) [6,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40580_6 : Upper (D 6) (R 6) [6,9,17,160,6] 13 :=
  permutation_upper _ _ _ [6,9,17,6,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27663

theorem m40580_34 : Upper (D 6) (R 6) [6,9,17,160,34] 13 :=
  permutation_upper _ _ _ [6,9,17,36,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27670

theorem m40580_36 : Upper (D 6) (R 6) [6,9,17,160,36] 13 :=
  permutation_upper _ _ _ [6,9,17,34,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27666

theorem m40580_66 : Upper (D 6) (R 6) [6,9,17,160,66] 13 :=
  permutation_upper _ _ _ [6,9,17,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27671

theorem m40580_68 : Upper (D 6) (R 6) [6,9,17,160,68] 13 :=
  permutation_upper _ _ _ [6,9,17,34,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27667

theorem m40580_96 : Upper (D 6) (R 6) [6,9,17,160,96] 13 :=
  permutation_upper _ _ _ [6,9,17,96,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27676

theorem m40580_258 : Upper (D 6) (R 6) [6,9,17,160,258] 13 :=
  permutation_upper _ _ _ [6,9,17,132,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27679

theorem m40580_260 : Upper (D 6) (R 6) [6,9,17,160,260] 13 :=
  permutation_upper _ _ _ [6,9,17,130,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27678

def r40580 : Route 9 := (fun mask => (mask,id))

def c40580 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40580 : Upper (D 6) (R 6) [6,9,17,160] 13 := by
  apply FastRouting.sound _ _ [6,9,17,160] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40580 c40580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40580_6
  · exact m40580_34
  · exact m40580_36
  · exact m40580_66
  · exact m40580_68
  · exact m40580_96
  · exact m40580_258
  · exact m40580_260
  · exact u27680
  · exact u27681

theorem m40581_6 : Upper (D 6) (R 6) [6,9,17,384,6] 13 :=
  permutation_upper _ _ _ [6,9,17,6,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27664

theorem m40581_34 : Upper (D 6) (R 6) [6,9,17,384,34] 13 :=
  permutation_upper _ _ _ [6,9,17,36,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27672

theorem m40581_36 : Upper (D 6) (R 6) [6,9,17,384,36] 13 :=
  permutation_upper _ _ _ [6,9,17,34,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27668

theorem m40581_96 : Upper (D 6) (R 6) [6,9,17,384,96] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27677

def r40581 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40581 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40581 : Upper (D 6) (R 6) [6,9,17,384] 13 := by
  apply FastRouting.sound _ _ [6,9,17,384] 13 (by decide) (choices 2) [6,34,36,96] r40581 c40581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m40581_6
  · exact m40581_34
  · exact m40581_36
  · exact m40581_96

def b40582 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 14 496 496 496 496 496), lower := (rows 7 11 37 14 16 32 64 128 256), losses := [] }

theorem u40582 : Upper (D 6) (R 6) [6,9,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40583 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 26 500 484 484 484 484), lower := (rows 7 11 37 26 16 32 64 128 256), losses := [] }

theorem u40583 : Upper (D 6) (R 6) [6,9,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40584 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 28 498 482 482 482 482), lower := (rows 7 11 37 28 16 32 64 128 256), losses := [] }

theorem u40584 : Upper (D 6) (R 6) [6,9,33,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40585 : PairBound 9 := { available := 468, camps := [{ cop := 5, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 42 468 500 468 468 468), lower := (rows 7 11 37 42 16 32 64 128 256), losses := [] }

theorem u40585 : Upper (D 6) (R 6) [6,9,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40586 : PairBound 9 := { available := 466, camps := [{ cop := 5, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 44 466 498 466 466 466), lower := (rows 7 11 37 44 16 32 64 128 256), losses := [] }

theorem u40586 : Upper (D 6) (R 6) [6,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40587 : PairBound 9 := { available := 454, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 56 470 486 454 454 454), lower := (rows 7 11 37 56 16 32 64 128 256), losses := [] }

theorem u40587 : Upper (D 6) (R 6) [6,9,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40588 : PairBound 9 := { available := 500, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 74 500 500 500 500 500), lower := (rows 7 11 37 74 16 32 64 128 256), losses := [] }

theorem u40588 : Upper (D 6) (R 6) [6,9,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40589 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 76 498 498 498 498 498), lower := (rows 7 11 37 76 16 32 64 128 256), losses := [] }

theorem u40589 : Upper (D 6) (R 6) [6,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40590 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40590 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40590 : Upper (D 6) (R 6) [6,9,33,80] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r40590 c40590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27682
  · exact u27683
  · exact u27684
  · exact u27685
  · exact u27686
  · exact u27687
  · exact u27688
  · exact u27689
  · exact u27690
  · exact u27691
  · exact u27692

def b40591 : PairBound 9 := { available := 470, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 104 470 502 470 470 470), lower := (rows 7 11 37 104 16 32 64 128 256), losses := [] }

theorem u40591 : Upper (D 6) (R 6) [6,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40592 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 37 138 372 372 372 500 372), lower := (rows 7 11 37 138 16 32 64 128 256), losses := [] }

theorem u40592 : Upper (D 6) (R 6) [6,9,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40593 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 37 140 370 370 370 498 370), lower := (rows 7 11 37 140 16 32 64 128 256), losses := [] }

theorem u40593 : Upper (D 6) (R 6) [6,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40594 : Route 9 := (fun mask => (mask,id))

def c40594 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40594 : Upper (D 6) (R 6) [6,9,33,144] 13 := by
  apply FastRouting.sound _ _ [6,9,33,144] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40594 c40594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27693
  · exact u27694
  · exact u27695
  · exact u27696
  · exact u27697
  · exact u27698
  · exact u27699
  · exact u27700
  · exact u27701
  · exact u27702

def b40595 : PairBound 9 := { available := 342, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 168 342 374 342 470 342), lower := (rows 7 11 37 168 16 32 64 128 256), losses := [] }

theorem u40595 : Upper (D 6) (R 6) [6,9,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40596 : Route 9 := (fun mask => (mask,id))

def c40596 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40596 : Upper (D 6) (R 6) [6,9,33,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40596 c40596
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27703
  · exact u27704
  · exact u27705
  · exact u27706
  · exact u27707
  · exact u27708
  · exact u27709
  · exact u27710
  · exact u27711
  · exact u27712

def r40597 : Route 9 := (fun mask => (mask,id))

def c40597 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40597 : Upper (D 6) (R 6) [6,9,33,384] 13 := by
  apply FastRouting.sound _ _ [6,9,33,384] 13 (by decide) (choices 2) [6,34,36,66,68,96] r40597 c40597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27713
  · exact u27714
  · exact u27715
  · exact u27716
  · exact u27717
  · exact u27718

def b40598 : PairBound 9 := { available := 484, camps := [{ cop := 0, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 52 11 500 484 484 484 484), lower := (rows 7 11 52 11 16 32 64 128 256), losses := [] }

theorem u40598 : Upper (D 6) (R 6) [6,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40599 : PairBound 9 := { available := 482, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 52 13 498 482 482 482 482), lower := (rows 7 11 52 13 16 32 64 128 256), losses := [] }

theorem u40599 : Upper (D 6) (R 6) [6,9,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40600 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 52 14 497 481 481 481 481), lower := (rows 7 11 52 14 16 32 64 128 256), losses := [] }

theorem u40600 : Upper (D 6) (R 6) [6,9,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40601 : PairBound 9 := { available := 454, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 41 470 486 454 454 454), lower := (rows 7 11 52 41 16 32 64 128 256), losses := [] }

theorem u40601 : Upper (D 6) (R 6) [6,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40602 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 42 469 485 453 453 453), lower := (rows 7 11 52 42 16 32 64 128 256), losses := [] }

theorem u40602 : Upper (D 6) (R 6) [6,9,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40603 : PairBound 9 := { available := 451, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 52 44 467 483 451 451 451), lower := (rows 7 11 52 44 16 32 64 128 256), losses := [] }

theorem u40603 : Upper (D 6) (R 6) [6,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40604 : PairBound 9 := { available := 486, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 52 73 502 486 486 486 486), lower := (rows 7 11 52 73 16 32 64 128 256), losses := [] }

theorem u40604 : Upper (D 6) (R 6) [6,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40605 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40605 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40605 : Upper (D 6) (R 6) [6,9,48,66] 13 := by
  apply FastRouting.sound _ _ [6,9,48,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r40605 c40605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27719
  · exact u27720
  · exact u27721
  · exact u27722
  · exact u27723
  · exact u27724
  · exact u27725
  · exact u27726
  · exact u27727
  · exact u27728
  · exact u27729

def b40606 : PairBound 9 := { available := 483, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 52 76 499 483 483 483 483), lower := (rows 7 11 52 76 16 32 64 128 256), losses := [] }

theorem u40606 : Upper (D 6) (R 6) [6,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40607 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40607 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40607 : Upper (D 6) (R 6) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r40607 c40607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27730
  · exact u27731
  · exact u27732
  · exact u27733
  · exact u27734
  · exact u27735
  · exact u27736
  · exact u27737
  · exact u27738
  · exact u27739
  · exact u27740

def b40608 : PairBound 9 := { available := 358, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 52 137 374 358 358 486 358), lower := (rows 7 11 52 137 16 32 64 128 256), losses := [] }

theorem u40608 : Upper (D 6) (R 6) [6,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40609 : Route 9 := (fun mask => (mask,id))

def c40609 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40609 : Upper (D 6) (R 6) [6,9,48,130] 13 := by
  apply FastRouting.sound _ _ [6,9,48,130] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40609 c40609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27741
  · exact u27742
  · exact u27743
  · exact u27744
  · exact u27745
  · exact u27746
  · exact u27747
  · exact u27748
  · exact u27749
  · exact u27750

def b40610 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 52 140 371 355 355 483 355), lower := (rows 7 11 52 140 16 32 64 128 256), losses := [] }

theorem u40610 : Upper (D 6) (R 6) [6,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40611 : Route 9 := (fun mask => (mask,id))

def c40611 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40611 : Upper (D 6) (R 6) [6,9,48,160] 13 := by
  apply FastRouting.sound _ _ [6,9,48,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40611 c40611
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27751
  · exact u27752
  · exact u27753
  · exact u27754
  · exact u27755
  · exact u27756
  · exact u27757
  · exact u27758
  · exact u27759
  · exact u27760

def r40612 : Route 9 := (fun mask => (mask,id))

def c40612 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40612 : Upper (D 6) (R 6) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40612 c40612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27761
  · exact u27762
  · exact u27763
  · exact u27764
  · exact u27765
  · exact u27766
  · exact u27767
  · exact u27768
  · exact u27769
  · exact u27770
  · exact u27771
  · exact u27772
  · exact u27773
  · exact u27774
  · exact u27775

def r40613 : Route 9 := (fun mask => (mask,id))

def c40613 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40613 : Upper (D 6) (R 6) [6,9,48,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40613 c40613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27776
  · exact u27777
  · exact u27778
  · exact u27779
  · exact u27780
  · exact u27781
  · exact u27782
  · exact u27783
  · exact u27784
  · exact u27785

def b40614 : PairBound 9 := { available := 500, camps := [{ cop := 0, region := 10, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 100 11 500 500 500 500 500), lower := (rows 7 11 100 11 16 32 64 128 256), losses := [] }

theorem u40614 : Upper (D 6) (R 6) [6,9,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40615 : PairBound 9 := { available := 498, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 13 498 498 498 498 498), lower := (rows 7 11 100 13 16 32 64 128 256), losses := [] }

theorem u40615 : Upper (D 6) (R 6) [6,9,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40616 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 14 497 497 497 497 497), lower := (rows 7 11 100 14 16 32 64 128 256), losses := [] }

theorem u40616 : Upper (D 6) (R 6) [6,9,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40617 : PairBound 9 := { available := 486, camps := [{ cop := 3, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 7 11 100 25 502 486 486 486 486), lower := (rows 7 11 100 25 16 32 64 128 256), losses := [] }

theorem u40617 : Upper (D 6) (R 6) [6,9,96,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40618 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40618 : Upper (D 6) (R 6) [6,9,96,18] 13 := by
  apply FastRouting.sound _ _ [6,9,96,18] 13 (by decide) (choices 2) [5,33,36,96,129,132,160,384] r40618 c40618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u27786
  · exact u27787
  · exact u27788
  · exact u27789
  · exact u27790
  · exact u27791
  · exact u27792
  · exact u27793

def b40619 : PairBound 9 := { available := 483, camps := [{ cop := 3, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 11 100 28 499 483 483 483 483), lower := (rows 7 11 100 28 16 32 64 128 256), losses := [] }

theorem u40619 : Upper (D 6) (R 6) [6,9,96,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40619
end Delivery.IrregularNine14.P06
