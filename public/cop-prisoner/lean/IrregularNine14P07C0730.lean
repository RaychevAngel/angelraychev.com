import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0675
import IrregularNine14P07C0676
import IrregularNine14P07C0677
import IrregularNine14P07C0678
import IrregularNine14P07C0679

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43800 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 262 140 138 115 115 115 243 371), lower := (rows 97 262 140 138 16 32 64 128 256), losses := [] }

theorem u43800 : Upper (D 7) (R 7) [96,260,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43801 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 262 140 152 115 99 99 227 355), lower := (rows 97 262 140 152 16 32 64 128 256), losses := [] }

theorem u43801 : Upper (D 7) (R 7) [96,260,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43802 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 97 262 140 168 83 115 83 211 339), lower := (rows 97 262 140 168 16 32 64 128 256), losses := [] }

theorem u43802 : Upper (D 7) (R 7) [96,260,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43803 : Route 9 := (fun mask => (mask,id))

def c43803 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43803 : Upper (D 7) (R 7) [96,260,160,3] 13 := by
  apply FastRouting.sound _ _ [96,260,160,3] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43803 c43803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40528
  · exact u40529
  · exact u40530
  · exact u40531
  · exact u40532
  · exact u40533
  · exact u40534
  · exact u40535
  · exact u40536
  · exact u40537

theorem m43804_3 : Upper (D 7) (R 7) [96,260,160,17,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40529

def r43804 : Route 9 := (fun mask => (mask,id))

def c43804 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43804 : Upper (D 7) (R 7) [96,260,160,17] 13 := by
  apply FastRouting.sound _ _ [96,260,160,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43804 c43804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43804_3
  · exact u40538
  · exact u40539
  · exact u40540
  · exact u40541
  · exact u40542
  · exact u40543
  · exact u40544
  · exact u40545
  · exact u40546

theorem m43805_3 : Upper (D 7) (R 7) [96,260,160,18,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40530

theorem m43805_9 : Upper (D 7) (R 7) [96,260,160,18,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40539

def r43805 : Route 9 := (fun mask => (mask,id))

def c43805 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43805 : Upper (D 7) (R 7) [96,260,160,18] 13 := by
  apply FastRouting.sound _ _ [96,260,160,18] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43805 c43805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43805_3
  · exact m43805_9
  · exact u40547
  · exact u40548
  · exact u40549
  · exact u40550
  · exact u40551
  · exact u40552
  · exact u40553
  · exact u40554

def b43806 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 164 73 155 187 219 155 411), lower := (rows 97 262 164 73 16 32 64 128 256), losses := [] }

theorem u43806 : Upper (D 7) (R 7) [96,260,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43807_3 : Upper (D 7) (R 7) [96,260,160,66,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40532

theorem m43807_9 : Upper (D 7) (R 7) [96,260,160,66,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40541

theorem m43807_10 : Upper (D 7) (R 7) [96,260,160,66,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40549

def r43807 : Route 9 := (fun mask => (mask,id))

def c43807 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43807 : Upper (D 7) (R 7) [96,260,160,66] 13 := by
  apply FastRouting.sound _ _ [96,260,160,66] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43807 c43807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43807_3
  · exact m43807_9
  · exact m43807_10
  · exact u40558
  · exact u40559
  · exact u40560

theorem m43808_3 : Upper (D 7) (R 7) [96,260,160,80,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40533

theorem m43808_9 : Upper (D 7) (R 7) [96,260,160,80,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40542

theorem m43808_10 : Upper (D 7) (R 7) [96,260,160,80,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40550

def r43808 : Route 9 := (fun mask => (mask,id))

def c43808 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43808 : Upper (D 7) (R 7) [96,260,160,80] 13 := by
  apply FastRouting.sound _ _ [96,260,160,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43808 c43808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43808_3
  · exact m43808_9
  · exact m43808_10
  · exact u40561
  · exact u40562
  · exact u40563

theorem m43809_3 : Upper (D 7) (R 7) [96,260,160,129,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40534

theorem m43809_9 : Upper (D 7) (R 7) [96,260,160,129,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40543

theorem m43809_10 : Upper (D 7) (R 7) [96,260,160,129,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40551

theorem m43809_65 : Upper (D 7) (R 7) [96,260,160,129,65] 13 :=
  permutation_upper _ _ _ [96,260,160,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40555

theorem m43809_66 : Upper (D 7) (R 7) [96,260,160,129,66] 13 :=
  permutation_upper _ _ _ [96,260,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40558

theorem m43809_72 : Upper (D 7) (R 7) [96,260,160,129,72] 13 :=
  permutation_upper _ _ _ [96,260,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40561

def r43809 : Route 9 := (fun mask => (mask,id))

def c43809 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43809 : Upper (D 7) (R 7) [96,260,160,129] 13 := by
  apply FastRouting.sound _ _ [96,260,160,129] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43809 c43809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43809_3
  · exact m43809_9
  · exact m43809_10
  · exact m43809_65
  · exact m43809_66
  · exact m43809_72

theorem m43810_3 : Upper (D 7) (R 7) [96,260,160,130,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40535

theorem m43810_9 : Upper (D 7) (R 7) [96,260,160,130,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40544

theorem m43810_10 : Upper (D 7) (R 7) [96,260,160,130,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40552

theorem m43810_65 : Upper (D 7) (R 7) [96,260,160,130,65] 13 :=
  permutation_upper _ _ _ [96,260,160,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40556

theorem m43810_66 : Upper (D 7) (R 7) [96,260,160,130,66] 13 :=
  permutation_upper _ _ _ [96,260,160,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40559

theorem m43810_72 : Upper (D 7) (R 7) [96,260,160,130,72] 13 :=
  permutation_upper _ _ _ [96,260,160,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40562

def r43810 : Route 9 := (fun mask => (mask,id))

def c43810 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43810 : Upper (D 7) (R 7) [96,260,160,130] 13 := by
  apply FastRouting.sound _ _ [96,260,160,130] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43810 c43810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43810_3
  · exact m43810_9
  · exact m43810_10
  · exact m43810_65
  · exact m43810_66
  · exact m43810_72

theorem m43811_3 : Upper (D 7) (R 7) [96,260,160,144,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40536

theorem m43811_9 : Upper (D 7) (R 7) [96,260,160,144,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40545

theorem m43811_10 : Upper (D 7) (R 7) [96,260,160,144,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40553

theorem m43811_65 : Upper (D 7) (R 7) [96,260,160,144,65] 13 :=
  permutation_upper _ _ _ [96,260,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40557

theorem m43811_66 : Upper (D 7) (R 7) [96,260,160,144,66] 13 :=
  permutation_upper _ _ _ [96,260,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40560

theorem m43811_72 : Upper (D 7) (R 7) [96,260,160,144,72] 13 :=
  permutation_upper _ _ _ [96,260,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40563

def r43811 : Route 9 := (fun mask => (mask,id))

def c43811 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43811 : Upper (D 7) (R 7) [96,260,160,144] 13 := by
  apply FastRouting.sound _ _ [96,260,160,144] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43811 c43811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43811_3
  · exact m43811_9
  · exact m43811_10
  · exact m43811_65
  · exact m43811_66
  · exact m43811_72

theorem m43812_3 : Upper (D 7) (R 7) [96,260,160,192,3] 13 :=
  permutation_upper _ _ _ [96,260,160,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40537

theorem m43812_9 : Upper (D 7) (R 7) [96,260,160,192,9] 13 :=
  permutation_upper _ _ _ [96,260,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40546

theorem m43812_10 : Upper (D 7) (R 7) [96,260,160,192,10] 13 :=
  permutation_upper _ _ _ [96,260,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40554

def r43812 : Route 9 := (fun mask => (mask,id))

def c43812 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43812 : Upper (D 7) (R 7) [96,260,160,192] 13 := by
  apply FastRouting.sound _ _ [96,260,160,192] 13 (by decide) (choices 2) [3,9,10] r43812 c43812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43812_3
  · exact m43812_9
  · exact m43812_10

def b43813 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 290 7 11 220 252 220 220 476), lower := (rows 97 290 7 11 16 32 64 128 256), losses := [] }

theorem u43813 : Upper (D 7) (R 7) [96,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43814 : PairBound 9 := { available := 218, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 13 218 250 218 218 474), lower := (rows 97 290 7 13 16 32 64 128 256), losses := [] }

theorem u43814 : Upper (D 7) (R 7) [96,288,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43815 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 8, targets := 193 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 290 7 14 217 249 217 217 473), lower := (rows 97 290 7 14 16 32 64 128 256), losses := [] }

theorem u43815 : Upper (D 7) (R 7) [96,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43816_6 : Upper (D 7) (R 7) [96,288,3,17,6] 13 :=
  permutation_upper _ _ _ [96,288,3,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40574

def r43816 : Route 9 := (fun mask => (mask,id))

def c43816 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43816 : Upper (D 7) (R 7) [96,288,3,17] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192] r43816 c43816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43816_6
  · exact u40579
  · exact u40580
  · exact u40581
  · exact u40582
  · exact u40583
  · exact u40584
  · exact u40585
  · exact u40586
  · exact u40587

theorem m43817_5 : Upper (D 7) (R 7) [96,288,3,18,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40568

theorem m43817_9 : Upper (D 7) (R 7) [96,288,3,18,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40579

def r43817 : Route 9 := (fun mask => (mask,id))

def c43817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43817 : Upper (D 7) (R 7) [96,288,3,18] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r43817 c43817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43817_5
  · exact m43817_9
  · exact u40588
  · exact u40589
  · exact u40590
  · exact u40591
  · exact u40592
  · exact u40593
  · exact u40594
  · exact u40595

theorem m43818_3 : Upper (D 7) (R 7) [96,288,3,20,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40564

theorem m43818_9 : Upper (D 7) (R 7) [96,288,3,20,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40580

theorem m43818_10 : Upper (D 7) (R 7) [96,288,3,20,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40588

def r43818 : Route 9 := (fun mask => (mask,id))

def c43818 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43818 : Upper (D 7) (R 7) [96,288,3,20] 13 := by
  apply FastRouting.sound _ _ [96,288,3,20] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43818 c43818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43818_3
  · exact m43818_9
  · exact m43818_10
  · exact u40596
  · exact u40597
  · exact u40598
  · exact u40599
  · exact u40600
  · exact u40601
  · exact u40602

def b43819 : PairBound 9 := { available := 158, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 7 73 158 190 222 158 414), lower := (rows 97 290 7 73 16 32 64 128 256), losses := [] }

theorem u43819 : Upper (D 7) (R 7) [96,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43820_5 : Upper (D 7) (R 7) [96,288,3,66,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40569

theorem m43820_9 : Upper (D 7) (R 7) [96,288,3,66,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40581

theorem m43820_12 : Upper (D 7) (R 7) [96,288,3,66,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40597

def r43820 : Route 9 := (fun mask => (mask,id))

def c43820 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43820 : Upper (D 7) (R 7) [96,288,3,66] 13 := by
  apply FastRouting.sound _ _ [96,288,3,66] 13 (by decide) (choices 2) [5,9,12,129,132,136] r43820 c43820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43820_5
  · exact m43820_9
  · exact m43820_12
  · exact u40606
  · exact u40607
  · exact u40608

theorem m43821_3 : Upper (D 7) (R 7) [96,288,3,68,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40565

theorem m43821_9 : Upper (D 7) (R 7) [96,288,3,68,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40582

theorem m43821_10 : Upper (D 7) (R 7) [96,288,3,68,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40590

def r43821 : Route 9 := (fun mask => (mask,id))

def c43821 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43821 : Upper (D 7) (R 7) [96,288,3,68] 13 := by
  apply FastRouting.sound _ _ [96,288,3,68] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43821 c43821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43821_3
  · exact m43821_9
  · exact m43821_10
  · exact u40609
  · exact u40610
  · exact u40611

theorem m43822_3 : Upper (D 7) (R 7) [96,288,3,80,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40565

theorem m43822_5 : Upper (D 7) (R 7) [96,288,3,80,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40570

theorem m43822_6 : Upper (D 7) (R 7) [96,288,3,80,6] 13 :=
  permutation_upper _ _ _ [96,288,3,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40575

theorem m43822_9 : Upper (D 7) (R 7) [96,288,3,80,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40583

theorem m43822_10 : Upper (D 7) (R 7) [96,288,3,80,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40591

theorem m43822_12 : Upper (D 7) (R 7) [96,288,3,80,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40598

def r43822 : Route 9 := (fun mask => (mask,id))

def c43822 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43822 : Upper (D 7) (R 7) [96,288,3,80] 13 := by
  apply FastRouting.sound _ _ [96,288,3,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r43822 c43822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43822_3
  · exact m43822_5
  · exact m43822_6
  · exact m43822_9
  · exact m43822_10
  · exact m43822_12
  · exact u40612
  · exact u40613
  · exact u40614
  · exact u40615

theorem m43823_6 : Upper (D 7) (R 7) [96,288,3,129,6] 13 :=
  permutation_upper _ _ _ [96,288,3,6,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40576

theorem m43823_10 : Upper (D 7) (R 7) [96,288,3,129,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40592

theorem m43823_12 : Upper (D 7) (R 7) [96,288,3,129,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40599

theorem m43823_66 : Upper (D 7) (R 7) [96,288,3,129,66] 13 :=
  permutation_upper _ _ _ [96,288,3,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40606

theorem m43823_68 : Upper (D 7) (R 7) [96,288,3,129,68] 13 :=
  permutation_upper _ _ _ [96,288,3,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40609

theorem m43823_72 : Upper (D 7) (R 7) [96,288,3,129,72] 13 :=
  permutation_upper _ _ _ [96,288,3,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40612

def r43823 : Route 9 := (fun mask => (mask,id))

def c43823 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43823 : Upper (D 7) (R 7) [96,288,3,129] 13 := by
  apply FastRouting.sound _ _ [96,288,3,129] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192] r43823 c43823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43823_6
  · exact m43823_10
  · exact m43823_12
  · exact m43823_66
  · exact m43823_68
  · exact m43823_72
  · exact u40616
  · exact u40617
  · exact u40618
  · exact u40619

theorem m43824_5 : Upper (D 7) (R 7) [96,288,3,130,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40571

theorem m43824_9 : Upper (D 7) (R 7) [96,288,3,130,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40584

theorem m43824_12 : Upper (D 7) (R 7) [96,288,3,130,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40600

theorem m43824_65 : Upper (D 7) (R 7) [96,288,3,130,65] 13 :=
  permutation_upper _ _ _ [96,288,3,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40603

theorem m43824_68 : Upper (D 7) (R 7) [96,288,3,130,68] 13 :=
  permutation_upper _ _ _ [96,288,3,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40610

theorem m43824_72 : Upper (D 7) (R 7) [96,288,3,130,72] 13 :=
  permutation_upper _ _ _ [96,288,3,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40613

theorem m43824_129 : Upper (D 7) (R 7) [96,288,3,130,129] 13 :=
  permutation_upper _ _ _ [96,288,3,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40616

def r43824 : Route 9 := (fun mask => (mask,id))

def c43824 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43824 : Upper (D 7) (R 7) [96,288,3,130] 13 := by
  apply FastRouting.sound _ _ [96,288,3,130] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r43824 c43824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43824_5
  · exact m43824_9
  · exact m43824_12
  · exact m43824_65
  · exact m43824_68
  · exact m43824_72
  · exact m43824_129
  · exact u40620
  · exact u40621
  · exact u40622

theorem m43825_3 : Upper (D 7) (R 7) [96,288,3,132,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40566

theorem m43825_9 : Upper (D 7) (R 7) [96,288,3,132,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40585

theorem m43825_10 : Upper (D 7) (R 7) [96,288,3,132,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40593

theorem m43825_65 : Upper (D 7) (R 7) [96,288,3,132,65] 13 :=
  permutation_upper _ _ _ [96,288,3,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40604

theorem m43825_66 : Upper (D 7) (R 7) [96,288,3,132,66] 13 :=
  permutation_upper _ _ _ [96,288,3,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40607

theorem m43825_72 : Upper (D 7) (R 7) [96,288,3,132,72] 13 :=
  permutation_upper _ _ _ [96,288,3,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40614

theorem m43825_129 : Upper (D 7) (R 7) [96,288,3,132,129] 13 :=
  permutation_upper _ _ _ [96,288,3,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40617

theorem m43825_130 : Upper (D 7) (R 7) [96,288,3,132,130] 13 :=
  permutation_upper _ _ _ [96,288,3,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40620

def r43825 : Route 9 := (fun mask => (mask,id))

def c43825 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43825 : Upper (D 7) (R 7) [96,288,3,132] 13 := by
  apply FastRouting.sound _ _ [96,288,3,132] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43825 c43825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43825_3
  · exact m43825_9
  · exact m43825_10
  · exact m43825_65
  · exact m43825_66
  · exact m43825_72
  · exact m43825_129
  · exact m43825_130
  · exact u40623
  · exact u40624

theorem m43826_3 : Upper (D 7) (R 7) [96,288,3,144,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40566

theorem m43826_5 : Upper (D 7) (R 7) [96,288,3,144,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40572

theorem m43826_6 : Upper (D 7) (R 7) [96,288,3,144,6] 13 :=
  permutation_upper _ _ _ [96,288,3,6,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40577

theorem m43826_9 : Upper (D 7) (R 7) [96,288,3,144,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40586

theorem m43826_10 : Upper (D 7) (R 7) [96,288,3,144,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40594

theorem m43826_12 : Upper (D 7) (R 7) [96,288,3,144,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40601

theorem m43826_65 : Upper (D 7) (R 7) [96,288,3,144,65] 13 :=
  permutation_upper _ _ _ [96,288,3,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40605

theorem m43826_66 : Upper (D 7) (R 7) [96,288,3,144,66] 13 :=
  permutation_upper _ _ _ [96,288,3,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40608

theorem m43826_68 : Upper (D 7) (R 7) [96,288,3,144,68] 13 :=
  permutation_upper _ _ _ [96,288,3,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40611

theorem m43826_72 : Upper (D 7) (R 7) [96,288,3,144,72] 13 :=
  permutation_upper _ _ _ [96,288,3,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40615

theorem m43826_129 : Upper (D 7) (R 7) [96,288,3,144,129] 13 :=
  permutation_upper _ _ _ [96,288,3,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40618

theorem m43826_130 : Upper (D 7) (R 7) [96,288,3,144,130] 13 :=
  permutation_upper _ _ _ [96,288,3,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40621

theorem m43826_132 : Upper (D 7) (R 7) [96,288,3,144,132] 13 :=
  permutation_upper _ _ _ [96,288,3,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40623

def r43826 : Route 9 := (fun mask => (mask,id))

def c43826 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43826 : Upper (D 7) (R 7) [96,288,3,144] 13 := by
  apply FastRouting.sound _ _ [96,288,3,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,129,130,132,136,192] r43826 c43826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43826_3
  · exact m43826_5
  · exact m43826_6
  · exact m43826_9
  · exact m43826_10
  · exact m43826_12
  · exact m43826_65
  · exact m43826_66
  · exact m43826_68
  · exact m43826_72
  · exact m43826_129
  · exact m43826_130
  · exact m43826_132
  · exact u40625
  · exact u40626

theorem m43827_3 : Upper (D 7) (R 7) [96,288,3,192,3] 13 :=
  permutation_upper _ _ _ [96,288,3,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40567

theorem m43827_5 : Upper (D 7) (R 7) [96,288,3,192,5] 13 :=
  permutation_upper _ _ _ [96,288,3,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40573

theorem m43827_6 : Upper (D 7) (R 7) [96,288,3,192,6] 13 :=
  permutation_upper _ _ _ [96,288,3,6,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40578

theorem m43827_9 : Upper (D 7) (R 7) [96,288,3,192,9] 13 :=
  permutation_upper _ _ _ [96,288,3,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40587

theorem m43827_10 : Upper (D 7) (R 7) [96,288,3,192,10] 13 :=
  permutation_upper _ _ _ [96,288,3,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40595

theorem m43827_12 : Upper (D 7) (R 7) [96,288,3,192,12] 13 :=
  permutation_upper _ _ _ [96,288,3,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40602

theorem m43827_129 : Upper (D 7) (R 7) [96,288,3,192,129] 13 :=
  permutation_upper _ _ _ [96,288,3,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40619

theorem m43827_130 : Upper (D 7) (R 7) [96,288,3,192,130] 13 :=
  permutation_upper _ _ _ [96,288,3,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40622

theorem m43827_132 : Upper (D 7) (R 7) [96,288,3,192,132] 13 :=
  permutation_upper _ _ _ [96,288,3,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40624

theorem m43827_136 : Upper (D 7) (R 7) [96,288,3,192,136] 13 :=
  permutation_upper _ _ _ [96,288,3,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40626

def r43827 : Route 9 := (fun mask => (mask,id))

def c43827 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43827 : Upper (D 7) (R 7) [96,288,3,192] 13 := by
  apply FastRouting.sound _ _ [96,288,3,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r43827 c43827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43827_3
  · exact m43827_5
  · exact m43827_6
  · exact m43827_9
  · exact m43827_10
  · exact m43827_12
  · exact m43827_129
  · exact m43827_130
  · exact m43827_132
  · exact m43827_136

def b43828 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 13 210 242 210 210 466), lower := (rows 97 290 13 13 16 32 64 128 256), losses := [] }

theorem u43828 : Upper (D 7) (R 7) [96,288,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43829_3 : Upper (D 7) (R 7) [96,288,9,6,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40579

def r43829 : Route 9 := (fun mask => (mask,id))

def c43829 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43829 : Upper (D 7) (R 7) [96,288,9,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,6] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43829 c43829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43829_3
  · exact u40630
  · exact u40631
  · exact u40632
  · exact u40633
  · exact u40634

def b43830 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 25 214 230 198 198 454), lower := (rows 97 290 13 25 16 32 64 128 256), losses := [] }

theorem u43830 : Upper (D 7) (R 7) [96,288,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43831_3 : Upper (D 7) (R 7) [96,288,9,18,3] 13 :=
  permutation_upper _ _ _ [96,288,3,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40574

theorem m43831_5 : Upper (D 7) (R 7) [96,288,9,18,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40635

def r43831 : Route 9 := (fun mask => (mask,id))

def c43831 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43831 : Upper (D 7) (R 7) [96,288,9,18] 13 := by
  apply FastRouting.sound _ _ [96,288,9,18] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43831 c43831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43831_3
  · exact m43831_5
  · exact u40641
  · exact u40642
  · exact u40643
  · exact u40644
  · exact u40645
  · exact u40646
  · exact u40647
  · exact u40648

theorem m43832_3 : Upper (D 7) (R 7) [96,288,9,20,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40580

def r43832 : Route 9 := (fun mask => (mask,id))

def c43832 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43832 : Upper (D 7) (R 7) [96,288,9,20] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43832 c43832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43832_3
  · exact u40649
  · exact u40650
  · exact u40651
  · exact u40652
  · exact u40653

def b43833 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 73 150 182 214 150 406), lower := (rows 97 290 13 73 16 32 64 128 256), losses := [] }

theorem u43833 : Upper (D 7) (R 7) [96,288,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43834_3 : Upper (D 7) (R 7) [96,288,9,66,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40581

theorem m43834_5 : Upper (D 7) (R 7) [96,288,9,66,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40636

def r43834 : Route 9 := (fun mask => (mask,id))

def c43834 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43834 : Upper (D 7) (R 7) [96,288,9,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66] 13 (by decide) (choices 2) [3,5,6,129,130,132] r43834 c43834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43834_3
  · exact m43834_5
  · exact u40657
  · exact u40658
  · exact u40659
  · exact u40660

def b43835 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 290 13 76 147 179 211 147 403), lower := (rows 97 290 13 76 16 32 64 128 256), losses := [] }

theorem u43835 : Upper (D 7) (R 7) [96,288,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43836_3 : Upper (D 7) (R 7) [96,288,9,80,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40582

theorem m43836_5 : Upper (D 7) (R 7) [96,288,9,80,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40637

def r43836 : Route 9 := (fun mask => (mask,id))

def c43836 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43836 : Upper (D 7) (R 7) [96,288,9,80] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80] 13 (by decide) (choices 2) [3,5,6,129,130,132] r43836 c43836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43836_3
  · exact m43836_5
  · exact u40663
  · exact u40664
  · exact u40665
  · exact u40666

def b43837 : PairBound 9 := { available := 214, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 290 13 137 214 246 214 214 470), lower := (rows 97 290 13 137 16 32 64 128 256), losses := [] }

theorem u43837 : Upper (D 7) (R 7) [96,288,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43838_3 : Upper (D 7) (R 7) [96,288,9,130,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40584

theorem m43838_5 : Upper (D 7) (R 7) [96,288,9,130,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40638

def r43838 : Route 9 := (fun mask => (mask,id))

def c43838 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43838 : Upper (D 7) (R 7) [96,288,9,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43838 c43838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43838_3
  · exact m43838_5
  · exact u40673
  · exact u40674
  · exact u40675
  · exact u40676
  · exact u40677
  · exact u40678
  · exact u40679
  · exact u40680

theorem m43839_3 : Upper (D 7) (R 7) [96,288,9,132,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40586

def r43839 : Route 9 := (fun mask => (mask,id))

def c43839 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43839 : Upper (D 7) (R 7) [96,288,9,132] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43839 c43839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43839_3
  · exact u40681
  · exact u40682
  · exact u40683
  · exact u40684
  · exact u40685

theorem m43840_3 : Upper (D 7) (R 7) [96,288,9,144,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40585

theorem m43840_5 : Upper (D 7) (R 7) [96,288,9,144,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40639

def r43840 : Route 9 := (fun mask => (mask,id))

def c43840 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43840 : Upper (D 7) (R 7) [96,288,9,144] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43840 c43840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43840_3
  · exact m43840_5
  · exact u40686
  · exact u40687
  · exact u40688
  · exact u40689
  · exact u40690
  · exact u40691
  · exact u40692
  · exact u40693

theorem m43841_3 : Upper (D 7) (R 7) [96,288,9,192,3] 13 :=
  permutation_upper _ _ _ [96,288,3,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40587

theorem m43841_5 : Upper (D 7) (R 7) [96,288,9,192,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40640

def r43841 : Route 9 := (fun mask => (mask,id))

def c43841 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43841 : Upper (D 7) (R 7) [96,288,9,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192] 13 (by decide) (choices 2) [3,5,6,129,130,132] r43841 c43841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43841_3
  · exact m43841_5
  · exact u40694
  · exact u40695
  · exact u40696
  · exact u40697

def b43842 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 14 209 241 209 209 465), lower := (rows 97 290 14 14 16 32 64 128 256), losses := [] }

theorem u43842 : Upper (D 7) (R 7) [96,288,10,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43843_3 : Upper (D 7) (R 7) [96,288,10,17,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40568

theorem m43843_5 : Upper (D 7) (R 7) [96,288,10,17,5] 13 :=
  permutation_upper _ _ _ [96,288,9,17,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40635

theorem m43843_6 : Upper (D 7) (R 7) [96,288,10,17,6] 13 :=
  permutation_upper _ _ _ [96,288,9,18,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40641

theorem m43843_65 : Upper (D 7) (R 7) [96,288,10,17,65] 13 :=
  permutation_upper _ _ _ [96,288,9,65,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40654

theorem m43843_66 : Upper (D 7) (R 7) [96,288,10,17,66] 13 :=
  permutation_upper _ _ _ [96,288,9,66,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40657

theorem m43843_68 : Upper (D 7) (R 7) [96,288,10,17,68] 13 :=
  permutation_upper _ _ _ [96,288,9,80,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40663

theorem m43843_129 : Upper (D 7) (R 7) [96,288,10,17,129] 13 :=
  permutation_upper _ _ _ [96,288,9,129,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40667

theorem m43843_130 : Upper (D 7) (R 7) [96,288,10,17,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40673

theorem m43843_132 : Upper (D 7) (R 7) [96,288,10,17,132] 13 :=
  permutation_upper _ _ _ [96,288,9,144,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40686

theorem m43843_192 : Upper (D 7) (R 7) [96,288,10,17,192] 13 :=
  permutation_upper _ _ _ [96,288,9,192,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40694

def r43843 : Route 9 := (fun mask => (mask,id))

def c43843 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43843 : Upper (D 7) (R 7) [96,288,10,17] 13 := by
  apply FastRouting.sound _ _ [96,288,10,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43843 c43843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43843_3
  · exact m43843_5
  · exact m43843_6
  · exact m43843_65
  · exact m43843_66
  · exact m43843_68
  · exact m43843_129
  · exact m43843_130
  · exact m43843_132
  · exact m43843_192

def b43844 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 26 213 229 197 197 453), lower := (rows 97 290 14 26 16 32 64 128 256), losses := [] }

theorem u43844 : Upper (D 7) (R 7) [96,288,10,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43845_3 : Upper (D 7) (R 7) [96,288,10,20,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40588

def r43845 : Route 9 := (fun mask => (mask,id))

def c43845 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43845 : Upper (D 7) (R 7) [96,288,10,20] 13 := by
  apply FastRouting.sound _ _ [96,288,10,20] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43845 c43845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43845_3
  · exact u40704
  · exact u40705
  · exact u40706
  · exact u40707
  · exact u40708

def b43846 : PairBound 9 := { available := 151, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 14 73 151 183 215 151 407), lower := (rows 97 290 14 73 16 32 64 128 256), losses := [] }

theorem u43846 : Upper (D 7) (R 7) [96,288,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43847 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 74 149 181 213 149 405), lower := (rows 97 290 14 74 16 32 64 128 256), losses := [] }

theorem u43847 : Upper (D 7) (R 7) [96,288,10,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43848_3 : Upper (D 7) (R 7) [96,288,10,68,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40591

def r43848 : Route 9 := (fun mask => (mask,id))

def c43848 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43848 : Upper (D 7) (R 7) [96,288,10,68] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68] 13 (by decide) (choices 2) [3,129,130] r43848 c43848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43848_3
  · exact u40714
  · exact u40715

theorem m43849_3 : Upper (D 7) (R 7) [96,288,10,80,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40590

theorem m43849_5 : Upper (D 7) (R 7) [96,288,10,80,5] 13 :=
  permutation_upper _ _ _ [96,288,9,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40644

theorem m43849_6 : Upper (D 7) (R 7) [96,288,10,80,6] 13 :=
  permutation_upper _ _ _ [96,288,10,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40700

def r43849 : Route 9 := (fun mask => (mask,id))

def c43849 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43849 : Upper (D 7) (R 7) [96,288,10,80] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80] 13 (by decide) (choices 2) [3,5,6,129,130,132] r43849 c43849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43849_3
  · exact m43849_5
  · exact m43849_6
  · exact u40716
  · exact u40717
  · exact u40718

theorem m43850_3 : Upper (D 7) (R 7) [96,288,10,129,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40592

theorem m43850_5 : Upper (D 7) (R 7) [96,288,10,129,5] 13 :=
  permutation_upper _ _ _ [96,288,9,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40645

theorem m43850_6 : Upper (D 7) (R 7) [96,288,10,129,6] 13 :=
  permutation_upper _ _ _ [96,288,10,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40701

def r43850 : Route 9 := (fun mask => (mask,id))

def c43850 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43850 : Upper (D 7) (R 7) [96,288,10,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43850 c43850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43850_3
  · exact m43850_5
  · exact m43850_6
  · exact u40719
  · exact u40720
  · exact u40721
  · exact u40722
  · exact u40723
  · exact u40724
  · exact u40725

def b43851 : PairBound 9 := { available := 213, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 138 213 245 213 213 469), lower := (rows 97 290 14 138 16 32 64 128 256), losses := [] }

theorem u43851 : Upper (D 7) (R 7) [96,288,10,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43852_3 : Upper (D 7) (R 7) [96,288,10,132,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40594

def r43852 : Route 9 := (fun mask => (mask,id))

def c43852 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43852 : Upper (D 7) (R 7) [96,288,10,132] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43852 c43852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43852_3
  · exact u40730
  · exact u40731
  · exact u40732
  · exact u40733
  · exact u40734

theorem m43853_3 : Upper (D 7) (R 7) [96,288,10,144,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40593

theorem m43853_5 : Upper (D 7) (R 7) [96,288,10,144,5] 13 :=
  permutation_upper _ _ _ [96,288,9,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40647

theorem m43853_6 : Upper (D 7) (R 7) [96,288,10,144,6] 13 :=
  permutation_upper _ _ _ [96,288,10,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40702

def r43853 : Route 9 := (fun mask => (mask,id))

def c43853 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43853 : Upper (D 7) (R 7) [96,288,10,144] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r43853 c43853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43853_3
  · exact m43853_5
  · exact m43853_6
  · exact u40735
  · exact u40736
  · exact u40737
  · exact u40738
  · exact u40739
  · exact u40740
  · exact u40741

theorem m43854_3 : Upper (D 7) (R 7) [96,288,10,192,3] 13 :=
  permutation_upper _ _ _ [96,288,3,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40595

theorem m43854_5 : Upper (D 7) (R 7) [96,288,10,192,5] 13 :=
  permutation_upper _ _ _ [96,288,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40648

theorem m43854_6 : Upper (D 7) (R 7) [96,288,10,192,6] 13 :=
  permutation_upper _ _ _ [96,288,10,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40703

def r43854 : Route 9 := (fun mask => (mask,id))

def c43854 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43854 : Upper (D 7) (R 7) [96,288,10,192] 13 := by
  apply FastRouting.sound _ _ [96,288,10,192] 13 (by decide) (choices 2) [3,5,6,129,130,132] r43854 c43854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43854_3
  · exact m43854_5
  · exact m43854_6
  · exact u40742
  · exact u40743
  · exact u40744

theorem m43855_3 : Upper (D 7) (R 7) [96,288,17,66,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40569

theorem m43855_5 : Upper (D 7) (R 7) [96,288,17,66,5] 13 :=
  permutation_upper _ _ _ [96,288,9,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40627

theorem m43855_6 : Upper (D 7) (R 7) [96,288,17,66,6] 13 :=
  permutation_upper _ _ _ [96,288,9,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40631

theorem m43855_9 : Upper (D 7) (R 7) [96,288,17,66,9] 13 :=
  permutation_upper _ _ _ [96,288,9,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40636

theorem m43855_10 : Upper (D 7) (R 7) [96,288,17,66,10] 13 :=
  permutation_upper _ _ _ [96,288,9,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40643

theorem m43855_12 : Upper (D 7) (R 7) [96,288,17,66,12] 13 :=
  permutation_upper _ _ _ [96,288,9,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40650

theorem m43855_129 : Upper (D 7) (R 7) [96,288,17,66,129] 13 :=
  permutation_upper _ _ _ [96,288,9,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40668

theorem m43855_130 : Upper (D 7) (R 7) [96,288,17,66,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40675

theorem m43855_132 : Upper (D 7) (R 7) [96,288,17,66,132] 13 :=
  permutation_upper _ _ _ [96,288,9,132,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40682

theorem m43855_136 : Upper (D 7) (R 7) [96,288,17,66,136] 13 :=
  permutation_upper _ _ _ [96,288,9,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40688

def r43855 : Route 9 := (fun mask => (mask,id))

def c43855 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43855 : Upper (D 7) (R 7) [96,288,17,66] 13 := by
  apply FastRouting.sound _ _ [96,288,17,66] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r43855 c43855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43855_3
  · exact m43855_5
  · exact m43855_6
  · exact m43855_9
  · exact m43855_10
  · exact m43855_12
  · exact m43855_129
  · exact m43855_130
  · exact m43855_132
  · exact m43855_136

theorem m43856_3 : Upper (D 7) (R 7) [96,288,17,68,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40570

theorem m43856_9 : Upper (D 7) (R 7) [96,288,17,68,9] 13 :=
  permutation_upper _ _ _ [96,288,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40637

theorem m43856_10 : Upper (D 7) (R 7) [96,288,17,68,10] 13 :=
  permutation_upper _ _ _ [96,288,9,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40644

theorem m43856_129 : Upper (D 7) (R 7) [96,288,17,68,129] 13 :=
  permutation_upper _ _ _ [96,288,9,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40669

theorem m43856_130 : Upper (D 7) (R 7) [96,288,17,68,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40676

theorem m43856_136 : Upper (D 7) (R 7) [96,288,17,68,136] 13 :=
  permutation_upper _ _ _ [96,288,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40689

def r43856 : Route 9 := (fun mask => (mask,id))

def c43856 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43856 : Upper (D 7) (R 7) [96,288,17,68] 13 := by
  apply FastRouting.sound _ _ [96,288,17,68] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43856 c43856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43856_3
  · exact m43856_9
  · exact m43856_10
  · exact m43856_129
  · exact m43856_130
  · exact m43856_136

theorem m43857_6 : Upper (D 7) (R 7) [96,288,17,129,6] 13 :=
  permutation_upper _ _ _ [96,288,9,6,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40632

theorem m43857_10 : Upper (D 7) (R 7) [96,288,17,129,10] 13 :=
  permutation_upper _ _ _ [96,288,9,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40645

theorem m43857_12 : Upper (D 7) (R 7) [96,288,17,129,12] 13 :=
  permutation_upper _ _ _ [96,288,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40651

theorem m43857_66 : Upper (D 7) (R 7) [96,288,17,129,66] 13 :=
  permutation_upper _ _ _ [96,288,9,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40658

theorem m43857_68 : Upper (D 7) (R 7) [96,288,17,129,68] 13 :=
  permutation_upper _ _ _ [96,288,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40661

theorem m43857_72 : Upper (D 7) (R 7) [96,288,17,129,72] 13 :=
  permutation_upper _ _ _ [96,288,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40664

theorem m43857_130 : Upper (D 7) (R 7) [96,288,17,129,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40677

theorem m43857_132 : Upper (D 7) (R 7) [96,288,17,129,132] 13 :=
  permutation_upper _ _ _ [96,288,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40683

theorem m43857_136 : Upper (D 7) (R 7) [96,288,17,129,136] 13 :=
  permutation_upper _ _ _ [96,288,9,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40690

theorem m43857_192 : Upper (D 7) (R 7) [96,288,17,129,192] 13 :=
  permutation_upper _ _ _ [96,288,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40695

def r43857 : Route 9 := (fun mask => (mask,id))

def c43857 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43857 : Upper (D 7) (R 7) [96,288,17,129] 13 := by
  apply FastRouting.sound _ _ [96,288,17,129] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192] r43857 c43857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43857_6
  · exact m43857_10
  · exact m43857_12
  · exact m43857_66
  · exact m43857_68
  · exact m43857_72
  · exact m43857_130
  · exact m43857_132
  · exact m43857_136
  · exact m43857_192

theorem m43858_3 : Upper (D 7) (R 7) [96,288,17,130,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40571

theorem m43858_5 : Upper (D 7) (R 7) [96,288,17,130,5] 13 :=
  permutation_upper _ _ _ [96,288,9,5,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40628

theorem m43858_6 : Upper (D 7) (R 7) [96,288,17,130,6] 13 :=
  permutation_upper _ _ _ [96,288,9,6,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40633

theorem m43858_9 : Upper (D 7) (R 7) [96,288,17,130,9] 13 :=
  permutation_upper _ _ _ [96,288,9,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40638

theorem m43858_10 : Upper (D 7) (R 7) [96,288,17,130,10] 13 :=
  permutation_upper _ _ _ [96,288,9,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40646

theorem m43858_12 : Upper (D 7) (R 7) [96,288,17,130,12] 13 :=
  permutation_upper _ _ _ [96,288,9,20,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40652

theorem m43858_65 : Upper (D 7) (R 7) [96,288,17,130,65] 13 :=
  permutation_upper _ _ _ [96,288,9,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40655

theorem m43858_66 : Upper (D 7) (R 7) [96,288,17,130,66] 13 :=
  permutation_upper _ _ _ [96,288,9,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40659

theorem m43858_68 : Upper (D 7) (R 7) [96,288,17,130,68] 13 :=
  permutation_upper _ _ _ [96,288,9,68,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40662

theorem m43858_72 : Upper (D 7) (R 7) [96,288,17,130,72] 13 :=
  permutation_upper _ _ _ [96,288,9,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40665

theorem m43858_129 : Upper (D 7) (R 7) [96,288,17,130,129] 13 :=
  permutation_upper _ _ _ [96,288,9,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40670

theorem m43858_130 : Upper (D 7) (R 7) [96,288,17,130,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40678

theorem m43858_132 : Upper (D 7) (R 7) [96,288,17,130,132] 13 :=
  permutation_upper _ _ _ [96,288,9,132,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40684

theorem m43858_136 : Upper (D 7) (R 7) [96,288,17,130,136] 13 :=
  permutation_upper _ _ _ [96,288,9,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40691

theorem m43858_192 : Upper (D 7) (R 7) [96,288,17,130,192] 13 :=
  permutation_upper _ _ _ [96,288,9,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40696

def r43858 : Route 9 := (fun mask => (mask,id))

def c43858 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43858 : Upper (D 7) (R 7) [96,288,17,130] 13 := by
  apply FastRouting.sound _ _ [96,288,17,130] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,129,130,132,136,192] r43858 c43858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43858_3
  · exact m43858_5
  · exact m43858_6
  · exact m43858_9
  · exact m43858_10
  · exact m43858_12
  · exact m43858_65
  · exact m43858_66
  · exact m43858_68
  · exact m43858_72
  · exact m43858_129
  · exact m43858_130
  · exact m43858_132
  · exact m43858_136
  · exact m43858_192

theorem m43859_3 : Upper (D 7) (R 7) [96,288,17,132,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40572

theorem m43859_9 : Upper (D 7) (R 7) [96,288,17,132,9] 13 :=
  permutation_upper _ _ _ [96,288,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40639

theorem m43859_10 : Upper (D 7) (R 7) [96,288,17,132,10] 13 :=
  permutation_upper _ _ _ [96,288,9,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40647

theorem m43859_65 : Upper (D 7) (R 7) [96,288,17,132,65] 13 :=
  permutation_upper _ _ _ [96,288,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40656

theorem m43859_66 : Upper (D 7) (R 7) [96,288,17,132,66] 13 :=
  permutation_upper _ _ _ [96,288,9,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40660

theorem m43859_72 : Upper (D 7) (R 7) [96,288,17,132,72] 13 :=
  permutation_upper _ _ _ [96,288,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40666

theorem m43859_129 : Upper (D 7) (R 7) [96,288,17,132,129] 13 :=
  permutation_upper _ _ _ [96,288,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40671

theorem m43859_130 : Upper (D 7) (R 7) [96,288,17,132,130] 13 :=
  permutation_upper _ _ _ [96,288,9,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40679

theorem m43859_136 : Upper (D 7) (R 7) [96,288,17,132,136] 13 :=
  permutation_upper _ _ _ [96,288,9,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40692

theorem m43859_192 : Upper (D 7) (R 7) [96,288,17,132,192] 13 :=
  permutation_upper _ _ _ [96,288,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40697

def r43859 : Route 9 := (fun mask => (mask,id))

def c43859 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43859 : Upper (D 7) (R 7) [96,288,17,132] 13 := by
  apply FastRouting.sound _ _ [96,288,17,132] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43859 c43859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43859_3
  · exact m43859_9
  · exact m43859_10
  · exact m43859_65
  · exact m43859_66
  · exact m43859_72
  · exact m43859_129
  · exact m43859_130
  · exact m43859_136
  · exact m43859_192

#print axioms u43859
end Delivery.IrregularNine14.P07
