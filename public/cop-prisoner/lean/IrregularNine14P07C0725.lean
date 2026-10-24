import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0658
import IrregularNine14P07C0659
import IrregularNine14P07C0660
import IrregularNine14P07C0661
import IrregularNine14P07C0662
import IrregularNine14P07C0663
import IrregularNine14P07C0664

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43500_3 : Upper (D 7) (R 7) [36,320,129,192,3] 13 :=
  permutation_upper _ _ _ [36,320,129,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39533

theorem m43500_9 : Upper (D 7) (R 7) [36,320,129,192,9] 13 :=
  permutation_upper _ _ _ [36,320,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39543

theorem m43500_10 : Upper (D 7) (R 7) [36,320,129,192,10] 13 :=
  permutation_upper _ _ _ [36,320,129,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39556

theorem m43500_33 : Upper (D 7) (R 7) [36,320,129,192,33] 13 :=
  permutation_upper _ _ _ [36,320,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39560

theorem m43500_34 : Upper (D 7) (R 7) [36,320,129,192,34] 13 :=
  permutation_upper _ _ _ [36,320,129,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39567

theorem m43500_40 : Upper (D 7) (R 7) [36,320,129,192,40] 13 :=
  permutation_upper _ _ _ [36,320,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39574

def r43500 : Route 9 := (fun mask => (mask,id))

def c43500 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43500 : Upper (D 7) (R 7) [36,320,129,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43500 c43500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43500_3
  · exact m43500_9
  · exact m43500_10
  · exact m43500_33
  · exact m43500_34
  · exact m43500_40

def r43501 : Route 9 := (fun mask => (mask,id))

def c43501 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43501 : Upper (D 7) (R 7) [36,320,130,3] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43501 c43501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39587
  · exact u39588
  · exact u39589
  · exact u39590
  · exact u39591
  · exact u39592
  · exact u39593
  · exact u39594
  · exact u39595
  · exact u39596

theorem m43502_3 : Upper (D 7) (R 7) [36,320,130,17,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39587

def r43502 : Route 9 := (fun mask => (mask,id))

def c43502 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43502 : Upper (D 7) (R 7) [36,320,130,17] 13 := by
  apply FastRouting.sound _ _ [36,320,130,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r43502 c43502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43502_3
  · exact u39597
  · exact u39598
  · exact u39599
  · exact u39600
  · exact u39601
  · exact u39602
  · exact u39603
  · exact u39604
  · exact u39605
  · exact u39606
  · exact u39607
  · exact u39608
  · exact u39609
  · exact u39610

theorem m43503_9 : Upper (D 7) (R 7) [36,320,130,18,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39598

def r43503 : Route 9 := (fun mask => (mask,id))

def c43503 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43503 : Upper (D 7) (R 7) [36,320,130,18] 13 := by
  apply FastRouting.sound _ _ [36,320,130,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43503 c43503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43503_9
  · exact u39611
  · exact u39612
  · exact u39613
  · exact u39614
  · exact u39615
  · exact u39616
  · exact u39617
  · exact u39618
  · exact u39619

def b43504 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 134 41 219 251 219 219 475), lower := (rows 37 322 134 41 16 32 64 128 256), losses := [] }

theorem u43504 : Upper (D 7) (R 7) [36,320,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43505_9 : Upper (D 7) (R 7) [36,320,130,34,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39600

def r43505 : Route 9 := (fun mask => (mask,id))

def c43505 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43505 : Upper (D 7) (R 7) [36,320,130,34] 13 := by
  apply FastRouting.sound _ _ [36,320,130,34] 13 (by decide) (choices 2) [9,65,72,129,136,192] r43505 c43505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43505_9
  · exact u39625
  · exact u39626
  · exact u39627
  · exact u39628
  · exact u39629

theorem m43506_3 : Upper (D 7) (R 7) [36,320,130,48,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39589

theorem m43506_9 : Upper (D 7) (R 7) [36,320,130,48,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39601

theorem m43506_10 : Upper (D 7) (R 7) [36,320,130,48,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39612

def r43506 : Route 9 := (fun mask => (mask,id))

def c43506 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43506 : Upper (D 7) (R 7) [36,320,130,48] 13 := by
  apply FastRouting.sound _ _ [36,320,130,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43506 c43506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43506_3
  · exact m43506_9
  · exact m43506_10
  · exact u39630
  · exact u39631
  · exact u39632
  · exact u39633
  · exact u39634
  · exact u39635
  · exact u39636

theorem m43507_3 : Upper (D 7) (R 7) [36,320,130,65,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39590

theorem m43507_9 : Upper (D 7) (R 7) [36,320,130,65,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39602

theorem m43507_10 : Upper (D 7) (R 7) [36,320,130,65,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39613

theorem m43507_33 : Upper (D 7) (R 7) [36,320,130,65,33] 13 :=
  permutation_upper _ _ _ [36,320,130,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39620

theorem m43507_34 : Upper (D 7) (R 7) [36,320,130,65,34] 13 :=
  permutation_upper _ _ _ [36,320,130,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39625

theorem m43507_40 : Upper (D 7) (R 7) [36,320,130,65,40] 13 :=
  permutation_upper _ _ _ [36,320,130,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39630

def r43507 : Route 9 := (fun mask => (mask,id))

def c43507 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43507 : Upper (D 7) (R 7) [36,320,130,65] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43507 c43507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43507_3
  · exact m43507_9
  · exact m43507_10
  · exact m43507_33
  · exact m43507_34
  · exact m43507_40
  · exact u39637
  · exact u39638
  · exact u39639
  · exact u39640

def b43508 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 134 74 185 185 249 185 441), lower := (rows 37 322 134 74 16 32 64 128 256), losses := [] }

theorem u43508 : Upper (D 7) (R 7) [36,320,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43509_3 : Upper (D 7) (R 7) [36,320,130,80,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39591

theorem m43509_9 : Upper (D 7) (R 7) [36,320,130,80,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39604

theorem m43509_10 : Upper (D 7) (R 7) [36,320,130,80,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39614

theorem m43509_33 : Upper (D 7) (R 7) [36,320,130,80,33] 13 :=
  permutation_upper _ _ _ [36,320,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39621

theorem m43509_34 : Upper (D 7) (R 7) [36,320,130,80,34] 13 :=
  permutation_upper _ _ _ [36,320,130,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39626

theorem m43509_40 : Upper (D 7) (R 7) [36,320,130,80,40] 13 :=
  permutation_upper _ _ _ [36,320,130,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39632

def r43509 : Route 9 := (fun mask => (mask,id))

def c43509 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43509 : Upper (D 7) (R 7) [36,320,130,80] 13 := by
  apply FastRouting.sound _ _ [36,320,130,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43509 c43509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43509_3
  · exact m43509_9
  · exact m43509_10
  · exact m43509_33
  · exact m43509_34
  · exact m43509_40
  · exact u39644
  · exact u39645
  · exact u39646
  · exact u39647

theorem m43510_3 : Upper (D 7) (R 7) [36,320,130,96,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39592

theorem m43510_9 : Upper (D 7) (R 7) [36,320,130,96,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39605

theorem m43510_10 : Upper (D 7) (R 7) [36,320,130,96,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39615

def r43510 : Route 9 := (fun mask => (mask,id))

def c43510 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43510 : Upper (D 7) (R 7) [36,320,130,96] 13 := by
  apply FastRouting.sound _ _ [36,320,130,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43510 c43510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43510_3
  · exact m43510_9
  · exact m43510_10
  · exact u39648
  · exact u39649
  · exact u39650

theorem m43511_3 : Upper (D 7) (R 7) [36,320,130,129,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39593

theorem m43511_9 : Upper (D 7) (R 7) [36,320,130,129,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39606

theorem m43511_10 : Upper (D 7) (R 7) [36,320,130,129,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39616

theorem m43511_33 : Upper (D 7) (R 7) [36,320,130,129,33] 13 :=
  permutation_upper _ _ _ [36,320,130,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39622

theorem m43511_34 : Upper (D 7) (R 7) [36,320,130,129,34] 13 :=
  permutation_upper _ _ _ [36,320,130,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39627

theorem m43511_40 : Upper (D 7) (R 7) [36,320,130,129,40] 13 :=
  permutation_upper _ _ _ [36,320,130,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39633

theorem m43511_65 : Upper (D 7) (R 7) [36,320,130,129,65] 13 :=
  permutation_upper _ _ _ [36,320,130,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39637

theorem m43511_66 : Upper (D 7) (R 7) [36,320,130,129,66] 13 :=
  permutation_upper _ _ _ [36,320,130,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39641

theorem m43511_72 : Upper (D 7) (R 7) [36,320,130,129,72] 13 :=
  permutation_upper _ _ _ [36,320,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39644

theorem m43511_96 : Upper (D 7) (R 7) [36,320,130,129,96] 13 :=
  permutation_upper _ _ _ [36,320,130,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39648

def r43511 : Route 9 := (fun mask => (mask,id))

def c43511 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43511 : Upper (D 7) (R 7) [36,320,130,129] 13 := by
  apply FastRouting.sound _ _ [36,320,130,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43511 c43511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43511_3
  · exact m43511_9
  · exact m43511_10
  · exact m43511_33
  · exact m43511_34
  · exact m43511_40
  · exact m43511_65
  · exact m43511_66
  · exact m43511_72
  · exact m43511_96

def b43512 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 322 134 138 121 121 121 249 377), lower := (rows 37 322 134 138 16 32 64 128 256), losses := [] }

theorem u43512 : Upper (D 7) (R 7) [36,320,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43513_3 : Upper (D 7) (R 7) [36,320,130,144,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39594

theorem m43513_9 : Upper (D 7) (R 7) [36,320,130,144,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39608

theorem m43513_10 : Upper (D 7) (R 7) [36,320,130,144,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39617

theorem m43513_33 : Upper (D 7) (R 7) [36,320,130,144,33] 13 :=
  permutation_upper _ _ _ [36,320,130,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39623

theorem m43513_34 : Upper (D 7) (R 7) [36,320,130,144,34] 13 :=
  permutation_upper _ _ _ [36,320,130,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39628

theorem m43513_40 : Upper (D 7) (R 7) [36,320,130,144,40] 13 :=
  permutation_upper _ _ _ [36,320,130,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39635

theorem m43513_65 : Upper (D 7) (R 7) [36,320,130,144,65] 13 :=
  permutation_upper _ _ _ [36,320,130,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39639

theorem m43513_66 : Upper (D 7) (R 7) [36,320,130,144,66] 13 :=
  permutation_upper _ _ _ [36,320,130,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39642

theorem m43513_72 : Upper (D 7) (R 7) [36,320,130,144,72] 13 :=
  permutation_upper _ _ _ [36,320,130,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39646

theorem m43513_96 : Upper (D 7) (R 7) [36,320,130,144,96] 13 :=
  permutation_upper _ _ _ [36,320,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39650

def r43513 : Route 9 := (fun mask => (mask,id))

def c43513 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43513 : Upper (D 7) (R 7) [36,320,130,144] 13 := by
  apply FastRouting.sound _ _ [36,320,130,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r43513 c43513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43513_3
  · exact m43513_9
  · exact m43513_10
  · exact m43513_33
  · exact m43513_34
  · exact m43513_40
  · exact m43513_65
  · exact m43513_66
  · exact m43513_72
  · exact m43513_96

theorem m43514_3 : Upper (D 7) (R 7) [36,320,130,160,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39595

theorem m43514_9 : Upper (D 7) (R 7) [36,320,130,160,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39609

theorem m43514_10 : Upper (D 7) (R 7) [36,320,130,160,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39618

theorem m43514_65 : Upper (D 7) (R 7) [36,320,130,160,65] 13 :=
  permutation_upper _ _ _ [36,320,130,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39640

theorem m43514_66 : Upper (D 7) (R 7) [36,320,130,160,66] 13 :=
  permutation_upper _ _ _ [36,320,130,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39643

theorem m43514_72 : Upper (D 7) (R 7) [36,320,130,160,72] 13 :=
  permutation_upper _ _ _ [36,320,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39647

def r43514 : Route 9 := (fun mask => (mask,id))

def c43514 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43514 : Upper (D 7) (R 7) [36,320,130,160] 13 := by
  apply FastRouting.sound _ _ [36,320,130,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43514 c43514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43514_3
  · exact m43514_9
  · exact m43514_10
  · exact m43514_65
  · exact m43514_66
  · exact m43514_72

theorem m43515_3 : Upper (D 7) (R 7) [36,320,130,192,3] 13 :=
  permutation_upper _ _ _ [36,320,130,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39596

theorem m43515_9 : Upper (D 7) (R 7) [36,320,130,192,9] 13 :=
  permutation_upper _ _ _ [36,320,130,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39610

theorem m43515_10 : Upper (D 7) (R 7) [36,320,130,192,10] 13 :=
  permutation_upper _ _ _ [36,320,130,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39619

theorem m43515_33 : Upper (D 7) (R 7) [36,320,130,192,33] 13 :=
  permutation_upper _ _ _ [36,320,130,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39624

theorem m43515_34 : Upper (D 7) (R 7) [36,320,130,192,34] 13 :=
  permutation_upper _ _ _ [36,320,130,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39629

theorem m43515_40 : Upper (D 7) (R 7) [36,320,130,192,40] 13 :=
  permutation_upper _ _ _ [36,320,130,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39636

def r43515 : Route 9 := (fun mask => (mask,id))

def c43515 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43515 : Upper (D 7) (R 7) [36,320,130,192] 13 := by
  apply FastRouting.sound _ _ [36,320,130,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43515 c43515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43515_3
  · exact m43515_9
  · exact m43515_10
  · exact m43515_33
  · exact m43515_34
  · exact m43515_40

def r43516 : Route 9 := (fun mask => (mask,id))

def c43516 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43516 : Upper (D 7) (R 7) [36,320,136,3] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43516 c43516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39651
  · exact u39652
  · exact u39653
  · exact u39654
  · exact u39655
  · exact u39656
  · exact u39657
  · exact u39658
  · exact u39659
  · exact u39660

def r43517 : Route 9 := (fun mask => (mask,id))

def c43517 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43517 : Upper (D 7) (R 7) [36,320,136,17] 13 := by
  apply FastRouting.sound _ _ [36,320,136,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43517 c43517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39661
  · exact u39662
  · exact u39663
  · exact u39664
  · exact u39665
  · exact u39666
  · exact u39667
  · exact u39668
  · exact u39669
  · exact u39670

def r43518 : Route 9 := (fun mask => (mask,id))

def c43518 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43518 : Upper (D 7) (R 7) [36,320,136,18] 13 := by
  apply FastRouting.sound _ _ [36,320,136,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43518 c43518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39671
  · exact u39672
  · exact u39673
  · exact u39674
  · exact u39675
  · exact u39676
  · exact u39677
  · exact u39678
  · exact u39679
  · exact u39680

def b43519 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 140 41 211 243 211 211 467), lower := (rows 37 322 140 41 16 32 64 128 256), losses := [] }

theorem u43519 : Upper (D 7) (R 7) [36,320,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43520 : Route 9 := (fun mask => (mask,id))

def c43520 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43520 : Upper (D 7) (R 7) [36,320,136,34] 13 := by
  apply FastRouting.sound _ _ [36,320,136,34] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43520 c43520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39681
  · exact u39682
  · exact u39683
  · exact u39684
  · exact u39685
  · exact u39686

def r43521 : Route 9 := (fun mask => (mask,id))

def c43521 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43521 : Upper (D 7) (R 7) [36,320,136,48] 13 := by
  apply FastRouting.sound _ _ [36,320,136,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43521 c43521
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39687
  · exact u39688
  · exact u39689
  · exact u39690
  · exact u39691
  · exact u39692

def r43522 : Route 9 := (fun mask => (mask,id))

def c43522 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43522 : Upper (D 7) (R 7) [36,320,136,65] 13 := by
  apply FastRouting.sound _ _ [36,320,136,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43522 c43522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39693
  · exact u39694
  · exact u39695
  · exact u39696
  · exact u39697
  · exact u39698

def b43523 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 140 74 179 179 243 179 435), lower := (rows 37 322 140 74 16 32 64 128 256), losses := [] }

theorem u43523 : Upper (D 7) (R 7) [36,320,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43524 : Route 9 := (fun mask => (mask,id))

def c43524 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43524 : Upper (D 7) (R 7) [36,320,136,80] 13 := by
  apply FastRouting.sound _ _ [36,320,136,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43524 c43524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39699
  · exact u39700
  · exact u39701
  · exact u39702
  · exact u39703
  · exact u39704

def r43525 : Route 9 := (fun mask => (mask,id))

def c43525 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43525 : Upper (D 7) (R 7) [36,320,136,96] 13 := by
  apply FastRouting.sound _ _ [36,320,136,96] 13 (by decide) (choices 2) [3,129,130] r43525 c43525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39705
  · exact u39706
  · exact u39707

def b43526 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 322 140 137 115 115 115 243 371), lower := (rows 37 322 140 137 16 32 64 128 256), losses := [] }

theorem u43526 : Upper (D 7) (R 7) [36,320,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43527 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 322 140 138 115 115 115 243 371), lower := (rows 37 322 140 138 16 32 64 128 256), losses := [] }

theorem u43527 : Upper (D 7) (R 7) [36,320,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43528 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 322 140 152 115 99 99 227 355), lower := (rows 37 322 140 152 16 32 64 128 256), losses := [] }

theorem u43528 : Upper (D 7) (R 7) [36,320,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43529 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 140 168 83 115 83 211 339), lower := (rows 37 322 140 168 16 32 64 128 256), losses := [] }

theorem u43529 : Upper (D 7) (R 7) [36,320,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43530 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 322 140 200 51 51 115 179 307), lower := (rows 37 322 140 200 16 32 64 128 256), losses := [] }

theorem u43530 : Upper (D 7) (R 7) [36,320,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43531 : Route 9 := (fun mask => (mask,id))

def c43531 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43531 : Upper (D 7) (R 7) [36,320,192,3] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43531 c43531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39708
  · exact u39709
  · exact u39710
  · exact u39711
  · exact u39712
  · exact u39713
  · exact u39714
  · exact u39715
  · exact u39716
  · exact u39717

theorem m43532_3 : Upper (D 7) (R 7) [36,320,192,17,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39709

def r43532 : Route 9 := (fun mask => (mask,id))

def c43532 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43532 : Upper (D 7) (R 7) [36,320,192,17] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43532 c43532
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43532_3
  · exact u39718
  · exact u39719
  · exact u39720
  · exact u39721
  · exact u39722
  · exact u39723
  · exact u39724
  · exact u39725
  · exact u39726

theorem m43533_3 : Upper (D 7) (R 7) [36,320,192,18,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39710

theorem m43533_9 : Upper (D 7) (R 7) [36,320,192,18,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39719

def r43533 : Route 9 := (fun mask => (mask,id))

def c43533 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43533 : Upper (D 7) (R 7) [36,320,192,18] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43533 c43533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43533_3
  · exact m43533_9
  · exact u39727
  · exact u39728
  · exact u39729
  · exact u39730
  · exact u39731
  · exact u39732
  · exact u39733
  · exact u39734

def b43534 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 196 41 155 187 219 155 411), lower := (rows 37 322 196 41 16 32 64 128 256), losses := [] }

theorem u43534 : Upper (D 7) (R 7) [36,320,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43535_3 : Upper (D 7) (R 7) [36,320,192,34,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39712

theorem m43535_9 : Upper (D 7) (R 7) [36,320,192,34,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39721

theorem m43535_10 : Upper (D 7) (R 7) [36,320,192,34,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39729

def r43535 : Route 9 := (fun mask => (mask,id))

def c43535 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43535 : Upper (D 7) (R 7) [36,320,192,34] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43535 c43535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43535_3
  · exact m43535_9
  · exact m43535_10
  · exact u39738
  · exact u39739
  · exact u39740

theorem m43536_3 : Upper (D 7) (R 7) [36,320,192,48,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39713

theorem m43536_9 : Upper (D 7) (R 7) [36,320,192,48,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39722

theorem m43536_10 : Upper (D 7) (R 7) [36,320,192,48,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39730

def r43536 : Route 9 := (fun mask => (mask,id))

def c43536 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43536 : Upper (D 7) (R 7) [36,320,192,48] 13 := by
  apply FastRouting.sound _ _ [36,320,192,48] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43536 c43536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43536_3
  · exact m43536_9
  · exact m43536_10
  · exact u39741
  · exact u39742
  · exact u39743

theorem m43537_3 : Upper (D 7) (R 7) [36,320,192,129,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39714

theorem m43537_9 : Upper (D 7) (R 7) [36,320,192,129,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39723

theorem m43537_10 : Upper (D 7) (R 7) [36,320,192,129,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39731

theorem m43537_33 : Upper (D 7) (R 7) [36,320,192,129,33] 13 :=
  permutation_upper _ _ _ [36,320,192,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39735

theorem m43537_34 : Upper (D 7) (R 7) [36,320,192,129,34] 13 :=
  permutation_upper _ _ _ [36,320,192,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39738

theorem m43537_40 : Upper (D 7) (R 7) [36,320,192,129,40] 13 :=
  permutation_upper _ _ _ [36,320,192,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39741

def r43537 : Route 9 := (fun mask => (mask,id))

def c43537 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43537 : Upper (D 7) (R 7) [36,320,192,129] 13 := by
  apply FastRouting.sound _ _ [36,320,192,129] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43537 c43537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43537_3
  · exact m43537_9
  · exact m43537_10
  · exact m43537_33
  · exact m43537_34
  · exact m43537_40

theorem m43538_3 : Upper (D 7) (R 7) [36,320,192,130,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39715

theorem m43538_9 : Upper (D 7) (R 7) [36,320,192,130,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39724

theorem m43538_10 : Upper (D 7) (R 7) [36,320,192,130,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39732

theorem m43538_33 : Upper (D 7) (R 7) [36,320,192,130,33] 13 :=
  permutation_upper _ _ _ [36,320,192,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39736

theorem m43538_34 : Upper (D 7) (R 7) [36,320,192,130,34] 13 :=
  permutation_upper _ _ _ [36,320,192,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39739

theorem m43538_40 : Upper (D 7) (R 7) [36,320,192,130,40] 13 :=
  permutation_upper _ _ _ [36,320,192,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39742

def r43538 : Route 9 := (fun mask => (mask,id))

def c43538 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43538 : Upper (D 7) (R 7) [36,320,192,130] 13 := by
  apply FastRouting.sound _ _ [36,320,192,130] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43538 c43538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43538_3
  · exact m43538_9
  · exact m43538_10
  · exact m43538_33
  · exact m43538_34
  · exact m43538_40

theorem m43539_3 : Upper (D 7) (R 7) [36,320,192,144,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39716

theorem m43539_9 : Upper (D 7) (R 7) [36,320,192,144,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39725

theorem m43539_10 : Upper (D 7) (R 7) [36,320,192,144,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39733

theorem m43539_33 : Upper (D 7) (R 7) [36,320,192,144,33] 13 :=
  permutation_upper _ _ _ [36,320,192,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39737

theorem m43539_34 : Upper (D 7) (R 7) [36,320,192,144,34] 13 :=
  permutation_upper _ _ _ [36,320,192,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39740

theorem m43539_40 : Upper (D 7) (R 7) [36,320,192,144,40] 13 :=
  permutation_upper _ _ _ [36,320,192,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39743

def r43539 : Route 9 := (fun mask => (mask,id))

def c43539 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43539 : Upper (D 7) (R 7) [36,320,192,144] 13 := by
  apply FastRouting.sound _ _ [36,320,192,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r43539 c43539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43539_3
  · exact m43539_9
  · exact m43539_10
  · exact m43539_33
  · exact m43539_34
  · exact m43539_40

theorem m43540_3 : Upper (D 7) (R 7) [36,320,192,160,3] 13 :=
  permutation_upper _ _ _ [36,320,192,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39717

theorem m43540_9 : Upper (D 7) (R 7) [36,320,192,160,9] 13 :=
  permutation_upper _ _ _ [36,320,192,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39726

theorem m43540_10 : Upper (D 7) (R 7) [36,320,192,160,10] 13 :=
  permutation_upper _ _ _ [36,320,192,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39734

def r43540 : Route 9 := (fun mask => (mask,id))

def c43540 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43540 : Upper (D 7) (R 7) [36,320,192,160] 13 := by
  apply FastRouting.sound _ _ [36,320,192,160] 13 (by decide) (choices 2) [3,9,10] r43540 c43540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43540_3
  · exact m43540_9
  · exact m43540_10

def b43541 : PairBound 9 := { available := 476, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 162 7 11 476 508 476 476 476), lower := (rows 97 162 7 11 16 32 64 128 256), losses := [] }

theorem u43541 : Upper (D 7) (R 7) [96,160,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43542 : PairBound 9 := { available := 474, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 474 506 474 474 474), lower := (rows 97 162 7 13 16 32 64 128 256), losses := [] }

theorem u43542 : Upper (D 7) (R 7) [96,160,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43543_6 : Upper (D 7) (R 7) [96,160,3,17,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,10] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39749

def r43543 : Route 9 := (fun mask => (mask,id))

def c43543 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43543 : Upper (D 7) (R 7) [96,160,3,17] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192,258,260,264,320,384] r43543 c43543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43543_6
  · exact u39758
  · exact u39759
  · exact u39760
  · exact u39761
  · exact u39762
  · exact u39763
  · exact u39764
  · exact u39765
  · exact u39766
  · exact u39767
  · exact u39768
  · exact u39769
  · exact u39770
  · exact u39771

theorem m43544_3 : Upper (D 7) (R 7) [96,160,3,20,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39744

theorem m43544_9 : Upper (D 7) (R 7) [96,160,3,20,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39759

theorem m43544_10 : Upper (D 7) (R 7) [96,160,3,20,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,12] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39759

theorem m43544_129 : Upper (D 7) (R 7) [96,160,3,20,129] 13 :=
  permutation_upper _ _ _ [96,160,3,20,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39773

theorem m43544_130 : Upper (D 7) (R 7) [96,160,3,20,130] 13 :=
  permutation_upper _ _ _ [96,160,3,20,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39772

theorem m43544_136 : Upper (D 7) (R 7) [96,160,3,20,136] 13 :=
  permutation_upper _ _ _ [96,160,3,20,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39774

theorem m43544_258 : Upper (D 7) (R 7) [96,160,3,20,258] 13 :=
  permutation_upper _ _ _ [96,160,3,20,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39776

theorem m43544_384 : Upper (D 7) (R 7) [96,160,3,20,384] 13 :=
  permutation_upper _ _ _ [96,160,3,20,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39778

def r43544 : Route 9 := (fun mask => (mask,id))

def c43544 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43544 : Upper (D 7) (R 7) [96,160,3,20] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r43544 c43544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43544_3
  · exact m43544_9
  · exact m43544_10
  · exact u39772
  · exact u39773
  · exact u39774
  · exact m43544_129
  · exact m43544_130
  · exact m43544_136
  · exact u39775
  · exact u39776
  · exact m43544_258
  · exact u39777
  · exact u39778
  · exact m43544_384

def b43545 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 414 446 478 414 414), lower := (rows 97 162 7 73 16 32 64 128 256), losses := [] }

theorem u43545 : Upper (D 7) (R 7) [96,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43546_5 : Upper (D 7) (R 7) [96,160,3,66,5] 13 :=
  permutation_upper _ _ _ [96,160,3,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39750

theorem m43546_9 : Upper (D 7) (R 7) [96,160,3,66,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39760

theorem m43546_12 : Upper (D 7) (R 7) [96,160,3,66,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39773

def r43546 : Route 9 := (fun mask => (mask,id))

def c43546 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43546 : Upper (D 7) (R 7) [96,160,3,66] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r43546 c43546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43546_5
  · exact m43546_9
  · exact m43546_12
  · exact u39785
  · exact u39786
  · exact u39787
  · exact u39788
  · exact u39789
  · exact u39790
  · exact u39791

theorem m43547_3 : Upper (D 7) (R 7) [96,160,3,68,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39745

theorem m43547_9 : Upper (D 7) (R 7) [96,160,3,68,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39761

theorem m43547_10 : Upper (D 7) (R 7) [96,160,3,68,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39764

theorem m43547_129 : Upper (D 7) (R 7) [96,160,3,68,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39786

theorem m43547_130 : Upper (D 7) (R 7) [96,160,3,68,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39779

def r43547 : Route 9 := (fun mask => (mask,id))

def c43547 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43547 : Upper (D 7) (R 7) [96,160,3,68] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43547 c43547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43547_3
  · exact m43547_9
  · exact m43547_10
  · exact m43547_129
  · exact m43547_130
  · exact u39792
  · exact u39793
  · exact u39794
  · exact u39795
  · exact u39796

theorem m43548_3 : Upper (D 7) (R 7) [96,160,3,80,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39745

theorem m43548_5 : Upper (D 7) (R 7) [96,160,3,80,5] 13 :=
  permutation_upper _ _ _ [96,160,3,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39751

theorem m43548_6 : Upper (D 7) (R 7) [96,160,3,80,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39752

theorem m43548_9 : Upper (D 7) (R 7) [96,160,3,80,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39762

theorem m43548_10 : Upper (D 7) (R 7) [96,160,3,80,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39765

theorem m43548_12 : Upper (D 7) (R 7) [96,160,3,80,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39774

theorem m43548_129 : Upper (D 7) (R 7) [96,160,3,80,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39787

theorem m43548_130 : Upper (D 7) (R 7) [96,160,3,80,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39780

theorem m43548_132 : Upper (D 7) (R 7) [96,160,3,80,132] 13 :=
  permutation_upper _ _ _ [96,160,3,68,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39792

def r43548 : Route 9 := (fun mask => (mask,id))

def c43548 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43548 : Upper (D 7) (R 7) [96,160,3,80] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,257,258,260,264,384] r43548 c43548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43548_3
  · exact m43548_5
  · exact m43548_6
  · exact m43548_9
  · exact m43548_10
  · exact m43548_12
  · exact m43548_129
  · exact m43548_130
  · exact m43548_132
  · exact u39797
  · exact u39798
  · exact u39799
  · exact u39800
  · exact u39801
  · exact u39802

theorem m43549_3 : Upper (D 7) (R 7) [96,160,3,192,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39746

theorem m43549_5 : Upper (D 7) (R 7) [96,160,3,192,5] 13 :=
  permutation_upper _ _ _ [96,160,3,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39753

theorem m43549_6 : Upper (D 7) (R 7) [96,160,3,192,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39753

theorem m43549_9 : Upper (D 7) (R 7) [96,160,3,192,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39766

theorem m43549_10 : Upper (D 7) (R 7) [96,160,3,192,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39766

theorem m43549_12 : Upper (D 7) (R 7) [96,160,3,192,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39775

theorem m43549_258 : Upper (D 7) (R 7) [96,160,3,192,258] 13 :=
  permutation_upper _ _ _ [96,160,3,192,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39803

def r43549 : Route 9 := (fun mask => (mask,id))

def c43549 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43549 : Upper (D 7) (R 7) [96,160,3,192] 13 := by
  apply FastRouting.sound _ _ [96,160,3,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r43549 c43549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43549_3
  · exact m43549_5
  · exact m43549_6
  · exact m43549_9
  · exact m43549_10
  · exact m43549_12
  · exact u39803
  · exact m43549_258
  · exact u39804
  · exact u39805

theorem m43550_6 : Upper (D 7) (R 7) [96,160,3,257,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39754

theorem m43550_10 : Upper (D 7) (R 7) [96,160,3,257,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39767

theorem m43550_12 : Upper (D 7) (R 7) [96,160,3,257,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39776

theorem m43550_66 : Upper (D 7) (R 7) [96,160,3,257,66] 13 :=
  permutation_upper _ _ _ [96,160,3,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39788

theorem m43550_68 : Upper (D 7) (R 7) [96,160,3,257,68] 13 :=
  permutation_upper _ _ _ [96,160,3,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39793

theorem m43550_72 : Upper (D 7) (R 7) [96,160,3,257,72] 13 :=
  permutation_upper _ _ _ [96,160,3,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39798

theorem m43550_130 : Upper (D 7) (R 7) [96,160,3,257,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39781

theorem m43550_132 : Upper (D 7) (R 7) [96,160,3,257,132] 13 :=
  permutation_upper _ _ _ [96,160,3,68,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39794

theorem m43550_136 : Upper (D 7) (R 7) [96,160,3,257,136] 13 :=
  permutation_upper _ _ _ [96,160,3,80,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39799

theorem m43550_192 : Upper (D 7) (R 7) [96,160,3,257,192] 13 :=
  permutation_upper _ _ _ [96,160,3,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39803

def r43550 : Route 9 := (fun mask => (mask,id))

def c43550 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43550 : Upper (D 7) (R 7) [96,160,3,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,257] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192] r43550 c43550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43550_6
  · exact m43550_10
  · exact m43550_12
  · exact m43550_66
  · exact m43550_68
  · exact m43550_72
  · exact m43550_130
  · exact m43550_132
  · exact m43550_136
  · exact m43550_192

theorem m43551_3 : Upper (D 7) (R 7) [96,160,3,260,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39747

theorem m43551_9 : Upper (D 7) (R 7) [96,160,3,260,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39768

theorem m43551_10 : Upper (D 7) (R 7) [96,160,3,260,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39768

theorem m43551_65 : Upper (D 7) (R 7) [96,160,3,260,65] 13 :=
  permutation_upper _ _ _ [96,160,3,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39782

theorem m43551_66 : Upper (D 7) (R 7) [96,160,3,260,66] 13 :=
  permutation_upper _ _ _ [96,160,3,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39789

theorem m43551_72 : Upper (D 7) (R 7) [96,160,3,260,72] 13 :=
  permutation_upper _ _ _ [96,160,3,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39800

theorem m43551_129 : Upper (D 7) (R 7) [96,160,3,260,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39789

theorem m43551_130 : Upper (D 7) (R 7) [96,160,3,260,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39782

theorem m43551_136 : Upper (D 7) (R 7) [96,160,3,260,136] 13 :=
  permutation_upper _ _ _ [96,160,3,80,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39800

theorem m43551_192 : Upper (D 7) (R 7) [96,160,3,260,192] 13 :=
  permutation_upper _ _ _ [96,160,3,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39804

def r43551 : Route 9 := (fun mask => (mask,id))

def c43551 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43551 : Upper (D 7) (R 7) [96,160,3,260] 13 := by
  apply FastRouting.sound _ _ [96,160,3,260] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43551 c43551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43551_3
  · exact m43551_9
  · exact m43551_10
  · exact m43551_65
  · exact m43551_66
  · exact m43551_72
  · exact m43551_129
  · exact m43551_130
  · exact m43551_136
  · exact m43551_192

theorem m43552_3 : Upper (D 7) (R 7) [96,160,3,272,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39747

theorem m43552_5 : Upper (D 7) (R 7) [96,160,3,272,5] 13 :=
  permutation_upper _ _ _ [96,160,3,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39755

theorem m43552_6 : Upper (D 7) (R 7) [96,160,3,272,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39755

theorem m43552_9 : Upper (D 7) (R 7) [96,160,3,272,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39769

theorem m43552_10 : Upper (D 7) (R 7) [96,160,3,272,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39769

theorem m43552_12 : Upper (D 7) (R 7) [96,160,3,272,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39777

theorem m43552_65 : Upper (D 7) (R 7) [96,160,3,272,65] 13 :=
  permutation_upper _ _ _ [96,160,3,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39783

theorem m43552_66 : Upper (D 7) (R 7) [96,160,3,272,66] 13 :=
  permutation_upper _ _ _ [96,160,3,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39790

theorem m43552_68 : Upper (D 7) (R 7) [96,160,3,272,68] 13 :=
  permutation_upper _ _ _ [96,160,3,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39795

theorem m43552_72 : Upper (D 7) (R 7) [96,160,3,272,72] 13 :=
  permutation_upper _ _ _ [96,160,3,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39801

theorem m43552_129 : Upper (D 7) (R 7) [96,160,3,272,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39790

theorem m43552_130 : Upper (D 7) (R 7) [96,160,3,272,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39783

theorem m43552_132 : Upper (D 7) (R 7) [96,160,3,272,132] 13 :=
  permutation_upper _ _ _ [96,160,3,68,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39795

theorem m43552_136 : Upper (D 7) (R 7) [96,160,3,272,136] 13 :=
  permutation_upper _ _ _ [96,160,3,80,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39801

theorem m43552_192 : Upper (D 7) (R 7) [96,160,3,272,192] 13 :=
  permutation_upper _ _ _ [96,160,3,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39805

def r43552 : Route 9 := (fun mask => (mask,id))

def c43552 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43552 : Upper (D 7) (R 7) [96,160,3,272] 13 := by
  apply FastRouting.sound _ _ [96,160,3,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,129,130,132,136,192] r43552 c43552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43552_3
  · exact m43552_5
  · exact m43552_6
  · exact m43552_9
  · exact m43552_10
  · exact m43552_12
  · exact m43552_65
  · exact m43552_66
  · exact m43552_68
  · exact m43552_72
  · exact m43552_129
  · exact m43552_130
  · exact m43552_132
  · exact m43552_136
  · exact m43552_192

theorem m43553_3 : Upper (D 7) (R 7) [96,160,3,320,3] 13 :=
  permutation_upper _ _ _ [96,160,3,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39748

theorem m43553_5 : Upper (D 7) (R 7) [96,160,3,320,5] 13 :=
  permutation_upper _ _ _ [96,160,3,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39756

theorem m43553_6 : Upper (D 7) (R 7) [96,160,3,320,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39757

theorem m43553_9 : Upper (D 7) (R 7) [96,160,3,320,9] 13 :=
  permutation_upper _ _ _ [96,160,3,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39770

theorem m43553_10 : Upper (D 7) (R 7) [96,160,3,320,10] 13 :=
  permutation_upper _ _ _ [96,160,3,17,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39771

theorem m43553_12 : Upper (D 7) (R 7) [96,160,3,320,12] 13 :=
  permutation_upper _ _ _ [96,160,3,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39778

theorem m43553_129 : Upper (D 7) (R 7) [96,160,3,320,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39791

theorem m43553_130 : Upper (D 7) (R 7) [96,160,3,320,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39784

theorem m43553_132 : Upper (D 7) (R 7) [96,160,3,320,132] 13 :=
  permutation_upper _ _ _ [96,160,3,68,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39796

theorem m43553_136 : Upper (D 7) (R 7) [96,160,3,320,136] 13 :=
  permutation_upper _ _ _ [96,160,3,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39802

def r43553 : Route 9 := (fun mask => (mask,id))

def c43553 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43553 : Upper (D 7) (R 7) [96,160,3,320] 13 := by
  apply FastRouting.sound _ _ [96,160,3,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r43553 c43553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43553_3
  · exact m43553_5
  · exact m43553_6
  · exact m43553_9
  · exact m43553_10
  · exact m43553_12
  · exact m43553_129
  · exact m43553_130
  · exact m43553_132
  · exact m43553_136

def b43554 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 13 466 498 466 466 466), lower := (rows 97 162 13 13 16 32 64 128 256), losses := [] }

theorem u43554 : Upper (D 7) (R 7) [96,160,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43555_3 : Upper (D 7) (R 7) [96,160,9,6,3] 13 :=
  permutation_upper _ _ _ [96,160,3,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39758

theorem m43555_129 : Upper (D 7) (R 7) [96,160,9,6,129] 13 :=
  permutation_upper _ _ _ [96,160,9,6,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39812

theorem m43555_130 : Upper (D 7) (R 7) [96,160,9,6,130] 13 :=
  permutation_upper _ _ _ [96,160,9,6,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39811

theorem m43555_258 : Upper (D 7) (R 7) [96,160,9,6,258] 13 :=
  permutation_upper _ _ _ [96,160,9,6,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39814

theorem m43555_384 : Upper (D 7) (R 7) [96,160,9,6,384] 13 :=
  permutation_upper _ _ _ [96,160,9,6,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39815

def r43555 : Route 9 := (fun mask => (mask,id))

def c43555 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43555 : Upper (D 7) (R 7) [96,160,9,6] 13 := by
  apply FastRouting.sound _ _ [96,160,9,6] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r43555 c43555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43555_3
  · exact u39811
  · exact u39812
  · exact m43555_129
  · exact m43555_130
  · exact u39813
  · exact u39814
  · exact m43555_258
  · exact u39815
  · exact m43555_384

def b43556 : PairBound 9 := { available := 454, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 97 162 13 25 470 486 454 454 454), lower := (rows 97 162 13 25 16 32 64 128 256), losses := [] }

theorem u43556 : Upper (D 7) (R 7) [96,160,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43557_3 : Upper (D 7) (R 7) [96,160,9,18,3] 13 :=
  permutation_upper _ _ _ [96,160,3,5,10] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39749

theorem m43557_5 : Upper (D 7) (R 7) [96,160,9,18,5] 13 :=
  permutation_upper _ _ _ [96,160,9,17,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39816

theorem m43557_6 : Upper (D 7) (R 7) [96,160,9,18,6] 13 :=
  permutation_upper _ _ _ [96,160,9,17,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39816

def r43557 : Route 9 := (fun mask => (mask,id))

def c43557 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43557 : Upper (D 7) (R 7) [96,160,9,18] 13 := by
  apply FastRouting.sound _ _ [96,160,9,18] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,257,258,260,320,384] r43557 c43557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43557_3
  · exact m43557_5
  · exact m43557_6
  · exact u39825
  · exact u39826
  · exact u39827
  · exact u39828
  · exact u39829
  · exact u39830
  · exact u39831
  · exact u39832
  · exact u39833
  · exact u39834
  · exact u39835
  · exact u39836

theorem m43558_3 : Upper (D 7) (R 7) [96,160,9,20,3] 13 :=
  permutation_upper _ _ _ [96,160,3,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39759

def r43558 : Route 9 := (fun mask => (mask,id))

def c43558 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43558 : Upper (D 7) (R 7) [96,160,9,20] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r43558 c43558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43558_3
  · exact u39837
  · exact u39838
  · exact u39839
  · exact u39840
  · exact u39841
  · exact u39842
  · exact u39843
  · exact u39844
  · exact u39845

def b43559 : PairBound 9 := { available := 406, camps := [{ cop := 0, region := 12, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 13 73 406 438 470 406 406), lower := (rows 97 162 13 73 16 32 64 128 256), losses := [] }

theorem u43559 : Upper (D 7) (R 7) [96,160,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u43559
end Delivery.IrregularNine14.P07
