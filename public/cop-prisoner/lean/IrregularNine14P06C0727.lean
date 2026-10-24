import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0674
import IrregularNine14P06C0675
import IrregularNine14P06C0676
import IrregularNine14P06C0677
import IrregularNine14P06C0678
import IrregularNine14P06C0679

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43620_3 : Upper (D 6) (R 6) [96,132,288,80,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40467

theorem m43620_5 : Upper (D 6) (R 6) [96,132,288,80,5] 13 :=
  permutation_upper _ _ _ [96,132,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40472

theorem m43620_6 : Upper (D 6) (R 6) [96,132,288,80,6] 13 :=
  permutation_upper _ _ _ [96,132,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40476

theorem m43620_9 : Upper (D 6) (R 6) [96,132,288,80,9] 13 :=
  permutation_upper _ _ _ [96,132,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40483

theorem m43620_10 : Upper (D 6) (R 6) [96,132,288,80,10] 13 :=
  permutation_upper _ _ _ [96,132,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40489

theorem m43620_12 : Upper (D 6) (R 6) [96,132,288,80,12] 13 :=
  permutation_upper _ _ _ [96,132,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40492

def r43620 : Route 9 := (fun mask => (mask,id))

def c43620 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43620 : Upper (D 6) (R 6) [96,132,288,80] 13 := by
  apply FastRouting.sound _ _ [96,132,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43620 c43620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43620_3
  · exact m43620_5
  · exact m43620_6
  · exact m43620_9
  · exact m43620_10
  · exact m43620_12

def r43621 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43621 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43621 : Upper (D 6) (R 6) [96,136,272,3] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43621 c43621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40493
  · exact u40494
  · exact u40495
  · exact u40496
  · exact u40497
  · exact u40498
  · exact u40499

theorem m43622_5 : Upper (D 6) (R 6) [96,136,272,5,5] 13 :=
  permutation_upper _ _ _ [96,136,272,3,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40493

def r43622 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43622 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43622 : Upper (D 6) (R 6) [96,136,272,5] 13 := by
  apply FastRouting.sound _ _ [96,136,272,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43622 c43622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40500
  · exact m43622_5
  · exact u40501
  · exact u40502
  · exact u40503
  · exact u40504
  · exact u40505

theorem m43623_3 : Upper (D 6) (R 6) [96,136,272,6,3] 13 :=
  permutation_upper _ _ _ [96,136,272,5,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40501

theorem m43623_5 : Upper (D 6) (R 6) [96,136,272,6,5] 13 :=
  permutation_upper _ _ _ [96,136,272,3,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40495

def r43623 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43623 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43623 : Upper (D 6) (R 6) [96,136,272,6] 13 := by
  apply FastRouting.sound _ _ [96,136,272,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43623 c43623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43623_3
  · exact m43623_5
  · exact u40506
  · exact u40507
  · exact u40508
  · exact u40509
  · exact u40510

def b43624 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 138 276 41 87 103 71 199 327), lower := (rows 97 138 276 41 16 32 64 128 256), losses := [] }

theorem u43624 : Upper (D 6) (R 6) [96,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43625_3 : Upper (D 6) (R 6) [96,136,272,34,3] 13 :=
  permutation_upper _ _ _ [96,136,272,5,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40504

theorem m43625_5 : Upper (D 6) (R 6) [96,136,272,34,5] 13 :=
  permutation_upper _ _ _ [96,136,272,3,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40498

theorem m43625_6 : Upper (D 6) (R 6) [96,136,272,34,6] 13 :=
  permutation_upper _ _ _ [96,136,272,6,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40509

theorem m43625_65 : Upper (D 6) (R 6) [96,136,272,34,65] 13 :=
  permutation_upper _ _ _ [96,136,272,33,68] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40512

def r43625 : Route 9 := (fun mask => (mask,id))

def c43625 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43625 : Upper (D 6) (R 6) [96,136,272,34] 13 := by
  apply FastRouting.sound _ _ [96,136,272,34] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43625 c43625
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43625_3
  · exact m43625_5
  · exact m43625_6
  · exact m43625_65
  · exact u40513
  · exact u40514

theorem m43626_3 : Upper (D 6) (R 6) [96,136,272,36,3] 13 :=
  permutation_upper _ _ _ [96,136,272,5,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40503

theorem m43626_5 : Upper (D 6) (R 6) [96,136,272,36,5] 13 :=
  permutation_upper _ _ _ [96,136,272,3,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40497

theorem m43626_6 : Upper (D 6) (R 6) [96,136,272,36,6] 13 :=
  permutation_upper _ _ _ [96,136,272,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40508

theorem m43626_65 : Upper (D 6) (R 6) [96,136,272,36,65] 13 :=
  permutation_upper _ _ _ [96,136,272,33,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40511

theorem m43626_68 : Upper (D 6) (R 6) [96,136,272,36,68] 13 :=
  permutation_upper _ _ _ [96,136,272,34,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40513

def r43626 : Route 9 := (fun mask => (mask,id))

def c43626 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43626 : Upper (D 6) (R 6) [96,136,272,36] 13 := by
  apply FastRouting.sound _ _ [96,136,272,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43626 c43626
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43626_3
  · exact m43626_5
  · exact m43626_6
  · exact m43626_65
  · exact u40515
  · exact m43626_68

def b43627 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 138 276 104 23 39 71 135 263), lower := (rows 97 138 276 104 16 32 64 128 256), losses := [] }

theorem u43627 : Upper (D 6) (R 6) [96,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43628 : Route 9 := (fun mask => (mask,id))

def c43628 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43628 : Upper (D 6) (R 6) [96,136,288,3] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43628 c43628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40516
  · exact u40517
  · exact u40518
  · exact u40519
  · exact u40520
  · exact u40521

def r43629 : Route 9 := (fun mask => (mask,id))

def c43629 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43629 : Upper (D 6) (R 6) [96,136,288,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43629 c43629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40522
  · exact u40523
  · exact u40524
  · exact u40525
  · exact u40526
  · exact u40527

def r43630 : Route 9 := (fun mask => (mask,id))

def c43630 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43630 : Upper (D 6) (R 6) [96,136,288,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43630 c43630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40528
  · exact u40529
  · exact u40530
  · exact u40531
  · exact u40532
  · exact u40533

def r43631 : Route 9 := (fun mask => (mask,id))

def c43631 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43631 : Upper (D 6) (R 6) [96,136,288,17] 13 := by
  apply FastRouting.sound _ _ [96,136,288,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43631 c43631
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40534
  · exact u40535
  · exact u40536
  · exact u40537
  · exact u40538
  · exact u40539

def r43632 : Route 9 := (fun mask => (mask,id))

def c43632 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43632 : Upper (D 6) (R 6) [96,136,288,18] 13 := by
  apply FastRouting.sound _ _ [96,136,288,18] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43632 c43632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40540
  · exact u40541
  · exact u40542
  · exact u40543
  · exact u40544
  · exact u40545

def r43633 : Route 9 := (fun mask => (mask,id))

def c43633 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43633 : Upper (D 6) (R 6) [96,136,288,20] 13 := by
  apply FastRouting.sound _ _ [96,136,288,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43633 c43633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40546
  · exact u40547
  · exact u40548
  · exact u40549
  · exact u40550
  · exact u40551

def b43634 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 138 292 73 23 55 87 151 279), lower := (rows 97 138 292 73 16 32 64 128 256), losses := [] }

theorem u43634 : Upper (D 6) (R 6) [96,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43635 : Route 9 := (fun mask => (mask,id))

def c43635 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43635 : Upper (D 6) (R 6) [96,136,288,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,66] 13 (by decide) (choices 2) [3,5,6] r43635 c43635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40552
  · exact u40553
  · exact u40554

def r43636 : Route 9 := (fun mask => (mask,id))

def c43636 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43636 : Upper (D 6) (R 6) [96,136,288,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68] 13 (by decide) (choices 2) [3,5,6] r43636 c43636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40555
  · exact u40556
  · exact u40557

def r43637 : Route 9 := (fun mask => (mask,id))

def c43637 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43637 : Upper (D 6) (R 6) [96,136,288,80] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80] 13 (by decide) (choices 2) [3,5,6] r43637 c43637
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40558
  · exact u40559
  · exact u40560

def r43638 : Route 9 := (fun mask => (mask,id))

def c43638 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43638 : Upper (D 6) (R 6) [96,160,320,3] 13 := by
  apply FastRouting.sound _ _ [96,160,320,3] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43638 c43638
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40561
  · exact u40562
  · exact u40563
  · exact u40564
  · exact u40565
  · exact u40566

theorem m43639_3 : Upper (D 6) (R 6) [96,160,320,6,3] 13 :=
  permutation_upper _ _ _ [96,160,320,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40563

theorem m43639_5 : Upper (D 6) (R 6) [96,160,320,6,5] 13 :=
  permutation_upper _ _ _ [96,160,320,3,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40563

theorem m43639_12 : Upper (D 6) (R 6) [96,160,320,6,12] 13 :=
  permutation_upper _ _ _ [96,160,320,6,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40569

def r43639 : Route 9 := (fun mask => (mask,id))

def c43639 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43639 : Upper (D 6) (R 6) [96,160,320,6] 13 := by
  apply FastRouting.sound _ _ [96,160,320,6] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43639 c43639
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43639_3
  · exact m43639_5
  · exact u40567
  · exact u40568
  · exact u40569
  · exact m43639_12

theorem m43640_3 : Upper (D 6) (R 6) [96,160,320,17,3] 13 :=
  permutation_upper _ _ _ [96,160,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40564

theorem m43640_5 : Upper (D 6) (R 6) [96,160,320,17,5] 13 :=
  permutation_upper _ _ _ [96,160,320,3,9] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40564

theorem m43640_6 : Upper (D 6) (R 6) [96,160,320,17,6] 13 :=
  permutation_upper _ _ _ [96,160,320,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40568

theorem m43640_12 : Upper (D 6) (R 6) [96,160,320,17,12] 13 :=
  permutation_upper _ _ _ [96,160,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40571

def r43640 : Route 9 := (fun mask => (mask,id))

def c43640 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43640 : Upper (D 6) (R 6) [96,160,320,17] 13 := by
  apply FastRouting.sound _ _ [96,160,320,17] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43640 c43640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43640_3
  · exact m43640_5
  · exact m43640_6
  · exact u40570
  · exact u40571
  · exact m43640_12

theorem m43641_3 : Upper (D 6) (R 6) [96,160,320,18,3] 13 :=
  permutation_upper _ _ _ [96,160,320,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40565

theorem m43641_5 : Upper (D 6) (R 6) [96,160,320,18,5] 13 :=
  permutation_upper _ _ _ [96,160,320,3,12] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40566

theorem m43641_6 : Upper (D 6) (R 6) [96,160,320,18,6] 13 :=
  permutation_upper _ _ _ [96,160,320,6,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40569

theorem m43641_9 : Upper (D 6) (R 6) [96,160,320,18,9] 13 :=
  permutation_upper _ _ _ [96,160,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40571

def r43641 : Route 9 := (fun mask => (mask,id))

def c43641 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43641 : Upper (D 6) (R 6) [96,160,320,18] 13 := by
  apply FastRouting.sound _ _ [96,160,320,18] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43641 c43641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43641_3
  · exact m43641_5
  · exact m43641_6
  · exact m43641_9
  · exact u40572
  · exact u40573

def b43642 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 7, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 13 506 498 498 498 498 498), lower := (rows 7 7 13 8 16 32 64 128 256), losses := [] }

theorem u43642 : Upper (D 6) (R 6) [6,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43643 : PairBound 9 := { available := 483, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 28 491 499 483 483 483 483), lower := (rows 7 7 28 8 16 32 64 128 256), losses := [] }

theorem u43643 : Upper (D 6) (R 6) [6,5,24] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43644 : PairBound 9 := { available := 506, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 7 37 506 506 506 506 506 506), lower := (rows 7 7 37 8 16 32 64 128 256), losses := [] }

theorem u43644 : Upper (D 6) (R 6) [6,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43645 : PairBound 9 := { available := 499, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 44 507 499 499 499 499 499), lower := (rows 7 7 44 8 16 32 64 128 256), losses := [] }

theorem u43645 : Upper (D 6) (R 6) [6,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43646 : PairBound 9 := { available := 507, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 100 507 507 507 507 507 507), lower := (rows 7 7 100 8 16 32 64 128 256), losses := [] }

theorem u43646 : Upper (D 6) (R 6) [6,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43647 : PairBound 9 := { available := 378, camps := [{ cop := 7, region := 7, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 133 378 378 378 378 506 378), lower := (rows 7 7 133 8 16 32 64 128 256), losses := [] }

theorem u43647 : Upper (D 6) (R 6) [6,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43648 : PairBound 9 := { available := 371, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 140 379 371 371 371 499 371), lower := (rows 7 7 140 8 16 32 64 128 256), losses := [] }

theorem u43648 : Upper (D 6) (R 6) [6,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43649 : PairBound 9 := { available := 379, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 164 379 379 379 379 507 379), lower := (rows 7 7 164 8 16 32 64 128 256), losses := [] }

theorem u43649 : Upper (D 6) (R 6) [6,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43650 : PairBound 9 := { available := 123, camps := [{ cop := 2, region := 3, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 7 388 123 123 123 123 251 379), lower := (rows 7 7 388 8 16 32 64 128 256), losses := [] }

theorem u43650 : Upper (D 6) (R 6) [6,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43651 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43651 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43651 : Upper (D 6) (R 6) [6,9,17] 13 := by
  apply FastRouting.sound _ _ [6,9,17] 13 (by decide) (choices 2) [6,34,36,96,130,132,160,384] r43651 c43651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40574
  · exact u40575
  · exact u40576
  · exact u40577
  · exact u40578
  · exact u40579
  · exact u40580
  · exact u40581

def b43652 : PairBound 9 := { available := 485, camps := [{ cop := 0, region := 504, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 11 22 493 501 485 485 485 485), lower := (rows 7 11 22 8 16 32 64 128 256), losses := [] }

theorem u43652 : Upper (D 6) (R 6) [6,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43653 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43653 : Nat → Fin 9 := (fun _ => 0)

theorem u43653 : Upper (D 6) (R 6) [6,9,33] 13 := by
  apply FastRouting.sound _ _ [6,9,33] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,130,132,144,160,192,384] r43653 c43653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40582
  · exact u40583
  · exact u40584
  · exact u40585
  · exact u40586
  · exact u40587
  · exact u40588
  · exact u40589
  · exact u40590
  · exact u40591
  · exact u40592
  · exact u40593
  · exact u40594
  · exact u40595
  · exact u40596
  · exact u40597

def b43654 : PairBound 9 := { available := 501, camps := [{ cop := 0, region := 504, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 11 38 509 501 501 501 501 501), lower := (rows 7 11 38 8 16 32 64 128 256), losses := [] }

theorem u43654 : Upper (D 6) (R 6) [6,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43655 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43655 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43655 : Upper (D 6) (R 6) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43655 c43655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40598
  · exact u40599
  · exact u40600
  · exact u40601
  · exact u40602
  · exact u40603
  · exact u40604
  · exact u40605
  · exact u40606
  · exact u40607
  · exact u40608
  · exact u40609
  · exact u40610
  · exact u40611
  · exact u40612
  · exact u40613

def r43656 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43656 : Nat → Fin 9 := (fun _ => 0)

theorem u43656 : Upper (D 6) (R 6) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160,384] r43656 c43656
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40614
  · exact u40615
  · exact u40616
  · exact u40617
  · exact u40618
  · exact u40619
  · exact u40620
  · exact u40621
  · exact u40622
  · exact u40623
  · exact u40624
  · exact u40625
  · exact u40626
  · exact u40627
  · exact u40628
  · exact u40629
  · exact u40630

def r43657 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43657 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43657 : Upper (D 6) (R 6) [6,9,129] 13 := by
  apply FastRouting.sound _ _ [6,9,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,96,258,260,272,288] r43657 c43657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40631
  · exact u40632
  · exact u40633
  · exact u40634
  · exact u40635
  · exact u40636
  · exact u40637
  · exact u40638
  · exact u40639
  · exact u40640
  · exact u40641

def b43658 : PairBound 9 := { available := 373, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 11 134 381 373 373 373 501 373), lower := (rows 7 11 134 8 16 32 64 128 256), losses := [] }

theorem u43658 : Upper (D 6) (R 6) [6,9,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43659 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43659 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43659 : Upper (D 6) (R 6) [6,9,144] 13 := by
  apply FastRouting.sound _ _ [6,9,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43659 c43659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40642
  · exact u40643
  · exact u40644
  · exact u40645
  · exact u40646
  · exact u40647
  · exact u40648
  · exact u40649
  · exact u40650
  · exact u40651
  · exact u40652

def r43660 : Route 9 := (fun mask => (mask,id))

def c43660 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43660 : Upper (D 6) (R 6) [6,9,160] 13 := by
  apply FastRouting.sound _ _ [6,9,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r43660 c43660
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40653
  · exact u40654
  · exact u40655
  · exact u40656
  · exact u40657
  · exact u40658
  · exact u40659
  · exact u40660
  · exact u40661
  · exact u40662
  · exact u40663
  · exact u40664
  · exact u40665
  · exact u40666
  · exact u40667
  · exact u40668
  · exact u40669
  · exact u40670
  · exact u40671
  · exact u40672
  · exact u40673

def r43661 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43661 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43661 : Upper (D 6) (R 6) [6,9,384] 13 := by
  apply FastRouting.sound _ _ [6,9,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96] r43661 c43661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40674
  · exact u40675
  · exact u40676
  · exact u40677
  · exact u40678
  · exact u40679
  · exact u40680
  · exact u40681
  · exact u40682
  · exact u40683
  · exact u40684

def b43662 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 14 22 489 497 481 481 481 481), lower := (rows 7 14 22 8 16 32 64 128 256), losses := [] }

theorem u43662 : Upper (D 6) (R 6) [6,12,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43663 : PairBound 9 := { available := 499, camps := [{ cop := 0, region := 504, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 37 507 499 499 499 499 499), lower := (rows 7 14 37 8 16 32 64 128 256), losses := [] }

theorem u43663 : Upper (D 6) (R 6) [6,12,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43664 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 14 38 505 497 497 497 497 497), lower := (rows 7 14 38 8 16 32 64 128 256), losses := [] }

theorem u43664 : Upper (D 6) (R 6) [6,12,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43665 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 504, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 52 491 499 483 483 483 483), lower := (rows 7 14 52 8 16 32 64 128 256), losses := [] }

theorem u43665 : Upper (D 6) (R 6) [6,12,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43666 : PairBound 9 := { available := 499, camps := [{ cop := 0, region := 504, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 100 507 499 499 499 499 499), lower := (rows 7 14 100 8 16 32 64 128 256), losses := [] }

theorem u43666 : Upper (D 6) (R 6) [6,12,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43667 : PairBound 9 := { available := 371, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 133 379 371 371 371 499 371), lower := (rows 7 14 133 8 16 32 64 128 256), losses := [] }

theorem u43667 : Upper (D 6) (R 6) [6,12,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43668 : PairBound 9 := { available := 369, camps := [{ cop := 0, region := 376, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 14 134 377 369 369 369 497 369), lower := (rows 7 14 134 8 16 32 64 128 256), losses := [] }

theorem u43668 : Upper (D 6) (R 6) [6,12,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43669 : PairBound 9 := { available := 355, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 148 363 371 355 355 483 355), lower := (rows 7 14 148 8 16 32 64 128 256), losses := [] }

theorem u43669 : Upper (D 6) (R 6) [6,12,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43670 : PairBound 9 := { available := 371, camps := [{ cop := 0, region := 376, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 164 379 371 371 371 499 371), lower := (rows 7 14 164 8 16 32 64 128 256), losses := [] }

theorem u43670 : Upper (D 6) (R 6) [6,12,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43671 : PairBound 9 := { available := 115, camps := [{ cop := 0, region := 120, targets := 4 },{ cop := 1, region := 1, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 14 388 123 115 115 115 243 371), lower := (rows 7 14 388 8 16 32 64 128 256), losses := [] }

theorem u43671 : Upper (D 6) (R 6) [6,12,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43672 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43672 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43672 : Upper (D 6) (R 6) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192,384] r43672 c43672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40685
  · exact u40686
  · exact u40687
  · exact u40688
  · exact u40689
  · exact u40690
  · exact u40691
  · exact u40692
  · exact u40693
  · exact u40694
  · exact u40695
  · exact u40696
  · exact u40697
  · exact u40698
  · exact u40699
  · exact u40700

def b43673 : PairBound 9 := { available := 485, camps := [{ cop := 0, region := 504, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 26 38 493 501 485 485 485 485), lower := (rows 7 26 38 8 16 32 64 128 256), losses := [] }

theorem u43673 : Upper (D 6) (R 6) [6,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43674 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c43674 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u43674 : Upper (D 6) (R 6) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160,384] r43674 c43674
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40701
  · exact u40702
  · exact u40703
  · exact u40704
  · exact u40705
  · exact u40706
  · exact u40707
  · exact u40708
  · exact u40709
  · exact u40710
  · exact u40711
  · exact u40712

def r43675 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43675 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43675 : Upper (D 6) (R 6) [6,24,129] 13 := by
  apply FastRouting.sound _ _ [6,24,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r43675 c43675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40713
  · exact u40714
  · exact u40715
  · exact u40716
  · exact u40717
  · exact u40718
  · exact u40719
  · exact u40720
  · exact u40721
  · exact u40722
  · exact u40723

def b43676 : PairBound 9 := { available := 357, camps := [{ cop := 0, region := 376, targets := 2 },{ cop := 2, region := 1, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 7 26 134 365 373 357 357 485 357), lower := (rows 7 26 134 8 16 32 64 128 256), losses := [] }

theorem u43676 : Upper (D 6) (R 6) [6,24,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43677 : Route 9 := (fun mask => (mask,id))

def c43677 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 18 => 4 | 130 => 7 | 20 => 4 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u43677 : Upper (D 6) (R 6) [6,24,160] 13 := by
  apply FastRouting.sound _ _ [6,24,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r43677 c43677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40724
  · exact u40725
  · exact u40726
  · exact u40727
  · exact u40728
  · exact u40729
  · exact u40730
  · exact u40731
  · exact u40732
  · exact u40733
  · exact u40734
  · exact u40735
  · exact u40736
  · exact u40737
  · exact u40738

def r43678 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43678 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43678 : Upper (D 6) (R 6) [6,24,384] 13 := by
  apply FastRouting.sound _ _ [6,24,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43678 c43678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40739
  · exact u40740
  · exact u40741
  · exact u40742
  · exact u40743
  · exact u40744
  · exact u40745

def b43679 : PairBound 9 := { available := 478, camps := [{ cop := 5, region := 7, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 37 478 478 510 478 478 478), lower := (rows 7 35 37 8 16 32 64 128 256), losses := [] }

theorem u43679 : Upper (D 6) (R 6) [6,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u43679
end Delivery.IrregularNine14.P06
