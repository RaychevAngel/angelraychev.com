import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0159
import IrregularNine14P08C0160
import IrregularNine14P08C0161
import IrregularNine14P08C0162

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19680 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 13 41 240 240 240 240 496), lower := (rows 35 262 13 41 16 32 64 128 256), losses := [] }

theorem u19680 : Upper (D 8) (R 8) [34,260,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19681 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19681 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19681 : Upper (D 8) (R 8) [34,260,9,48] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48] 13 (by decide) (choices 2) [33,65,96,192] r19681 c19681
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9566
  · exact u9567
  · exact u9568
  · exact u9569

def b19682 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 13 73 240 240 240 240 496), lower := (rows 35 262 13 73 16 32 64 128 256), losses := [] }

theorem u19682 : Upper (D 8) (R 8) [34,260,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19683 : Route 9 := (fun mask => (mask,id))

def c19683 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19683 : Upper (D 8) (R 8) [34,260,9,80] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19683 c19683
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9570
  · exact u9571
  · exact u9572
  · exact u9573
  · exact u9574
  · exact u9575

def r19684 : Route 9 := (fun mask => (mask,id))

def c19684 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19684 : Upper (D 8) (R 8) [34,260,9,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19684 c19684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9576
  · exact u9577
  · exact u9578
  · exact u9579
  · exact u9580
  · exact u9581

def r19685 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19685 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19685 : Upper (D 8) (R 8) [34,260,9,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192] 13 (by decide) (choices 2) [33,65,96,192] r19685 c19685
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9582
  · exact u9583
  · exact u9584
  · exact u9585

def b19686 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 28 41 241 225 225 225 481), lower := (rows 35 262 28 41 16 32 64 128 256), losses := [] }

theorem u19686 : Upper (D 8) (R 8) [34,260,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19687_33 : Upper (D 8) (R 8) [34,260,24,65,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9586

def r19687 : Route 9 := (fun mask => (mask,id))

def c19687 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19687 : Upper (D 8) (R 8) [34,260,24,65] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19687 c19687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19687_33
  · exact u9589
  · exact u9590
  · exact u9591
  · exact u9592
  · exact u9593

theorem m19688_33 : Upper (D 8) (R 8) [34,260,24,96,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9587

theorem m19688_65 : Upper (D 8) (R 8) [34,260,24,96,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9590

theorem m19688_129 : Upper (D 8) (R 8) [34,260,24,96,129] 13 :=
  permutation_upper _ _ _ [34,260,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9592

def r19688 : Route 9 := (fun mask => (mask,id))

def c19688 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19688 : Upper (D 8) (R 8) [34,260,24,96] 13 := by
  apply FastRouting.sound _ _ [34,260,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19688 c19688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19688_33
  · exact m19688_65
  · exact u9594
  · exact m19688_129
  · exact u9595
  · exact u9596

theorem m19689_33 : Upper (D 8) (R 8) [34,260,24,192,33] 13 :=
  permutation_upper _ _ _ [34,260,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9588

theorem m19689_65 : Upper (D 8) (R 8) [34,260,24,192,65] 13 :=
  permutation_upper _ _ _ [34,260,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9593

theorem m19689_96 : Upper (D 8) (R 8) [34,260,24,192,96] 13 :=
  permutation_upper _ _ _ [34,260,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9596

def r19689 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19689 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19689 : Upper (D 8) (R 8) [34,260,24,192] 13 := by
  apply FastRouting.sound _ _ [34,260,24,192] 13 (by decide) (choices 2) [33,65,96,192] r19689 c19689
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m19689_33
  · exact m19689_65
  · exact m19689_96
  · exact u9597

def r19690 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19690 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19690 : Upper (D 8) (R 8) [34,260,40,17] 13 := by
  apply FastRouting.sound _ _ [34,260,40,17] 13 (by decide) (choices 2) [33,65,96,192] r19690 c19690
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9598
  · exact u9599
  · exact u9600
  · exact u9601

def b19691 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 44 41 209 241 209 209 465), lower := (rows 35 262 44 41 16 32 64 128 256), losses := [] }

theorem u19691 : Upper (D 8) (R 8) [34,260,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19692 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 44 56 209 225 193 193 449), lower := (rows 35 262 44 56 16 32 64 128 256), losses := [] }

theorem u19692 : Upper (D 8) (R 8) [34,260,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19693 : Route 9 := (fun mask => (mask,id))

def c19693 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19693 : Upper (D 8) (R 8) [34,260,40,65] 13 := by
  apply FastRouting.sound _ _ [34,260,40,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19693 c19693
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9602
  · exact u9603
  · exact u9604
  · exact u9605
  · exact u9606
  · exact u9607

def r19694 : Route 9 := (fun mask => (mask,id))

def c19694 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19694 : Upper (D 8) (R 8) [34,260,40,80] 13 := by
  apply FastRouting.sound _ _ [34,260,40,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19694 c19694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9608
  · exact u9609
  · exact u9610
  · exact u9611
  · exact u9612
  · exact u9613

def b19695 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 44 104 209 241 209 209 465), lower := (rows 35 262 44 104 16 32 64 128 256), losses := [] }

theorem u19695 : Upper (D 8) (R 8) [34,260,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19696 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19696 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19696 : Upper (D 8) (R 8) [34,260,40,192] 13 := by
  apply FastRouting.sound _ _ [34,260,40,192] 13 (by decide) (choices 2) [33,65,96,192] r19696 c19696
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9614
  · exact u9615
  · exact u9616
  · exact u9617

def b19697 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 25 248 232 232 232 488), lower := (rows 35 262 69 25 16 32 64 128 256), losses := [] }

theorem u19697 : Upper (D 8) (R 8) [34,260,65,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19698 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 41 248 248 248 248 504), lower := (rows 35 262 69 41 16 32 64 128 256), losses := [] }

theorem u19698 : Upper (D 8) (R 8) [34,260,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19699_9 : Upper (D 8) (R 8) [34,260,65,48,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9618

theorem m19699_33 : Upper (D 8) (R 8) [34,260,65,48,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9624

def r19699 : Route 9 := (fun mask => (mask,id))

def c19699 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19699 : Upper (D 8) (R 8) [34,260,65,48] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19699 c19699
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19699_9
  · exact m19699_33
  · exact u9630
  · exact u9631
  · exact u9632
  · exact u9633
  · exact u9634
  · exact u9635
  · exact u9636
  · exact u9637

def b19700 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 184 184 248 184 440), lower := (rows 35 262 69 73 16 32 64 128 256), losses := [] }

theorem u19700 : Upper (D 8) (R 8) [34,260,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19701_9 : Upper (D 8) (R 8) [34,260,65,80,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9619

theorem m19701_33 : Upper (D 8) (R 8) [34,260,65,80,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9625

theorem m19701_40 : Upper (D 8) (R 8) [34,260,65,80,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9632

def r19701 : Route 9 := (fun mask => (mask,id))

def c19701 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19701 : Upper (D 8) (R 8) [34,260,65,80] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19701 c19701
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19701_9
  · exact m19701_33
  · exact m19701_40
  · exact u9640
  · exact u9641
  · exact u9642

theorem m19702_9 : Upper (D 8) (R 8) [34,260,65,96,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9620

theorem m19702_33 : Upper (D 8) (R 8) [34,260,65,96,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9626

theorem m19702_40 : Upper (D 8) (R 8) [34,260,65,96,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9633

def r19702 : Route 9 := (fun mask => (mask,id))

def c19702 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19702 : Upper (D 8) (R 8) [34,260,65,96] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19702 c19702
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19702_9
  · exact m19702_33
  · exact m19702_40
  · exact u9643
  · exact u9644
  · exact u9645

def b19703 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 137 248 248 248 248 504), lower := (rows 35 262 69 137 16 32 64 128 256), losses := [] }

theorem u19703 : Upper (D 8) (R 8) [34,260,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19704_9 : Upper (D 8) (R 8) [34,260,65,144,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9621

theorem m19704_33 : Upper (D 8) (R 8) [34,260,65,144,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9627

theorem m19704_40 : Upper (D 8) (R 8) [34,260,65,144,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9635

theorem m19704_65 : Upper (D 8) (R 8) [34,260,65,144,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9638

theorem m19704_72 : Upper (D 8) (R 8) [34,260,65,144,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9641

theorem m19704_96 : Upper (D 8) (R 8) [34,260,65,144,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9644

theorem m19704_129 : Upper (D 8) (R 8) [34,260,65,144,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9646

def r19704 : Route 9 := (fun mask => (mask,id))

def c19704 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19704 : Upper (D 8) (R 8) [34,260,65,144] 13 := by
  apply FastRouting.sound _ _ [34,260,65,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19704 c19704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19704_9
  · exact m19704_33
  · exact m19704_40
  · exact m19704_65
  · exact m19704_72
  · exact m19704_96
  · exact m19704_129
  · exact u9649
  · exact u9650
  · exact u9651

theorem m19705_9 : Upper (D 8) (R 8) [34,260,65,160,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9622

theorem m19705_33 : Upper (D 8) (R 8) [34,260,65,160,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9628

theorem m19705_40 : Upper (D 8) (R 8) [34,260,65,160,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9636

theorem m19705_65 : Upper (D 8) (R 8) [34,260,65,160,65] 13 :=
  permutation_upper _ _ _ [34,260,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9639

theorem m19705_72 : Upper (D 8) (R 8) [34,260,65,160,72] 13 :=
  permutation_upper _ _ _ [34,260,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9642

theorem m19705_96 : Upper (D 8) (R 8) [34,260,65,160,96] 13 :=
  permutation_upper _ _ _ [34,260,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9645

theorem m19705_129 : Upper (D 8) (R 8) [34,260,65,160,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9647

theorem m19705_136 : Upper (D 8) (R 8) [34,260,65,160,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9650

def r19705 : Route 9 := (fun mask => (mask,id))

def c19705 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19705 : Upper (D 8) (R 8) [34,260,65,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19705 c19705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19705_9
  · exact m19705_33
  · exact m19705_40
  · exact m19705_65
  · exact m19705_72
  · exact m19705_96
  · exact m19705_129
  · exact m19705_136
  · exact u9652
  · exact u9653

theorem m19706_9 : Upper (D 8) (R 8) [34,260,65,192,9] 13 :=
  permutation_upper _ _ _ [34,260,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9623

theorem m19706_33 : Upper (D 8) (R 8) [34,260,65,192,33] 13 :=
  permutation_upper _ _ _ [34,260,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9629

theorem m19706_40 : Upper (D 8) (R 8) [34,260,65,192,40] 13 :=
  permutation_upper _ _ _ [34,260,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9637

theorem m19706_129 : Upper (D 8) (R 8) [34,260,65,192,129] 13 :=
  permutation_upper _ _ _ [34,260,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9648

theorem m19706_136 : Upper (D 8) (R 8) [34,260,65,192,136] 13 :=
  permutation_upper _ _ _ [34,260,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9651

theorem m19706_160 : Upper (D 8) (R 8) [34,260,65,192,160] 13 :=
  permutation_upper _ _ _ [34,260,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9653

def r19706 : Route 9 := (fun mask => (mask,id))

def c19706 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19706 : Upper (D 8) (R 8) [34,260,65,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19706 c19706
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19706_9
  · exact m19706_33
  · exact m19706_40
  · exact m19706_129
  · exact m19706_136
  · exact m19706_160

def r19707 : Route 9 := (fun mask => (mask,id))

def c19707 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19707 : Upper (D 8) (R 8) [34,260,72,17] 13 := by
  apply FastRouting.sound _ _ [34,260,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19707 c19707
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9654
  · exact u9655
  · exact u9656
  · exact u9657
  · exact u9658
  · exact u9659

def b19708 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 41 241 241 241 241 497), lower := (rows 35 262 76 41 16 32 64 128 256), losses := [] }

theorem u19708 : Upper (D 8) (R 8) [34,260,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19709 : Route 9 := (fun mask => (mask,id))

def c19709 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19709 : Upper (D 8) (R 8) [34,260,72,48] 13 := by
  apply FastRouting.sound _ _ [34,260,72,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19709 c19709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9660
  · exact u9661
  · exact u9662
  · exact u9663
  · exact u9664
  · exact u9665

def b19710 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 73 177 177 241 177 433), lower := (rows 35 262 76 73 16 32 64 128 256), losses := [] }

theorem u19710 : Upper (D 8) (R 8) [34,260,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19711 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 88 177 161 225 161 417), lower := (rows 35 262 76 88 16 32 64 128 256), losses := [] }

theorem u19711 : Upper (D 8) (R 8) [34,260,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19712 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 104 177 177 241 177 433), lower := (rows 35 262 76 104 16 32 64 128 256), losses := [] }

theorem u19712 : Upper (D 8) (R 8) [34,260,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19713 : Route 9 := (fun mask => (mask,id))

def c19713 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19713 : Upper (D 8) (R 8) [34,260,72,129] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19713 c19713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9666
  · exact u9667
  · exact u9668
  · exact u9669
  · exact u9670
  · exact u9671

def r19714 : Route 9 := (fun mask => (mask,id))

def c19714 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19714 : Upper (D 8) (R 8) [34,260,72,144] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19714 c19714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9672
  · exact u9673
  · exact u9674
  · exact u9675
  · exact u9676
  · exact u9677

def r19715 : Route 9 := (fun mask => (mask,id))

def c19715 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19715 : Upper (D 8) (R 8) [34,260,72,160] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19715 c19715
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9678
  · exact u9679
  · exact u9680
  · exact u9681
  · exact u9682
  · exact u9683

def b19716 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 200 177 177 241 177 433), lower := (rows 35 262 76 200 16 32 64 128 256), losses := [] }

theorem u19716 : Upper (D 8) (R 8) [34,260,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19717 : Route 9 := (fun mask => (mask,id))

def c19717 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19717 : Upper (D 8) (R 8) [34,260,96,17] 13 := by
  apply FastRouting.sound _ _ [34,260,96,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19717 c19717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9684
  · exact u9685
  · exact u9686
  · exact u9687
  · exact u9688
  · exact u9689
  · exact u9690
  · exact u9691
  · exact u9692
  · exact u9693

def b19718 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 100 41 217 249 217 217 473), lower := (rows 35 262 100 41 16 32 64 128 256), losses := [] }

theorem u19718 : Upper (D 8) (R 8) [34,260,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19719_9 : Upper (D 8) (R 8) [34,260,96,48,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9686

def r19719 : Route 9 := (fun mask => (mask,id))

def c19719 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19719 : Upper (D 8) (R 8) [34,260,96,48] 13 := by
  apply FastRouting.sound _ _ [34,260,96,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19719 c19719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19719_9
  · exact u9698
  · exact u9699
  · exact u9700
  · exact u9701
  · exact u9702

def b19720 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 100 73 185 185 249 185 441), lower := (rows 35 262 100 73 16 32 64 128 256), losses := [] }

theorem u19720 : Upper (D 8) (R 8) [34,260,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19721_9 : Upper (D 8) (R 8) [34,260,96,80,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9688

theorem m19721_33 : Upper (D 8) (R 8) [34,260,96,80,33] 13 :=
  permutation_upper _ _ _ [34,260,96,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9694

theorem m19721_40 : Upper (D 8) (R 8) [34,260,96,80,40] 13 :=
  permutation_upper _ _ _ [34,260,96,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9699

def r19721 : Route 9 := (fun mask => (mask,id))

def c19721 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19721 : Upper (D 8) (R 8) [34,260,96,80] 13 := by
  apply FastRouting.sound _ _ [34,260,96,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19721 c19721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19721_9
  · exact m19721_33
  · exact m19721_40
  · exact u9706
  · exact u9707
  · exact u9708

def b19722 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 104 153 185 217 153 409), lower := (rows 35 262 100 104 16 32 64 128 256), losses := [] }

theorem u19722 : Upper (D 8) (R 8) [34,260,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19723_9 : Upper (D 8) (R 8) [34,260,96,129,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9690

theorem m19723_33 : Upper (D 8) (R 8) [34,260,96,129,33] 13 :=
  permutation_upper _ _ _ [34,260,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9695

theorem m19723_40 : Upper (D 8) (R 8) [34,260,96,129,40] 13 :=
  permutation_upper _ _ _ [34,260,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9700

theorem m19723_65 : Upper (D 8) (R 8) [34,260,96,129,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9703

theorem m19723_72 : Upper (D 8) (R 8) [34,260,96,129,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9706

theorem m19723_96 : Upper (D 8) (R 8) [34,260,96,129,96] 13 :=
  permutation_upper _ _ _ [34,260,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9709

def r19723 : Route 9 := (fun mask => (mask,id))

def c19723 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19723 : Upper (D 8) (R 8) [34,260,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19723 c19723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19723_9
  · exact m19723_33
  · exact m19723_40
  · exact m19723_65
  · exact m19723_72
  · exact m19723_96
  · exact u9711
  · exact u9712
  · exact u9713
  · exact u9714

theorem m19724_9 : Upper (D 8) (R 8) [34,260,96,144,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9691

theorem m19724_33 : Upper (D 8) (R 8) [34,260,96,144,33] 13 :=
  permutation_upper _ _ _ [34,260,96,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9696

theorem m19724_40 : Upper (D 8) (R 8) [34,260,96,144,40] 13 :=
  permutation_upper _ _ _ [34,260,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9701

theorem m19724_65 : Upper (D 8) (R 8) [34,260,96,144,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9704

theorem m19724_72 : Upper (D 8) (R 8) [34,260,96,144,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9707

theorem m19724_96 : Upper (D 8) (R 8) [34,260,96,144,96] 13 :=
  permutation_upper _ _ _ [34,260,96,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9710

theorem m19724_129 : Upper (D 8) (R 8) [34,260,96,144,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9712

def r19724 : Route 9 := (fun mask => (mask,id))

def c19724 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19724 : Upper (D 8) (R 8) [34,260,96,144] 13 := by
  apply FastRouting.sound _ _ [34,260,96,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19724 c19724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19724_9
  · exact m19724_33
  · exact m19724_40
  · exact m19724_65
  · exact m19724_72
  · exact m19724_96
  · exact m19724_129
  · exact u9715
  · exact u9716
  · exact u9717

theorem m19725_9 : Upper (D 8) (R 8) [34,260,96,160,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9692

theorem m19725_65 : Upper (D 8) (R 8) [34,260,96,160,65] 13 :=
  permutation_upper _ _ _ [34,260,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9705

theorem m19725_72 : Upper (D 8) (R 8) [34,260,96,160,72] 13 :=
  permutation_upper _ _ _ [34,260,96,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9708

theorem m19725_129 : Upper (D 8) (R 8) [34,260,96,160,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9713

theorem m19725_136 : Upper (D 8) (R 8) [34,260,96,160,136] 13 :=
  permutation_upper _ _ _ [34,260,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9716

def r19725 : Route 9 := (fun mask => (mask,id))

def c19725 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19725 : Upper (D 8) (R 8) [34,260,96,160] 13 := by
  apply FastRouting.sound _ _ [34,260,96,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19725 c19725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19725_9
  · exact m19725_65
  · exact m19725_72
  · exact m19725_129
  · exact m19725_136
  · exact u9718

theorem m19726_9 : Upper (D 8) (R 8) [34,260,96,192,9] 13 :=
  permutation_upper _ _ _ [34,260,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9693

theorem m19726_33 : Upper (D 8) (R 8) [34,260,96,192,33] 13 :=
  permutation_upper _ _ _ [34,260,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9697

theorem m19726_40 : Upper (D 8) (R 8) [34,260,96,192,40] 13 :=
  permutation_upper _ _ _ [34,260,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9702

theorem m19726_129 : Upper (D 8) (R 8) [34,260,96,192,129] 13 :=
  permutation_upper _ _ _ [34,260,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9714

theorem m19726_136 : Upper (D 8) (R 8) [34,260,96,192,136] 13 :=
  permutation_upper _ _ _ [34,260,96,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9717

theorem m19726_160 : Upper (D 8) (R 8) [34,260,96,192,160] 13 :=
  permutation_upper _ _ _ [34,260,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9718

def r19726 : Route 9 := (fun mask => (mask,id))

def c19726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19726 : Upper (D 8) (R 8) [34,260,96,192] 13 := by
  apply FastRouting.sound _ _ [34,260,96,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19726 c19726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19726_9
  · exact m19726_33
  · exact m19726_40
  · exact m19726_129
  · exact m19726_136
  · exact m19726_160

def r19727 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19727 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19727 : Upper (D 8) (R 8) [34,260,192,17] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19727 c19727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9719
  · exact u9720
  · exact u9721
  · exact u9722
  · exact u9723
  · exact u9724
  · exact u9725

def b19728 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 196 41 249 249 249 249 505), lower := (rows 35 262 196 41 16 32 64 128 256), losses := [] }

theorem u19728 : Upper (D 8) (R 8) [34,260,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19729_9 : Upper (D 8) (R 8) [34,260,192,48,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9721

theorem m19729_33 : Upper (D 8) (R 8) [34,260,192,48,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9726

def r19729 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19729 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19729 : Upper (D 8) (R 8) [34,260,192,48] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19729 c19729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19729_9
  · exact m19729_33
  · exact u9729
  · exact u9730
  · exact u9731
  · exact u9732
  · exact u9733

def b19730 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 262 196 73 185 185 249 185 441), lower := (rows 35 262 196 73 16 32 64 128 256), losses := [] }

theorem u19730 : Upper (D 8) (R 8) [34,260,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19731_9 : Upper (D 8) (R 8) [34,260,192,80,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9723

theorem m19731_33 : Upper (D 8) (R 8) [34,260,192,80,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9727

theorem m19731_40 : Upper (D 8) (R 8) [34,260,192,80,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9731

theorem m19731_129 : Upper (D 8) (R 8) [34,260,192,80,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9734

def r19731 : Route 9 := (fun mask => (mask,id))

def c19731 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19731 : Upper (D 8) (R 8) [34,260,192,80] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19731 c19731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19731_9
  · exact m19731_33
  · exact m19731_40
  · exact m19731_129
  · exact u9736
  · exact u9737

theorem m19732_9 : Upper (D 8) (R 8) [34,260,192,96,9] 13 :=
  permutation_upper _ _ _ [34,260,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9724

theorem m19732_33 : Upper (D 8) (R 8) [34,260,192,96,33] 13 :=
  permutation_upper _ _ _ [34,260,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9728

theorem m19732_40 : Upper (D 8) (R 8) [34,260,192,96,40] 13 :=
  permutation_upper _ _ _ [34,260,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9732

theorem m19732_129 : Upper (D 8) (R 8) [34,260,192,96,129] 13 :=
  permutation_upper _ _ _ [34,260,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9735

theorem m19732_136 : Upper (D 8) (R 8) [34,260,192,96,136] 13 :=
  permutation_upper _ _ _ [34,260,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9737

def r19732 : Route 9 := (fun mask => (mask,id))

def c19732 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19732 : Upper (D 8) (R 8) [34,260,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19732 c19732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19732_9
  · exact m19732_33
  · exact m19732_40
  · exact m19732_129
  · exact m19732_136
  · exact u9738

def b19733 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 196 200 57 57 121 185 313), lower := (rows 35 262 196 200 16 32 64 128 256), losses := [] }

theorem u19733 : Upper (D 8) (R 8) [34,260,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19733 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19734 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 13 240 240 240 240 496), lower := (rows 35 322 13 13 16 32 64 128 256), losses := [] }

theorem u19734 : Upper (D 8) (R 8) [34,320,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19735 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 25 244 228 228 228 484), lower := (rows 35 322 13 25 16 32 64 128 256), losses := [] }

theorem u19735 : Upper (D 8) (R 8) [34,320,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19736 : Route 9 := (fun mask => (mask,id))

def c19736 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19736 : Upper (D 8) (R 8) [34,320,9,20] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19736 c19736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9748
  · exact u9749
  · exact u9750
  · exact u9751
  · exact u9752
  · exact u9753

def b19737 : PairBound 9 := { available := 244, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 41 244 244 244 244 500), lower := (rows 35 322 13 41 16 32 64 128 256), losses := [] }

theorem u19737 : Upper (D 8) (R 8) [34,320,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19738 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 44 241 241 241 241 497), lower := (rows 35 322 13 44 16 32 64 128 256), losses := [] }

theorem u19738 : Upper (D 8) (R 8) [34,320,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19739_5 : Upper (D 8) (R 8) [34,320,9,48,5] 13 :=
  permutation_upper _ _ _ [34,320,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9742

def r19739 : Route 9 := (fun mask => (mask,id))

def c19739 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19739 : Upper (D 8) (R 8) [34,320,9,48] 13 := by
  apply FastRouting.sound _ _ [34,320,9,48] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r19739 c19739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19739_5
  · exact u9764
  · exact u9765
  · exact u9766
  · exact u9767
  · exact u9768
  · exact u9769
  · exact u9770
  · exact u9771
  · exact u9772

#print axioms u19739
end Delivery.IrregularNine14.P08
