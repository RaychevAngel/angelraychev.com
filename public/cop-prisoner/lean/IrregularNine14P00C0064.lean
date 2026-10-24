import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0062
import IrregularNine14P00C0063

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 239, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 239 239 255 239 239 239 495), lower := (rows 305 19 4 8 16 32 64 128 256), losses := [] }

theorem u3840 : Upper (D 0) (R 0) [304,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3840
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3841_3 : Upper (D 0) (R 0) [304,20,3] 13 :=
  permutation_upper _ _ _ [304,5,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3724

theorem m3841_9 : Upper (D 0) (R 0) [304,20,9] 13 :=
  permutation_upper _ _ _ [304,9,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3732

theorem m3841_10 : Upper (D 0) (R 0) [304,20,10] 13 :=
  permutation_upper _ _ _ [304,12,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3738

theorem m3841_33 : Upper (D 0) (R 0) [304,20,33] 13 :=
  permutation_upper _ _ _ [304,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3744

def r3841 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3841 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3841 : Upper (D 0) (R 0) [304,20] 13 := by
  apply FastRouting.sound _ _ [304,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r3841 c3841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3841_3
  · exact m3841_9
  · exact m3841_10
  · exact m3841_33
  · exact u3749
  · exact u3750
  · exact u3751
  · exact u3752
  · exact u3753
  · exact u3754
  · exact u3755

def b3842 : PairBound 9 := { available := 207, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 207 207 223 239 207 207 463), lower := (rows 305 50 4 8 16 32 64 128 256), losses := [] }

theorem u3842 : Upper (D 0) (R 0) [304,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3842
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3843_3 : Upper (D 0) (R 0) [304,65,3] 13 :=
  permutation_upper _ _ _ [304,5,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3727

theorem m3843_9 : Upper (D 0) (R 0) [304,65,9] 13 :=
  permutation_upper _ _ _ [304,9,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3733

theorem m3843_10 : Upper (D 0) (R 0) [304,65,10] 13 :=
  permutation_upper _ _ _ [304,12,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3740

theorem m3843_17 : Upper (D 0) (R 0) [304,65,17] 13 :=
  permutation_upper _ _ _ [304,17,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3745

theorem m3843_18 : Upper (D 0) (R 0) [304,65,18] 13 :=
  permutation_upper _ _ _ [304,20,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3751

theorem m3843_24 : Upper (D 0) (R 0) [304,65,24] 13 :=
  permutation_upper _ _ _ [304,24,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3756

theorem m3843_48 : Upper (D 0) (R 0) [304,65,48] 13 :=
  permutation_upper _ _ _ [304,48,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3760

def r3843 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c3843 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3843 : Upper (D 0) (R 0) [304,65] 13 := by
  apply FastRouting.sound _ _ [304,65] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192] r3843 c3843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3843_3
  · exact m3843_9
  · exact m3843_10
  · exact m3843_17
  · exact m3843_18
  · exact m3843_24
  · exact m3843_48
  · exact u3763
  · exact u3764
  · exact u3765
  · exact u3766
  · exact u3767
  · exact u3768
  · exact u3769
  · exact u3770
  · exact u3771

theorem m3844_3 : Upper (D 0) (R 0) [304,68,3] 13 :=
  permutation_upper _ _ _ [304,5,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3728

theorem m3844_9 : Upper (D 0) (R 0) [304,68,9] 13 :=
  permutation_upper _ _ _ [304,9,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3734

theorem m3844_10 : Upper (D 0) (R 0) [304,68,10] 13 :=
  permutation_upper _ _ _ [304,12,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3741

theorem m3844_17 : Upper (D 0) (R 0) [304,68,17] 13 :=
  permutation_upper _ _ _ [304,17,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3746

theorem m3844_18 : Upper (D 0) (R 0) [304,68,18] 13 :=
  permutation_upper _ _ _ [304,20,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3752

theorem m3844_24 : Upper (D 0) (R 0) [304,68,24] 13 :=
  permutation_upper _ _ _ [304,24,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3757

theorem m3844_48 : Upper (D 0) (R 0) [304,68,48] 13 :=
  permutation_upper _ _ _ [304,48,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3761

theorem m3844_65 : Upper (D 0) (R 0) [304,68,65] 13 :=
  permutation_upper _ _ _ [304,65,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3764

theorem m3844_129 : Upper (D 0) (R 0) [304,68,129] 13 :=
  permutation_upper _ _ _ [304,65,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3768

def r3844 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c3844 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3844 : Upper (D 0) (R 0) [304,68] 13 := by
  apply FastRouting.sound _ _ [304,68] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192] r3844 c3844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3844_3
  · exact m3844_9
  · exact m3844_10
  · exact m3844_17
  · exact m3844_18
  · exact m3844_24
  · exact m3844_48
  · exact m3844_65
  · exact u3772
  · exact u3773
  · exact u3774
  · exact m3844_129
  · exact u3775
  · exact u3776
  · exact u3777
  · exact u3778

theorem m3845_3 : Upper (D 0) (R 0) [304,80,3] 13 :=
  permutation_upper _ _ _ [304,5,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3730

theorem m3845_9 : Upper (D 0) (R 0) [304,80,9] 13 :=
  permutation_upper _ _ _ [304,9,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3735

theorem m3845_10 : Upper (D 0) (R 0) [304,80,10] 13 :=
  permutation_upper _ _ _ [304,12,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3742

theorem m3845_33 : Upper (D 0) (R 0) [304,80,33] 13 :=
  permutation_upper _ _ _ [304,17,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3747

theorem m3845_34 : Upper (D 0) (R 0) [304,80,34] 13 :=
  permutation_upper _ _ _ [304,20,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3754

theorem m3845_40 : Upper (D 0) (R 0) [304,80,40] 13 :=
  permutation_upper _ _ _ [304,24,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3758

theorem m3845_65 : Upper (D 0) (R 0) [304,80,65] 13 :=
  permutation_upper _ _ _ [304,65,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3766

theorem m3845_66 : Upper (D 0) (R 0) [304,80,66] 13 :=
  permutation_upper _ _ _ [304,68,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3774

theorem m3845_72 : Upper (D 0) (R 0) [304,80,72] 13 :=
  permutation_upper _ _ _ [304,72,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3779

theorem m3845_129 : Upper (D 0) (R 0) [304,80,129] 13 :=
  permutation_upper _ _ _ [304,65,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3770

theorem m3845_130 : Upper (D 0) (R 0) [304,80,130] 13 :=
  permutation_upper _ _ _ [304,68,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3777

theorem m3845_136 : Upper (D 0) (R 0) [304,80,136] 13 :=
  permutation_upper _ _ _ [304,72,144] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3780

def r3845 : Route 9 := (fun mask => (mask,id))

def c3845 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3845 : Upper (D 0) (R 0) [304,80] 13 := by
  apply FastRouting.sound _ _ [304,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r3845 c3845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3845_3
  · exact m3845_9
  · exact m3845_10
  · exact m3845_33
  · exact m3845_34
  · exact m3845_40
  · exact m3845_65
  · exact m3845_66
  · exact m3845_72
  · exact u3782
  · exact m3845_129
  · exact m3845_130
  · exact m3845_136
  · exact u3783
  · exact u3784

theorem m3846_3 : Upper (D 0) (R 0) [304,192,3] 13 :=
  permutation_upper _ _ _ [304,5,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3731

theorem m3846_9 : Upper (D 0) (R 0) [304,192,9] 13 :=
  permutation_upper _ _ _ [304,9,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3736

theorem m3846_10 : Upper (D 0) (R 0) [304,192,10] 13 :=
  permutation_upper _ _ _ [304,12,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3743

theorem m3846_17 : Upper (D 0) (R 0) [304,192,17] 13 :=
  permutation_upper _ _ _ [304,17,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3748

theorem m3846_18 : Upper (D 0) (R 0) [304,192,18] 13 :=
  permutation_upper _ _ _ [304,20,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3755

theorem m3846_24 : Upper (D 0) (R 0) [304,192,24] 13 :=
  permutation_upper _ _ _ [304,24,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3759

theorem m3846_48 : Upper (D 0) (R 0) [304,192,48] 13 :=
  permutation_upper _ _ _ [304,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3762

theorem m3846_65 : Upper (D 0) (R 0) [304,192,65] 13 :=
  permutation_upper _ _ _ [304,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3771

theorem m3846_66 : Upper (D 0) (R 0) [304,192,66] 13 :=
  permutation_upper _ _ _ [304,68,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3778

theorem m3846_72 : Upper (D 0) (R 0) [304,192,72] 13 :=
  permutation_upper _ _ _ [304,72,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3781

theorem m3846_80 : Upper (D 0) (R 0) [304,192,80] 13 :=
  permutation_upper _ _ _ [304,80,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3784

def r3846 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3846 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3846 : Upper (D 0) (R 0) [304,192] 13 := by
  apply FastRouting.sound _ _ [304,192] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192] r3846 c3846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3846_3
  · exact m3846_9
  · exact m3846_10
  · exact m3846_17
  · exact m3846_18
  · exact m3846_24
  · exact m3846_48
  · exact m3846_65
  · exact m3846_66
  · exact m3846_72
  · exact m3846_80
  · exact u3785

def r3847 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 384 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

def c3847 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3847 : Upper (D 0) (R 0) [14] 13 := by
  apply FastRouting.sound _ _ [14] 13 (by decide) (choices 2) [17,48,257,272] r3847 c3847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3786
  · exact u3787
  · exact u3788
  · exact u3789

def r3848 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c3848 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3848 : Upper (D 0) (R 0) [22] 13 := by
  apply FastRouting.sound _ _ [22] 13 (by decide) (choices 2) [9,17,24,33,40,48,96,257,264,272,288] r3848 c3848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3790
  · exact u3791
  · exact u3792
  · exact u3793
  · exact u3794
  · exact u3795
  · exact u3796
  · exact u3797
  · exact u3798
  · exact u3799
  · exact u3800

def r3849 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3849 : Nat → Fin 9 := (fun _ => 0)

theorem u3849 : Upper (D 0) (R 0) [50] 13 := by
  apply FastRouting.sound _ _ [50] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192,257,260,272,320] r3849 c3849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3801
  · exact u3802
  · exact u3803
  · exact u3804
  · exact u3805
  · exact u3806
  · exact u3807
  · exact u3808
  · exact u3809
  · exact u3810
  · exact u3811
  · exact u3812
  · exact u3813

def r3850 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c3850 : Nat → Fin 9 := (fun _ => 0)

theorem u3850 : Upper (D 0) (R 0) [112] 13 := by
  apply FastRouting.sound _ _ [112] 13 (by decide) (choices 2) [5,12,17,20,48,129,132,144,257,260,272,384] r3850 c3850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3814
  · exact u3815
  · exact u3816
  · exact u3817
  · exact u3818
  · exact u3819
  · exact u3820
  · exact u3821
  · exact u3822
  · exact u3823
  · exact u3824
  · exact u3825

def r3851 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c3851 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3851 : Upper (D 0) (R 0) [262] 13 := by
  apply FastRouting.sound _ _ [262] 13 (by decide) (choices 2) [9,17,24,48] r3851 c3851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3826
  · exact u3827
  · exact u3828
  · exact u3829

def r3852 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c3852 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3852 : Upper (D 0) (R 0) [274] 13 := by
  apply FastRouting.sound _ _ [274] 13 (by decide) (choices 2) [5,12,17,20,33,36,48,96] r3852 c3852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3830
  · exact u3831
  · exact u3832
  · exact u3833
  · exact u3834
  · exact u3835
  · exact u3836
  · exact u3837

def r3853 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3853 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3853 : Upper (D 0) (R 0) [304] 13 := by
  apply FastRouting.sound _ _ [304] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192] r3853 c3853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3838
  · exact u3839
  · exact u3840
  · exact u3841
  · exact u3842
  · exact u3843
  · exact u3844
  · exact u3845
  · exact u3846

def r3854 : Route 9 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 70 => (22,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 134 => (22,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 42 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 74 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 138 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 266 => (262,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 162 => (50,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 290 => (274,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 194 => (50,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 322 => (274,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 386 => (274,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 28 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 44 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 76 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 140 => (22,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 268 => (262,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 52 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 84 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 148 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 276 => (274,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 100 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 164 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 292 => (274,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 196 => (50,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 324 => (274,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 388 => (274,(fun i => match i.val with | 1 => 2 | 2 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 56 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 88 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 152 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 280 => (274,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 104 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 168 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 296 => (274,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | _ => i)) | 200 => (50,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 328 => (274,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 6 | 6 => 4 | _ => i)) | 392 => (274,(fun i => match i.val with | 1 => 3 | 3 => 1 | 4 => 7 | 7 => 4 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 336 => (304,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 400 => (304,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 224 => (112,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 352 => (304,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 416 => (304,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 448 => (304,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c3854 : Nat → Fin 9 := (fun _ => 0)

theorem u3854 : Upper (D 0) (R 0) [] 13 := by
  apply FastRouting.sound _ _ [] 13 (by decide) (choices 3) [14,22,50,112,262,274,304] r3854 c3854
    (by exact cover_three)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3847
  · exact u3848
  · exact u3849
  · exact u3850
  · exact u3851
  · exact u3852
  · exact u3853

#print axioms u3854
end Delivery.IrregularNine14.P00
