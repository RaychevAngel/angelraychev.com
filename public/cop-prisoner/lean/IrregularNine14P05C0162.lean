import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0141
import IrregularNine14P05C0142
import IrregularNine14P05C0143
import IrregularNine14P05C0144
import IrregularNine14P05C0145
import IrregularNine14P05C0146
import IrregularNine14P05C0147
import IrregularNine14P05C0148
import IrregularNine14P05C0149
import IrregularNine14P05C0150
import IrregularNine14P05C0151
import IrregularNine14P05C0152
import IrregularNine14P05C0153
import IrregularNine14P05C0154
import IrregularNine14P05C0155

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9720_3 : Upper (D 5) (R 5) [10,80,160,3] 13 :=
  permutation_upper _ _ _ [6,5,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8509

theorem m9720_5 : Upper (D 5) (R 5) [10,80,160,5] 13 :=
  permutation_upper _ _ _ [6,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8582

theorem m9720_6 : Upper (D 5) (R 5) [10,80,160,6] 13 :=
  permutation_upper _ _ _ [6,12,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8649

theorem m9720_33 : Upper (D 5) (R 5) [10,80,160,33] 13 :=
  permutation_upper _ _ _ [6,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8885

theorem m9720_34 : Upper (D 5) (R 5) [10,80,160,34] 13 :=
  permutation_upper _ _ _ [6,36,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8942

theorem m9720_36 : Upper (D 5) (R 5) [10,80,160,36] 13 :=
  permutation_upper _ _ _ [6,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9004

theorem m9720_257 : Upper (D 5) (R 5) [10,80,160,257] 13 :=
  permutation_upper _ _ _ [6,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9097

theorem m9720_258 : Upper (D 5) (R 5) [10,80,160,258] 13 :=
  permutation_upper _ _ _ [6,68,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9138

theorem m9720_260 : Upper (D 5) (R 5) [10,80,160,260] 13 :=
  permutation_upper _ _ _ [6,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9168

theorem m9720_288 : Upper (D 5) (R 5) [10,80,160,288] 13 :=
  permutation_upper _ _ _ [6,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9195

def r9720 : Route 9 := (fun mask => (mask,id))

def c9720 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9720 : Upper (D 5) (R 5) [10,80,160] 13 := by
  apply FastRouting.sound _ _ [10,80,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9720 c9720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9720_3
  · exact m9720_5
  · exact m9720_6
  · exact m9720_33
  · exact m9720_34
  · exact m9720_36
  · exact m9720_257
  · exact m9720_258
  · exact m9720_260
  · exact m9720_288

theorem m9721_3 : Upper (D 5) (R 5) [10,80,384,3] 13 :=
  permutation_upper _ _ _ [6,5,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8510

theorem m9721_5 : Upper (D 5) (R 5) [10,80,384,5] 13 :=
  permutation_upper _ _ _ [6,9,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8583

theorem m9721_6 : Upper (D 5) (R 5) [10,80,384,6] 13 :=
  permutation_upper _ _ _ [6,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8650

theorem m9721_33 : Upper (D 5) (R 5) [10,80,384,33] 13 :=
  permutation_upper _ _ _ [6,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8886

theorem m9721_34 : Upper (D 5) (R 5) [10,80,384,34] 13 :=
  permutation_upper _ _ _ [6,36,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8943

theorem m9721_36 : Upper (D 5) (R 5) [10,80,384,36] 13 :=
  permutation_upper _ _ _ [6,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9005

def r9721 : Route 9 := (fun mask => (mask,id))

def c9721 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9721 : Upper (D 5) (R 5) [10,80,384] 13 := by
  apply FastRouting.sound _ _ [10,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9721 c9721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9721_3
  · exact m9721_5
  · exact m9721_6
  · exact m9721_33
  · exact m9721_34
  · exact m9721_36

theorem m9722_3 : Upper (D 5) (R 5) [10,96,17,3] 13 :=
  permutation_upper _ _ _ [6,5,96,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8511

theorem m9722_5 : Upper (D 5) (R 5) [10,96,17,5] 13 :=
  permutation_upper _ _ _ [6,9,18,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8538

theorem m9722_6 : Upper (D 5) (R 5) [10,96,17,6] 13 :=
  permutation_upper _ _ _ [6,12,96,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8651

theorem m9722_33 : Upper (D 5) (R 5) [10,96,17,33] 13 :=
  permutation_upper _ _ _ [6,33,96,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8887

theorem m9722_34 : Upper (D 5) (R 5) [10,96,17,34] 13 :=
  permutation_upper _ _ _ [6,36,96,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8944

theorem m9722_36 : Upper (D 5) (R 5) [10,96,17,36] 13 :=
  permutation_upper _ _ _ [6,40,96,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9006

theorem m9722_129 : Upper (D 5) (R 5) [10,96,17,129] 13 :=
  permutation_upper _ _ _ [6,65,160,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9099

theorem m9722_130 : Upper (D 5) (R 5) [10,96,17,130] 13 :=
  permutation_upper _ _ _ [6,68,160,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9139

theorem m9722_132 : Upper (D 5) (R 5) [10,96,17,132] 13 :=
  permutation_upper _ _ _ [6,72,160,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9169

theorem m9722_160 : Upper (D 5) (R 5) [10,96,17,160] 13 :=
  permutation_upper _ _ _ [6,96,160,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9200

theorem m9722_384 : Upper (D 5) (R 5) [10,96,17,384] 13 :=
  permutation_upper _ _ _ [6,96,384,17] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9206

def r9722 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9722 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9722 : Upper (D 5) (R 5) [10,96,17] 13 := by
  apply FastRouting.sound _ _ [10,96,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9722 c9722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9722_3
  · exact m9722_5
  · exact m9722_6
  · exact m9722_33
  · exact m9722_34
  · exact m9722_36
  · exact m9722_129
  · exact m9722_130
  · exact m9722_132
  · exact m9722_160
  · exact m9722_384

theorem m9723_5 : Upper (D 5) (R 5) [10,96,18,5] 13 :=
  permutation_upper _ _ _ [6,9,24,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8546

theorem m9723_33 : Upper (D 5) (R 5) [10,96,18,33] 13 :=
  permutation_upper _ _ _ [6,33,96,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8889

theorem m9723_36 : Upper (D 5) (R 5) [10,96,18,36] 13 :=
  permutation_upper _ _ _ [6,40,96,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9008

theorem m9723_129 : Upper (D 5) (R 5) [10,96,18,129] 13 :=
  permutation_upper _ _ _ [6,65,160,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9101

theorem m9723_132 : Upper (D 5) (R 5) [10,96,18,132] 13 :=
  permutation_upper _ _ _ [6,72,160,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9171

theorem m9723_160 : Upper (D 5) (R 5) [10,96,18,160] 13 :=
  permutation_upper _ _ _ [6,96,160,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9201

theorem m9723_384 : Upper (D 5) (R 5) [10,96,18,384] 13 :=
  permutation_upper _ _ _ [6,96,384,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9207

def r9723 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9723 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9723 : Upper (D 5) (R 5) [10,96,18] 13 := by
  apply FastRouting.sound _ _ [10,96,18] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9723 c9723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9723_5
  · exact m9723_33
  · exact m9723_36
  · exact m9723_129
  · exact m9723_132
  · exact m9723_160
  · exact m9723_384

theorem m9724_3 : Upper (D 5) (R 5) [10,96,33,3] 13 :=
  permutation_upper _ _ _ [6,5,96,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8512

theorem m9724_5 : Upper (D 5) (R 5) [10,96,33,5] 13 :=
  permutation_upper _ _ _ [6,9,34,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8556

theorem m9724_6 : Upper (D 5) (R 5) [10,96,33,6] 13 :=
  permutation_upper _ _ _ [6,12,96,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8653

theorem m9724_17 : Upper (D 5) (R 5) [10,96,33,17] 13 :=
  permutation_upper _ _ _ [6,17,96,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8712

theorem m9724_18 : Upper (D 5) (R 5) [10,96,33,18] 13 :=
  permutation_upper _ _ _ [6,20,96,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8756

theorem m9724_20 : Upper (D 5) (R 5) [10,96,33,20] 13 :=
  permutation_upper _ _ _ [6,24,96,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8810

theorem m9724_129 : Upper (D 5) (R 5) [10,96,33,129] 13 :=
  permutation_upper _ _ _ [6,65,160,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9102

theorem m9724_130 : Upper (D 5) (R 5) [10,96,33,130] 13 :=
  permutation_upper _ _ _ [6,68,160,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9141

theorem m9724_132 : Upper (D 5) (R 5) [10,96,33,132] 13 :=
  permutation_upper _ _ _ [6,72,160,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9172

theorem m9724_144 : Upper (D 5) (R 5) [10,96,33,144] 13 :=
  permutation_upper _ _ _ [6,80,160,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9189

theorem m9724_384 : Upper (D 5) (R 5) [10,96,33,384] 13 :=
  permutation_upper _ _ _ [6,96,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9209

def r9724 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9724 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9724 : Upper (D 5) (R 5) [10,96,33] 13 := by
  apply FastRouting.sound _ _ [10,96,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r9724 c9724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9724_3
  · exact m9724_5
  · exact m9724_6
  · exact m9724_17
  · exact m9724_18
  · exact m9724_20
  · exact m9724_129
  · exact m9724_130
  · exact m9724_132
  · exact m9724_144
  · exact m9724_384

theorem m9725_3 : Upper (D 5) (R 5) [10,96,48,3] 13 :=
  permutation_upper _ _ _ [6,5,96,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8513

theorem m9725_5 : Upper (D 5) (R 5) [10,96,48,5] 13 :=
  permutation_upper _ _ _ [6,9,48,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8568

theorem m9725_6 : Upper (D 5) (R 5) [10,96,48,6] 13 :=
  permutation_upper _ _ _ [6,12,96,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8654

theorem m9725_129 : Upper (D 5) (R 5) [10,96,48,129] 13 :=
  permutation_upper _ _ _ [6,65,160,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9105

theorem m9725_130 : Upper (D 5) (R 5) [10,96,48,130] 13 :=
  permutation_upper _ _ _ [6,68,160,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9143

theorem m9725_132 : Upper (D 5) (R 5) [10,96,48,132] 13 :=
  permutation_upper _ _ _ [6,72,160,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9175

theorem m9725_384 : Upper (D 5) (R 5) [10,96,48,384] 13 :=
  permutation_upper _ _ _ [6,96,384,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9212

def r9725 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9725 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9725 : Upper (D 5) (R 5) [10,96,48] 13 := by
  apply FastRouting.sound _ _ [10,96,48] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9725 c9725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9725_3
  · exact m9725_5
  · exact m9725_6
  · exact m9725_129
  · exact m9725_130
  · exact m9725_132
  · exact m9725_384

theorem m9726_3 : Upper (D 5) (R 5) [10,96,129,3] 13 :=
  permutation_upper _ _ _ [6,5,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8514

theorem m9726_5 : Upper (D 5) (R 5) [10,96,129,5] 13 :=
  permutation_upper _ _ _ [6,9,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8576

theorem m9726_6 : Upper (D 5) (R 5) [10,96,129,6] 13 :=
  permutation_upper _ _ _ [6,12,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8655

theorem m9726_17 : Upper (D 5) (R 5) [10,96,129,17] 13 :=
  permutation_upper _ _ _ [6,17,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8715

theorem m9726_18 : Upper (D 5) (R 5) [10,96,129,18] 13 :=
  permutation_upper _ _ _ [6,20,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8758

theorem m9726_20 : Upper (D 5) (R 5) [10,96,129,20] 13 :=
  permutation_upper _ _ _ [6,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8813

theorem m9726_33 : Upper (D 5) (R 5) [10,96,129,33] 13 :=
  permutation_upper _ _ _ [6,33,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8890

theorem m9726_34 : Upper (D 5) (R 5) [10,96,129,34] 13 :=
  permutation_upper _ _ _ [6,36,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8945

theorem m9726_36 : Upper (D 5) (R 5) [10,96,129,36] 13 :=
  permutation_upper _ _ _ [6,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9009

theorem m9726_48 : Upper (D 5) (R 5) [10,96,129,48] 13 :=
  permutation_upper _ _ _ [6,48,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9049

theorem m9726_257 : Upper (D 5) (R 5) [10,96,129,257] 13 :=
  permutation_upper _ _ _ [6,65,160,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9106

theorem m9726_258 : Upper (D 5) (R 5) [10,96,129,258] 13 :=
  permutation_upper _ _ _ [6,68,160,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9144

theorem m9726_260 : Upper (D 5) (R 5) [10,96,129,260] 13 :=
  permutation_upper _ _ _ [6,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9176

theorem m9726_272 : Upper (D 5) (R 5) [10,96,129,272] 13 :=
  permutation_upper _ _ _ [6,80,160,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9192

theorem m9726_288 : Upper (D 5) (R 5) [10,96,129,288] 13 :=
  permutation_upper _ _ _ [6,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9202

def r9726 : Route 9 := (fun mask => (mask,id))

def c9726 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9726 : Upper (D 5) (R 5) [10,96,129] 13 := by
  apply FastRouting.sound _ _ [10,96,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9726 c9726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9726_3
  · exact m9726_5
  · exact m9726_6
  · exact m9726_17
  · exact m9726_18
  · exact m9726_20
  · exact m9726_33
  · exact m9726_34
  · exact m9726_36
  · exact m9726_48
  · exact m9726_257
  · exact m9726_258
  · exact m9726_260
  · exact m9726_272
  · exact m9726_288

theorem m9727_5 : Upper (D 5) (R 5) [10,96,130,5] 13 :=
  permutation_upper _ _ _ [6,9,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8580

theorem m9727_17 : Upper (D 5) (R 5) [10,96,130,17] 13 :=
  permutation_upper _ _ _ [6,17,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8717

theorem m9727_20 : Upper (D 5) (R 5) [10,96,130,20] 13 :=
  permutation_upper _ _ _ [6,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8815

theorem m9727_33 : Upper (D 5) (R 5) [10,96,130,33] 13 :=
  permutation_upper _ _ _ [6,33,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8892

theorem m9727_36 : Upper (D 5) (R 5) [10,96,130,36] 13 :=
  permutation_upper _ _ _ [6,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9011

theorem m9727_48 : Upper (D 5) (R 5) [10,96,130,48] 13 :=
  permutation_upper _ _ _ [6,48,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9051

theorem m9727_257 : Upper (D 5) (R 5) [10,96,130,257] 13 :=
  permutation_upper _ _ _ [6,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9108

theorem m9727_260 : Upper (D 5) (R 5) [10,96,130,260] 13 :=
  permutation_upper _ _ _ [6,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9178

theorem m9727_272 : Upper (D 5) (R 5) [10,96,130,272] 13 :=
  permutation_upper _ _ _ [6,80,160,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9194

theorem m9727_288 : Upper (D 5) (R 5) [10,96,130,288] 13 :=
  permutation_upper _ _ _ [6,96,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9203

def r9727 : Route 9 := (fun mask => (mask,id))

def c9727 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9727 : Upper (D 5) (R 5) [10,96,130] 13 := by
  apply FastRouting.sound _ _ [10,96,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r9727 c9727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9727_5
  · exact m9727_17
  · exact m9727_20
  · exact m9727_33
  · exact m9727_36
  · exact m9727_48
  · exact m9727_257
  · exact m9727_260
  · exact m9727_272
  · exact m9727_288

theorem m9728_3 : Upper (D 5) (R 5) [10,96,144,3] 13 :=
  permutation_upper _ _ _ [6,5,96,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8515

theorem m9728_5 : Upper (D 5) (R 5) [10,96,144,5] 13 :=
  permutation_upper _ _ _ [6,9,80,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8582

theorem m9728_6 : Upper (D 5) (R 5) [10,96,144,6] 13 :=
  permutation_upper _ _ _ [6,12,96,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8657

theorem m9728_33 : Upper (D 5) (R 5) [10,96,144,33] 13 :=
  permutation_upper _ _ _ [6,33,96,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8893

theorem m9728_34 : Upper (D 5) (R 5) [10,96,144,34] 13 :=
  permutation_upper _ _ _ [6,36,96,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8946

theorem m9728_36 : Upper (D 5) (R 5) [10,96,144,36] 13 :=
  permutation_upper _ _ _ [6,40,96,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9012

theorem m9728_257 : Upper (D 5) (R 5) [10,96,144,257] 13 :=
  permutation_upper _ _ _ [6,65,160,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9109

theorem m9728_258 : Upper (D 5) (R 5) [10,96,144,258] 13 :=
  permutation_upper _ _ _ [6,68,160,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9146

theorem m9728_260 : Upper (D 5) (R 5) [10,96,144,260] 13 :=
  permutation_upper _ _ _ [6,72,160,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9179

theorem m9728_288 : Upper (D 5) (R 5) [10,96,144,288] 13 :=
  permutation_upper _ _ _ [6,96,160,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9204

def r9728 : Route 9 := (fun mask => (mask,id))

def c9728 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9728 : Upper (D 5) (R 5) [10,96,144] 13 := by
  apply FastRouting.sound _ _ [10,96,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9728 c9728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9728_3
  · exact m9728_5
  · exact m9728_6
  · exact m9728_33
  · exact m9728_34
  · exact m9728_36
  · exact m9728_257
  · exact m9728_258
  · exact m9728_260
  · exact m9728_288

theorem m9729_3 : Upper (D 5) (R 5) [10,96,160,3] 13 :=
  permutation_upper _ _ _ [6,5,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8516

theorem m9729_5 : Upper (D 5) (R 5) [10,96,160,5] 13 :=
  permutation_upper _ _ _ [6,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8584

theorem m9729_6 : Upper (D 5) (R 5) [10,96,160,6] 13 :=
  permutation_upper _ _ _ [6,12,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8658

theorem m9729_17 : Upper (D 5) (R 5) [10,96,160,17] 13 :=
  permutation_upper _ _ _ [6,17,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8718

theorem m9729_18 : Upper (D 5) (R 5) [10,96,160,18] 13 :=
  permutation_upper _ _ _ [6,20,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8760

theorem m9729_20 : Upper (D 5) (R 5) [10,96,160,20] 13 :=
  permutation_upper _ _ _ [6,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8816

theorem m9729_257 : Upper (D 5) (R 5) [10,96,160,257] 13 :=
  permutation_upper _ _ _ [6,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9110

theorem m9729_258 : Upper (D 5) (R 5) [10,96,160,258] 13 :=
  permutation_upper _ _ _ [6,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9147

theorem m9729_260 : Upper (D 5) (R 5) [10,96,160,260] 13 :=
  permutation_upper _ _ _ [6,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9180

theorem m9729_272 : Upper (D 5) (R 5) [10,96,160,272] 13 :=
  permutation_upper _ _ _ [6,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9195

def r9729 : Route 9 := (fun mask => (mask,id))

def c9729 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9729 : Upper (D 5) (R 5) [10,96,160] 13 := by
  apply FastRouting.sound _ _ [10,96,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r9729 c9729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9729_3
  · exact m9729_5
  · exact m9729_6
  · exact m9729_17
  · exact m9729_18
  · exact m9729_20
  · exact m9729_257
  · exact m9729_258
  · exact m9729_260
  · exact m9729_272

theorem m9730_3 : Upper (D 5) (R 5) [10,96,384,3] 13 :=
  permutation_upper _ _ _ [6,5,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8517

theorem m9730_5 : Upper (D 5) (R 5) [10,96,384,5] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8585

theorem m9730_6 : Upper (D 5) (R 5) [10,96,384,6] 13 :=
  permutation_upper _ _ _ [6,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8659

theorem m9730_17 : Upper (D 5) (R 5) [10,96,384,17] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8719

theorem m9730_18 : Upper (D 5) (R 5) [10,96,384,18] 13 :=
  permutation_upper _ _ _ [6,20,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8761

theorem m9730_20 : Upper (D 5) (R 5) [10,96,384,20] 13 :=
  permutation_upper _ _ _ [6,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8817

theorem m9730_33 : Upper (D 5) (R 5) [10,96,384,33] 13 :=
  permutation_upper _ _ _ [6,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8894

theorem m9730_34 : Upper (D 5) (R 5) [10,96,384,34] 13 :=
  permutation_upper _ _ _ [6,36,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8947

theorem m9730_36 : Upper (D 5) (R 5) [10,96,384,36] 13 :=
  permutation_upper _ _ _ [6,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9013

theorem m9730_48 : Upper (D 5) (R 5) [10,96,384,48] 13 :=
  permutation_upper _ _ _ [6,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9052

def r9730 : Route 9 := (fun mask => (mask,id))

def c9730 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9730 : Upper (D 5) (R 5) [10,96,384] 13 := by
  apply FastRouting.sound _ _ [10,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9730 c9730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9730_3
  · exact m9730_5
  · exact m9730_6
  · exact m9730_17
  · exact m9730_18
  · exact m9730_20
  · exact m9730_33
  · exact m9730_34
  · exact m9730_36
  · exact m9730_48

theorem m9731_3 : Upper (D 5) (R 5) [10,192,17,3] 13 :=
  permutation_upper _ _ _ [6,5,192,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8518

theorem m9731_5 : Upper (D 5) (R 5) [10,192,17,5] 13 :=
  permutation_upper _ _ _ [6,9,18,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8539

theorem m9731_6 : Upper (D 5) (R 5) [10,192,17,6] 13 :=
  permutation_upper _ _ _ [6,12,192,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8660

theorem m9731_33 : Upper (D 5) (R 5) [10,192,17,33] 13 :=
  permutation_upper _ _ _ [6,33,192,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8896

theorem m9731_34 : Upper (D 5) (R 5) [10,192,17,34] 13 :=
  permutation_upper _ _ _ [6,36,192,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8948

theorem m9731_36 : Upper (D 5) (R 5) [10,192,17,36] 13 :=
  permutation_upper _ _ _ [6,40,192,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9014

theorem m9731_257 : Upper (D 5) (R 5) [10,192,17,257] 13 :=
  permutation_upper _ _ _ [6,65,384,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9112

theorem m9731_258 : Upper (D 5) (R 5) [10,192,17,258] 13 :=
  permutation_upper _ _ _ [6,68,384,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9148

theorem m9731_260 : Upper (D 5) (R 5) [10,192,17,260] 13 :=
  permutation_upper _ _ _ [6,72,384,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9181

theorem m9731_288 : Upper (D 5) (R 5) [10,192,17,288] 13 :=
  permutation_upper _ _ _ [6,96,384,17] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9206

def r9731 : Route 9 := (fun mask => (mask,id))

def c9731 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9731 : Upper (D 5) (R 5) [10,192,17] 13 := by
  apply FastRouting.sound _ _ [10,192,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9731 c9731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9731_3
  · exact m9731_5
  · exact m9731_6
  · exact m9731_33
  · exact m9731_34
  · exact m9731_36
  · exact m9731_257
  · exact m9731_258
  · exact m9731_260
  · exact m9731_288

theorem m9732_5 : Upper (D 5) (R 5) [10,192,18,5] 13 :=
  permutation_upper _ _ _ [6,9,24,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8547

theorem m9732_33 : Upper (D 5) (R 5) [10,192,18,33] 13 :=
  permutation_upper _ _ _ [6,33,192,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8898

theorem m9732_36 : Upper (D 5) (R 5) [10,192,18,36] 13 :=
  permutation_upper _ _ _ [6,40,192,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9016

theorem m9732_257 : Upper (D 5) (R 5) [10,192,18,257] 13 :=
  permutation_upper _ _ _ [6,65,384,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9114

theorem m9732_260 : Upper (D 5) (R 5) [10,192,18,260] 13 :=
  permutation_upper _ _ _ [6,72,384,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9183

theorem m9732_288 : Upper (D 5) (R 5) [10,192,18,288] 13 :=
  permutation_upper _ _ _ [6,96,384,20] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9208

def r9732 : Route 9 := (fun mask => (mask,id))

def c9732 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9732 : Upper (D 5) (R 5) [10,192,18] 13 := by
  apply FastRouting.sound _ _ [10,192,18] 13 (by decide) (choices 2) [5,33,36,257,260,288] r9732 c9732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9732_5
  · exact m9732_33
  · exact m9732_36
  · exact m9732_257
  · exact m9732_260
  · exact m9732_288

theorem m9733_3 : Upper (D 5) (R 5) [10,192,33,3] 13 :=
  permutation_upper _ _ _ [6,5,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8519

theorem m9733_5 : Upper (D 5) (R 5) [10,192,33,5] 13 :=
  permutation_upper _ _ _ [6,9,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8557

theorem m9733_6 : Upper (D 5) (R 5) [10,192,33,6] 13 :=
  permutation_upper _ _ _ [6,12,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8662

theorem m9733_17 : Upper (D 5) (R 5) [10,192,33,17] 13 :=
  permutation_upper _ _ _ [6,17,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8721

theorem m9733_18 : Upper (D 5) (R 5) [10,192,33,18] 13 :=
  permutation_upper _ _ _ [6,20,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8762

theorem m9733_20 : Upper (D 5) (R 5) [10,192,33,20] 13 :=
  permutation_upper _ _ _ [6,24,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8818

theorem m9733_33 : Upper (D 5) (R 5) [10,192,33,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8899

theorem m9733_34 : Upper (D 5) (R 5) [10,192,33,34] 13 :=
  permutation_upper _ _ _ [6,36,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8950

theorem m9733_36 : Upper (D 5) (R 5) [10,192,33,36] 13 :=
  permutation_upper _ _ _ [6,40,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9017

theorem m9733_48 : Upper (D 5) (R 5) [10,192,33,48] 13 :=
  permutation_upper _ _ _ [6,48,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9054

theorem m9733_257 : Upper (D 5) (R 5) [10,192,33,257] 13 :=
  permutation_upper _ _ _ [6,65,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9115

theorem m9733_258 : Upper (D 5) (R 5) [10,192,33,258] 13 :=
  permutation_upper _ _ _ [6,68,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9150

theorem m9733_260 : Upper (D 5) (R 5) [10,192,33,260] 13 :=
  permutation_upper _ _ _ [6,72,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9184

theorem m9733_272 : Upper (D 5) (R 5) [10,192,33,272] 13 :=
  permutation_upper _ _ _ [6,80,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9197

theorem m9733_288 : Upper (D 5) (R 5) [10,192,33,288] 13 :=
  permutation_upper _ _ _ [6,96,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9209

def r9733 : Route 9 := (fun mask => (mask,id))

def c9733 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9733 : Upper (D 5) (R 5) [10,192,33] 13 := by
  apply FastRouting.sound _ _ [10,192,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9733 c9733
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9733_3
  · exact m9733_5
  · exact m9733_6
  · exact m9733_17
  · exact m9733_18
  · exact m9733_20
  · exact m9733_33
  · exact m9733_34
  · exact m9733_36
  · exact m9733_48
  · exact m9733_257
  · exact m9733_258
  · exact m9733_260
  · exact m9733_272
  · exact m9733_288

theorem m9734_5 : Upper (D 5) (R 5) [10,192,34,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8564

theorem m9734_17 : Upper (D 5) (R 5) [10,192,34,17] 13 :=
  permutation_upper _ _ _ [6,17,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8723

theorem m9734_20 : Upper (D 5) (R 5) [10,192,34,20] 13 :=
  permutation_upper _ _ _ [6,24,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8820

theorem m9734_33 : Upper (D 5) (R 5) [10,192,34,33] 13 :=
  permutation_upper _ _ _ [6,33,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8901

theorem m9734_36 : Upper (D 5) (R 5) [10,192,34,36] 13 :=
  permutation_upper _ _ _ [6,40,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9019

theorem m9734_48 : Upper (D 5) (R 5) [10,192,34,48] 13 :=
  permutation_upper _ _ _ [6,48,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9056

theorem m9734_257 : Upper (D 5) (R 5) [10,192,34,257] 13 :=
  permutation_upper _ _ _ [6,65,384,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9117

theorem m9734_260 : Upper (D 5) (R 5) [10,192,34,260] 13 :=
  permutation_upper _ _ _ [6,72,384,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9186

theorem m9734_272 : Upper (D 5) (R 5) [10,192,34,272] 13 :=
  permutation_upper _ _ _ [6,80,384,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9199

theorem m9734_288 : Upper (D 5) (R 5) [10,192,34,288] 13 :=
  permutation_upper _ _ _ [6,96,384,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9211

def r9734 : Route 9 := (fun mask => (mask,id))

def c9734 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9734 : Upper (D 5) (R 5) [10,192,34] 13 := by
  apply FastRouting.sound _ _ [10,192,34] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r9734 c9734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9734_5
  · exact m9734_17
  · exact m9734_20
  · exact m9734_33
  · exact m9734_36
  · exact m9734_48
  · exact m9734_257
  · exact m9734_260
  · exact m9734_272
  · exact m9734_288

theorem m9735_3 : Upper (D 5) (R 5) [10,192,48,3] 13 :=
  permutation_upper _ _ _ [6,5,192,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8520

theorem m9735_5 : Upper (D 5) (R 5) [10,192,48,5] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8569

theorem m9735_6 : Upper (D 5) (R 5) [10,192,48,6] 13 :=
  permutation_upper _ _ _ [6,12,192,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8664

theorem m9735_33 : Upper (D 5) (R 5) [10,192,48,33] 13 :=
  permutation_upper _ _ _ [6,33,192,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8902

theorem m9735_34 : Upper (D 5) (R 5) [10,192,48,34] 13 :=
  permutation_upper _ _ _ [6,36,192,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8951

theorem m9735_36 : Upper (D 5) (R 5) [10,192,48,36] 13 :=
  permutation_upper _ _ _ [6,40,192,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9020

theorem m9735_257 : Upper (D 5) (R 5) [10,192,48,257] 13 :=
  permutation_upper _ _ _ [6,65,384,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9118

theorem m9735_258 : Upper (D 5) (R 5) [10,192,48,258] 13 :=
  permutation_upper _ _ _ [6,68,384,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9152

theorem m9735_260 : Upper (D 5) (R 5) [10,192,48,260] 13 :=
  permutation_upper _ _ _ [6,72,384,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9187

theorem m9735_288 : Upper (D 5) (R 5) [10,192,48,288] 13 :=
  permutation_upper _ _ _ [6,96,384,48] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9212

def r9735 : Route 9 := (fun mask => (mask,id))

def c9735 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9735 : Upper (D 5) (R 5) [10,192,48] 13 := by
  apply FastRouting.sound _ _ [10,192,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9735 c9735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9735_3
  · exact m9735_5
  · exact m9735_6
  · exact m9735_33
  · exact m9735_34
  · exact m9735_36
  · exact m9735_257
  · exact m9735_258
  · exact m9735_260
  · exact m9735_288

theorem m9736_3 : Upper (D 5) (R 5) [10,192,257,3] 13 :=
  permutation_upper _ _ _ [6,5,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8521

theorem m9736_5 : Upper (D 5) (R 5) [10,192,257,5] 13 :=
  permutation_upper _ _ _ [6,9,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8577

theorem m9736_6 : Upper (D 5) (R 5) [10,192,257,6] 13 :=
  permutation_upper _ _ _ [6,12,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8665

theorem m9736_17 : Upper (D 5) (R 5) [10,192,257,17] 13 :=
  permutation_upper _ _ _ [6,17,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8724

theorem m9736_18 : Upper (D 5) (R 5) [10,192,257,18] 13 :=
  permutation_upper _ _ _ [6,20,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8764

theorem m9736_20 : Upper (D 5) (R 5) [10,192,257,20] 13 :=
  permutation_upper _ _ _ [6,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8821

theorem m9736_33 : Upper (D 5) (R 5) [10,192,257,33] 13 :=
  permutation_upper _ _ _ [6,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8903

theorem m9736_34 : Upper (D 5) (R 5) [10,192,257,34] 13 :=
  permutation_upper _ _ _ [6,36,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8952

theorem m9736_36 : Upper (D 5) (R 5) [10,192,257,36] 13 :=
  permutation_upper _ _ _ [6,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9021

theorem m9736_48 : Upper (D 5) (R 5) [10,192,257,48] 13 :=
  permutation_upper _ _ _ [6,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9057

def r9736 : Route 9 := (fun mask => (mask,id))

def c9736 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9736 : Upper (D 5) (R 5) [10,192,257] 13 := by
  apply FastRouting.sound _ _ [10,192,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9736 c9736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9736_3
  · exact m9736_5
  · exact m9736_6
  · exact m9736_17
  · exact m9736_18
  · exact m9736_20
  · exact m9736_33
  · exact m9736_34
  · exact m9736_36
  · exact m9736_48

theorem m9737_5 : Upper (D 5) (R 5) [10,192,258,5] 13 :=
  permutation_upper _ _ _ [6,9,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8581

theorem m9737_17 : Upper (D 5) (R 5) [10,192,258,17] 13 :=
  permutation_upper _ _ _ [6,17,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8726

theorem m9737_20 : Upper (D 5) (R 5) [10,192,258,20] 13 :=
  permutation_upper _ _ _ [6,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8823

theorem m9737_33 : Upper (D 5) (R 5) [10,192,258,33] 13 :=
  permutation_upper _ _ _ [6,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8905

theorem m9737_36 : Upper (D 5) (R 5) [10,192,258,36] 13 :=
  permutation_upper _ _ _ [6,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9023

theorem m9737_48 : Upper (D 5) (R 5) [10,192,258,48] 13 :=
  permutation_upper _ _ _ [6,48,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9059

def r9737 : Route 9 := (fun mask => (mask,id))

def c9737 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9737 : Upper (D 5) (R 5) [10,192,258] 13 := by
  apply FastRouting.sound _ _ [10,192,258] 13 (by decide) (choices 2) [5,17,20,33,36,48] r9737 c9737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9737_5
  · exact m9737_17
  · exact m9737_20
  · exact m9737_33
  · exact m9737_36
  · exact m9737_48

theorem m9738_3 : Upper (D 5) (R 5) [10,192,272,3] 13 :=
  permutation_upper _ _ _ [6,5,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8522

theorem m9738_5 : Upper (D 5) (R 5) [10,192,272,5] 13 :=
  permutation_upper _ _ _ [6,9,80,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8583

theorem m9738_6 : Upper (D 5) (R 5) [10,192,272,6] 13 :=
  permutation_upper _ _ _ [6,12,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8667

theorem m9738_33 : Upper (D 5) (R 5) [10,192,272,33] 13 :=
  permutation_upper _ _ _ [6,33,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8906

theorem m9738_34 : Upper (D 5) (R 5) [10,192,272,34] 13 :=
  permutation_upper _ _ _ [6,36,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8954

theorem m9738_36 : Upper (D 5) (R 5) [10,192,272,36] 13 :=
  permutation_upper _ _ _ [6,40,192,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9024

def r9738 : Route 9 := (fun mask => (mask,id))

def c9738 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9738 : Upper (D 5) (R 5) [10,192,272] 13 := by
  apply FastRouting.sound _ _ [10,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9738 c9738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9738_3
  · exact m9738_5
  · exact m9738_6
  · exact m9738_33
  · exact m9738_34
  · exact m9738_36

theorem m9739_3 : Upper (D 5) (R 5) [10,192,288,3] 13 :=
  permutation_upper _ _ _ [6,5,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8523

theorem m9739_5 : Upper (D 5) (R 5) [10,192,288,5] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8585

theorem m9739_6 : Upper (D 5) (R 5) [10,192,288,6] 13 :=
  permutation_upper _ _ _ [6,12,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8668

theorem m9739_17 : Upper (D 5) (R 5) [10,192,288,17] 13 :=
  permutation_upper _ _ _ [6,17,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8727

theorem m9739_18 : Upper (D 5) (R 5) [10,192,288,18] 13 :=
  permutation_upper _ _ _ [6,20,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8766

theorem m9739_20 : Upper (D 5) (R 5) [10,192,288,20] 13 :=
  permutation_upper _ _ _ [6,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8824

theorem m9739_33 : Upper (D 5) (R 5) [10,192,288,33] 13 :=
  permutation_upper _ _ _ [6,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8907

theorem m9739_34 : Upper (D 5) (R 5) [10,192,288,34] 13 :=
  permutation_upper _ _ _ [6,36,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8955

theorem m9739_36 : Upper (D 5) (R 5) [10,192,288,36] 13 :=
  permutation_upper _ _ _ [6,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9025

theorem m9739_48 : Upper (D 5) (R 5) [10,192,288,48] 13 :=
  permutation_upper _ _ _ [6,48,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9060

def r9739 : Route 9 := (fun mask => (mask,id))

def c9739 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9739 : Upper (D 5) (R 5) [10,192,288] 13 := by
  apply FastRouting.sound _ _ [10,192,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9739 c9739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9739_3
  · exact m9739_5
  · exact m9739_6
  · exact m9739_17
  · exact m9739_18
  · exact m9739_20
  · exact m9739_33
  · exact m9739_34
  · exact m9739_36
  · exact m9739_48

def b9740 : PairBound 9 := { available := 462, camps := [{ cop := 1, region := 4, targets := 2 },{ cop := 1, region := 4, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 37 462 478 494 462 462 462), lower := (rows 19 35 37 8 16 32 64 128 256), losses := [] }

theorem u9740 : Upper (D 5) (R 5) [18,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9741 : PairBound 9 := { available := 461, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 35 38 461 477 493 461 461 461), lower := (rows 19 35 38 8 16 32 64 128 256), losses := [] }

theorem u9741 : Upper (D 5) (R 5) [18,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9741
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9742_3 : Upper (D 5) (R 5) [18,33,40,3] 13 :=
  permutation_upper _ _ _ [6,20,34,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8733

theorem m9742_5 : Upper (D 5) (R 5) [18,33,40,5] 13 :=
  permutation_upper _ _ _ [6,24,33,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8768

theorem m9742_6 : Upper (D 5) (R 5) [18,33,40,6] 13 :=
  permutation_upper _ _ _ [6,33,40,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8835

def r9742 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9742 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9742 : Upper (D 5) (R 5) [18,33,40] 13 := by
  apply FastRouting.sound _ _ [18,33,40] 13 (by decide) (choices 2) [3,5,6,65,66,68,192] r9742 c9742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9742_3
  · exact m9742_5
  · exact m9742_6
  · exact u9219
  · exact u9220
  · exact u9221
  · exact u9222

theorem m9743_6 : Upper (D 5) (R 5) [18,33,65,6] 13 :=
  permutation_upper _ _ _ [6,40,72,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8986

theorem m9743_34 : Upper (D 5) (R 5) [18,33,65,34] 13 :=
  permutation_upper _ _ _ [18,33,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9216

theorem m9743_36 : Upper (D 5) (R 5) [18,33,65,36] 13 :=
  permutation_upper _ _ _ [18,33,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9219

def r9743 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9743 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9743 : Upper (D 5) (R 5) [18,33,65] 13 := by
  apply FastRouting.sound _ _ [18,33,65] 13 (by decide) (choices 2) [6,34,36,130,132,160,384] r9743 c9743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9743_6
  · exact m9743_34
  · exact m9743_36
  · exact u9223
  · exact u9224
  · exact u9225
  · exact u9226

theorem m9744_5 : Upper (D 5) (R 5) [18,33,66,5] 13 :=
  permutation_upper _ _ _ [6,24,72,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8803

theorem m9744_33 : Upper (D 5) (R 5) [18,33,66,33] 13 :=
  permutation_upper _ _ _ [18,33,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9213

theorem m9744_36 : Upper (D 5) (R 5) [18,33,66,36] 13 :=
  permutation_upper _ _ _ [18,33,40,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9220

theorem m9744_129 : Upper (D 5) (R 5) [18,33,66,129] 13 :=
  permutation_upper _ _ _ [18,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9223

def r9744 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9744 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9744 : Upper (D 5) (R 5) [18,33,66] 13 := by
  apply FastRouting.sound _ _ [18,33,66] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9744 c9744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9744_5
  · exact m9744_33
  · exact m9744_36
  · exact m9744_129
  · exact u9227
  · exact u9228
  · exact u9229

theorem m9745_3 : Upper (D 5) (R 5) [18,33,72,3] 13 :=
  permutation_upper _ _ _ [6,20,34,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8734

theorem m9745_5 : Upper (D 5) (R 5) [18,33,72,5] 13 :=
  permutation_upper _ _ _ [6,24,65,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8789

theorem m9745_6 : Upper (D 5) (R 5) [18,33,72,6] 13 :=
  permutation_upper _ _ _ [6,40,65,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8967

theorem m9745_33 : Upper (D 5) (R 5) [18,33,72,33] 13 :=
  permutation_upper _ _ _ [18,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9214

theorem m9745_34 : Upper (D 5) (R 5) [18,33,72,34] 13 :=
  permutation_upper _ _ _ [18,33,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9217

theorem m9745_36 : Upper (D 5) (R 5) [18,33,72,36] 13 :=
  permutation_upper _ _ _ [18,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9221

theorem m9745_129 : Upper (D 5) (R 5) [18,33,72,129] 13 :=
  permutation_upper _ _ _ [18,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9224

theorem m9745_130 : Upper (D 5) (R 5) [18,33,72,130] 13 :=
  permutation_upper _ _ _ [18,33,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9227

def r9745 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9745 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9745 : Upper (D 5) (R 5) [18,33,72] 13 := by
  apply FastRouting.sound _ _ [18,33,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9745 c9745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9745_3
  · exact m9745_5
  · exact m9745_6
  · exact m9745_33
  · exact m9745_34
  · exact m9745_36
  · exact m9745_129
  · exact m9745_130
  · exact u9230
  · exact u9231
  · exact u9232

theorem m9746_3 : Upper (D 5) (R 5) [18,33,96,3] 13 :=
  permutation_upper _ _ _ [6,20,34,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8735

theorem m9746_5 : Upper (D 5) (R 5) [18,33,96,5] 13 :=
  permutation_upper _ _ _ [6,24,96,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8811

theorem m9746_6 : Upper (D 5) (R 5) [18,33,96,6] 13 :=
  permutation_upper _ _ _ [6,40,96,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9007

theorem m9746_129 : Upper (D 5) (R 5) [18,33,96,129] 13 :=
  permutation_upper _ _ _ [18,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9225

theorem m9746_130 : Upper (D 5) (R 5) [18,33,96,130] 13 :=
  permutation_upper _ _ _ [18,33,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9228

theorem m9746_132 : Upper (D 5) (R 5) [18,33,96,132] 13 :=
  permutation_upper _ _ _ [18,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9231

def r9746 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9746 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9746 : Upper (D 5) (R 5) [18,33,96] 13 := by
  apply FastRouting.sound _ _ [18,33,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9746 c9746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9746_3
  · exact m9746_5
  · exact m9746_6
  · exact m9746_129
  · exact m9746_130
  · exact m9746_132
  · exact u9233

theorem m9747_3 : Upper (D 5) (R 5) [18,33,192,3] 13 :=
  permutation_upper _ _ _ [6,20,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8736

theorem m9747_5 : Upper (D 5) (R 5) [18,33,192,5] 13 :=
  permutation_upper _ _ _ [6,24,192,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8819

theorem m9747_6 : Upper (D 5) (R 5) [18,33,192,6] 13 :=
  permutation_upper _ _ _ [6,40,192,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9015

theorem m9747_33 : Upper (D 5) (R 5) [18,33,192,33] 13 :=
  permutation_upper _ _ _ [18,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9215

theorem m9747_34 : Upper (D 5) (R 5) [18,33,192,34] 13 :=
  permutation_upper _ _ _ [18,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9218

theorem m9747_36 : Upper (D 5) (R 5) [18,33,192,36] 13 :=
  permutation_upper _ _ _ [18,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9222

theorem m9747_257 : Upper (D 5) (R 5) [18,33,192,257] 13 :=
  permutation_upper _ _ _ [18,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9226

theorem m9747_258 : Upper (D 5) (R 5) [18,33,192,258] 13 :=
  permutation_upper _ _ _ [18,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9229

theorem m9747_260 : Upper (D 5) (R 5) [18,33,192,260] 13 :=
  permutation_upper _ _ _ [18,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9232

theorem m9747_288 : Upper (D 5) (R 5) [18,33,192,288] 13 :=
  permutation_upper _ _ _ [18,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9233

def r9747 : Route 9 := (fun mask => (mask,id))

def c9747 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9747 : Upper (D 5) (R 5) [18,33,192] 13 := by
  apply FastRouting.sound _ _ [18,33,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9747 c9747
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9747_3
  · exact m9747_5
  · exact m9747_6
  · exact m9747_33
  · exact m9747_34
  · exact m9747_36
  · exact m9747_257
  · exact m9747_258
  · exact m9747_260
  · exact m9747_288

def b9748 : PairBound 9 := { available := 463, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 37 463 479 495 463 463 463), lower := (rows 19 38 37 8 16 32 64 128 256), losses := [] }

theorem u9748 : Upper (D 5) (R 5) [18,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9749 : PairBound 9 := { available := 461, camps := [{ cop := 5, region := 6, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 38 461 477 493 461 461 461), lower := (rows 19 38 38 8 16 32 64 128 256), losses := [] }

theorem u9749 : Upper (D 5) (R 5) [18,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9750 : PairBound 9 := { available := 463, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 44 463 479 495 463 463 463), lower := (rows 19 38 44 8 16 32 64 128 256), losses := [] }

theorem u9750 : Upper (D 5) (R 5) [18,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9750
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9751_3 : Upper (D 5) (R 5) [18,36,65,3] 13 :=
  permutation_upper _ _ _ [6,20,40,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8738

theorem m9751_5 : Upper (D 5) (R 5) [18,36,65,5] 13 :=
  permutation_upper _ _ _ [6,24,66,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8797

theorem m9751_6 : Upper (D 5) (R 5) [18,36,65,6] 13 :=
  permutation_upper _ _ _ [6,36,72,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8931

def r9751 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9751 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9751 : Upper (D 5) (R 5) [18,36,65] 13 := by
  apply FastRouting.sound _ _ [18,36,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9751 c9751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9751_3
  · exact m9751_5
  · exact m9751_6
  · exact u9242
  · exact u9243
  · exact u9244
  · exact u9245
  · exact u9246
  · exact u9247
  · exact u9248
  · exact u9249

theorem m9752_5 : Upper (D 5) (R 5) [18,36,66,5] 13 :=
  permutation_upper _ _ _ [6,24,72,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8804

def r9752 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9752 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9752 : Upper (D 5) (R 5) [18,36,66] 13 := by
  apply FastRouting.sound _ _ [18,36,66] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9752 c9752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9752_5
  · exact u9250
  · exact u9251
  · exact u9252
  · exact u9253
  · exact u9254
  · exact u9255

theorem m9753_3 : Upper (D 5) (R 5) [18,36,72,3] 13 :=
  permutation_upper _ _ _ [6,20,40,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8737

theorem m9753_5 : Upper (D 5) (R 5) [18,36,72,5] 13 :=
  permutation_upper _ _ _ [6,24,65,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8790

theorem m9753_6 : Upper (D 5) (R 5) [18,36,72,6] 13 :=
  permutation_upper _ _ _ [6,36,65,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8915

def r9753 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9753 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9753 : Upper (D 5) (R 5) [18,36,72] 13 := by
  apply FastRouting.sound _ _ [18,36,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9753 c9753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9753_3
  · exact m9753_5
  · exact m9753_6
  · exact u9256
  · exact u9257
  · exact u9258
  · exact u9259
  · exact u9260
  · exact u9261
  · exact u9262
  · exact u9263

def b9754 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 100 399 415 431 463 399 399), lower := (rows 19 38 100 8 16 32 64 128 256), losses := [] }

theorem u9754 : Upper (D 5) (R 5) [18,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9754
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9755_3 : Upper (D 5) (R 5) [18,36,192,3] 13 :=
  permutation_upper _ _ _ [6,20,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8739

theorem m9755_5 : Upper (D 5) (R 5) [18,36,192,5] 13 :=
  permutation_upper _ _ _ [6,24,192,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8820

theorem m9755_6 : Upper (D 5) (R 5) [18,36,192,6] 13 :=
  permutation_upper _ _ _ [6,36,192,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8949

def r9755 : Route 9 := (fun mask => (mask,id))

def c9755 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9755 : Upper (D 5) (R 5) [18,36,192] 13 := by
  apply FastRouting.sound _ _ [18,36,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9755 c9755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9755_3
  · exact m9755_5
  · exact m9755_6
  · exact u9267
  · exact u9268
  · exact u9269
  · exact u9270
  · exact u9271
  · exact u9272
  · exact u9273

theorem m9756_3 : Upper (D 5) (R 5) [18,40,33,3] 13 :=
  permutation_upper _ _ _ [6,20,33,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8728

theorem m9756_5 : Upper (D 5) (R 5) [18,40,33,5] 13 :=
  permutation_upper _ _ _ [6,24,34,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8775

theorem m9756_6 : Upper (D 5) (R 5) [18,40,33,6] 13 :=
  permutation_upper _ _ _ [6,33,40,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8834

theorem m9756_65 : Upper (D 5) (R 5) [18,40,33,65] 13 :=
  permutation_upper _ _ _ [18,36,65,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9242

theorem m9756_66 : Upper (D 5) (R 5) [18,40,33,66] 13 :=
  permutation_upper _ _ _ [18,36,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9250

theorem m9756_68 : Upper (D 5) (R 5) [18,40,33,68] 13 :=
  permutation_upper _ _ _ [18,36,72,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9256

theorem m9756_192 : Upper (D 5) (R 5) [18,40,33,192] 13 :=
  permutation_upper _ _ _ [18,36,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9267

def r9756 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9756 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9756 : Upper (D 5) (R 5) [18,40,33] 13 := by
  apply FastRouting.sound _ _ [18,40,33] 13 (by decide) (choices 2) [3,5,6,65,66,68,192] r9756 c9756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9756_3
  · exact m9756_5
  · exact m9756_6
  · exact m9756_65
  · exact m9756_66
  · exact m9756_68
  · exact m9756_192

theorem m9757_3 : Upper (D 5) (R 5) [18,40,65,3] 13 :=
  permutation_upper _ _ _ [6,20,33,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8730

theorem m9757_5 : Upper (D 5) (R 5) [18,40,65,5] 13 :=
  permutation_upper _ _ _ [6,24,66,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8796

theorem m9757_6 : Upper (D 5) (R 5) [18,40,65,6] 13 :=
  permutation_upper _ _ _ [6,33,72,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8866

theorem m9757_33 : Upper (D 5) (R 5) [18,40,65,33] 13 :=
  permutation_upper _ _ _ [18,36,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9234

theorem m9757_34 : Upper (D 5) (R 5) [18,40,65,34] 13 :=
  permutation_upper _ _ _ [18,36,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9237

theorem m9757_36 : Upper (D 5) (R 5) [18,40,65,36] 13 :=
  permutation_upper _ _ _ [18,36,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9239

theorem m9757_129 : Upper (D 5) (R 5) [18,40,65,129] 13 :=
  permutation_upper _ _ _ [18,36,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9245

theorem m9757_130 : Upper (D 5) (R 5) [18,40,65,130] 13 :=
  permutation_upper _ _ _ [18,36,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9252

theorem m9757_132 : Upper (D 5) (R 5) [18,40,65,132] 13 :=
  permutation_upper _ _ _ [18,36,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9259

theorem m9757_160 : Upper (D 5) (R 5) [18,40,65,160] 13 :=
  permutation_upper _ _ _ [18,36,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9264

theorem m9757_384 : Upper (D 5) (R 5) [18,40,65,384] 13 :=
  permutation_upper _ _ _ [18,36,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9270

def r9757 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9757 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9757 : Upper (D 5) (R 5) [18,40,65] 13 := by
  apply FastRouting.sound _ _ [18,40,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9757 c9757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9757_3
  · exact m9757_5
  · exact m9757_6
  · exact m9757_33
  · exact m9757_34
  · exact m9757_36
  · exact m9757_129
  · exact m9757_130
  · exact m9757_132
  · exact m9757_160
  · exact m9757_384

theorem m9758_3 : Upper (D 5) (R 5) [18,40,96,3] 13 :=
  permutation_upper _ _ _ [6,20,33,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8731

theorem m9758_5 : Upper (D 5) (R 5) [18,40,96,5] 13 :=
  permutation_upper _ _ _ [6,24,96,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8810

theorem m9758_6 : Upper (D 5) (R 5) [18,40,96,6] 13 :=
  permutation_upper _ _ _ [6,33,96,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8888

theorem m9758_129 : Upper (D 5) (R 5) [18,40,96,129] 13 :=
  permutation_upper _ _ _ [18,36,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9248

theorem m9758_130 : Upper (D 5) (R 5) [18,40,96,130] 13 :=
  permutation_upper _ _ _ [18,36,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9254

theorem m9758_132 : Upper (D 5) (R 5) [18,40,96,132] 13 :=
  permutation_upper _ _ _ [18,36,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9262

theorem m9758_384 : Upper (D 5) (R 5) [18,40,96,384] 13 :=
  permutation_upper _ _ _ [18,36,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9273

def r9758 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9758 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9758 : Upper (D 5) (R 5) [18,40,96] 13 := by
  apply FastRouting.sound _ _ [18,40,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9758 c9758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9758_3
  · exact m9758_5
  · exact m9758_6
  · exact m9758_129
  · exact m9758_130
  · exact m9758_132
  · exact m9758_384

theorem m9759_3 : Upper (D 5) (R 5) [18,40,192,3] 13 :=
  permutation_upper _ _ _ [6,20,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8732

theorem m9759_5 : Upper (D 5) (R 5) [18,40,192,5] 13 :=
  permutation_upper _ _ _ [6,24,192,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8818

theorem m9759_6 : Upper (D 5) (R 5) [18,40,192,6] 13 :=
  permutation_upper _ _ _ [6,33,192,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8897

theorem m9759_33 : Upper (D 5) (R 5) [18,40,192,33] 13 :=
  permutation_upper _ _ _ [18,36,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9236

theorem m9759_34 : Upper (D 5) (R 5) [18,40,192,34] 13 :=
  permutation_upper _ _ _ [18,36,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9238

theorem m9759_36 : Upper (D 5) (R 5) [18,40,192,36] 13 :=
  permutation_upper _ _ _ [18,36,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9241

theorem m9759_257 : Upper (D 5) (R 5) [18,40,192,257] 13 :=
  permutation_upper _ _ _ [18,36,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9249

theorem m9759_258 : Upper (D 5) (R 5) [18,40,192,258] 13 :=
  permutation_upper _ _ _ [18,36,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9255

theorem m9759_260 : Upper (D 5) (R 5) [18,40,192,260] 13 :=
  permutation_upper _ _ _ [18,36,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9263

theorem m9759_288 : Upper (D 5) (R 5) [18,40,192,288] 13 :=
  permutation_upper _ _ _ [18,36,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9266

def r9759 : Route 9 := (fun mask => (mask,id))

def c9759 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9759 : Upper (D 5) (R 5) [18,40,192] 13 := by
  apply FastRouting.sound _ _ [18,40,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9759 c9759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9759_3
  · exact m9759_5
  · exact m9759_6
  · exact m9759_33
  · exact m9759_34
  · exact m9759_36
  · exact m9759_257
  · exact m9759_258
  · exact m9759_260
  · exact m9759_288

theorem m9760_6 : Upper (D 5) (R 5) [18,65,33,6] 13 :=
  permutation_upper _ _ _ [6,40,72,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8987

def r9760 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9760 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9760 : Upper (D 5) (R 5) [18,65,33] 13 := by
  apply FastRouting.sound _ _ [18,65,33] 13 (by decide) (choices 2) [6,34,36,130,132,160,384] r9760 c9760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9760_6
  · exact u9274
  · exact u9275
  · exact u9276
  · exact u9277
  · exact u9278
  · exact u9279

theorem m9761_5 : Upper (D 5) (R 5) [18,65,34,5] 13 :=
  permutation_upper _ _ _ [6,24,40,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8784

theorem m9761_33 : Upper (D 5) (R 5) [18,65,34,33] 13 :=
  permutation_upper _ _ _ [18,65,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9274

def r9761 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9761 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9761 : Upper (D 5) (R 5) [18,65,34] 13 := by
  apply FastRouting.sound _ _ [18,65,34] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9761 c9761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9761_5
  · exact m9761_33
  · exact u9280
  · exact u9281
  · exact u9282
  · exact u9283
  · exact u9284

theorem m9762_3 : Upper (D 5) (R 5) [18,65,40,3] 13 :=
  permutation_upper _ _ _ [6,20,66,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8746

theorem m9762_5 : Upper (D 5) (R 5) [18,65,40,5] 13 :=
  permutation_upper _ _ _ [6,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8771

theorem m9762_6 : Upper (D 5) (R 5) [18,65,40,6] 13 :=
  permutation_upper _ _ _ [6,33,72,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8867

theorem m9762_33 : Upper (D 5) (R 5) [18,65,40,33] 13 :=
  permutation_upper _ _ _ [18,65,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9275

theorem m9762_34 : Upper (D 5) (R 5) [18,65,40,34] 13 :=
  permutation_upper _ _ _ [18,65,34,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9280

def r9762 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9762 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9762 : Upper (D 5) (R 5) [18,65,40] 13 := by
  apply FastRouting.sound _ _ [18,65,40] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9762 c9762
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9762_3
  · exact m9762_5
  · exact m9762_6
  · exact m9762_33
  · exact m9762_34
  · exact u9285
  · exact u9286
  · exact u9287
  · exact u9288
  · exact u9289
  · exact u9290

theorem m9763_6 : Upper (D 5) (R 5) [18,65,129,6] 13 :=
  permutation_upper _ _ _ [6,72,136,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9154

theorem m9763_34 : Upper (D 5) (R 5) [18,65,129,34] 13 :=
  permutation_upper _ _ _ [18,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9281

theorem m9763_36 : Upper (D 5) (R 5) [18,65,129,36] 13 :=
  permutation_upper _ _ _ [18,65,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9286

def r9763 : Route 9 := (fun mask => (mask,id))

def c9763 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9763 : Upper (D 5) (R 5) [18,65,129] 13 := by
  apply FastRouting.sound _ _ [18,65,129] 13 (by decide) (choices 2) [6,34,36,258,260,288] r9763 c9763
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9763_6
  · exact m9763_34
  · exact m9763_36
  · exact u9291
  · exact u9292
  · exact u9293

theorem m9764_5 : Upper (D 5) (R 5) [18,65,130,5] 13 :=
  permutation_upper _ _ _ [6,24,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8806

theorem m9764_33 : Upper (D 5) (R 5) [18,65,130,33] 13 :=
  permutation_upper _ _ _ [18,65,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9276

theorem m9764_36 : Upper (D 5) (R 5) [18,65,130,36] 13 :=
  permutation_upper _ _ _ [18,65,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9287

theorem m9764_257 : Upper (D 5) (R 5) [18,65,130,257] 13 :=
  permutation_upper _ _ _ [18,65,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9291

def r9764 : Route 9 := (fun mask => (mask,id))

def c9764 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9764 : Upper (D 5) (R 5) [18,65,130] 13 := by
  apply FastRouting.sound _ _ [18,65,130] 13 (by decide) (choices 2) [5,33,36,257,260,288] r9764 c9764
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9764_5
  · exact m9764_33
  · exact m9764_36
  · exact m9764_257
  · exact u9294
  · exact u9295

theorem m9765_3 : Upper (D 5) (R 5) [18,65,136,3] 13 :=
  permutation_upper _ _ _ [6,20,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8747

theorem m9765_5 : Upper (D 5) (R 5) [18,65,136,5] 13 :=
  permutation_upper _ _ _ [6,24,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8792

theorem m9765_6 : Upper (D 5) (R 5) [18,65,136,6] 13 :=
  permutation_upper _ _ _ [6,65,136,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9080

theorem m9765_33 : Upper (D 5) (R 5) [18,65,136,33] 13 :=
  permutation_upper _ _ _ [18,65,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9277

theorem m9765_34 : Upper (D 5) (R 5) [18,65,136,34] 13 :=
  permutation_upper _ _ _ [18,65,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9282

theorem m9765_36 : Upper (D 5) (R 5) [18,65,136,36] 13 :=
  permutation_upper _ _ _ [18,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9288

theorem m9765_257 : Upper (D 5) (R 5) [18,65,136,257] 13 :=
  permutation_upper _ _ _ [18,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9292

theorem m9765_258 : Upper (D 5) (R 5) [18,65,136,258] 13 :=
  permutation_upper _ _ _ [18,65,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9294

def r9765 : Route 9 := (fun mask => (mask,id))

def c9765 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9765 : Upper (D 5) (R 5) [18,65,136] 13 := by
  apply FastRouting.sound _ _ [18,65,136] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9765 c9765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9765_3
  · exact m9765_5
  · exact m9765_6
  · exact m9765_33
  · exact m9765_34
  · exact m9765_36
  · exact m9765_257
  · exact m9765_258
  · exact u9296
  · exact u9297

theorem m9766_3 : Upper (D 5) (R 5) [18,65,160,3] 13 :=
  permutation_upper _ _ _ [6,20,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8748

theorem m9766_5 : Upper (D 5) (R 5) [18,65,160,5] 13 :=
  permutation_upper _ _ _ [6,24,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8814

theorem m9766_6 : Upper (D 5) (R 5) [18,65,160,6] 13 :=
  permutation_upper _ _ _ [6,72,160,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9170

theorem m9766_33 : Upper (D 5) (R 5) [18,65,160,33] 13 :=
  permutation_upper _ _ _ [18,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9278

theorem m9766_34 : Upper (D 5) (R 5) [18,65,160,34] 13 :=
  permutation_upper _ _ _ [18,65,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9283

theorem m9766_36 : Upper (D 5) (R 5) [18,65,160,36] 13 :=
  permutation_upper _ _ _ [18,65,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9289

theorem m9766_257 : Upper (D 5) (R 5) [18,65,160,257] 13 :=
  permutation_upper _ _ _ [18,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9293

theorem m9766_258 : Upper (D 5) (R 5) [18,65,160,258] 13 :=
  permutation_upper _ _ _ [18,65,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9295

theorem m9766_260 : Upper (D 5) (R 5) [18,65,160,260] 13 :=
  permutation_upper _ _ _ [18,65,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9297

def r9766 : Route 9 := (fun mask => (mask,id))

def c9766 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9766 : Upper (D 5) (R 5) [18,65,160] 13 := by
  apply FastRouting.sound _ _ [18,65,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9766 c9766
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9766_3
  · exact m9766_5
  · exact m9766_6
  · exact m9766_33
  · exact m9766_34
  · exact m9766_36
  · exact m9766_257
  · exact m9766_258
  · exact m9766_260
  · exact u9298

theorem m9767_3 : Upper (D 5) (R 5) [18,65,384,3] 13 :=
  permutation_upper _ _ _ [6,20,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8749

theorem m9767_5 : Upper (D 5) (R 5) [18,65,384,5] 13 :=
  permutation_upper _ _ _ [6,24,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8822

theorem m9767_6 : Upper (D 5) (R 5) [18,65,384,6] 13 :=
  permutation_upper _ _ _ [6,72,384,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9182

theorem m9767_33 : Upper (D 5) (R 5) [18,65,384,33] 13 :=
  permutation_upper _ _ _ [18,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9279

theorem m9767_34 : Upper (D 5) (R 5) [18,65,384,34] 13 :=
  permutation_upper _ _ _ [18,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9284

theorem m9767_36 : Upper (D 5) (R 5) [18,65,384,36] 13 :=
  permutation_upper _ _ _ [18,65,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9290

def r9767 : Route 9 := (fun mask => (mask,id))

def c9767 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9767 : Upper (D 5) (R 5) [18,65,384] 13 := by
  apply FastRouting.sound _ _ [18,65,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9767 c9767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9767_3
  · exact m9767_5
  · exact m9767_6
  · exact m9767_33
  · exact m9767_34
  · exact m9767_36

theorem m9768_3 : Upper (D 5) (R 5) [18,68,33,3] 13 :=
  permutation_upper _ _ _ [6,20,72,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8751

theorem m9768_5 : Upper (D 5) (R 5) [18,68,33,5] 13 :=
  permutation_upper _ _ _ [6,24,34,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8777

theorem m9768_6 : Upper (D 5) (R 5) [18,68,33,6] 13 :=
  permutation_upper _ _ _ [6,40,66,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8980

def r9768 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9768 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9768 : Upper (D 5) (R 5) [18,68,33] 13 := by
  apply FastRouting.sound _ _ [18,68,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9768 c9768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9768_3
  · exact m9768_5
  · exact m9768_6
  · exact u9299
  · exact u9300
  · exact u9301
  · exact u9302
  · exact u9303
  · exact u9304
  · exact u9305
  · exact u9306

theorem m9769_5 : Upper (D 5) (R 5) [18,68,34,5] 13 :=
  permutation_upper _ _ _ [6,24,40,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8785

def r9769 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9769 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9769 : Upper (D 5) (R 5) [18,68,34] 13 := by
  apply FastRouting.sound _ _ [18,68,34] 13 (by decide) (choices 2) [5,33,36,129,132,160,384] r9769 c9769
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9769_5
  · exact u9307
  · exact u9308
  · exact u9309
  · exact u9310
  · exact u9311
  · exact u9312

theorem m9770_3 : Upper (D 5) (R 5) [18,68,40,3] 13 :=
  permutation_upper _ _ _ [6,20,72,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8750

theorem m9770_5 : Upper (D 5) (R 5) [18,68,40,5] 13 :=
  permutation_upper _ _ _ [6,24,33,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8772

theorem m9770_6 : Upper (D 5) (R 5) [18,68,40,6] 13 :=
  permutation_upper _ _ _ [6,33,66,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8856

def r9770 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9770 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9770 : Upper (D 5) (R 5) [18,68,40] 13 := by
  apply FastRouting.sound _ _ [18,68,40] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9770 c9770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9770_3
  · exact m9770_5
  · exact m9770_6
  · exact u9313
  · exact u9314
  · exact u9315
  · exact u9316
  · exact u9317
  · exact u9318
  · exact u9319
  · exact u9320

theorem m9771_3 : Upper (D 5) (R 5) [18,68,129,3] 13 :=
  permutation_upper _ _ _ [6,20,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8753

theorem m9771_5 : Upper (D 5) (R 5) [18,68,129,5] 13 :=
  permutation_upper _ _ _ [6,24,66,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8799

theorem m9771_6 : Upper (D 5) (R 5) [18,68,129,6] 13 :=
  permutation_upper _ _ _ [6,68,136,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9126

def r9771 : Route 9 := (fun mask => (mask,id))

def c9771 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9771 : Upper (D 5) (R 5) [18,68,129] 13 := by
  apply FastRouting.sound _ _ [18,68,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9771 c9771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9771_3
  · exact m9771_5
  · exact m9771_6
  · exact u9321
  · exact u9322
  · exact u9323
  · exact u9324
  · exact u9325
  · exact u9326
  · exact u9327

theorem m9772_5 : Upper (D 5) (R 5) [18,68,130,5] 13 :=
  permutation_upper _ _ _ [6,24,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8807

def r9772 : Route 9 := (fun mask => (mask,id))

def c9772 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9772 : Upper (D 5) (R 5) [18,68,130] 13 := by
  apply FastRouting.sound _ _ [18,68,130] 13 (by decide) (choices 2) [5,33,36,257,260,288] r9772 c9772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9772_5
  · exact u9328
  · exact u9329
  · exact u9330
  · exact u9331
  · exact u9332

theorem m9773_3 : Upper (D 5) (R 5) [18,68,136,3] 13 :=
  permutation_upper _ _ _ [6,20,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8752

theorem m9773_5 : Upper (D 5) (R 5) [18,68,136,5] 13 :=
  permutation_upper _ _ _ [6,24,65,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8793

theorem m9773_6 : Upper (D 5) (R 5) [18,68,136,6] 13 :=
  permutation_upper _ _ _ [6,65,130,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9069

def r9773 : Route 9 := (fun mask => (mask,id))

def c9773 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9773 : Upper (D 5) (R 5) [18,68,136] 13 := by
  apply FastRouting.sound _ _ [18,68,136] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9773 c9773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9773_3
  · exact m9773_5
  · exact m9773_6
  · exact u9333
  · exact u9334
  · exact u9335
  · exact u9336
  · exact u9337
  · exact u9338
  · exact u9339

theorem m9774_3 : Upper (D 5) (R 5) [18,68,160,3] 13 :=
  permutation_upper _ _ _ [6,20,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8754

theorem m9774_5 : Upper (D 5) (R 5) [18,68,160,5] 13 :=
  permutation_upper _ _ _ [6,24,96,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8815

theorem m9774_6 : Upper (D 5) (R 5) [18,68,160,6] 13 :=
  permutation_upper _ _ _ [6,68,160,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9140

def r9774 : Route 9 := (fun mask => (mask,id))

def c9774 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9774 : Upper (D 5) (R 5) [18,68,160] 13 := by
  apply FastRouting.sound _ _ [18,68,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9774 c9774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9774_3
  · exact m9774_5
  · exact m9774_6
  · exact u9340
  · exact u9341
  · exact u9342
  · exact u9343
  · exact u9344
  · exact u9345
  · exact u9346

theorem m9775_3 : Upper (D 5) (R 5) [18,68,384,3] 13 :=
  permutation_upper _ _ _ [6,20,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8755

theorem m9775_5 : Upper (D 5) (R 5) [18,68,384,5] 13 :=
  permutation_upper _ _ _ [6,24,192,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8823

theorem m9775_6 : Upper (D 5) (R 5) [18,68,384,6] 13 :=
  permutation_upper _ _ _ [6,68,384,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9149

def r9775 : Route 9 := (fun mask => (mask,id))

def c9775 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9775 : Upper (D 5) (R 5) [18,68,384] 13 := by
  apply FastRouting.sound _ _ [18,68,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9775 c9775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9775_3
  · exact m9775_5
  · exact m9775_6
  · exact u9347
  · exact u9348
  · exact u9349

theorem m9776_3 : Upper (D 5) (R 5) [18,72,33,3] 13 :=
  permutation_upper _ _ _ [6,20,65,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8741

theorem m9776_5 : Upper (D 5) (R 5) [18,72,33,5] 13 :=
  permutation_upper _ _ _ [6,24,34,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8776

theorem m9776_6 : Upper (D 5) (R 5) [18,72,33,6] 13 :=
  permutation_upper _ _ _ [6,40,65,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8968

theorem m9776_33 : Upper (D 5) (R 5) [18,72,33,33] 13 :=
  permutation_upper _ _ _ [18,68,33,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9299

theorem m9776_34 : Upper (D 5) (R 5) [18,72,33,34] 13 :=
  permutation_upper _ _ _ [18,68,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9307

theorem m9776_36 : Upper (D 5) (R 5) [18,72,33,36] 13 :=
  permutation_upper _ _ _ [18,68,40,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9313

theorem m9776_129 : Upper (D 5) (R 5) [18,72,33,129] 13 :=
  permutation_upper _ _ _ [18,68,129,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9321

theorem m9776_130 : Upper (D 5) (R 5) [18,72,33,130] 13 :=
  permutation_upper _ _ _ [18,68,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9328

theorem m9776_132 : Upper (D 5) (R 5) [18,72,33,132] 13 :=
  permutation_upper _ _ _ [18,68,136,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9333

theorem m9776_160 : Upper (D 5) (R 5) [18,72,33,160] 13 :=
  permutation_upper _ _ _ [18,68,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9340

theorem m9776_384 : Upper (D 5) (R 5) [18,72,33,384] 13 :=
  permutation_upper _ _ _ [18,68,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9347

def r9776 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9776 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9776 : Upper (D 5) (R 5) [18,72,33] 13 := by
  apply FastRouting.sound _ _ [18,72,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9776 c9776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9776_3
  · exact m9776_5
  · exact m9776_6
  · exact m9776_33
  · exact m9776_34
  · exact m9776_36
  · exact m9776_129
  · exact m9776_130
  · exact m9776_132
  · exact m9776_160
  · exact m9776_384

theorem m9777_3 : Upper (D 5) (R 5) [18,72,129,3] 13 :=
  permutation_upper _ _ _ [6,20,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8743

theorem m9777_5 : Upper (D 5) (R 5) [18,72,129,5] 13 :=
  permutation_upper _ _ _ [6,24,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8798

theorem m9777_6 : Upper (D 5) (R 5) [18,72,129,6] 13 :=
  permutation_upper _ _ _ [6,65,136,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9079

theorem m9777_33 : Upper (D 5) (R 5) [18,72,129,33] 13 :=
  permutation_upper _ _ _ [18,68,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9302

theorem m9777_34 : Upper (D 5) (R 5) [18,72,129,34] 13 :=
  permutation_upper _ _ _ [18,68,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9309

theorem m9777_36 : Upper (D 5) (R 5) [18,72,129,36] 13 :=
  permutation_upper _ _ _ [18,68,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9316

theorem m9777_257 : Upper (D 5) (R 5) [18,72,129,257] 13 :=
  permutation_upper _ _ _ [18,68,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9324

theorem m9777_258 : Upper (D 5) (R 5) [18,72,129,258] 13 :=
  permutation_upper _ _ _ [18,68,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9330

theorem m9777_260 : Upper (D 5) (R 5) [18,72,129,260] 13 :=
  permutation_upper _ _ _ [18,68,136,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9336

theorem m9777_288 : Upper (D 5) (R 5) [18,72,129,288] 13 :=
  permutation_upper _ _ _ [18,68,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9343

def r9777 : Route 9 := (fun mask => (mask,id))

def c9777 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9777 : Upper (D 5) (R 5) [18,72,129] 13 := by
  apply FastRouting.sound _ _ [18,72,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9777 c9777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9777_3
  · exact m9777_5
  · exact m9777_6
  · exact m9777_33
  · exact m9777_34
  · exact m9777_36
  · exact m9777_257
  · exact m9777_258
  · exact m9777_260
  · exact m9777_288

theorem m9778_3 : Upper (D 5) (R 5) [18,72,160,3] 13 :=
  permutation_upper _ _ _ [6,20,65,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8744

theorem m9778_5 : Upper (D 5) (R 5) [18,72,160,5] 13 :=
  permutation_upper _ _ _ [6,24,96,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8813

theorem m9778_6 : Upper (D 5) (R 5) [18,72,160,6] 13 :=
  permutation_upper _ _ _ [6,65,160,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9100

theorem m9778_33 : Upper (D 5) (R 5) [18,72,160,33] 13 :=
  permutation_upper _ _ _ [18,68,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9305

theorem m9778_34 : Upper (D 5) (R 5) [18,72,160,34] 13 :=
  permutation_upper _ _ _ [18,68,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9311

theorem m9778_36 : Upper (D 5) (R 5) [18,72,160,36] 13 :=
  permutation_upper _ _ _ [18,68,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9319

theorem m9778_257 : Upper (D 5) (R 5) [18,72,160,257] 13 :=
  permutation_upper _ _ _ [18,68,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9327

theorem m9778_258 : Upper (D 5) (R 5) [18,72,160,258] 13 :=
  permutation_upper _ _ _ [18,68,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9332

theorem m9778_260 : Upper (D 5) (R 5) [18,72,160,260] 13 :=
  permutation_upper _ _ _ [18,68,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9339

theorem m9778_288 : Upper (D 5) (R 5) [18,72,160,288] 13 :=
  permutation_upper _ _ _ [18,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9346

def r9778 : Route 9 := (fun mask => (mask,id))

def c9778 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9778 : Upper (D 5) (R 5) [18,72,160] 13 := by
  apply FastRouting.sound _ _ [18,72,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9778 c9778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9778_3
  · exact m9778_5
  · exact m9778_6
  · exact m9778_33
  · exact m9778_34
  · exact m9778_36
  · exact m9778_257
  · exact m9778_258
  · exact m9778_260
  · exact m9778_288

theorem m9779_3 : Upper (D 5) (R 5) [18,72,384,3] 13 :=
  permutation_upper _ _ _ [6,20,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8745

theorem m9779_5 : Upper (D 5) (R 5) [18,72,384,5] 13 :=
  permutation_upper _ _ _ [6,24,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8821

theorem m9779_6 : Upper (D 5) (R 5) [18,72,384,6] 13 :=
  permutation_upper _ _ _ [6,65,384,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9113

theorem m9779_33 : Upper (D 5) (R 5) [18,72,384,33] 13 :=
  permutation_upper _ _ _ [18,68,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9306

theorem m9779_34 : Upper (D 5) (R 5) [18,72,384,34] 13 :=
  permutation_upper _ _ _ [18,68,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9312

theorem m9779_36 : Upper (D 5) (R 5) [18,72,384,36] 13 :=
  permutation_upper _ _ _ [18,68,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9320

def r9779 : Route 9 := (fun mask => (mask,id))

def c9779 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9779 : Upper (D 5) (R 5) [18,72,384] 13 := by
  apply FastRouting.sound _ _ [18,72,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9779 c9779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9779_3
  · exact m9779_5
  · exact m9779_6
  · exact m9779_33
  · exact m9779_34
  · exact m9779_36

#print axioms u9779
end Delivery.IrregularNine14.P05
