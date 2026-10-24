import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0047
import IrregularNine14P00C0048
import IrregularNine14P00C0049
import IrregularNine14P00C0050
import IrregularNine14P00C0051
import IrregularNine14P00C0052
import IrregularNine14P00C0053

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m3660_3 : Upper (D 0) (R 0) [112,144,264,3] 13 :=
  permutation_upper _ _ _ [112,5,144,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2837

theorem m3660_5 : Upper (D 0) (R 0) [112,144,264,5] 13 :=
  permutation_upper _ _ _ [112,5,258,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2846

theorem m3660_6 : Upper (D 0) (R 0) [112,144,264,6] 13 :=
  permutation_upper _ _ _ [112,12,144,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2895

theorem m3660_33 : Upper (D 0) (R 0) [112,144,264,33] 13 :=
  permutation_upper _ _ _ [112,17,160,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2930

theorem m3660_34 : Upper (D 0) (R 0) [112,144,264,34] 13 :=
  permutation_upper _ _ _ [112,20,160,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2977

theorem m3660_36 : Upper (D 0) (R 0) [112,144,264,36] 13 :=
  permutation_upper _ _ _ [112,20,258,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2985

theorem m3660_96 : Upper (D 0) (R 0) [112,144,264,96] 13 :=
  permutation_upper _ _ _ [112,48,192,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3014

theorem m3660_129 : Upper (D 0) (R 0) [112,144,264,129] 13 :=
  permutation_upper _ _ _ [112,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3027

theorem m3660_130 : Upper (D 0) (R 0) [112,144,264,130] 13 :=
  permutation_upper _ _ _ [112,132,144,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3036

theorem m3660_132 : Upper (D 0) (R 0) [112,144,264,132] 13 :=
  permutation_upper _ _ _ [112,132,258,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3039

theorem m3660_160 : Upper (D 0) (R 0) [112,144,264,160] 13 :=
  permutation_upper _ _ _ [112,144,160,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3043

def r3660 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3660 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3660 : Upper (D 0) (R 0) [112,144,264] 13 := by
  apply FastRouting.sound _ _ [112,144,264] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r3660 c3660
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3660_3
  · exact m3660_5
  · exact m3660_6
  · exact m3660_33
  · exact m3660_34
  · exact m3660_36
  · exact m3660_96
  · exact m3660_129
  · exact m3660_130
  · exact m3660_132
  · exact m3660_160

theorem m3661_3 : Upper (D 0) (R 0) [112,144,288,3] 13 :=
  permutation_upper _ _ _ [112,5,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2838

theorem m3661_5 : Upper (D 0) (R 0) [112,144,288,5] 13 :=
  permutation_upper _ _ _ [112,5,272,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2856

theorem m3661_6 : Upper (D 0) (R 0) [112,144,288,6] 13 :=
  permutation_upper _ _ _ [112,12,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2896

theorem m3661_65 : Upper (D 0) (R 0) [112,144,288,65] 13 :=
  permutation_upper _ _ _ [112,17,160,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2932

theorem m3661_66 : Upper (D 0) (R 0) [112,144,288,66] 13 :=
  permutation_upper _ _ _ [112,20,160,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2978

theorem m3661_68 : Upper (D 0) (R 0) [112,144,288,68] 13 :=
  permutation_upper _ _ _ [112,20,288,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 5 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2992

theorem m3661_129 : Upper (D 0) (R 0) [112,144,288,129] 13 :=
  permutation_upper _ _ _ [112,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3029

theorem m3661_130 : Upper (D 0) (R 0) [112,144,288,130] 13 :=
  permutation_upper _ _ _ [112,132,144,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3037

theorem m3661_132 : Upper (D 0) (R 0) [112,144,288,132] 13 :=
  permutation_upper _ _ _ [112,132,272,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3041

theorem m3661_192 : Upper (D 0) (R 0) [112,144,288,192] 13 :=
  permutation_upper _ _ _ [112,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3044

def r3661 : Route 9 := (fun mask => (mask,id))

def c3661 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3661 : Upper (D 0) (R 0) [112,144,288] 13 := by
  apply FastRouting.sound _ _ [112,144,288] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r3661 c3661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3661_3
  · exact m3661_5
  · exact m3661_6
  · exact m3661_65
  · exact m3661_66
  · exact m3661_68
  · exact m3661_129
  · exact m3661_130
  · exact m3661_132
  · exact m3661_192

theorem m3662_3 : Upper (D 0) (R 0) [112,144,384,3] 13 :=
  permutation_upper _ _ _ [112,5,144,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2839

theorem m3662_5 : Upper (D 0) (R 0) [112,144,384,5] 13 :=
  permutation_upper _ _ _ [112,5,384,144] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2862

theorem m3662_6 : Upper (D 0) (R 0) [112,144,384,6] 13 :=
  permutation_upper _ _ _ [112,12,144,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2897

theorem m3662_33 : Upper (D 0) (R 0) [112,144,384,33] 13 :=
  permutation_upper _ _ _ [112,17,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2933

theorem m3662_34 : Upper (D 0) (R 0) [112,144,384,34] 13 :=
  permutation_upper _ _ _ [112,20,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2979

theorem m3662_36 : Upper (D 0) (R 0) [112,144,384,36] 13 :=
  permutation_upper _ _ _ [112,20,384,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2996

theorem m3662_96 : Upper (D 0) (R 0) [112,144,384,96] 13 :=
  permutation_upper _ _ _ [112,48,192,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3016

def r3662 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3662 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3662 : Upper (D 0) (R 0) [112,144,384] 13 := by
  apply FastRouting.sound _ _ [112,144,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r3662 c3662
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3662_3
  · exact m3662_5
  · exact m3662_6
  · exact m3662_33
  · exact m3662_34
  · exact m3662_36
  · exact m3662_96

def b3663 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 263 11 21 248 240 240 240 240 496), lower := (rows 263 11 21 8 16 32 64 128 256), losses := [] }

theorem u3663 : Upper (D 0) (R 0) [262,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3663
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3664 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3664 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3664 : Upper (D 0) (R 0) [262,9,48] 13 := by
  apply FastRouting.sound _ _ [262,9,48] 13 (by decide) (choices 2) [17,48,65,80,192] r3664 c3664
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3045
  · exact u3046
  · exact u3047
  · exact u3048
  · exact u3049

def b3665 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 263 19 21 232 248 232 232 232 488), lower := (rows 263 19 21 8 16 32 64 128 256), losses := [] }

theorem u3665 : Upper (D 0) (R 0) [262,17,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3665
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 19 28 233 241 225 225 225 481), lower := (rows 263 19 28 8 16 32 64 128 256), losses := [] }

theorem u3666 : Upper (D 0) (R 0) [262,17,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3666
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 263 19 37 248 248 248 248 248 504), lower := (rows 263 19 37 8 16 32 64 128 256), losses := [] }

theorem u3667 : Upper (D 0) (R 0) [262,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3667
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3668 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3668 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3668 : Upper (D 0) (R 0) [262,17,40] 13 := by
  apply FastRouting.sound _ _ [262,17,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3668 c3668
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3050
  · exact u3051
  · exact u3052
  · exact u3053
  · exact u3054
  · exact u3055
  · exact u3056

def b3669 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 19 52 233 249 233 233 233 489), lower := (rows 263 19 52 8 16 32 64 128 256), losses := [] }

theorem u3669 : Upper (D 0) (R 0) [262,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3669
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3670 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3670 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3670 : Upper (D 0) (R 0) [262,17,96] 13 := by
  apply FastRouting.sound _ _ [262,17,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3670 c3670
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3057
  · exact u3058
  · exact u3059
  · exact u3060
  · exact u3061
  · exact u3062
  · exact u3063

def b3671 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 26 52 233 241 225 225 225 481), lower := (rows 263 26 52 8 16 32 64 128 256), losses := [] }

theorem u3671 : Upper (D 0) (R 0) [262,24,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3671
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3672 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3672 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3672 : Upper (D 0) (R 0) [262,24,96] 13 := by
  apply FastRouting.sound _ _ [262,24,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3672 c3672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3064
  · exact u3065
  · exact u3066
  · exact u3067
  · exact u3068
  · exact u3069
  · exact u3070

def b3673 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 263 50 52 201 217 233 201 201 457), lower := (rows 263 50 52 8 16 32 64 128 256), losses := [] }

theorem u3673 : Upper (D 0) (R 0) [262,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3673
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 84 233 249 233 233 233 489), lower := (rows 263 50 84 8 16 32 64 128 256), losses := [] }

theorem u3674 : Upper (D 0) (R 0) [262,48,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3674
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3675_65 : Upper (D 0) (R 0) [262,48,192,65] 13 :=
  permutation_upper _ _ _ [262,48,192,17] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3071

theorem m3675_192 : Upper (D 0) (R 0) [262,48,192,192] 13 :=
  permutation_upper _ _ _ [262,48,192,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3072

def r3675 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3675 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3675 : Upper (D 0) (R 0) [262,48,192] 13 := by
  apply FastRouting.sound _ _ [262,48,192] 13 (by decide) (choices 2) [17,48,65,80,192] r3675 c3675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3071
  · exact u3072
  · exact m3675_65
  · exact u3073
  · exact m3675_192

def b3676 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 7 13 248 240 240 240 240 496), lower := (rows 275 7 13 8 16 32 64 128 256), losses := [] }

theorem u3676 : Upper (D 0) (R 0) [274,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3676
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 275 7 21 232 248 232 232 232 488), lower := (rows 275 7 21 8 16 32 64 128 256), losses := [] }

theorem u3677 : Upper (D 0) (R 0) [274,5,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3677
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3678 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 7 28 233 241 225 225 225 481), lower := (rows 275 7 28 8 16 32 64 128 256), losses := [] }

theorem u3678 : Upper (D 0) (R 0) [274,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3678
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3679 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 7 37 248 248 248 248 248 504), lower := (rows 275 7 37 8 16 32 64 128 256), losses := [] }

theorem u3679 : Upper (D 0) (R 0) [274,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3679
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3680 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3680 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3680 : Upper (D 0) (R 0) [274,5,40] 13 := by
  apply FastRouting.sound _ _ [274,5,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3680 c3680
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3074
  · exact u3075
  · exact u3076
  · exact u3077
  · exact u3078
  · exact u3079
  · exact u3080

def b3681 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 7 52 233 249 233 233 233 489), lower := (rows 275 7 52 8 16 32 64 128 256), losses := [] }

theorem u3681 : Upper (D 0) (R 0) [274,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3681
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3682 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3682 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3682 : Upper (D 0) (R 0) [274,5,96] 13 := by
  apply FastRouting.sound _ _ [274,5,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3682 c3682
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3081
  · exact u3082
  · exact u3083
  · exact u3084
  · exact u3085
  · exact u3086
  · exact u3087

def b3683 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 21 233 241 225 225 225 481), lower := (rows 275 14 21 8 16 32 64 128 256), losses := [] }

theorem u3683 : Upper (D 0) (R 0) [274,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3683
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3684_17 : Upper (D 0) (R 0) [274,12,33,17] 13 :=
  permutation_upper _ _ _ [274,12,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3088

def r3684 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3684 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3684 : Upper (D 0) (R 0) [274,12,33] 13 := by
  apply FastRouting.sound _ _ [274,12,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3684 c3684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3684_17
  · exact u3090
  · exact u3091
  · exact u3092
  · exact u3093
  · exact u3094
  · exact u3095

def b3685 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 233 241 225 225 225 481), lower := (rows 275 14 52 8 16 32 64 128 256), losses := [] }

theorem u3685 : Upper (D 0) (R 0) [274,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3685
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3686_17 : Upper (D 0) (R 0) [274,12,96,17] 13 :=
  permutation_upper _ _ _ [274,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3089

theorem m3686_33 : Upper (D 0) (R 0) [274,12,96,33] 13 :=
  permutation_upper _ _ _ [274,12,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3094

theorem m3686_48 : Upper (D 0) (R 0) [274,12,96,48] 13 :=
  permutation_upper _ _ _ [274,12,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3096

theorem m3686_129 : Upper (D 0) (R 0) [274,12,96,129] 13 :=
  permutation_upper _ _ _ [274,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3095

theorem m3686_144 : Upper (D 0) (R 0) [274,12,96,144] 13 :=
  permutation_upper _ _ _ [274,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3097

def r3686 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3686 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3686 : Upper (D 0) (R 0) [274,12,96] 13 := by
  apply FastRouting.sound _ _ [274,12,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r3686 c3686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3686_17
  · exact m3686_33
  · exact m3686_48
  · exact u3098
  · exact m3686_129
  · exact m3686_144
  · exact u3099

def b3687 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 13 252 244 244 244 244 500), lower := (rows 275 35 13 8 16 32 64 128 256), losses := [] }

theorem u3687 : Upper (D 0) (R 0) [274,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3687
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 21 236 252 236 236 236 492), lower := (rows 275 35 21 8 16 32 64 128 256), losses := [] }

theorem u3688 : Upper (D 0) (R 0) [274,33,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3688
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3689_5 : Upper (D 0) (R 0) [274,33,24,5] 13 :=
  permutation_upper _ _ _ [274,33,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3100

def r3689 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3689 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3689 : Upper (D 0) (R 0) [274,33,24] 13 := by
  apply FastRouting.sound _ _ [274,33,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r3689 c3689
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3689_5
  · exact u3111
  · exact u3112
  · exact u3113
  · exact u3114
  · exact u3115
  · exact u3116

def b3690 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 37 220 220 252 220 220 476), lower := (rows 275 35 37 8 16 32 64 128 256), losses := [] }

theorem u3690 : Upper (D 0) (R 0) [274,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3690
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3691_5 : Upper (D 0) (R 0) [274,33,40,5] 13 :=
  permutation_upper _ _ _ [274,33,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3101

theorem m3691_17 : Upper (D 0) (R 0) [274,33,40,17] 13 :=
  permutation_upper _ _ _ [274,33,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3107

theorem m3691_20 : Upper (D 0) (R 0) [274,33,40,20] 13 :=
  permutation_upper _ _ _ [274,33,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3112

def r3691 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3691 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3691 : Upper (D 0) (R 0) [274,33,40] 13 := by
  apply FastRouting.sound _ _ [274,33,40] 13 (by decide) (choices 2) [5,17,20,65,68,80,192] r3691 c3691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3691_5
  · exact m3691_17
  · exact m3691_20
  · exact u3120
  · exact u3121
  · exact u3122
  · exact u3123

theorem m3692_5 : Upper (D 0) (R 0) [274,33,48,5] 13 :=
  permutation_upper _ _ _ [274,33,9,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3102

def r3692 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3692 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3692 : Upper (D 0) (R 0) [274,33,48] 13 := by
  apply FastRouting.sound _ _ [274,33,48] 13 (by decide) (choices 2) [5,65,68,192] r3692 c3692
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m3692_5
  · exact u3124
  · exact u3125
  · exact u3126

def b3693 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 275 35 69 252 252 252 252 252 508), lower := (rows 275 35 69 8 16 32 64 128 256), losses := [] }

theorem u3693 : Upper (D 0) (R 0) [274,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3693
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3694_5 : Upper (D 0) (R 0) [274,33,72,5] 13 :=
  permutation_upper _ _ _ [274,33,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3103

theorem m3694_17 : Upper (D 0) (R 0) [274,33,72,17] 13 :=
  permutation_upper _ _ _ [274,33,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3108

theorem m3694_20 : Upper (D 0) (R 0) [274,33,72,20] 13 :=
  permutation_upper _ _ _ [274,33,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3114

theorem m3694_33 : Upper (D 0) (R 0) [274,33,72,33] 13 :=
  permutation_upper _ _ _ [274,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3117

theorem m3694_36 : Upper (D 0) (R 0) [274,33,72,36] 13 :=
  permutation_upper _ _ _ [274,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3121

theorem m3694_48 : Upper (D 0) (R 0) [274,33,72,48] 13 :=
  permutation_upper _ _ _ [274,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3125

theorem m3694_65 : Upper (D 0) (R 0) [274,33,72,65] 13 :=
  permutation_upper _ _ _ [274,33,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3127

theorem m3694_129 : Upper (D 0) (R 0) [274,33,72,129] 13 :=
  permutation_upper _ _ _ [274,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3130

def r3694 : Route 9 := (fun mask => (mask,id))

def c3694 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3694 : Upper (D 0) (R 0) [274,33,72] 13 := by
  apply FastRouting.sound _ _ [274,33,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r3694 c3694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3694_5
  · exact m3694_17
  · exact m3694_20
  · exact m3694_33
  · exact m3694_36
  · exact m3694_48
  · exact m3694_65
  · exact u3134
  · exact u3135
  · exact u3136
  · exact m3694_129
  · exact u3137
  · exact u3138
  · exact u3139
  · exact u3140

theorem m3695_5 : Upper (D 0) (R 0) [274,33,80,5] 13 :=
  permutation_upper _ _ _ [274,33,9,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3104

theorem m3695_33 : Upper (D 0) (R 0) [274,33,80,33] 13 :=
  permutation_upper _ _ _ [274,33,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3118

theorem m3695_36 : Upper (D 0) (R 0) [274,33,80,36] 13 :=
  permutation_upper _ _ _ [274,33,40,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3122

theorem m3695_65 : Upper (D 0) (R 0) [274,33,80,65] 13 :=
  permutation_upper _ _ _ [274,33,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3128

theorem m3695_68 : Upper (D 0) (R 0) [274,33,80,68] 13 :=
  permutation_upper _ _ _ [274,33,72,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3135

theorem m3695_129 : Upper (D 0) (R 0) [274,33,80,129] 13 :=
  permutation_upper _ _ _ [274,33,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3131

theorem m3695_132 : Upper (D 0) (R 0) [274,33,80,132] 13 :=
  permutation_upper _ _ _ [274,33,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3138

def r3695 : Route 9 := (fun mask => (mask,id))

def c3695 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3695 : Upper (D 0) (R 0) [274,33,80] 13 := by
  apply FastRouting.sound _ _ [274,33,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r3695 c3695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3695_5
  · exact m3695_33
  · exact m3695_36
  · exact m3695_65
  · exact m3695_68
  · exact u3141
  · exact m3695_129
  · exact m3695_132
  · exact u3142
  · exact u3143

theorem m3696_5 : Upper (D 0) (R 0) [274,33,96,5] 13 :=
  permutation_upper _ _ _ [274,33,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3105

theorem m3696_17 : Upper (D 0) (R 0) [274,33,96,17] 13 :=
  permutation_upper _ _ _ [274,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3109

theorem m3696_20 : Upper (D 0) (R 0) [274,33,96,20] 13 :=
  permutation_upper _ _ _ [274,33,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3115

theorem m3696_65 : Upper (D 0) (R 0) [274,33,96,65] 13 :=
  permutation_upper _ _ _ [274,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3129

theorem m3696_68 : Upper (D 0) (R 0) [274,33,96,68] 13 :=
  permutation_upper _ _ _ [274,33,72,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3136

theorem m3696_80 : Upper (D 0) (R 0) [274,33,96,80] 13 :=
  permutation_upper _ _ _ [274,33,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3141

theorem m3696_129 : Upper (D 0) (R 0) [274,33,96,129] 13 :=
  permutation_upper _ _ _ [274,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3132

theorem m3696_132 : Upper (D 0) (R 0) [274,33,96,132] 13 :=
  permutation_upper _ _ _ [274,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3139

theorem m3696_144 : Upper (D 0) (R 0) [274,33,96,144] 13 :=
  permutation_upper _ _ _ [274,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3142

def r3696 : Route 9 := (fun mask => (mask,id))

def c3696 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3696 : Upper (D 0) (R 0) [274,33,96] 13 := by
  apply FastRouting.sound _ _ [274,33,96] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192] r3696 c3696
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3696_5
  · exact m3696_17
  · exact m3696_20
  · exact m3696_65
  · exact m3696_68
  · exact m3696_80
  · exact m3696_129
  · exact m3696_132
  · exact m3696_144
  · exact u3144

theorem m3697_5 : Upper (D 0) (R 0) [274,33,192,5] 13 :=
  permutation_upper _ _ _ [274,33,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3106

theorem m3697_17 : Upper (D 0) (R 0) [274,33,192,17] 13 :=
  permutation_upper _ _ _ [274,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3110

theorem m3697_20 : Upper (D 0) (R 0) [274,33,192,20] 13 :=
  permutation_upper _ _ _ [274,33,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3116

theorem m3697_33 : Upper (D 0) (R 0) [274,33,192,33] 13 :=
  permutation_upper _ _ _ [274,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3119

theorem m3697_36 : Upper (D 0) (R 0) [274,33,192,36] 13 :=
  permutation_upper _ _ _ [274,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3123

theorem m3697_48 : Upper (D 0) (R 0) [274,33,192,48] 13 :=
  permutation_upper _ _ _ [274,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3126

theorem m3697_65 : Upper (D 0) (R 0) [274,33,192,65] 13 :=
  permutation_upper _ _ _ [274,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3133

theorem m3697_68 : Upper (D 0) (R 0) [274,33,192,68] 13 :=
  permutation_upper _ _ _ [274,33,72,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3140

theorem m3697_80 : Upper (D 0) (R 0) [274,33,192,80] 13 :=
  permutation_upper _ _ _ [274,33,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3143

theorem m3697_96 : Upper (D 0) (R 0) [274,33,192,96] 13 :=
  permutation_upper _ _ _ [274,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3144

def r3697 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3697 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3697 : Upper (D 0) (R 0) [274,33,192] 13 := by
  apply FastRouting.sound _ _ [274,33,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r3697 c3697
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3697_5
  · exact m3697_17
  · exact m3697_20
  · exact m3697_33
  · exact m3697_36
  · exact m3697_48
  · exact m3697_65
  · exact m3697_68
  · exact m3697_80
  · exact m3697_96
  · exact u3145

def r3698 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3698 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3698 : Upper (D 0) (R 0) [274,36,9] 13 := by
  apply FastRouting.sound _ _ [274,36,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3698 c3698
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3146
  · exact u3147
  · exact u3148
  · exact u3149
  · exact u3150
  · exact u3151
  · exact u3152

def b3699 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 21 233 249 233 233 233 489), lower := (rows 275 38 21 8 16 32 64 128 256), losses := [] }

theorem u3699 : Upper (D 0) (R 0) [274,36,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3699
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 28 233 241 225 225 225 481), lower := (rows 275 38 28 8 16 32 64 128 256), losses := [] }

theorem u3700 : Upper (D 0) (R 0) [274,36,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3700
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 37 217 217 249 217 217 473), lower := (rows 275 38 37 8 16 32 64 128 256), losses := [] }

theorem u3701 : Upper (D 0) (R 0) [274,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3701
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 44 217 209 241 209 209 465), lower := (rows 275 38 44 8 16 32 64 128 256), losses := [] }

theorem u3702 : Upper (D 0) (R 0) [274,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3702
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 52 201 217 233 201 201 457), lower := (rows 275 38 52 8 16 32 64 128 256), losses := [] }

theorem u3703 : Upper (D 0) (R 0) [274,36,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3703
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3704 : Route 9 := (fun mask => (mask,id))

def c3704 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3704 : Upper (D 0) (R 0) [274,36,65] 13 := by
  apply FastRouting.sound _ _ [274,36,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r3704 c3704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3153
  · exact u3154
  · exact u3155
  · exact u3156
  · exact u3157
  · exact u3158
  · exact u3159
  · exact u3160
  · exact u3161
  · exact u3162

def r3705 : Route 9 := (fun mask => (mask,id))

def c3705 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3705 : Upper (D 0) (R 0) [274,36,72] 13 := by
  apply FastRouting.sound _ _ [274,36,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r3705 c3705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3163
  · exact u3164
  · exact u3165
  · exact u3166
  · exact u3167
  · exact u3168
  · exact u3169
  · exact u3170
  · exact u3171
  · exact u3172

def b3706 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 84 233 249 233 233 233 489), lower := (rows 275 38 84 8 16 32 64 128 256), losses := [] }

theorem u3706 : Upper (D 0) (R 0) [274,36,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3706
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 100 217 217 249 217 217 473), lower := (rows 275 38 100 8 16 32 64 128 256), losses := [] }

theorem u3707 : Upper (D 0) (R 0) [274,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3707
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3708 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3708 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3708 : Upper (D 0) (R 0) [274,36,192] 13 := by
  apply FastRouting.sound _ _ [274,36,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3708 c3708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3173
  · exact u3174
  · exact u3175
  · exact u3176
  · exact u3177
  · exact u3178
  · exact u3179

def r3709 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3709 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3709 : Upper (D 0) (R 0) [274,96,9] 13 := by
  apply FastRouting.sound _ _ [274,96,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,129,132,144,160] r3709 c3709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3180
  · exact u3181
  · exact u3182
  · exact u3183
  · exact u3184
  · exact u3185
  · exact u3186
  · exact u3187
  · exact u3188
  · exact u3189
  · exact u3190

def b3710 : PairBound 9 := { available := 237, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 21 237 253 237 237 237 493), lower := (rows 275 98 21 8 16 32 64 128 256), losses := [] }

theorem u3710 : Upper (D 0) (R 0) [274,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3710
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3711_5 : Upper (D 0) (R 0) [274,96,24,5] 13 :=
  permutation_upper _ _ _ [274,96,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3182

def r3711 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3711 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3711 : Upper (D 0) (R 0) [274,96,24] 13 := by
  apply FastRouting.sound _ _ [274,96,24] 13 (by decide) (choices 2) [5,33,36,96,129,132,160] r3711 c3711
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3711_5
  · exact u3195
  · exact u3196
  · exact u3197
  · exact u3198
  · exact u3199
  · exact u3200

def b3712 : PairBound 9 := { available := 221, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 221 221 253 221 221 477), lower := (rows 275 98 37 8 16 32 64 128 256), losses := [] }

theorem u3712 : Upper (D 0) (R 0) [274,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3712
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3713_5 : Upper (D 0) (R 0) [274,96,40,5] 13 :=
  permutation_upper _ _ _ [274,96,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3184

theorem m3713_17 : Upper (D 0) (R 0) [274,96,40,17] 13 :=
  permutation_upper _ _ _ [274,96,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3191

theorem m3713_20 : Upper (D 0) (R 0) [274,96,40,20] 13 :=
  permutation_upper _ _ _ [274,96,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3196

theorem m3713_65 : Upper (D 0) (R 0) [274,96,40,65] 13 :=
  permutation_upper _ _ _ [274,96,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3201

def r3713 : Route 9 := (fun mask => (mask,id))

def c3713 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3713 : Upper (D 0) (R 0) [274,96,40] 13 := by
  apply FastRouting.sound _ _ [274,96,40] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192] r3713 c3713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3713_5
  · exact m3713_17
  · exact m3713_20
  · exact m3713_65
  · exact u3207
  · exact u3208
  · exact u3209
  · exact u3210
  · exact u3211
  · exact u3212

theorem m3714_5 : Upper (D 0) (R 0) [274,96,48,5] 13 :=
  permutation_upper _ _ _ [274,96,9,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3185

theorem m3714_65 : Upper (D 0) (R 0) [274,96,48,65] 13 :=
  permutation_upper _ _ _ [274,96,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3202

theorem m3714_68 : Upper (D 0) (R 0) [274,96,48,68] 13 :=
  permutation_upper _ _ _ [274,96,40,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3208

def r3714 : Route 9 := (fun mask => (mask,id))

def c3714 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3714 : Upper (D 0) (R 0) [274,96,48] 13 := by
  apply FastRouting.sound _ _ [274,96,48] 13 (by decide) (choices 2) [5,65,68,129,132,192] r3714 c3714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3714_5
  · exact m3714_65
  · exact m3714_68
  · exact u3213
  · exact u3214
  · exact u3215

def b3715 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 100 157 157 189 221 157 413), lower := (rows 275 98 100 8 16 32 64 128 256), losses := [] }

theorem u3715 : Upper (D 0) (R 0) [274,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3715
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3716_5 : Upper (D 0) (R 0) [274,96,129,5] 13 :=
  permutation_upper _ _ _ [274,96,9,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3187

theorem m3716_17 : Upper (D 0) (R 0) [274,96,129,17] 13 :=
  permutation_upper _ _ _ [274,96,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3192

theorem m3716_20 : Upper (D 0) (R 0) [274,96,129,20] 13 :=
  permutation_upper _ _ _ [274,96,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3198

theorem m3716_33 : Upper (D 0) (R 0) [274,96,129,33] 13 :=
  permutation_upper _ _ _ [274,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3203

theorem m3716_36 : Upper (D 0) (R 0) [274,96,129,36] 13 :=
  permutation_upper _ _ _ [274,96,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3209

theorem m3716_48 : Upper (D 0) (R 0) [274,96,129,48] 13 :=
  permutation_upper _ _ _ [274,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3213

theorem m3716_96 : Upper (D 0) (R 0) [274,96,129,96] 13 :=
  permutation_upper _ _ _ [274,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3216

def r3716 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3716 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3716 : Upper (D 0) (R 0) [274,96,129] 13 := by
  apply FastRouting.sound _ _ [274,96,129] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,129,132,144,160] r3716 c3716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3716_5
  · exact m3716_17
  · exact m3716_20
  · exact m3716_33
  · exact m3716_36
  · exact m3716_48
  · exact m3716_96
  · exact u3219
  · exact u3220
  · exact u3221
  · exact u3222

theorem m3717_5 : Upper (D 0) (R 0) [274,96,136,5] 13 :=
  permutation_upper _ _ _ [274,96,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3188

theorem m3717_17 : Upper (D 0) (R 0) [274,96,136,17] 13 :=
  permutation_upper _ _ _ [274,96,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3193

theorem m3717_20 : Upper (D 0) (R 0) [274,96,136,20] 13 :=
  permutation_upper _ _ _ [274,96,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3199

theorem m3717_33 : Upper (D 0) (R 0) [274,96,136,33] 13 :=
  permutation_upper _ _ _ [274,96,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3204

theorem m3717_36 : Upper (D 0) (R 0) [274,96,136,36] 13 :=
  permutation_upper _ _ _ [274,96,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3210

theorem m3717_48 : Upper (D 0) (R 0) [274,96,136,48] 13 :=
  permutation_upper _ _ _ [274,96,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3214

theorem m3717_96 : Upper (D 0) (R 0) [274,96,136,96] 13 :=
  permutation_upper _ _ _ [274,96,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3217

theorem m3717_129 : Upper (D 0) (R 0) [274,96,136,129] 13 :=
  permutation_upper _ _ _ [274,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3220

def r3717 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3717 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3717 : Upper (D 0) (R 0) [274,96,136] 13 := by
  apply FastRouting.sound _ _ [274,96,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,129,132,144,160] r3717 c3717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3717_5
  · exact m3717_17
  · exact m3717_20
  · exact m3717_33
  · exact m3717_36
  · exact m3717_48
  · exact m3717_96
  · exact m3717_129
  · exact u3223
  · exact u3224
  · exact u3225

theorem m3718_5 : Upper (D 0) (R 0) [274,96,144,5] 13 :=
  permutation_upper _ _ _ [274,96,9,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3189

theorem m3718_33 : Upper (D 0) (R 0) [274,96,144,33] 13 :=
  permutation_upper _ _ _ [274,96,33,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3205

theorem m3718_36 : Upper (D 0) (R 0) [274,96,144,36] 13 :=
  permutation_upper _ _ _ [274,96,40,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3211

theorem m3718_96 : Upper (D 0) (R 0) [274,96,144,96] 13 :=
  permutation_upper _ _ _ [274,96,96,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3218

theorem m3718_129 : Upper (D 0) (R 0) [274,96,144,129] 13 :=
  permutation_upper _ _ _ [274,96,129,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3221

theorem m3718_132 : Upper (D 0) (R 0) [274,96,144,132] 13 :=
  permutation_upper _ _ _ [274,96,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3224

def r3718 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3718 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3718 : Upper (D 0) (R 0) [274,96,144] 13 := by
  apply FastRouting.sound _ _ [274,96,144] 13 (by decide) (choices 2) [5,33,36,96,129,132,160] r3718 c3718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3718_5
  · exact m3718_33
  · exact m3718_36
  · exact m3718_96
  · exact m3718_129
  · exact m3718_132
  · exact u3226

theorem m3719_5 : Upper (D 0) (R 0) [274,96,160,5] 13 :=
  permutation_upper _ _ _ [274,96,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3190

theorem m3719_17 : Upper (D 0) (R 0) [274,96,160,17] 13 :=
  permutation_upper _ _ _ [274,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3194

theorem m3719_20 : Upper (D 0) (R 0) [274,96,160,20] 13 :=
  permutation_upper _ _ _ [274,96,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3200

theorem m3719_65 : Upper (D 0) (R 0) [274,96,160,65] 13 :=
  permutation_upper _ _ _ [274,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3206

theorem m3719_68 : Upper (D 0) (R 0) [274,96,160,68] 13 :=
  permutation_upper _ _ _ [274,96,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3212

theorem m3719_80 : Upper (D 0) (R 0) [274,96,160,80] 13 :=
  permutation_upper _ _ _ [274,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3215

theorem m3719_129 : Upper (D 0) (R 0) [274,96,160,129] 13 :=
  permutation_upper _ _ _ [274,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3222

theorem m3719_132 : Upper (D 0) (R 0) [274,96,160,132] 13 :=
  permutation_upper _ _ _ [274,96,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3225

theorem m3719_144 : Upper (D 0) (R 0) [274,96,160,144] 13 :=
  permutation_upper _ _ _ [274,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3226

def r3719 : Route 9 := (fun mask => (mask,id))

def c3719 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3719 : Upper (D 0) (R 0) [274,96,160] 13 := by
  apply FastRouting.sound _ _ [274,96,160] 13 (by decide) (choices 2) [5,17,20,65,68,80,129,132,144,192] r3719 c3719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3719_5
  · exact m3719_17
  · exact m3719_20
  · exact m3719_65
  · exact m3719_68
  · exact m3719_80
  · exact m3719_129
  · exact m3719_132
  · exact m3719_144
  · exact u3227

#print axioms u3719
end Delivery.IrregularNine14.P00
