import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0083
import IrregularNine14P03C0084
import IrregularNine14P03C0085
import IrregularNine14P03C0086
import IrregularNine14P03C0087

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m7140_5 : Upper (D 3) (R 3) [258,33,65,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5036

theorem m7140_9 : Upper (D 3) (R 3) [258,33,65,160,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5055

theorem m7140_12 : Upper (D 3) (R 3) [258,33,65,160,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5074

theorem m7140_65 : Upper (D 3) (R 3) [258,33,65,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5105

theorem m7140_68 : Upper (D 3) (R 3) [258,33,65,160,68] 13 :=
  permutation_upper _ _ _ [258,33,65,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5108

theorem m7140_72 : Upper (D 3) (R 3) [258,33,65,160,72] 13 :=
  permutation_upper _ _ _ [258,33,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5112

theorem m7140_129 : Upper (D 3) (R 3) [258,33,65,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5113

theorem m7140_132 : Upper (D 3) (R 3) [258,33,65,160,132] 13 :=
  permutation_upper _ _ _ [258,33,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5118

theorem m7140_136 : Upper (D 3) (R 3) [258,33,65,160,136] 13 :=
  permutation_upper _ _ _ [258,33,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5121

def r7140 : Route 9 := (fun mask => (mask,id))

def c7140 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7140 : Upper (D 3) (R 3) [258,33,65,160] 13 := by
  apply FastRouting.sound _ _ [258,33,65,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7140 c7140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7140_5
  · exact m7140_9
  · exact m7140_12
  · exact m7140_65
  · exact m7140_68
  · exact m7140_72
  · exact m7140_129
  · exact m7140_132
  · exact m7140_136
  · exact u5123

theorem m7141_5 : Upper (D 3) (R 3) [258,33,65,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5037

theorem m7141_9 : Upper (D 3) (R 3) [258,33,65,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5060

theorem m7141_12 : Upper (D 3) (R 3) [258,33,65,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5075

theorem m7141_33 : Upper (D 3) (R 3) [258,33,65,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5084

theorem m7141_36 : Upper (D 3) (R 3) [258,33,65,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5092

theorem m7141_40 : Upper (D 3) (R 3) [258,33,65,192,40] 13 :=
  permutation_upper _ _ _ [258,33,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5101

theorem m7141_129 : Upper (D 3) (R 3) [258,33,65,192,129] 13 :=
  permutation_upper _ _ _ [258,33,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5116

theorem m7141_132 : Upper (D 3) (R 3) [258,33,65,192,132] 13 :=
  permutation_upper _ _ _ [258,33,65,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5119

theorem m7141_136 : Upper (D 3) (R 3) [258,33,65,192,136] 13 :=
  permutation_upper _ _ _ [258,33,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5122

theorem m7141_160 : Upper (D 3) (R 3) [258,33,65,192,160] 13 :=
  permutation_upper _ _ _ [258,33,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5123

def r7141 : Route 9 := (fun mask => (mask,id))

def c7141 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7141 : Upper (D 3) (R 3) [258,33,65,192] 13 := by
  apply FastRouting.sound _ _ [258,33,65,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r7141 c7141
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7141_5
  · exact m7141_9
  · exact m7141_12
  · exact m7141_33
  · exact m7141_36
  · exact m7141_40
  · exact m7141_129
  · exact m7141_132
  · exact m7141_136
  · exact m7141_160

def b7142 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 76 177 177 241 177 433), lower := (rows 259 35 76 76 16 32 64 128 256), losses := [] }

theorem u7142 : Upper (D 3) (R 3) [258,33,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7143 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 181 165 229 165 421), lower := (rows 259 35 76 88 16 32 64 128 256), losses := [] }

theorem u7143 : Upper (D 3) (R 3) [258,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7144 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 104 149 181 213 149 405), lower := (rows 259 35 76 104 16 32 64 128 256), losses := [] }

theorem u7144 : Upper (D 3) (R 3) [258,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7144
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7145_33 : Upper (D 3) (R 3) [258,33,72,132,33] 13 :=
  permutation_upper _ _ _ [258,33,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5087

theorem m7145_65 : Upper (D 3) (R 3) [258,33,72,132,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5111

theorem m7145_129 : Upper (D 3) (R 3) [258,33,72,132,129] 13 :=
  permutation_upper _ _ _ [258,33,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5111

theorem m7145_160 : Upper (D 3) (R 3) [258,33,72,132,160] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5128

def r7145 : Route 9 := (fun mask => (mask,id))

def c7145 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7145 : Upper (D 3) (R 3) [258,33,72,132] 13 := by
  apply FastRouting.sound _ _ [258,33,72,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7145 c7145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7145_33
  · exact m7145_65
  · exact u5128
  · exact m7145_129
  · exact m7145_160
  · exact u5129

theorem m7146_5 : Upper (D 3) (R 3) [258,33,72,144,5] 13 :=
  permutation_upper _ _ _ [258,33,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5050

theorem m7146_33 : Upper (D 3) (R 3) [258,33,72,144,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5085

theorem m7146_36 : Upper (D 3) (R 3) [258,33,72,144,36] 13 :=
  permutation_upper _ _ _ [258,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5099

theorem m7146_65 : Upper (D 3) (R 3) [258,33,72,144,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5110

theorem m7146_68 : Upper (D 3) (R 3) [258,33,72,144,68] 13 :=
  permutation_upper _ _ _ [258,33,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5125

theorem m7146_129 : Upper (D 3) (R 3) [258,33,72,144,129] 13 :=
  permutation_upper _ _ _ [258,33,65,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5107

theorem m7146_132 : Upper (D 3) (R 3) [258,33,72,144,132] 13 :=
  permutation_upper _ _ _ [258,33,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5125

theorem m7146_160 : Upper (D 3) (R 3) [258,33,72,144,160] 13 :=
  permutation_upper _ _ _ [258,33,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5127

def r7146 : Route 9 := (fun mask => (mask,id))

def c7146 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7146 : Upper (D 3) (R 3) [258,33,72,144] 13 := by
  apply FastRouting.sound _ _ [258,33,72,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r7146 c7146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7146_5
  · exact m7146_33
  · exact m7146_36
  · exact m7146_65
  · exact m7146_68
  · exact u5130
  · exact m7146_129
  · exact m7146_132
  · exact m7146_160
  · exact u5131

theorem m7147_5 : Upper (D 3) (R 3) [258,33,72,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5051

theorem m7147_65 : Upper (D 3) (R 3) [258,33,72,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5112

theorem m7147_68 : Upper (D 3) (R 3) [258,33,72,160,68] 13 :=
  permutation_upper _ _ _ [258,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5126

theorem m7147_129 : Upper (D 3) (R 3) [258,33,72,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5115

theorem m7147_132 : Upper (D 3) (R 3) [258,33,72,160,132] 13 :=
  permutation_upper _ _ _ [258,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5130

def r7147 : Route 9 := (fun mask => (mask,id))

def c7147 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7147 : Upper (D 3) (R 3) [258,33,72,160] 13 := by
  apply FastRouting.sound _ _ [258,33,72,160] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7147 c7147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7147_5
  · exact m7147_65
  · exact m7147_68
  · exact m7147_129
  · exact m7147_132
  · exact u5132

def b7148 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 200 181 181 245 181 437), lower := (rows 259 35 76 200 16 32 64 128 256), losses := [] }

theorem u7148 : Upper (D 3) (R 3) [258,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7148
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7149_5 : Upper (D 3) (R 3) [258,33,80,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5040

theorem m7149_9 : Upper (D 3) (R 3) [258,33,80,96,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5054

theorem m7149_12 : Upper (D 3) (R 3) [258,33,80,96,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5076

theorem m7149_129 : Upper (D 3) (R 3) [258,33,80,96,129] 13 :=
  permutation_upper _ _ _ [258,33,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5118

theorem m7149_132 : Upper (D 3) (R 3) [258,33,80,96,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5128

theorem m7149_136 : Upper (D 3) (R 3) [258,33,80,96,136] 13 :=
  permutation_upper _ _ _ [258,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5130

def r7149 : Route 9 := (fun mask => (mask,id))

def c7149 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7149 : Upper (D 3) (R 3) [258,33,80,96] 13 := by
  apply FastRouting.sound _ _ [258,33,80,96] 13 (by decide) (choices 2) [5,9,12,129,132,136] r7149 c7149
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7149_5
  · exact m7149_9
  · exact m7149_12
  · exact m7149_129
  · exact m7149_132
  · exact m7149_136

theorem m7150_5 : Upper (D 3) (R 3) [258,33,80,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5042

theorem m7150_9 : Upper (D 3) (R 3) [258,33,80,160,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5056

theorem m7150_12 : Upper (D 3) (R 3) [258,33,80,160,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5077

theorem m7150_65 : Upper (D 3) (R 3) [258,33,80,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5108

theorem m7150_68 : Upper (D 3) (R 3) [258,33,80,160,68] 13 :=
  permutation_upper _ _ _ [258,33,72,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5124

theorem m7150_72 : Upper (D 3) (R 3) [258,33,80,160,72] 13 :=
  permutation_upper _ _ _ [258,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5126

theorem m7150_129 : Upper (D 3) (R 3) [258,33,80,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5114

theorem m7150_132 : Upper (D 3) (R 3) [258,33,80,160,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5128

theorem m7150_136 : Upper (D 3) (R 3) [258,33,80,160,136] 13 :=
  permutation_upper _ _ _ [258,33,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5127

theorem m7150_192 : Upper (D 3) (R 3) [258,33,80,160,192] 13 :=
  permutation_upper _ _ _ [258,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5133

def r7150 : Route 9 := (fun mask => (mask,id))

def c7150 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7150 : Upper (D 3) (R 3) [258,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,33,80,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7150 c7150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7150_5
  · exact m7150_9
  · exact m7150_12
  · exact m7150_65
  · exact m7150_68
  · exact m7150_72
  · exact m7150_129
  · exact m7150_132
  · exact m7150_136
  · exact m7150_192

theorem m7151_5 : Upper (D 3) (R 3) [258,33,80,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5043

theorem m7151_9 : Upper (D 3) (R 3) [258,33,80,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5061

theorem m7151_12 : Upper (D 3) (R 3) [258,33,80,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5078

theorem m7151_33 : Upper (D 3) (R 3) [258,33,80,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5086

theorem m7151_36 : Upper (D 3) (R 3) [258,33,80,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5095

theorem m7151_40 : Upper (D 3) (R 3) [258,33,80,192,40] 13 :=
  permutation_upper _ _ _ [258,33,40,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5102

theorem m7151_129 : Upper (D 3) (R 3) [258,33,80,192,129] 13 :=
  permutation_upper _ _ _ [258,33,65,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5119

theorem m7151_132 : Upper (D 3) (R 3) [258,33,80,192,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5129

theorem m7151_136 : Upper (D 3) (R 3) [258,33,80,192,136] 13 :=
  permutation_upper _ _ _ [258,33,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5131

theorem m7151_160 : Upper (D 3) (R 3) [258,33,80,192,160] 13 :=
  permutation_upper _ _ _ [258,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5132

def r7151 : Route 9 := (fun mask => (mask,id))

def c7151 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7151 : Upper (D 3) (R 3) [258,33,80,192] 13 := by
  apply FastRouting.sound _ _ [258,33,80,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r7151 c7151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7151_5
  · exact m7151_9
  · exact m7151_12
  · exact m7151_33
  · exact m7151_36
  · exact m7151_40
  · exact m7151_129
  · exact m7151_132
  · exact m7151_136
  · exact m7151_160

theorem m7152_5 : Upper (D 3) (R 3) [258,33,96,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5057

theorem m7152_9 : Upper (D 3) (R 3) [258,33,96,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5062

theorem m7152_12 : Upper (D 3) (R 3) [258,33,96,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5079

theorem m7152_129 : Upper (D 3) (R 3) [258,33,96,192,129] 13 :=
  permutation_upper _ _ _ [258,33,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5123

theorem m7152_132 : Upper (D 3) (R 3) [258,33,96,192,132] 13 :=
  permutation_upper _ _ _ [258,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5132

theorem m7152_136 : Upper (D 3) (R 3) [258,33,96,192,136] 13 :=
  permutation_upper _ _ _ [258,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5133

def r7152 : Route 9 := (fun mask => (mask,id))

def c7152 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7152 : Upper (D 3) (R 3) [258,33,96,192] 13 := by
  apply FastRouting.sound _ _ [258,33,96,192] 13 (by decide) (choices 2) [5,9,12,129,132,136] r7152 c7152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7152_5
  · exact m7152_9
  · exact m7152_12
  · exact m7152_129
  · exact m7152_132
  · exact m7152_136

def b7153 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 196 200 61 61 125 189 317), lower := (rows 259 35 196 200 16 32 64 128 256), losses := [] }

theorem u7153 : Upper (D 3) (R 3) [258,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7154 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 25 241 225 225 225 481), lower := (rows 259 38 13 25 16 32 64 128 256), losses := [] }

theorem u7154 : Upper (D 3) (R 3) [258,36,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7155 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 41 209 241 209 209 465), lower := (rows 259 38 13 41 16 32 64 128 256), losses := [] }

theorem u7155 : Upper (D 3) (R 3) [258,36,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7156 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 13 56 209 225 193 193 449), lower := (rows 259 38 13 56 16 32 64 128 256), losses := [] }

theorem u7156 : Upper (D 3) (R 3) [258,36,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 73 241 241 241 241 497), lower := (rows 259 38 13 73 16 32 64 128 256), losses := [] }

theorem u7157 : Upper (D 3) (R 3) [258,36,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7158 : Route 9 := (fun mask => (mask,id))

def c7158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7158 : Upper (D 3) (R 3) [258,36,9,80] 13 := by
  apply FastRouting.sound _ _ [258,36,9,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7158 c7158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5134
  · exact u5135
  · exact u5136
  · exact u5137
  · exact u5138
  · exact u5139

def b7159 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 13 104 209 241 209 209 465), lower := (rows 259 38 13 104 16 32 64 128 256), losses := [] }

theorem u7159 : Upper (D 3) (R 3) [258,36,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7159
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7160 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7160 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7160 : Upper (D 3) (R 3) [258,36,9,192] 13 := by
  apply FastRouting.sound _ _ [258,36,9,192] 13 (by decide) (choices 2) [33,65,96,192] r7160 c7160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5140
  · exact u5141
  · exact u5142
  · exact u5143

def b7161 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 41 209 225 193 193 449), lower := (rows 259 38 28 41 16 32 64 128 256), losses := [] }

theorem u7161 : Upper (D 3) (R 3) [258,36,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7161
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7162_33 : Upper (D 3) (R 3) [258,36,24,65,33] 13 :=
  permutation_upper _ _ _ [258,36,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5144

def r7162 : Route 9 := (fun mask => (mask,id))

def c7162 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7162 : Upper (D 3) (R 3) [258,36,24,65] 13 := by
  apply FastRouting.sound _ _ [258,36,24,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7162 c7162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7162_33
  · exact u5146
  · exact u5147
  · exact u5148
  · exact u5149
  · exact u5150

def b7163 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 28 104 209 225 193 193 449), lower := (rows 259 38 28 104 16 32 64 128 256), losses := [] }

theorem u7163 : Upper (D 3) (R 3) [258,36,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7163
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7164_33 : Upper (D 3) (R 3) [258,36,24,192,33] 13 :=
  permutation_upper _ _ _ [258,36,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5145

theorem m7164_65 : Upper (D 3) (R 3) [258,36,24,192,65] 13 :=
  permutation_upper _ _ _ [258,36,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5150

theorem m7164_96 : Upper (D 3) (R 3) [258,36,24,192,96] 13 :=
  permutation_upper _ _ _ [258,36,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5151

def r7164 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7164 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7164 : Upper (D 3) (R 3) [258,36,24,192] 13 := by
  apply FastRouting.sound _ _ [258,36,24,192] 13 (by decide) (choices 2) [33,65,96,192] r7164 c7164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7164_33
  · exact m7164_65
  · exact m7164_96
  · exact u5152

def r7165 : Route 9 := (fun mask => (mask,id))

def c7165 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7165 : Upper (D 3) (R 3) [258,36,65,17] 13 := by
  apply FastRouting.sound _ _ [258,36,65,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7165 c7165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5153
  · exact u5154
  · exact u5155
  · exact u5156
  · exact u5157
  · exact u5158
  · exact u5159
  · exact u5160
  · exact u5161
  · exact u5162

def b7166 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 41 217 249 217 217 473), lower := (rows 259 38 69 41 16 32 64 128 256), losses := [] }

theorem u7166 : Upper (D 3) (R 3) [258,36,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7166
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7167_9 : Upper (D 3) (R 3) [258,36,65,48,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5155

def r7167 : Route 9 := (fun mask => (mask,id))

def c7167 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7167 : Upper (D 3) (R 3) [258,36,65,48] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7167 c7167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7167_9
  · exact u5167
  · exact u5168
  · exact u5169
  · exact u5170
  · exact u5171

def b7168 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 185 185 249 185 441), lower := (rows 259 38 69 73 16 32 64 128 256), losses := [] }

theorem u7168 : Upper (D 3) (R 3) [258,36,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7168
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7169_9 : Upper (D 3) (R 3) [258,36,65,80,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5157

theorem m7169_33 : Upper (D 3) (R 3) [258,36,65,80,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5163

theorem m7169_40 : Upper (D 3) (R 3) [258,36,65,80,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5168

def r7169 : Route 9 := (fun mask => (mask,id))

def c7169 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7169 : Upper (D 3) (R 3) [258,36,65,80] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r7169 c7169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7169_9
  · exact m7169_33
  · exact m7169_40
  · exact u5175
  · exact u5176
  · exact u5177

theorem m7170_9 : Upper (D 3) (R 3) [258,36,65,96,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5158

def r7170 : Route 9 := (fun mask => (mask,id))

def c7170 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7170 : Upper (D 3) (R 3) [258,36,65,96] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96] 13 (by decide) (choices 2) [9,129,136] r7170 c7170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7170_9
  · exact u5178
  · exact u5179

theorem m7171_9 : Upper (D 3) (R 3) [258,36,65,129,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5159

theorem m7171_33 : Upper (D 3) (R 3) [258,36,65,129,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5164

theorem m7171_40 : Upper (D 3) (R 3) [258,36,65,129,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5169

theorem m7171_65 : Upper (D 3) (R 3) [258,36,65,129,65] 13 :=
  permutation_upper _ _ _ [258,36,65,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5172

theorem m7171_72 : Upper (D 3) (R 3) [258,36,65,129,72] 13 :=
  permutation_upper _ _ _ [258,36,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5175

theorem m7171_96 : Upper (D 3) (R 3) [258,36,65,129,96] 13 :=
  permutation_upper _ _ _ [258,36,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5178

def r7171 : Route 9 := (fun mask => (mask,id))

def c7171 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7171 : Upper (D 3) (R 3) [258,36,65,129] 13 := by
  apply FastRouting.sound _ _ [258,36,65,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7171 c7171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7171_9
  · exact m7171_33
  · exact m7171_40
  · exact m7171_65
  · exact m7171_72
  · exact m7171_96
  · exact u5180
  · exact u5181
  · exact u5182
  · exact u5183

theorem m7172_9 : Upper (D 3) (R 3) [258,36,65,144,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5160

theorem m7172_33 : Upper (D 3) (R 3) [258,36,65,144,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5165

theorem m7172_40 : Upper (D 3) (R 3) [258,36,65,144,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5170

theorem m7172_65 : Upper (D 3) (R 3) [258,36,65,144,65] 13 :=
  permutation_upper _ _ _ [258,36,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5173

theorem m7172_72 : Upper (D 3) (R 3) [258,36,65,144,72] 13 :=
  permutation_upper _ _ _ [258,36,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5176

theorem m7172_96 : Upper (D 3) (R 3) [258,36,65,144,96] 13 :=
  permutation_upper _ _ _ [258,36,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5179

theorem m7172_129 : Upper (D 3) (R 3) [258,36,65,144,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5181

def r7172 : Route 9 := (fun mask => (mask,id))

def c7172 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7172 : Upper (D 3) (R 3) [258,36,65,144] 13 := by
  apply FastRouting.sound _ _ [258,36,65,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7172 c7172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7172_9
  · exact m7172_33
  · exact m7172_40
  · exact m7172_65
  · exact m7172_72
  · exact m7172_96
  · exact m7172_129
  · exact u5184
  · exact u5185
  · exact u5186

theorem m7173_9 : Upper (D 3) (R 3) [258,36,65,160,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5161

theorem m7173_65 : Upper (D 3) (R 3) [258,36,65,160,65] 13 :=
  permutation_upper _ _ _ [258,36,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5174

theorem m7173_72 : Upper (D 3) (R 3) [258,36,65,160,72] 13 :=
  permutation_upper _ _ _ [258,36,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5177

theorem m7173_129 : Upper (D 3) (R 3) [258,36,65,160,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5182

theorem m7173_136 : Upper (D 3) (R 3) [258,36,65,160,136] 13 :=
  permutation_upper _ _ _ [258,36,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5185

def r7173 : Route 9 := (fun mask => (mask,id))

def c7173 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7173 : Upper (D 3) (R 3) [258,36,65,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7173 c7173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7173_9
  · exact m7173_65
  · exact m7173_72
  · exact m7173_129
  · exact m7173_136
  · exact u5187

theorem m7174_9 : Upper (D 3) (R 3) [258,36,65,192,9] 13 :=
  permutation_upper _ _ _ [258,36,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5162

theorem m7174_33 : Upper (D 3) (R 3) [258,36,65,192,33] 13 :=
  permutation_upper _ _ _ [258,36,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5166

theorem m7174_40 : Upper (D 3) (R 3) [258,36,65,192,40] 13 :=
  permutation_upper _ _ _ [258,36,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5171

theorem m7174_129 : Upper (D 3) (R 3) [258,36,65,192,129] 13 :=
  permutation_upper _ _ _ [258,36,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5183

theorem m7174_136 : Upper (D 3) (R 3) [258,36,65,192,136] 13 :=
  permutation_upper _ _ _ [258,36,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5186

theorem m7174_160 : Upper (D 3) (R 3) [258,36,65,192,160] 13 :=
  permutation_upper _ _ _ [258,36,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5187

def r7174 : Route 9 := (fun mask => (mask,id))

def c7174 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7174 : Upper (D 3) (R 3) [258,36,65,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r7174 c7174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7174_9
  · exact m7174_33
  · exact m7174_40
  · exact m7174_129
  · exact m7174_136
  · exact m7174_160

def r7175 : Route 9 := (fun mask => (mask,id))

def c7175 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7175 : Upper (D 3) (R 3) [258,36,72,17] 13 := by
  apply FastRouting.sound _ _ [258,36,72,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7175 c7175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5188
  · exact u5189
  · exact u5190
  · exact u5191
  · exact u5192
  · exact u5193

def b7176 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 76 41 209 241 209 209 465), lower := (rows 259 38 76 41 16 32 64 128 256), losses := [] }

theorem u7176 : Upper (D 3) (R 3) [258,36,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7177 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 76 56 209 225 193 193 449), lower := (rows 259 38 76 56 16 32 64 128 256), losses := [] }

theorem u7177 : Upper (D 3) (R 3) [258,36,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7177
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7178 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 73 177 177 241 177 433), lower := (rows 259 38 76 73 16 32 64 128 256), losses := [] }

theorem u7178 : Upper (D 3) (R 3) [258,36,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7178
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7179 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 88 177 161 225 161 417), lower := (rows 259 38 76 88 16 32 64 128 256), losses := [] }

theorem u7179 : Upper (D 3) (R 3) [258,36,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7179
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7180 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 104 145 177 209 145 401), lower := (rows 259 38 76 104 16 32 64 128 256), losses := [] }

theorem u7180 : Upper (D 3) (R 3) [258,36,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7181 : Route 9 := (fun mask => (mask,id))

def c7181 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7181 : Upper (D 3) (R 3) [258,36,72,129] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7181 c7181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5194
  · exact u5195
  · exact u5196
  · exact u5197
  · exact u5198
  · exact u5199

def r7182 : Route 9 := (fun mask => (mask,id))

def c7182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7182 : Upper (D 3) (R 3) [258,36,72,144] 13 := by
  apply FastRouting.sound _ _ [258,36,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7182 c7182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5200
  · exact u5201
  · exact u5202
  · exact u5203
  · exact u5204
  · exact u5205

def b7183 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 76 168 209 241 209 209 465), lower := (rows 259 38 76 168 16 32 64 128 256), losses := [] }

theorem u7183 : Upper (D 3) (R 3) [258,36,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7184 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 200 177 177 241 177 433), lower := (rows 259 38 76 200 16 32 64 128 256), losses := [] }

theorem u7184 : Upper (D 3) (R 3) [258,36,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7185 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7185 : Upper (D 3) (R 3) [258,36,192,17] 13 := by
  apply FastRouting.sound _ _ [258,36,192,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r7185 c7185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5206
  · exact u5207
  · exact u5208
  · exact u5209
  · exact u5210
  · exact u5211
  · exact u5212

def b7186 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 196 41 217 249 217 217 473), lower := (rows 259 38 196 41 16 32 64 128 256), losses := [] }

theorem u7186 : Upper (D 3) (R 3) [258,36,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7186
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7187_9 : Upper (D 3) (R 3) [258,36,192,48,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5208

def r7187 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7187 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7187 : Upper (D 3) (R 3) [258,36,192,48] 13 := by
  apply FastRouting.sound _ _ [258,36,192,48] 13 (by decide) (choices 2) [9,65,72,192] r7187 c7187
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7187_9
  · exact u5214
  · exact u5215
  · exact u5216

def b7188 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 185 185 249 185 441), lower := (rows 259 38 196 73 16 32 64 128 256), losses := [] }

theorem u7188 : Upper (D 3) (R 3) [258,36,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7188
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7189_9 : Upper (D 3) (R 3) [258,36,192,80,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5210

theorem m7189_33 : Upper (D 3) (R 3) [258,36,192,80,33] 13 :=
  permutation_upper _ _ _ [258,36,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5213

theorem m7189_40 : Upper (D 3) (R 3) [258,36,192,80,40] 13 :=
  permutation_upper _ _ _ [258,36,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5215

theorem m7189_129 : Upper (D 3) (R 3) [258,36,192,80,129] 13 :=
  permutation_upper _ _ _ [258,36,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5217

def r7189 : Route 9 := (fun mask => (mask,id))

def c7189 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7189 : Upper (D 3) (R 3) [258,36,192,80] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r7189 c7189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7189_9
  · exact m7189_33
  · exact m7189_40
  · exact m7189_129
  · exact u5219
  · exact u5220

theorem m7190_9 : Upper (D 3) (R 3) [258,36,192,96,9] 13 :=
  permutation_upper _ _ _ [258,36,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5211

theorem m7190_129 : Upper (D 3) (R 3) [258,36,192,96,129] 13 :=
  permutation_upper _ _ _ [258,36,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5218

theorem m7190_136 : Upper (D 3) (R 3) [258,36,192,96,136] 13 :=
  permutation_upper _ _ _ [258,36,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5220

def r7190 : Route 9 := (fun mask => (mask,id))

def c7190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7190 : Upper (D 3) (R 3) [258,36,192,96] 13 := by
  apply FastRouting.sound _ _ [258,36,192,96] 13 (by decide) (choices 2) [9,129,136] r7190 c7190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7190_9
  · exact m7190_129
  · exact m7190_136

def b7191 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 200 57 57 121 185 313), lower := (rows 259 38 196 200 16 32 64 128 256), losses := [] }

theorem u7191 : Upper (D 3) (R 3) [258,36,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7192 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 13 241 241 241 241 497), lower := (rows 259 98 13 13 16 32 64 128 256), losses := [] }

theorem u7192 : Upper (D 3) (R 3) [258,96,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 25 245 229 229 229 485), lower := (rows 259 98 13 25 16 32 64 128 256), losses := [] }

theorem u7193 : Upper (D 3) (R 3) [258,96,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7194 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7194 : Upper (D 3) (R 3) [258,96,9,20] 13 := by
  apply FastRouting.sound _ _ [258,96,9,20] 13 (by decide) (choices 2) [33,96,129,160] r7194 c7194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5227
  · exact u5228
  · exact u5229
  · exact u5230

def b7195 : PairBound 9 := { available := 213, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 41 213 245 213 213 469), lower := (rows 259 98 13 41 16 32 64 128 256), losses := [] }

theorem u7195 : Upper (D 3) (R 3) [258,96,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7196 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 13 44 209 241 209 209 465), lower := (rows 259 98 13 44 16 32 64 128 256), losses := [] }

theorem u7196 : Upper (D 3) (R 3) [258,96,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7196
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7197 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 56 213 229 197 197 453), lower := (rows 259 98 13 56 16 32 64 128 256), losses := [] }

theorem u7197 : Upper (D 3) (R 3) [258,96,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7198 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 149 181 213 149 405), lower := (rows 259 98 13 104 16 32 64 128 256), losses := [] }

theorem u7198 : Upper (D 3) (R 3) [258,96,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7198
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7199 : PairBound 9 := { available := 245, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 245 245 245 245 501), lower := (rows 259 98 13 137 16 32 64 128 256), losses := [] }

theorem u7199 : Upper (D 3) (R 3) [258,96,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7199
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P03
