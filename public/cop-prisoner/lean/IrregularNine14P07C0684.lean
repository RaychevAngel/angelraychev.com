import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0501
import IrregularNine14P07C0502
import IrregularNine14P07C0503
import IrregularNine14P07C0504
import IrregularNine14P07C0505

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41040 : PairBound 9 := { available := 403, camps := [{ cop := 2, region := 11, targets := 128 },{ cop := 2, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(3,7)], upper := (rows 7 11 100 104 403 435 467 403 403), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u41040 : Upper (D 7) (R 7) [6,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41041_129 : Upper (D 7) (R 7) [6,9,96,160,129] 13 :=
  permutation_upper _ _ _ [6,9,96,160,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30113

theorem m41041_130 : Upper (D 7) (R 7) [6,9,96,160,130] 13 :=
  permutation_upper _ _ _ [6,9,96,160,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30112

theorem m41041_258 : Upper (D 7) (R 7) [6,9,96,160,258] 13 :=
  permutation_upper _ _ _ [6,9,96,160,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30115

theorem m41041_384 : Upper (D 7) (R 7) [6,9,96,160,384] 13 :=
  permutation_upper _ _ _ [6,9,96,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30116

def r41041 : Route 9 := (fun mask => (mask,id))

def c41041 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41041 : Upper (D 7) (R 7) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41041 c41041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30111
  · exact u30112
  · exact u30113
  · exact m41041_129
  · exact m41041_130
  · exact u30114
  · exact u30115
  · exact m41041_258
  · exact u30116
  · exact m41041_384

def b41042 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 2, targets := 224 },{ cop := 0, region := 244, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(2,0)], upper := (rows 7 11 100 265 242 242 242 242 498), lower := (rows 7 11 100 265 16 32 64 128 256), losses := [] }

theorem u41042 : Upper (D 7) (R 7) [6,9,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41043 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41043 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41043 : Upper (D 7) (R 7) [6,9,96,258] 13 := by
  apply FastRouting.sound _ _ [6,9,96,258] 13 (by decide) (choices 2) [33,96,129,160] r41043 c41043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30117
  · exact u30118
  · exact u30119
  · exact u30120

def r41044 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41044 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41044 : Upper (D 7) (R 7) [6,9,96,272] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41044 c41044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30121
  · exact u30122
  · exact u30123
  · exact u30124
  · exact u30125
  · exact u30126
  · exact u30127

def r41045 : Route 9 := (fun mask => (mask,id))

def c41045 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41045 : Upper (D 7) (R 7) [6,9,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41045 c41045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30128
  · exact u30129
  · exact u30130
  · exact u30131
  · exact u30132
  · exact u30133

def r41046 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41046 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41046 : Upper (D 7) (R 7) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41046 c41046
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30134
  · exact u30135
  · exact u30136
  · exact u30137
  · exact u30138
  · exact u30139
  · exact u30140

def b41047 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 37 11 496 480 480 480 480), lower := (rows 7 26 37 11 16 32 64 128 256), losses := [] }

theorem u41047 : Upper (D 7) (R 7) [6,24,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41048 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6),(3,7)], upper := (rows 7 26 37 41 466 482 450 450 450), lower := (rows 7 26 37 41 16 32 64 128 256), losses := [] }

theorem u41048 : Upper (D 7) (R 7) [6,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41049 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 26 37 42 465 481 449 449 449), lower := (rows 7 26 37 42 16 32 64 128 256), losses := [] }

theorem u41049 : Upper (D 7) (R 7) [6,24,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41050_34 : Upper (D 7) (R 7) [6,24,33,65,34] 13 :=
  permutation_upper _ _ _ [6,24,33,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30149

def r41050 : Route 9 := (fun mask => (mask,id))

def c41050 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41050 : Upper (D 7) (R 7) [6,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41050 c41050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41050_34
  · exact u30153
  · exact u30154
  · exact u30155
  · exact u30156
  · exact u30157
  · exact u30158
  · exact u30159
  · exact u30160
  · exact u30161

theorem m41051_33 : Upper (D 7) (R 7) [6,24,33,66,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30145

theorem m41051_65 : Upper (D 7) (R 7) [6,24,33,66,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30153

theorem m41051_129 : Upper (D 7) (R 7) [6,24,33,66,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30155

def r41051 : Route 9 := (fun mask => (mask,id))

def c41051 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41051 : Upper (D 7) (R 7) [6,24,33,66] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41051 c41051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41051_33
  · exact m41051_65
  · exact u30162
  · exact m41051_129
  · exact u30163
  · exact u30164
  · exact u30165
  · exact u30166
  · exact u30167
  · exact u30168

theorem m41052_3 : Upper (D 7) (R 7) [6,24,33,96,3] 13 :=
  permutation_upper _ _ _ [6,24,33,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30141

theorem m41052_65 : Upper (D 7) (R 7) [6,24,33,96,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30154

theorem m41052_66 : Upper (D 7) (R 7) [6,24,33,96,66] 13 :=
  permutation_upper _ _ _ [6,24,33,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30162

theorem m41052_129 : Upper (D 7) (R 7) [6,24,33,96,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30156

theorem m41052_130 : Upper (D 7) (R 7) [6,24,33,96,130] 13 :=
  permutation_upper _ _ _ [6,24,33,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30163

def r41052 : Route 9 := (fun mask => (mask,id))

def c41052 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41052 : Upper (D 7) (R 7) [6,24,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41052 c41052
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41052_3
  · exact m41052_65
  · exact m41052_66
  · exact m41052_129
  · exact m41052_130
  · exact u30169
  · exact u30170
  · exact u30171
  · exact u30172
  · exact u30173

theorem m41053_3 : Upper (D 7) (R 7) [6,24,33,192,3] 13 :=
  permutation_upper _ _ _ [6,24,33,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30142

theorem m41053_33 : Upper (D 7) (R 7) [6,24,33,192,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30146

theorem m41053_34 : Upper (D 7) (R 7) [6,24,33,192,34] 13 :=
  permutation_upper _ _ _ [6,24,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30150

theorem m41053_65 : Upper (D 7) (R 7) [6,24,33,192,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30157

theorem m41053_66 : Upper (D 7) (R 7) [6,24,33,192,66] 13 :=
  permutation_upper _ _ _ [6,24,33,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30164

theorem m41053_96 : Upper (D 7) (R 7) [6,24,33,192,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30169

def r41053 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41053 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41053 : Upper (D 7) (R 7) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41053 c41053
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41053_3
  · exact m41053_33
  · exact m41053_34
  · exact m41053_65
  · exact m41053_66
  · exact m41053_96
  · exact u30174
  · exact u30175
  · exact u30176
  · exact u30177
  · exact u30178

theorem m41054_34 : Upper (D 7) (R 7) [6,24,33,257,34] 13 :=
  permutation_upper _ _ _ [6,24,33,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30151

theorem m41054_66 : Upper (D 7) (R 7) [6,24,33,257,66] 13 :=
  permutation_upper _ _ _ [6,24,33,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30165

theorem m41054_96 : Upper (D 7) (R 7) [6,24,33,257,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30170

theorem m41054_192 : Upper (D 7) (R 7) [6,24,33,257,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30175

def r41054 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41054 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41054 : Upper (D 7) (R 7) [6,24,33,257] 13 := by
  apply FastRouting.sound _ _ [6,24,33,257] 13 (by decide) (choices 2) [34,66,96,192] r41054 c41054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41054_34
  · exact m41054_66
  · exact m41054_96
  · exact m41054_192

theorem m41055_33 : Upper (D 7) (R 7) [6,24,33,258,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30147

theorem m41055_65 : Upper (D 7) (R 7) [6,24,33,258,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30158

theorem m41055_96 : Upper (D 7) (R 7) [6,24,33,258,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30171

theorem m41055_192 : Upper (D 7) (R 7) [6,24,33,258,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30176

def r41055 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41055 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41055 : Upper (D 7) (R 7) [6,24,33,258] 13 := by
  apply FastRouting.sound _ _ [6,24,33,258] 13 (by decide) (choices 2) [33,65,96,192] r41055 c41055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41055_33
  · exact m41055_65
  · exact m41055_96
  · exact m41055_192

theorem m41056_3 : Upper (D 7) (R 7) [6,24,33,288,3] 13 :=
  permutation_upper _ _ _ [6,24,33,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30143

theorem m41056_65 : Upper (D 7) (R 7) [6,24,33,288,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30159

theorem m41056_66 : Upper (D 7) (R 7) [6,24,33,288,66] 13 :=
  permutation_upper _ _ _ [6,24,33,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30166

theorem m41056_192 : Upper (D 7) (R 7) [6,24,33,288,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30177

def r41056 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41056 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41056 : Upper (D 7) (R 7) [6,24,33,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,288] 13 (by decide) (choices 2) [3,65,66,192] r41056 c41056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41056_3
  · exact m41056_65
  · exact m41056_66
  · exact m41056_192

theorem m41057_3 : Upper (D 7) (R 7) [6,24,33,320,3] 13 :=
  permutation_upper _ _ _ [6,24,33,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30144

theorem m41057_33 : Upper (D 7) (R 7) [6,24,33,320,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30148

theorem m41057_34 : Upper (D 7) (R 7) [6,24,33,320,34] 13 :=
  permutation_upper _ _ _ [6,24,33,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30152

theorem m41057_65 : Upper (D 7) (R 7) [6,24,33,320,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30160

theorem m41057_66 : Upper (D 7) (R 7) [6,24,33,320,66] 13 :=
  permutation_upper _ _ _ [6,24,33,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30167

theorem m41057_96 : Upper (D 7) (R 7) [6,24,33,320,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30172

theorem m41057_129 : Upper (D 7) (R 7) [6,24,33,320,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30161

theorem m41057_130 : Upper (D 7) (R 7) [6,24,33,320,130] 13 :=
  permutation_upper _ _ _ [6,24,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30168

theorem m41057_160 : Upper (D 7) (R 7) [6,24,33,320,160] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30173

theorem m41057_192 : Upper (D 7) (R 7) [6,24,33,320,192] 13 :=
  permutation_upper _ _ _ [6,24,33,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30178

def r41057 : Route 9 := (fun mask => (mask,id))

def c41057 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41057 : Upper (D 7) (R 7) [6,24,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41057 c41057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41057_3
  · exact m41057_33
  · exact m41057_34
  · exact m41057_65
  · exact m41057_66
  · exact m41057_96
  · exact m41057_129
  · exact m41057_130
  · exact m41057_160
  · exact m41057_192

def b41058 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 100 11 497 481 481 481 481), lower := (rows 7 26 100 11 16 32 64 128 256), losses := [] }

theorem u41058 : Upper (D 7) (R 7) [6,24,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41059_3 : Upper (D 7) (R 7) [6,24,96,33,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30179

def r41059 : Route 9 := (fun mask => (mask,id))

def c41059 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41059 : Upper (D 7) (R 7) [6,24,96,33] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41059 c41059
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41059_3
  · exact u30185
  · exact u30186
  · exact u30187
  · exact u30188
  · exact u30189
  · exact u30190
  · exact u30191
  · exact u30192
  · exact u30193

theorem m41060_65 : Upper (D 7) (R 7) [6,24,96,34,65] 13 :=
  permutation_upper _ _ _ [6,24,96,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30186

def r41060 : Route 9 := (fun mask => (mask,id))

def c41060 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41060 : Upper (D 7) (R 7) [6,24,96,34] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34] 13 (by decide) (choices 2) [65,129,192,257,320,384] r41060 c41060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41060_65
  · exact u30194
  · exact u30195
  · exact u30196
  · exact u30197
  · exact u30198

def b41061 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 8, targets := 131 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 26 100 104 403 419 451 387 387), lower := (rows 7 26 100 104 16 32 64 128 256), losses := [] }

theorem u41061 : Upper (D 7) (R 7) [6,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41062_3 : Upper (D 7) (R 7) [6,24,96,129,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30180

theorem m41062_33 : Upper (D 7) (R 7) [6,24,96,129,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30187

theorem m41062_34 : Upper (D 7) (R 7) [6,24,96,129,34] 13 :=
  permutation_upper _ _ _ [6,24,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30194

theorem m41062_96 : Upper (D 7) (R 7) [6,24,96,129,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30199

def r41062 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41062 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41062 : Upper (D 7) (R 7) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41062 c41062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41062_3
  · exact m41062_33
  · exact m41062_34
  · exact m41062_96
  · exact u30204
  · exact u30205
  · exact u30206
  · exact u30207
  · exact u30208
  · exact u30209
  · exact u30210

theorem m41063_33 : Upper (D 7) (R 7) [6,24,96,130,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30188

theorem m41063_96 : Upper (D 7) (R 7) [6,24,96,130,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30200

theorem m41063_129 : Upper (D 7) (R 7) [6,24,96,130,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30205

def r41063 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41063 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41063 : Upper (D 7) (R 7) [6,24,96,130] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r41063 c41063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41063_33
  · exact m41063_96
  · exact m41063_129
  · exact u30211
  · exact u30212
  · exact u30213
  · exact u30214

theorem m41064_3 : Upper (D 7) (R 7) [6,24,96,160,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30181

theorem m41064_65 : Upper (D 7) (R 7) [6,24,96,160,65] 13 :=
  permutation_upper _ _ _ [6,24,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30189

theorem m41064_66 : Upper (D 7) (R 7) [6,24,96,160,66] 13 :=
  permutation_upper _ _ _ [6,24,96,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30195

theorem m41064_129 : Upper (D 7) (R 7) [6,24,96,160,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30206

theorem m41064_130 : Upper (D 7) (R 7) [6,24,96,160,130] 13 :=
  permutation_upper _ _ _ [6,24,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30211

def r41064 : Route 9 := (fun mask => (mask,id))

def c41064 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41064 : Upper (D 7) (R 7) [6,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41064 c41064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41064_3
  · exact m41064_65
  · exact m41064_66
  · exact m41064_129
  · exact m41064_130
  · exact u30215
  · exact u30216
  · exact u30217
  · exact u30218
  · exact u30219

theorem m41065_3 : Upper (D 7) (R 7) [6,24,96,257,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30182

theorem m41065_33 : Upper (D 7) (R 7) [6,24,96,257,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30190

theorem m41065_34 : Upper (D 7) (R 7) [6,24,96,257,34] 13 :=
  permutation_upper _ _ _ [6,24,96,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30196

theorem m41065_96 : Upper (D 7) (R 7) [6,24,96,257,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30201

theorem m41065_129 : Upper (D 7) (R 7) [6,24,96,257,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30207

theorem m41065_130 : Upper (D 7) (R 7) [6,24,96,257,130] 13 :=
  permutation_upper _ _ _ [6,24,96,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30212

theorem m41065_160 : Upper (D 7) (R 7) [6,24,96,257,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30216

def r41065 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41065 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41065 : Upper (D 7) (R 7) [6,24,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41065 c41065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41065_3
  · exact m41065_33
  · exact m41065_34
  · exact m41065_96
  · exact m41065_129
  · exact m41065_130
  · exact m41065_160

theorem m41066_33 : Upper (D 7) (R 7) [6,24,96,258,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30191

theorem m41066_96 : Upper (D 7) (R 7) [6,24,96,258,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30202

theorem m41066_129 : Upper (D 7) (R 7) [6,24,96,258,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30208

theorem m41066_160 : Upper (D 7) (R 7) [6,24,96,258,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30217

def r41066 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41066 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41066 : Upper (D 7) (R 7) [6,24,96,258] 13 := by
  apply FastRouting.sound _ _ [6,24,96,258] 13 (by decide) (choices 2) [33,96,129,160] r41066 c41066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41066_33
  · exact m41066_96
  · exact m41066_129
  · exact m41066_160

theorem m41067_3 : Upper (D 7) (R 7) [6,24,96,288,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30183

theorem m41067_65 : Upper (D 7) (R 7) [6,24,96,288,65] 13 :=
  permutation_upper _ _ _ [6,24,96,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30192

theorem m41067_66 : Upper (D 7) (R 7) [6,24,96,288,66] 13 :=
  permutation_upper _ _ _ [6,24,96,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30197

theorem m41067_129 : Upper (D 7) (R 7) [6,24,96,288,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30209

theorem m41067_130 : Upper (D 7) (R 7) [6,24,96,288,130] 13 :=
  permutation_upper _ _ _ [6,24,96,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30213

theorem m41067_192 : Upper (D 7) (R 7) [6,24,96,288,192] 13 :=
  permutation_upper _ _ _ [6,24,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30218

def r41067 : Route 9 := (fun mask => (mask,id))

def c41067 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41067 : Upper (D 7) (R 7) [6,24,96,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41067 c41067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41067_3
  · exact m41067_65
  · exact m41067_66
  · exact m41067_129
  · exact m41067_130
  · exact m41067_192

theorem m41068_3 : Upper (D 7) (R 7) [6,24,96,384,3] 13 :=
  permutation_upper _ _ _ [6,24,96,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30184

theorem m41068_33 : Upper (D 7) (R 7) [6,24,96,384,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30193

theorem m41068_34 : Upper (D 7) (R 7) [6,24,96,384,34] 13 :=
  permutation_upper _ _ _ [6,24,96,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30198

theorem m41068_96 : Upper (D 7) (R 7) [6,24,96,384,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30203

theorem m41068_129 : Upper (D 7) (R 7) [6,24,96,384,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30210

theorem m41068_130 : Upper (D 7) (R 7) [6,24,96,384,130] 13 :=
  permutation_upper _ _ _ [6,24,96,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30214

theorem m41068_160 : Upper (D 7) (R 7) [6,24,96,384,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30219

def r41068 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41068 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41068 : Upper (D 7) (R 7) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41068 c41068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41068_3
  · exact m41068_33
  · exact m41068_34
  · exact m41068_96
  · exact m41068_129
  · exact m41068_130
  · exact m41068_160

def b41069 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 261 11 240 224 224 224 480), lower := (rows 7 26 261 11 16 32 64 128 256), losses := [] }

theorem u41069 : Upper (D 7) (R 7) [6,24,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41070 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41070 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41070 : Upper (D 7) (R 7) [6,24,257,33] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33] 13 (by decide) (choices 2) [34,66,96,192] r41070 c41070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30221
  · exact u30222
  · exact u30223
  · exact u30224

theorem m41071_33 : Upper (D 7) (R 7) [6,24,257,34,33] 13 :=
  permutation_upper _ _ _ [6,24,257,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30221

theorem m41071_65 : Upper (D 7) (R 7) [6,24,257,34,65] 13 :=
  permutation_upper _ _ _ [6,24,257,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30222

def r41071 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41071 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41071 : Upper (D 7) (R 7) [6,24,257,34] 13 := by
  apply FastRouting.sound _ _ [6,24,257,34] 13 (by decide) (choices 2) [33,65,96,192] r41071 c41071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41071_33
  · exact m41071_65
  · exact u30225
  · exact u30226

theorem m41072_3 : Upper (D 7) (R 7) [6,24,257,96,3] 13 :=
  permutation_upper _ _ _ [6,24,257,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30220

theorem m41072_33 : Upper (D 7) (R 7) [6,24,257,96,33] 13 :=
  permutation_upper _ _ _ [6,24,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30223

theorem m41072_34 : Upper (D 7) (R 7) [6,24,257,96,34] 13 :=
  permutation_upper _ _ _ [6,24,257,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30225

theorem m41072_129 : Upper (D 7) (R 7) [6,24,257,96,129] 13 :=
  permutation_upper _ _ _ [6,24,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30224

theorem m41072_130 : Upper (D 7) (R 7) [6,24,257,96,130] 13 :=
  permutation_upper _ _ _ [6,24,257,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30226

def r41072 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41072 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41072 : Upper (D 7) (R 7) [6,24,257,96] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41072 c41072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41072_3
  · exact m41072_33
  · exact m41072_34
  · exact u30227
  · exact m41072_129
  · exact m41072_130
  · exact u30228

def b41073 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 26 292 11 241 225 225 225 481), lower := (rows 7 26 292 11 16 32 64 128 256), losses := [] }

theorem u41073 : Upper (D 7) (R 7) [6,24,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41074_3 : Upper (D 7) (R 7) [6,24,288,33,3] 13 :=
  permutation_upper _ _ _ [6,24,288,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30229

def r41074 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41074 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41074 : Upper (D 7) (R 7) [6,24,288,33] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33] 13 (by decide) (choices 2) [3,65,66,192] r41074 c41074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41074_3
  · exact u30233
  · exact u30234
  · exact u30235

def r41075 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41075 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41075 : Upper (D 7) (R 7) [6,24,288,34] 13 := by
  apply FastRouting.sound _ _ [6,24,288,34] 13 (by decide) (choices 2) [65,192] r41075 c41075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30236
  · exact u30237

theorem m41076_3 : Upper (D 7) (R 7) [6,24,288,65,3] 13 :=
  permutation_upper _ _ _ [6,24,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30230

theorem m41076_33 : Upper (D 7) (R 7) [6,24,288,65,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30233

theorem m41076_34 : Upper (D 7) (R 7) [6,24,288,65,34] 13 :=
  permutation_upper _ _ _ [6,24,288,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30236

def r41076 : Route 9 := (fun mask => (mask,id))

def c41076 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41076 : Upper (D 7) (R 7) [6,24,288,65] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41076 c41076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41076_3
  · exact m41076_33
  · exact m41076_34
  · exact u30238
  · exact u30239
  · exact u30240
  · exact u30241
  · exact u30242
  · exact u30243
  · exact u30244

theorem m41077_33 : Upper (D 7) (R 7) [6,24,288,66,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30234

theorem m41077_65 : Upper (D 7) (R 7) [6,24,288,66,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30239

theorem m41077_129 : Upper (D 7) (R 7) [6,24,288,66,129] 13 :=
  permutation_upper _ _ _ [6,24,288,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30242

def r41077 : Route 9 := (fun mask => (mask,id))

def c41077 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41077 : Upper (D 7) (R 7) [6,24,288,66] 13 := by
  apply FastRouting.sound _ _ [6,24,288,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41077 c41077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41077_33
  · exact m41077_65
  · exact u30245
  · exact m41077_129
  · exact u30246
  · exact u30247

theorem m41078_3 : Upper (D 7) (R 7) [6,24,288,96,3] 13 :=
  permutation_upper _ _ _ [6,24,288,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30231

theorem m41078_65 : Upper (D 7) (R 7) [6,24,288,96,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30240

theorem m41078_66 : Upper (D 7) (R 7) [6,24,288,96,66] 13 :=
  permutation_upper _ _ _ [6,24,288,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30245

theorem m41078_129 : Upper (D 7) (R 7) [6,24,288,96,129] 13 :=
  permutation_upper _ _ _ [6,24,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30243

theorem m41078_130 : Upper (D 7) (R 7) [6,24,288,96,130] 13 :=
  permutation_upper _ _ _ [6,24,288,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30246

def r41078 : Route 9 := (fun mask => (mask,id))

def c41078 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41078 : Upper (D 7) (R 7) [6,24,288,96] 13 := by
  apply FastRouting.sound _ _ [6,24,288,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41078 c41078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41078_3
  · exact m41078_65
  · exact m41078_66
  · exact m41078_129
  · exact m41078_130
  · exact u30248

theorem m41079_3 : Upper (D 7) (R 7) [6,24,288,192,3] 13 :=
  permutation_upper _ _ _ [6,24,288,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30232

theorem m41079_33 : Upper (D 7) (R 7) [6,24,288,192,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30235

theorem m41079_34 : Upper (D 7) (R 7) [6,24,288,192,34] 13 :=
  permutation_upper _ _ _ [6,24,288,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30237

theorem m41079_65 : Upper (D 7) (R 7) [6,24,288,192,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30244

theorem m41079_66 : Upper (D 7) (R 7) [6,24,288,192,66] 13 :=
  permutation_upper _ _ _ [6,24,288,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30247

theorem m41079_96 : Upper (D 7) (R 7) [6,24,288,192,96] 13 :=
  permutation_upper _ _ _ [6,24,288,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30248

def r41079 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41079 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41079 : Upper (D 7) (R 7) [6,24,288,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41079 c41079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41079_3
  · exact m41079_33
  · exact m41079_34
  · exact m41079_65
  · exact m41079_66
  · exact m41079_96
  · exact u30249

def b41080 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 35 13 26 496 480 480 480 480), lower := (rows 7 35 13 26 16 32 64 128 256), losses := [] }

theorem u41080 : Upper (D 7) (R 7) [6,33,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41081 : PairBound 9 := { available := 464, camps := [{ cop := 5, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 42 464 496 464 464 464), lower := (rows 7 35 13 42 16 32 64 128 256), losses := [] }

theorem u41081 : Upper (D 7) (R 7) [6,33,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41082 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 56 466 482 450 450 450), lower := (rows 7 35 13 56 16 32 64 128 256), losses := [] }

theorem u41082 : Upper (D 7) (R 7) [6,33,9,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41083 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 35 13 74 496 496 496 496 496), lower := (rows 7 35 13 74 16 32 64 128 256), losses := [] }

theorem u41083 : Upper (D 7) (R 7) [6,33,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41084 : Route 9 := (fun mask => (mask,id))

def c41084 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41084 : Upper (D 7) (R 7) [6,33,9,80] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41084 c41084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30250
  · exact u30251
  · exact u30252
  · exact u30253
  · exact u30254
  · exact u30255
  · exact u30256
  · exact u30257
  · exact u30258
  · exact u30259

def b41085 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 104 466 498 466 466 466), lower := (rows 7 35 13 104 16 32 64 128 256), losses := [] }

theorem u41085 : Upper (D 7) (R 7) [6,33,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41086 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41086 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41086 : Upper (D 7) (R 7) [6,33,9,192] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192] 13 (by decide) (choices 2) [34,66,96,192,258,288,320] r41086 c41086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30260
  · exact u30261
  · exact u30262
  · exact u30263
  · exact u30264
  · exact u30265
  · exact u30266

def b41087 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 35 13 266 240 240 240 240 496), lower := (rows 7 35 13 266 16 32 64 128 256), losses := [] }

theorem u41087 : Upper (D 7) (R 7) [6,33,9,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41088 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41088 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41088 : Upper (D 7) (R 7) [6,33,9,272] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272] 13 (by decide) (choices 2) [34,66,96,192] r41088 c41088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u30267
  · exact u30268
  · exact u30269
  · exact u30270

def b41089 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 296 210 242 210 210 466), lower := (rows 7 35 13 296 16 32 64 128 256), losses := [] }

theorem u41089 : Upper (D 7) (R 7) [6,33,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41090 : Route 9 := (fun mask => (mask,id))

def c41090 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41090 : Upper (D 7) (R 7) [6,33,9,320] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41090 c41090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u30271
  · exact u30272
  · exact u30273
  · exact u30274
  · exact u30275
  · exact u30276

def b41091 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 28 11 496 480 480 480 480), lower := (rows 7 35 28 11 16 32 64 128 256), losses := [] }

theorem u41091 : Upper (D 7) (R 7) [6,33,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41092 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 28 41 466 482 450 450 450), lower := (rows 7 35 28 41 16 32 64 128 256), losses := [] }

theorem u41092 : Upper (D 7) (R 7) [6,33,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41093 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 28 42 465 481 449 449 449), lower := (rows 7 35 28 42 16 32 64 128 256), losses := [] }

theorem u41093 : Upper (D 7) (R 7) [6,33,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41094_34 : Upper (D 7) (R 7) [6,33,24,65,34] 13 :=
  permutation_upper _ _ _ [6,33,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30285

def r41094 : Route 9 := (fun mask => (mask,id))

def c41094 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41094 : Upper (D 7) (R 7) [6,33,24,65] 13 := by
  apply FastRouting.sound _ _ [6,33,24,65] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41094 c41094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41094_34
  · exact u30289
  · exact u30290
  · exact u30291
  · exact u30292
  · exact u30293
  · exact u30294
  · exact u30295
  · exact u30296
  · exact u30297

theorem m41095_33 : Upper (D 7) (R 7) [6,33,24,66,33] 13 :=
  permutation_upper _ _ _ [6,33,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30281

theorem m41095_65 : Upper (D 7) (R 7) [6,33,24,66,65] 13 :=
  permutation_upper _ _ _ [6,33,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30289

theorem m41095_129 : Upper (D 7) (R 7) [6,33,24,66,129] 13 :=
  permutation_upper _ _ _ [6,33,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30291

def r41095 : Route 9 := (fun mask => (mask,id))

def c41095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41095 : Upper (D 7) (R 7) [6,33,24,66] 13 := by
  apply FastRouting.sound _ _ [6,33,24,66] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41095 c41095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41095_33
  · exact m41095_65
  · exact u30298
  · exact m41095_129
  · exact u30299
  · exact u30300
  · exact u30301
  · exact u30302
  · exact u30303
  · exact u30304

theorem m41096_3 : Upper (D 7) (R 7) [6,33,24,96,3] 13 :=
  permutation_upper _ _ _ [6,33,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30277

theorem m41096_65 : Upper (D 7) (R 7) [6,33,24,96,65] 13 :=
  permutation_upper _ _ _ [6,33,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30290

theorem m41096_66 : Upper (D 7) (R 7) [6,33,24,96,66] 13 :=
  permutation_upper _ _ _ [6,33,24,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30298

theorem m41096_129 : Upper (D 7) (R 7) [6,33,24,96,129] 13 :=
  permutation_upper _ _ _ [6,33,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30292

theorem m41096_130 : Upper (D 7) (R 7) [6,33,24,96,130] 13 :=
  permutation_upper _ _ _ [6,33,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30299

def r41096 : Route 9 := (fun mask => (mask,id))

def c41096 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41096 : Upper (D 7) (R 7) [6,33,24,96] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41096 c41096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41096_3
  · exact m41096_65
  · exact m41096_66
  · exact m41096_129
  · exact m41096_130
  · exact u30305
  · exact u30306
  · exact u30307
  · exact u30308
  · exact u30309

theorem m41097_3 : Upper (D 7) (R 7) [6,33,24,192,3] 13 :=
  permutation_upper _ _ _ [6,33,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30278

theorem m41097_33 : Upper (D 7) (R 7) [6,33,24,192,33] 13 :=
  permutation_upper _ _ _ [6,33,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30282

theorem m41097_34 : Upper (D 7) (R 7) [6,33,24,192,34] 13 :=
  permutation_upper _ _ _ [6,33,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30286

theorem m41097_65 : Upper (D 7) (R 7) [6,33,24,192,65] 13 :=
  permutation_upper _ _ _ [6,33,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30293

theorem m41097_66 : Upper (D 7) (R 7) [6,33,24,192,66] 13 :=
  permutation_upper _ _ _ [6,33,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30300

theorem m41097_96 : Upper (D 7) (R 7) [6,33,24,192,96] 13 :=
  permutation_upper _ _ _ [6,33,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30305

def r41097 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41097 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41097 : Upper (D 7) (R 7) [6,33,24,192] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41097 c41097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41097_3
  · exact m41097_33
  · exact m41097_34
  · exact m41097_65
  · exact m41097_66
  · exact m41097_96
  · exact u30310
  · exact u30311
  · exact u30312
  · exact u30313
  · exact u30314

theorem m41098_34 : Upper (D 7) (R 7) [6,33,24,257,34] 13 :=
  permutation_upper _ _ _ [6,33,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30287

theorem m41098_66 : Upper (D 7) (R 7) [6,33,24,257,66] 13 :=
  permutation_upper _ _ _ [6,33,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30301

theorem m41098_96 : Upper (D 7) (R 7) [6,33,24,257,96] 13 :=
  permutation_upper _ _ _ [6,33,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30306

theorem m41098_192 : Upper (D 7) (R 7) [6,33,24,257,192] 13 :=
  permutation_upper _ _ _ [6,33,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30311

def r41098 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41098 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41098 : Upper (D 7) (R 7) [6,33,24,257] 13 := by
  apply FastRouting.sound _ _ [6,33,24,257] 13 (by decide) (choices 2) [34,66,96,192] r41098 c41098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41098_34
  · exact m41098_66
  · exact m41098_96
  · exact m41098_192

theorem m41099_33 : Upper (D 7) (R 7) [6,33,24,258,33] 13 :=
  permutation_upper _ _ _ [6,33,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30283

theorem m41099_65 : Upper (D 7) (R 7) [6,33,24,258,65] 13 :=
  permutation_upper _ _ _ [6,33,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30294

theorem m41099_96 : Upper (D 7) (R 7) [6,33,24,258,96] 13 :=
  permutation_upper _ _ _ [6,33,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30307

theorem m41099_192 : Upper (D 7) (R 7) [6,33,24,258,192] 13 :=
  permutation_upper _ _ _ [6,33,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30312

def r41099 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41099 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41099 : Upper (D 7) (R 7) [6,33,24,258] 13 := by
  apply FastRouting.sound _ _ [6,33,24,258] 13 (by decide) (choices 2) [33,65,96,192] r41099 c41099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41099_33
  · exact m41099_65
  · exact m41099_96
  · exact m41099_192

#print axioms u41099
end Delivery.IrregularNine14.P07
