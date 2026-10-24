import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0651
import IrregularNine14P07C0652
import IrregularNine14P07C0653
import IrregularNine14P07C0654
import IrregularNine14P07C0655

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m43380_10 : Upper (D 7) (R 7) [36,288,65,129,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39125

theorem m43380_66 : Upper (D 7) (R 7) [36,288,65,129,66] 13 :=
  permutation_upper _ _ _ [36,288,65,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39131

theorem m43380_72 : Upper (D 7) (R 7) [36,288,65,129,72] 13 :=
  permutation_upper _ _ _ [36,288,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39134

def r43380 : Route 9 := (fun mask => (mask,id))

def c43380 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43380 : Upper (D 7) (R 7) [36,288,65,129] 13 := by
  apply FastRouting.sound _ _ [36,288,65,129] 13 (by decide) (choices 2) [10,66,72,130,136,192] r43380 c43380
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43380_10
  · exact m43380_66
  · exact m43380_72
  · exact u39137
  · exact u39138
  · exact u39139

theorem m43381_3 : Upper (D 7) (R 7) [36,288,65,130,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39112

theorem m43381_9 : Upper (D 7) (R 7) [36,288,65,130,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39118

theorem m43381_10 : Upper (D 7) (R 7) [36,288,65,130,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39126

theorem m43381_65 : Upper (D 7) (R 7) [36,288,65,130,65] 13 :=
  permutation_upper _ _ _ [36,288,65,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39129

theorem m43381_66 : Upper (D 7) (R 7) [36,288,65,130,66] 13 :=
  permutation_upper _ _ _ [36,288,65,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39132

theorem m43381_72 : Upper (D 7) (R 7) [36,288,65,130,72] 13 :=
  permutation_upper _ _ _ [36,288,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39135

theorem m43381_129 : Upper (D 7) (R 7) [36,288,65,130,129] 13 :=
  permutation_upper _ _ _ [36,288,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39137

def r43381 : Route 9 := (fun mask => (mask,id))

def c43381 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43381 : Upper (D 7) (R 7) [36,288,65,130] 13 := by
  apply FastRouting.sound _ _ [36,288,65,130] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43381 c43381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43381_3
  · exact m43381_9
  · exact m43381_10
  · exact m43381_65
  · exact m43381_66
  · exact m43381_72
  · exact m43381_129
  · exact u39140
  · exact u39141
  · exact u39142

theorem m43382_3 : Upper (D 7) (R 7) [36,288,65,144,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39113

theorem m43382_9 : Upper (D 7) (R 7) [36,288,65,144,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39119

theorem m43382_10 : Upper (D 7) (R 7) [36,288,65,144,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39127

theorem m43382_65 : Upper (D 7) (R 7) [36,288,65,144,65] 13 :=
  permutation_upper _ _ _ [36,288,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39130

theorem m43382_66 : Upper (D 7) (R 7) [36,288,65,144,66] 13 :=
  permutation_upper _ _ _ [36,288,65,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39133

theorem m43382_72 : Upper (D 7) (R 7) [36,288,65,144,72] 13 :=
  permutation_upper _ _ _ [36,288,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39136

theorem m43382_129 : Upper (D 7) (R 7) [36,288,65,144,129] 13 :=
  permutation_upper _ _ _ [36,288,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39138

theorem m43382_130 : Upper (D 7) (R 7) [36,288,65,144,130] 13 :=
  permutation_upper _ _ _ [36,288,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39141

def r43382 : Route 9 := (fun mask => (mask,id))

def c43382 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43382 : Upper (D 7) (R 7) [36,288,65,144] 13 := by
  apply FastRouting.sound _ _ [36,288,65,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43382 c43382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43382_3
  · exact m43382_9
  · exact m43382_10
  · exact m43382_65
  · exact m43382_66
  · exact m43382_72
  · exact m43382_129
  · exact m43382_130
  · exact u39143
  · exact u39144

theorem m43383_3 : Upper (D 7) (R 7) [36,288,65,192,3] 13 :=
  permutation_upper _ _ _ [36,288,65,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39114

theorem m43383_9 : Upper (D 7) (R 7) [36,288,65,192,9] 13 :=
  permutation_upper _ _ _ [36,288,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39120

theorem m43383_10 : Upper (D 7) (R 7) [36,288,65,192,10] 13 :=
  permutation_upper _ _ _ [36,288,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39128

theorem m43383_129 : Upper (D 7) (R 7) [36,288,65,192,129] 13 :=
  permutation_upper _ _ _ [36,288,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39139

theorem m43383_130 : Upper (D 7) (R 7) [36,288,65,192,130] 13 :=
  permutation_upper _ _ _ [36,288,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39142

theorem m43383_136 : Upper (D 7) (R 7) [36,288,65,192,136] 13 :=
  permutation_upper _ _ _ [36,288,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39144

def r43383 : Route 9 := (fun mask => (mask,id))

def c43383 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43383 : Upper (D 7) (R 7) [36,288,65,192] 13 := by
  apply FastRouting.sound _ _ [36,288,65,192] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43383 c43383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43383_3
  · exact m43383_9
  · exact m43383_10
  · exact m43383_129
  · exact m43383_130
  · exact m43383_136

def r43384 : Route 9 := (fun mask => (mask,id))

def c43384 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43384 : Upper (D 7) (R 7) [36,288,66,3] 13 := by
  apply FastRouting.sound _ _ [36,288,66,3] 13 (by decide) (choices 2) [9,65,72,129,136,192] r43384 c43384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39145
  · exact u39146
  · exact u39147
  · exact u39148
  · exact u39149
  · exact u39150

theorem m43385_3 : Upper (D 7) (R 7) [36,288,66,17,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39145

def r43385 : Route 9 := (fun mask => (mask,id))

def c43385 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43385 : Upper (D 7) (R 7) [36,288,66,17] 13 := by
  apply FastRouting.sound _ _ [36,288,66,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43385 c43385
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43385_3
  · exact u39151
  · exact u39152
  · exact u39153
  · exact u39154
  · exact u39155
  · exact u39156
  · exact u39157
  · exact u39158
  · exact u39159

theorem m43386_9 : Upper (D 7) (R 7) [36,288,66,18,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39152

def r43386 : Route 9 := (fun mask => (mask,id))

def c43386 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43386 : Upper (D 7) (R 7) [36,288,66,18] 13 := by
  apply FastRouting.sound _ _ [36,288,66,18] 13 (by decide) (choices 2) [9,65,72,129,136,192] r43386 c43386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43386_9
  · exact u39160
  · exact u39161
  · exact u39162
  · exact u39163
  · exact u39164

theorem m43387_3 : Upper (D 7) (R 7) [36,288,66,65,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39146

theorem m43387_9 : Upper (D 7) (R 7) [36,288,66,65,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39153

theorem m43387_10 : Upper (D 7) (R 7) [36,288,66,65,10] 13 :=
  permutation_upper _ _ _ [36,288,66,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39160

def r43387 : Route 9 := (fun mask => (mask,id))

def c43387 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43387 : Upper (D 7) (R 7) [36,288,66,65] 13 := by
  apply FastRouting.sound _ _ [36,288,66,65] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43387 c43387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43387_3
  · exact m43387_9
  · exact m43387_10
  · exact u39165
  · exact u39166
  · exact u39167

def b43388 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 161 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,7)], upper := (rows 37 290 70 74 153 185 217 153 409), lower := (rows 37 290 70 74 16 32 64 128 256), losses := [] }

theorem u43388 : Upper (D 7) (R 7) [36,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43389_3 : Upper (D 7) (R 7) [36,288,66,80,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39147

theorem m43389_9 : Upper (D 7) (R 7) [36,288,66,80,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39155

theorem m43389_10 : Upper (D 7) (R 7) [36,288,66,80,10] 13 :=
  permutation_upper _ _ _ [36,288,66,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39161

def r43389 : Route 9 := (fun mask => (mask,id))

def c43389 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43389 : Upper (D 7) (R 7) [36,288,66,80] 13 := by
  apply FastRouting.sound _ _ [36,288,66,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43389 c43389
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43389_3
  · exact m43389_9
  · exact m43389_10
  · exact u39170
  · exact u39171
  · exact u39172

theorem m43390_3 : Upper (D 7) (R 7) [36,288,66,129,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39148

theorem m43390_9 : Upper (D 7) (R 7) [36,288,66,129,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39156

theorem m43390_10 : Upper (D 7) (R 7) [36,288,66,129,10] 13 :=
  permutation_upper _ _ _ [36,288,66,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39162

theorem m43390_65 : Upper (D 7) (R 7) [36,288,66,129,65] 13 :=
  permutation_upper _ _ _ [36,288,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39165

theorem m43390_66 : Upper (D 7) (R 7) [36,288,66,129,66] 13 :=
  permutation_upper _ _ _ [36,288,66,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39168

theorem m43390_72 : Upper (D 7) (R 7) [36,288,66,129,72] 13 :=
  permutation_upper _ _ _ [36,288,66,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39170

def r43390 : Route 9 := (fun mask => (mask,id))

def c43390 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43390 : Upper (D 7) (R 7) [36,288,66,129] 13 := by
  apply FastRouting.sound _ _ [36,288,66,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43390 c43390
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43390_3
  · exact m43390_9
  · exact m43390_10
  · exact m43390_65
  · exact m43390_66
  · exact m43390_72
  · exact u39173
  · exact u39174
  · exact u39175
  · exact u39176

theorem m43391_9 : Upper (D 7) (R 7) [36,288,66,130,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39157

theorem m43391_65 : Upper (D 7) (R 7) [36,288,66,130,65] 13 :=
  permutation_upper _ _ _ [36,288,66,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39166

theorem m43391_72 : Upper (D 7) (R 7) [36,288,66,130,72] 13 :=
  permutation_upper _ _ _ [36,288,66,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39171

theorem m43391_129 : Upper (D 7) (R 7) [36,288,66,130,129] 13 :=
  permutation_upper _ _ _ [36,288,66,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39174

def r43391 : Route 9 := (fun mask => (mask,id))

def c43391 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43391 : Upper (D 7) (R 7) [36,288,66,130] 13 := by
  apply FastRouting.sound _ _ [36,288,66,130] 13 (by decide) (choices 2) [9,65,72,129,136,192] r43391 c43391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43391_9
  · exact m43391_65
  · exact m43391_72
  · exact m43391_129
  · exact u39177
  · exact u39178

theorem m43392_3 : Upper (D 7) (R 7) [36,288,66,144,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39149

theorem m43392_9 : Upper (D 7) (R 7) [36,288,66,144,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39158

theorem m43392_10 : Upper (D 7) (R 7) [36,288,66,144,10] 13 :=
  permutation_upper _ _ _ [36,288,66,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39163

theorem m43392_65 : Upper (D 7) (R 7) [36,288,66,144,65] 13 :=
  permutation_upper _ _ _ [36,288,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39167

theorem m43392_66 : Upper (D 7) (R 7) [36,288,66,144,66] 13 :=
  permutation_upper _ _ _ [36,288,66,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39169

theorem m43392_72 : Upper (D 7) (R 7) [36,288,66,144,72] 13 :=
  permutation_upper _ _ _ [36,288,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39172

theorem m43392_129 : Upper (D 7) (R 7) [36,288,66,144,129] 13 :=
  permutation_upper _ _ _ [36,288,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39175

theorem m43392_130 : Upper (D 7) (R 7) [36,288,66,144,130] 13 :=
  permutation_upper _ _ _ [36,288,66,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39177

def r43392 : Route 9 := (fun mask => (mask,id))

def c43392 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43392 : Upper (D 7) (R 7) [36,288,66,144] 13 := by
  apply FastRouting.sound _ _ [36,288,66,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43392 c43392
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43392_3
  · exact m43392_9
  · exact m43392_10
  · exact m43392_65
  · exact m43392_66
  · exact m43392_72
  · exact m43392_129
  · exact m43392_130
  · exact u39179
  · exact u39180

theorem m43393_3 : Upper (D 7) (R 7) [36,288,66,192,3] 13 :=
  permutation_upper _ _ _ [36,288,66,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39150

theorem m43393_9 : Upper (D 7) (R 7) [36,288,66,192,9] 13 :=
  permutation_upper _ _ _ [36,288,66,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39159

theorem m43393_10 : Upper (D 7) (R 7) [36,288,66,192,10] 13 :=
  permutation_upper _ _ _ [36,288,66,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39164

theorem m43393_129 : Upper (D 7) (R 7) [36,288,66,192,129] 13 :=
  permutation_upper _ _ _ [36,288,66,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39176

theorem m43393_130 : Upper (D 7) (R 7) [36,288,66,192,130] 13 :=
  permutation_upper _ _ _ [36,288,66,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39178

theorem m43393_136 : Upper (D 7) (R 7) [36,288,66,192,136] 13 :=
  permutation_upper _ _ _ [36,288,66,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39180

def r43393 : Route 9 := (fun mask => (mask,id))

def c43393 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43393 : Upper (D 7) (R 7) [36,288,66,192] 13 := by
  apply FastRouting.sound _ _ [36,288,66,192] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43393 c43393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43393_3
  · exact m43393_9
  · exact m43393_10
  · exact m43393_129
  · exact m43393_130
  · exact m43393_136

def r43394 : Route 9 := (fun mask => (mask,id))

def c43394 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43394 : Upper (D 7) (R 7) [36,288,72,3] 13 := by
  apply FastRouting.sound _ _ [36,288,72,3] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43394 c43394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39181
  · exact u39182
  · exact u39183
  · exact u39184
  · exact u39185
  · exact u39186

def r43395 : Route 9 := (fun mask => (mask,id))

def c43395 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43395 : Upper (D 7) (R 7) [36,288,72,17] 13 := by
  apply FastRouting.sound _ _ [36,288,72,17] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43395 c43395
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39187
  · exact u39188
  · exact u39189
  · exact u39190
  · exact u39191
  · exact u39192

def r43396 : Route 9 := (fun mask => (mask,id))

def c43396 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43396 : Upper (D 7) (R 7) [36,288,72,18] 13 := by
  apply FastRouting.sound _ _ [36,288,72,18] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43396 c43396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39193
  · exact u39194
  · exact u39195
  · exact u39196
  · exact u39197
  · exact u39198

def b43397 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 73 147 179 211 147 403), lower := (rows 37 290 76 73 16 32 64 128 256), losses := [] }

theorem u43397 : Upper (D 7) (R 7) [36,288,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43398 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 74 147 179 211 147 403), lower := (rows 37 290 76 74 16 32 64 128 256), losses := [] }

theorem u43398 : Upper (D 7) (R 7) [36,288,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43399 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 88 147 163 195 131 387), lower := (rows 37 290 76 88 16 32 64 128 256), losses := [] }

theorem u43399 : Upper (D 7) (R 7) [36,288,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43400 : Route 9 := (fun mask => (mask,id))

def c43400 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43400 : Upper (D 7) (R 7) [36,288,72,129] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43400 c43400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39199
  · exact u39200
  · exact u39201
  · exact u39202
  · exact u39203
  · exact u39204

def r43401 : Route 9 := (fun mask => (mask,id))

def c43401 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43401 : Upper (D 7) (R 7) [36,288,72,130] 13 := by
  apply FastRouting.sound _ _ [36,288,72,130] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43401 c43401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39205
  · exact u39206
  · exact u39207
  · exact u39208
  · exact u39209
  · exact u39210

def r43402 : Route 9 := (fun mask => (mask,id))

def c43402 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43402 : Upper (D 7) (R 7) [36,288,72,144] 13 := by
  apply FastRouting.sound _ _ [36,288,72,144] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43402 c43402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39211
  · exact u39212
  · exact u39213
  · exact u39214
  · exact u39215
  · exact u39216

def b43403 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 200 147 179 211 147 403), lower := (rows 37 290 76 200 16 32 64 128 256), losses := [] }

theorem u43403 : Upper (D 7) (R 7) [36,288,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43404 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43404 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43404 : Upper (D 7) (R 7) [36,288,192,3] 13 := by
  apply FastRouting.sound _ _ [36,288,192,3] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43404 c43404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39217
  · exact u39218
  · exact u39219
  · exact u39220
  · exact u39221
  · exact u39222
  · exact u39223

theorem m43405_3 : Upper (D 7) (R 7) [36,288,192,17,3] 13 :=
  permutation_upper _ _ _ [36,288,192,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39218

def r43405 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43405 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43405 : Upper (D 7) (R 7) [36,288,192,17] 13 := by
  apply FastRouting.sound _ _ [36,288,192,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43405 c43405
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43405_3
  · exact u39224
  · exact u39225
  · exact u39226
  · exact u39227
  · exact u39228
  · exact u39229

theorem m43406_3 : Upper (D 7) (R 7) [36,288,192,18,3] 13 :=
  permutation_upper _ _ _ [36,288,192,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39219

theorem m43406_9 : Upper (D 7) (R 7) [36,288,192,18,9] 13 :=
  permutation_upper _ _ _ [36,288,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39225

def r43406 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c43406 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43406 : Upper (D 7) (R 7) [36,288,192,18] 13 := by
  apply FastRouting.sound _ _ [36,288,192,18] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r43406 c43406
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43406_3
  · exact m43406_9
  · exact u39230
  · exact u39231
  · exact u39232
  · exact u39233
  · exact u39234

theorem m43407_3 : Upper (D 7) (R 7) [36,288,192,65,3] 13 :=
  permutation_upper _ _ _ [36,288,192,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39220

theorem m43407_9 : Upper (D 7) (R 7) [36,288,192,65,9] 13 :=
  permutation_upper _ _ _ [36,288,192,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39226

theorem m43407_10 : Upper (D 7) (R 7) [36,288,192,65,10] 13 :=
  permutation_upper _ _ _ [36,288,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39231

def r43407 : Route 9 := (fun mask => (mask,id))

def c43407 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43407 : Upper (D 7) (R 7) [36,288,192,65] 13 := by
  apply FastRouting.sound _ _ [36,288,192,65] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43407 c43407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43407_3
  · exact m43407_9
  · exact m43407_10
  · exact u39235
  · exact u39236
  · exact u39237

theorem m43408_3 : Upper (D 7) (R 7) [36,288,192,66,3] 13 :=
  permutation_upper _ _ _ [36,288,192,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39221

theorem m43408_9 : Upper (D 7) (R 7) [36,288,192,66,9] 13 :=
  permutation_upper _ _ _ [36,288,192,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39227

theorem m43408_10 : Upper (D 7) (R 7) [36,288,192,66,10] 13 :=
  permutation_upper _ _ _ [36,288,192,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39232

theorem m43408_129 : Upper (D 7) (R 7) [36,288,192,66,129] 13 :=
  permutation_upper _ _ _ [36,288,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39236

def r43408 : Route 9 := (fun mask => (mask,id))

def c43408 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43408 : Upper (D 7) (R 7) [36,288,192,66] 13 := by
  apply FastRouting.sound _ _ [36,288,192,66] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43408 c43408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43408_3
  · exact m43408_9
  · exact m43408_10
  · exact m43408_129
  · exact u39238
  · exact u39239

theorem m43409_3 : Upper (D 7) (R 7) [36,288,192,80,3] 13 :=
  permutation_upper _ _ _ [36,288,192,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39222

theorem m43409_9 : Upper (D 7) (R 7) [36,288,192,80,9] 13 :=
  permutation_upper _ _ _ [36,288,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39228

theorem m43409_10 : Upper (D 7) (R 7) [36,288,192,80,10] 13 :=
  permutation_upper _ _ _ [36,288,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39233

theorem m43409_129 : Upper (D 7) (R 7) [36,288,192,80,129] 13 :=
  permutation_upper _ _ _ [36,288,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39237

theorem m43409_130 : Upper (D 7) (R 7) [36,288,192,80,130] 13 :=
  permutation_upper _ _ _ [36,288,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39239

def r43409 : Route 9 := (fun mask => (mask,id))

def c43409 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43409 : Upper (D 7) (R 7) [36,288,192,80] 13 := by
  apply FastRouting.sound _ _ [36,288,192,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43409 c43409
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43409_3
  · exact m43409_9
  · exact m43409_10
  · exact m43409_129
  · exact m43409_130
  · exact u39240

def b43410 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 35 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 37 290 196 200 27 59 91 155 283), lower := (rows 37 290 196 200 16 32 64 128 256), losses := [] }

theorem u43410 : Upper (D 7) (R 7) [36,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43411 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 322 7 11 248 248 248 248 504), lower := (rows 37 322 7 11 16 32 64 128 256), losses := [] }

theorem u43411 : Upper (D 7) (R 7) [36,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43412 : Route 9 := (fun mask => (mask,id))

def c43412 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43412 : Upper (D 7) (R 7) [36,320,3,17] 13 := by
  apply FastRouting.sound _ _ [36,320,3,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43412 c43412
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39247
  · exact u39248
  · exact u39249
  · exact u39250
  · exact u39251
  · exact u39252
  · exact u39253
  · exact u39254
  · exact u39255
  · exact u39256

theorem m43413_9 : Upper (D 7) (R 7) [36,320,3,18,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39247

def r43413 : Route 9 := (fun mask => (mask,id))

def c43413 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43413 : Upper (D 7) (R 7) [36,320,3,18] 13 := by
  apply FastRouting.sound _ _ [36,320,3,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43413 c43413
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43413_9
  · exact u39257
  · exact u39258
  · exact u39259
  · exact u39260
  · exact u39261
  · exact u39262
  · exact u39263
  · exact u39264
  · exact u39265

def b43414 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 7 41 218 250 218 218 474), lower := (rows 37 322 7 41 16 32 64 128 256), losses := [] }

theorem u43414 : Upper (D 7) (R 7) [36,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43415 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 7 42 217 249 217 217 473), lower := (rows 37 322 7 42 16 32 64 128 256), losses := [] }

theorem u43415 : Upper (D 7) (R 7) [36,320,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43416_3 : Upper (D 7) (R 7) [36,320,3,48,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39241

theorem m43416_9 : Upper (D 7) (R 7) [36,320,3,48,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39249

theorem m43416_10 : Upper (D 7) (R 7) [36,320,3,48,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39258

def r43416 : Route 9 := (fun mask => (mask,id))

def c43416 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43416 : Upper (D 7) (R 7) [36,320,3,48] 13 := by
  apply FastRouting.sound _ _ [36,320,3,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43416 c43416
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43416_3
  · exact m43416_9
  · exact m43416_10
  · exact u39275
  · exact u39276
  · exact u39277
  · exact u39278
  · exact u39279
  · exact u39280
  · exact u39281

theorem m43417_10 : Upper (D 7) (R 7) [36,320,3,65,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39259

theorem m43417_34 : Upper (D 7) (R 7) [36,320,3,65,34] 13 :=
  permutation_upper _ _ _ [36,320,3,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39270

theorem m43417_40 : Upper (D 7) (R 7) [36,320,3,65,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39275

def r43417 : Route 9 := (fun mask => (mask,id))

def c43417 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43417 : Upper (D 7) (R 7) [36,320,3,65] 13 := by
  apply FastRouting.sound _ _ [36,320,3,65] 13 (by decide) (choices 2) [10,34,40,130,136,160] r43417 c43417
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43417_10
  · exact m43417_34
  · exact m43417_40
  · exact u39282
  · exact u39283
  · exact u39284

def b43418 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 7 74 185 185 249 185 441), lower := (rows 37 322 7 74 16 32 64 128 256), losses := [] }

theorem u43418 : Upper (D 7) (R 7) [36,320,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m43419_3 : Upper (D 7) (R 7) [36,320,3,80,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39242

theorem m43419_9 : Upper (D 7) (R 7) [36,320,3,80,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39251

theorem m43419_10 : Upper (D 7) (R 7) [36,320,3,80,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39260

theorem m43419_33 : Upper (D 7) (R 7) [36,320,3,80,33] 13 :=
  permutation_upper _ _ _ [36,320,3,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39266

theorem m43419_34 : Upper (D 7) (R 7) [36,320,3,80,34] 13 :=
  permutation_upper _ _ _ [36,320,3,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39271

theorem m43419_40 : Upper (D 7) (R 7) [36,320,3,80,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39277

def r43419 : Route 9 := (fun mask => (mask,id))

def c43419 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43419 : Upper (D 7) (R 7) [36,320,3,80] 13 := by
  apply FastRouting.sound _ _ [36,320,3,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43419 c43419
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43419_3
  · exact m43419_9
  · exact m43419_10
  · exact m43419_33
  · exact m43419_34
  · exact m43419_40
  · exact u39288
  · exact u39289
  · exact u39290
  · exact u39291

theorem m43420_3 : Upper (D 7) (R 7) [36,320,3,96,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39243

theorem m43420_9 : Upper (D 7) (R 7) [36,320,3,96,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39252

theorem m43420_10 : Upper (D 7) (R 7) [36,320,3,96,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39261

def r43420 : Route 9 := (fun mask => (mask,id))

def c43420 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43420 : Upper (D 7) (R 7) [36,320,3,96] 13 := by
  apply FastRouting.sound _ _ [36,320,3,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r43420 c43420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43420_3
  · exact m43420_9
  · exact m43420_10
  · exact u39292
  · exact u39293
  · exact u39294

theorem m43421_10 : Upper (D 7) (R 7) [36,320,3,129,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39262

theorem m43421_34 : Upper (D 7) (R 7) [36,320,3,129,34] 13 :=
  permutation_upper _ _ _ [36,320,3,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39272

theorem m43421_40 : Upper (D 7) (R 7) [36,320,3,129,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39278

theorem m43421_66 : Upper (D 7) (R 7) [36,320,3,129,66] 13 :=
  permutation_upper _ _ _ [36,320,3,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39285

theorem m43421_72 : Upper (D 7) (R 7) [36,320,3,129,72] 13 :=
  permutation_upper _ _ _ [36,320,3,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39288

theorem m43421_96 : Upper (D 7) (R 7) [36,320,3,129,96] 13 :=
  permutation_upper _ _ _ [36,320,3,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39292

def r43421 : Route 9 := (fun mask => (mask,id))

def c43421 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43421 : Upper (D 7) (R 7) [36,320,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,3,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r43421 c43421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43421_10
  · exact m43421_34
  · exact m43421_40
  · exact m43421_66
  · exact m43421_72
  · exact m43421_96
  · exact u39295
  · exact u39296
  · exact u39297
  · exact u39298

theorem m43422_9 : Upper (D 7) (R 7) [36,320,3,130,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39253

theorem m43422_33 : Upper (D 7) (R 7) [36,320,3,130,33] 13 :=
  permutation_upper _ _ _ [36,320,3,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39267

theorem m43422_40 : Upper (D 7) (R 7) [36,320,3,130,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39279

theorem m43422_65 : Upper (D 7) (R 7) [36,320,3,130,65] 13 :=
  permutation_upper _ _ _ [36,320,3,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39282

theorem m43422_72 : Upper (D 7) (R 7) [36,320,3,130,72] 13 :=
  permutation_upper _ _ _ [36,320,3,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39289

theorem m43422_96 : Upper (D 7) (R 7) [36,320,3,130,96] 13 :=
  permutation_upper _ _ _ [36,320,3,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39293

theorem m43422_129 : Upper (D 7) (R 7) [36,320,3,130,129] 13 :=
  permutation_upper _ _ _ [36,320,3,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39295

def r43422 : Route 9 := (fun mask => (mask,id))

def c43422 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43422 : Upper (D 7) (R 7) [36,320,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,3,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r43422 c43422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43422_9
  · exact m43422_33
  · exact m43422_40
  · exact m43422_65
  · exact m43422_72
  · exact m43422_96
  · exact m43422_129
  · exact u39299
  · exact u39300
  · exact u39301

theorem m43423_3 : Upper (D 7) (R 7) [36,320,3,144,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39244

theorem m43423_9 : Upper (D 7) (R 7) [36,320,3,144,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39254

theorem m43423_10 : Upper (D 7) (R 7) [36,320,3,144,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39263

theorem m43423_33 : Upper (D 7) (R 7) [36,320,3,144,33] 13 :=
  permutation_upper _ _ _ [36,320,3,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39268

theorem m43423_34 : Upper (D 7) (R 7) [36,320,3,144,34] 13 :=
  permutation_upper _ _ _ [36,320,3,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39273

theorem m43423_40 : Upper (D 7) (R 7) [36,320,3,144,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39280

theorem m43423_65 : Upper (D 7) (R 7) [36,320,3,144,65] 13 :=
  permutation_upper _ _ _ [36,320,3,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39283

theorem m43423_66 : Upper (D 7) (R 7) [36,320,3,144,66] 13 :=
  permutation_upper _ _ _ [36,320,3,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39286

theorem m43423_72 : Upper (D 7) (R 7) [36,320,3,144,72] 13 :=
  permutation_upper _ _ _ [36,320,3,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39290

theorem m43423_96 : Upper (D 7) (R 7) [36,320,3,144,96] 13 :=
  permutation_upper _ _ _ [36,320,3,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39294

theorem m43423_129 : Upper (D 7) (R 7) [36,320,3,144,129] 13 :=
  permutation_upper _ _ _ [36,320,3,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39296

theorem m43423_130 : Upper (D 7) (R 7) [36,320,3,144,130] 13 :=
  permutation_upper _ _ _ [36,320,3,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39299

def r43423 : Route 9 := (fun mask => (mask,id))

def c43423 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43423 : Upper (D 7) (R 7) [36,320,3,144] 13 := by
  apply FastRouting.sound _ _ [36,320,3,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r43423 c43423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43423_3
  · exact m43423_9
  · exact m43423_10
  · exact m43423_33
  · exact m43423_34
  · exact m43423_40
  · exact m43423_65
  · exact m43423_66
  · exact m43423_72
  · exact m43423_96
  · exact m43423_129
  · exact m43423_130
  · exact u39302
  · exact u39303
  · exact u39304

theorem m43424_3 : Upper (D 7) (R 7) [36,320,3,160,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39245

theorem m43424_9 : Upper (D 7) (R 7) [36,320,3,160,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39255

theorem m43424_10 : Upper (D 7) (R 7) [36,320,3,160,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39264

theorem m43424_65 : Upper (D 7) (R 7) [36,320,3,160,65] 13 :=
  permutation_upper _ _ _ [36,320,3,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39284

theorem m43424_66 : Upper (D 7) (R 7) [36,320,3,160,66] 13 :=
  permutation_upper _ _ _ [36,320,3,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39287

theorem m43424_72 : Upper (D 7) (R 7) [36,320,3,160,72] 13 :=
  permutation_upper _ _ _ [36,320,3,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39291

theorem m43424_129 : Upper (D 7) (R 7) [36,320,3,160,129] 13 :=
  permutation_upper _ _ _ [36,320,3,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39297

theorem m43424_130 : Upper (D 7) (R 7) [36,320,3,160,130] 13 :=
  permutation_upper _ _ _ [36,320,3,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39300

theorem m43424_136 : Upper (D 7) (R 7) [36,320,3,160,136] 13 :=
  permutation_upper _ _ _ [36,320,3,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39303

def r43424 : Route 9 := (fun mask => (mask,id))

def c43424 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43424 : Upper (D 7) (R 7) [36,320,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r43424 c43424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43424_3
  · exact m43424_9
  · exact m43424_10
  · exact m43424_65
  · exact m43424_66
  · exact m43424_72
  · exact m43424_129
  · exact m43424_130
  · exact m43424_136
  · exact u39305

theorem m43425_3 : Upper (D 7) (R 7) [36,320,3,192,3] 13 :=
  permutation_upper _ _ _ [36,320,3,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39246

theorem m43425_9 : Upper (D 7) (R 7) [36,320,3,192,9] 13 :=
  permutation_upper _ _ _ [36,320,3,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39256

theorem m43425_10 : Upper (D 7) (R 7) [36,320,3,192,10] 13 :=
  permutation_upper _ _ _ [36,320,3,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39265

theorem m43425_33 : Upper (D 7) (R 7) [36,320,3,192,33] 13 :=
  permutation_upper _ _ _ [36,320,3,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39269

theorem m43425_34 : Upper (D 7) (R 7) [36,320,3,192,34] 13 :=
  permutation_upper _ _ _ [36,320,3,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39274

theorem m43425_40 : Upper (D 7) (R 7) [36,320,3,192,40] 13 :=
  permutation_upper _ _ _ [36,320,3,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39281

theorem m43425_129 : Upper (D 7) (R 7) [36,320,3,192,129] 13 :=
  permutation_upper _ _ _ [36,320,3,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39298

theorem m43425_130 : Upper (D 7) (R 7) [36,320,3,192,130] 13 :=
  permutation_upper _ _ _ [36,320,3,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39301

theorem m43425_136 : Upper (D 7) (R 7) [36,320,3,192,136] 13 :=
  permutation_upper _ _ _ [36,320,3,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39304

theorem m43425_160 : Upper (D 7) (R 7) [36,320,3,192,160] 13 :=
  permutation_upper _ _ _ [36,320,3,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u39305

def r43425 : Route 9 := (fun mask => (mask,id))

def c43425 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43425 : Upper (D 7) (R 7) [36,320,3,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r43425 c43425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43425_3
  · exact m43425_9
  · exact m43425_10
  · exact m43425_33
  · exact m43425_34
  · exact m43425_40
  · exact m43425_129
  · exact m43425_130
  · exact m43425_136
  · exact m43425_160

def b43426 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 322 13 11 242 242 242 242 498), lower := (rows 37 322 13 11 16 32 64 128 256), losses := [] }

theorem u43426 : Upper (D 7) (R 7) [36,320,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43427 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 322 13 25 242 226 226 226 482), lower := (rows 37 322 13 25 16 32 64 128 256), losses := [] }

theorem u43427 : Upper (D 7) (R 7) [36,320,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43428 : Route 9 := (fun mask => (mask,id))

def c43428 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43428 : Upper (D 7) (R 7) [36,320,9,18] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43428 c43428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39306
  · exact u39307
  · exact u39308
  · exact u39309
  · exact u39310
  · exact u39311
  · exact u39312
  · exact u39313
  · exact u39314
  · exact u39315

def b43429 : PairBound 9 := { available := 210, camps := [{ cop := 5, region := 13, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 41 210 242 210 210 466), lower := (rows 37 322 13 41 16 32 64 128 256), losses := [] }

theorem u43429 : Upper (D 7) (R 7) [36,320,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43430 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 42 211 243 211 211 467), lower := (rows 37 322 13 42 16 32 64 128 256), losses := [] }

theorem u43430 : Upper (D 7) (R 7) [36,320,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43431 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 56 211 227 195 195 451), lower := (rows 37 322 13 56 16 32 64 128 256), losses := [] }

theorem u43431 : Upper (D 7) (R 7) [36,320,9,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43432 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 322 13 73 178 178 242 178 434), lower := (rows 37 322 13 73 16 32 64 128 256), losses := [] }

theorem u43432 : Upper (D 7) (R 7) [36,320,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43433 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 13 74 179 179 243 179 435), lower := (rows 37 322 13 74 16 32 64 128 256), losses := [] }

theorem u43433 : Upper (D 7) (R 7) [36,320,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43434 : Route 9 := (fun mask => (mask,id))

def c43434 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43434 : Upper (D 7) (R 7) [36,320,9,80] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r43434 c43434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39316
  · exact u39317
  · exact u39318
  · exact u39319
  · exact u39320
  · exact u39321

def b43435 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 104 147 179 211 147 403), lower := (rows 37 322 13 104 16 32 64 128 256), losses := [] }

theorem u43435 : Upper (D 7) (R 7) [36,320,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43436 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 37 322 13 137 242 242 242 242 498), lower := (rows 37 322 13 137 16 32 64 128 256), losses := [] }

theorem u43436 : Upper (D 7) (R 7) [36,320,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43437 : Route 9 := (fun mask => (mask,id))

def c43437 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43437 : Upper (D 7) (R 7) [36,320,9,130] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43437 c43437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39322
  · exact u39323
  · exact u39324
  · exact u39325
  · exact u39326
  · exact u39327
  · exact u39328
  · exact u39329
  · exact u39330
  · exact u39331

def r43438 : Route 9 := (fun mask => (mask,id))

def c43438 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43438 : Upper (D 7) (R 7) [36,320,9,144] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r43438 c43438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u39332
  · exact u39333
  · exact u39334
  · exact u39335
  · exact u39336
  · exact u39337
  · exact u39338
  · exact u39339
  · exact u39340
  · exact u39341

def b43439 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 13 168 211 243 211 211 467), lower := (rows 37 322 13 168 16 32 64 128 256), losses := [] }

theorem u43439 : Upper (D 7) (R 7) [36,320,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u43439
end Delivery.IrregularNine14.P07
