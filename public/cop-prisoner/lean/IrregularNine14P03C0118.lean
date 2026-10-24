import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0082
import IrregularNine14P03C0083
import IrregularNine14P03C0084
import IrregularNine14P03C0085

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7080 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 44 104 209 241 209 209 465), lower := (rows 259 7 44 104 16 32 64 128 256), losses := [] }

theorem u7080 : Upper (D 3) (R 3) [258,5,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7081 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7081 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7081 : Upper (D 3) (R 3) [258,5,40,192] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192] 13 (by decide) (choices 2) [33,65,96,192] r7081 c7081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4962
  · exact u4963
  · exact u4964
  · exact u4965

def r7082 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7082 : Upper (D 3) (R 3) [258,5,96,17] 13 := by
  apply FastRouting.sound _ _ [258,5,96,17] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r7082 c7082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4966
  · exact u4967
  · exact u4968
  · exact u4969
  · exact u4970
  · exact u4971
  · exact u4972

def b7083 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 100 41 217 249 217 217 473), lower := (rows 259 7 100 41 16 32 64 128 256), losses := [] }

theorem u7083 : Upper (D 3) (R 3) [258,5,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7083
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7084_9 : Upper (D 3) (R 3) [258,5,96,48,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4968

theorem m7084_65 : Upper (D 3) (R 3) [258,5,96,48,65] 13 :=
  permutation_upper _ _ _ [258,5,96,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4973

def r7084 : Route 9 := (fun mask => (mask,id))

def c7084 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7084 : Upper (D 3) (R 3) [258,5,96,48] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7084 c7084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7084_9
  · exact m7084_65
  · exact u4977
  · exact u4978
  · exact u4979
  · exact u4980

def b7085 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 153 185 217 153 409), lower := (rows 259 7 100 104 16 32 64 128 256), losses := [] }

theorem u7085 : Upper (D 3) (R 3) [258,5,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7085
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7086_9 : Upper (D 3) (R 3) [258,5,96,129,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4970

theorem m7086_33 : Upper (D 3) (R 3) [258,5,96,129,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4974

theorem m7086_40 : Upper (D 3) (R 3) [258,5,96,129,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4978

theorem m7086_96 : Upper (D 3) (R 3) [258,5,96,129,96] 13 :=
  permutation_upper _ _ _ [258,5,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4981

def r7086 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7086 : Upper (D 3) (R 3) [258,5,96,129] 13 := by
  apply FastRouting.sound _ _ [258,5,96,129] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r7086 c7086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7086_9
  · exact m7086_33
  · exact m7086_40
  · exact m7086_96
  · exact u4983
  · exact u4984
  · exact u4985

theorem m7087_9 : Upper (D 3) (R 3) [258,5,96,144,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4971

theorem m7087_33 : Upper (D 3) (R 3) [258,5,96,144,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4975

theorem m7087_40 : Upper (D 3) (R 3) [258,5,96,144,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4979

theorem m7087_96 : Upper (D 3) (R 3) [258,5,96,144,96] 13 :=
  permutation_upper _ _ _ [258,5,96,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4982

theorem m7087_129 : Upper (D 3) (R 3) [258,5,96,144,129] 13 :=
  permutation_upper _ _ _ [258,5,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4984

def r7087 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7087 : Upper (D 3) (R 3) [258,5,96,144] 13 := by
  apply FastRouting.sound _ _ [258,5,96,144] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r7087 c7087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7087_9
  · exact m7087_33
  · exact m7087_40
  · exact m7087_96
  · exact m7087_129
  · exact u4986
  · exact u4987

theorem m7088_9 : Upper (D 3) (R 3) [258,5,96,160,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4972

theorem m7088_65 : Upper (D 3) (R 3) [258,5,96,160,65] 13 :=
  permutation_upper _ _ _ [258,5,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4976

theorem m7088_72 : Upper (D 3) (R 3) [258,5,96,160,72] 13 :=
  permutation_upper _ _ _ [258,5,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4980

theorem m7088_129 : Upper (D 3) (R 3) [258,5,96,160,129] 13 :=
  permutation_upper _ _ _ [258,5,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4985

theorem m7088_136 : Upper (D 3) (R 3) [258,5,96,160,136] 13 :=
  permutation_upper _ _ _ [258,5,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4987

def r7088 : Route 9 := (fun mask => (mask,id))

def c7088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7088 : Upper (D 3) (R 3) [258,5,96,160] 13 := by
  apply FastRouting.sound _ _ [258,5,96,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7088 c7088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7088_9
  · exact m7088_65
  · exact m7088_72
  · exact m7088_129
  · exact m7088_136
  · exact u4988

def r7089 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7089 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7089 : Upper (D 3) (R 3) [258,12,17,33] 13 := by
  apply FastRouting.sound _ _ [258,12,17,33] 13 (by decide) (choices 2) [33,65,96,192] r7089 c7089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4989
  · exact u4990
  · exact u4991
  · exact u4992

def r7090 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7090 : Upper (D 3) (R 3) [258,12,17,96] 13 := by
  apply FastRouting.sound _ _ [258,12,17,96] 13 (by decide) (choices 2) [33,96,129,160] r7090 c7090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4993
  · exact u4994
  · exact u4995
  · exact u4996

def b7091 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 37 41 209 241 209 209 465), lower := (rows 259 14 37 41 16 32 64 128 256), losses := [] }

theorem u7091 : Upper (D 3) (R 3) [258,12,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7091
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7092 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 37 56 209 225 193 193 449), lower := (rows 259 14 37 56 16 32 64 128 256), losses := [] }

theorem u7092 : Upper (D 3) (R 3) [258,12,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7092
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7093_65 : Upper (D 3) (R 3) [258,12,33,65,65] 13 :=
  permutation_upper _ _ _ [258,12,33,65,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4997

theorem m7093_192 : Upper (D 3) (R 3) [258,12,33,65,192] 13 :=
  permutation_upper _ _ _ [258,12,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5000

def r7093 : Route 9 := (fun mask => (mask,id))

def c7093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7093 : Upper (D 3) (R 3) [258,12,33,65] 13 := by
  apply FastRouting.sound _ _ [258,12,33,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7093 c7093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4997
  · exact m7093_65
  · exact u4998
  · exact u4999
  · exact u5000
  · exact m7093_192

def r7094 : Route 9 := (fun mask => (mask,id))

def c7094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7094 : Upper (D 3) (R 3) [258,12,33,80] 13 := by
  apply FastRouting.sound _ _ [258,12,33,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7094 c7094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5001
  · exact u5002
  · exact u5003
  · exact u5004
  · exact u5005
  · exact u5006

def b7095 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 37 104 209 241 209 209 465), lower := (rows 259 14 37 104 16 32 64 128 256), losses := [] }

theorem u7095 : Upper (D 3) (R 3) [258,12,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7096 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7096 : Upper (D 3) (R 3) [258,12,33,192] 13 := by
  apply FastRouting.sound _ _ [258,12,33,192] 13 (by decide) (choices 2) [33,65,96,192] r7096 c7096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5007
  · exact u5008
  · exact u5009
  · exact u5010

def b7097 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 52 104 209 225 193 193 449), lower := (rows 259 14 52 104 16 32 64 128 256), losses := [] }

theorem u7097 : Upper (D 3) (R 3) [258,12,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7098 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7098 : Upper (D 3) (R 3) [258,12,48,192] 13 := by
  apply FastRouting.sound _ _ [258,12,48,192] 13 (by decide) (choices 2) [33,65,96,192] r7098 c7098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5011
  · exact u5012
  · exact u5013
  · exact u5014

def b7099 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 100 104 145 177 209 145 401), lower := (rows 259 14 100 104 16 32 64 128 256), losses := [] }

theorem u7099 : Upper (D 3) (R 3) [258,12,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7099
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7100 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 14 100 168 209 241 209 209 465), lower := (rows 259 14 100 168 16 32 64 128 256), losses := [] }

theorem u7100 : Upper (D 3) (R 3) [258,12,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 13 240 240 240 240 496), lower := (rows 259 35 13 13 16 32 64 128 256), losses := [] }

theorem u7101 : Upper (D 3) (R 3) [258,33,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 25 244 228 228 228 484), lower := (rows 259 35 13 25 16 32 64 128 256), losses := [] }

theorem u7102 : Upper (D 3) (R 3) [258,33,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7103 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7103 : Upper (D 3) (R 3) [258,33,9,20] 13 := by
  apply FastRouting.sound _ _ [258,33,9,20] 13 (by decide) (choices 2) [33,65,96,192] r7103 c7103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5021
  · exact u5022
  · exact u5023
  · exact u5024

def b7104 : PairBound 9 := { available := 212, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 41 212 244 212 212 468), lower := (rows 259 35 13 41 16 32 64 128 256), losses := [] }

theorem u7104 : Upper (D 3) (R 3) [258,33,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7105 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 209 241 209 209 465), lower := (rows 259 35 13 44 16 32 64 128 256), losses := [] }

theorem u7105 : Upper (D 3) (R 3) [258,33,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7106 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 56 213 229 197 197 453), lower := (rows 259 35 13 56 16 32 64 128 256), losses := [] }

theorem u7106 : Upper (D 3) (R 3) [258,33,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7107 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 35 13 73 244 244 244 244 500), lower := (rows 259 35 13 73 16 32 64 128 256), losses := [] }

theorem u7107 : Upper (D 3) (R 3) [258,33,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7108 : Route 9 := (fun mask => (mask,id))

def c7108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7108 : Upper (D 3) (R 3) [258,33,9,68] 13 := by
  apply FastRouting.sound _ _ [258,33,9,68] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7108 c7108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5038
  · exact u5039
  · exact u5040
  · exact u5041
  · exact u5042
  · exact u5043

theorem m7109_5 : Upper (D 3) (R 3) [258,33,9,80,5] 13 :=
  permutation_upper _ _ _ [258,33,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5018

def r7109 : Route 9 := (fun mask => (mask,id))

def c7109 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7109 : Upper (D 3) (R 3) [258,33,9,80] 13 := by
  apply FastRouting.sound _ _ [258,33,9,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r7109 c7109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7109_5
  · exact u5044
  · exact u5045
  · exact u5046
  · exact u5047
  · exact u5048
  · exact u5049
  · exact u5050
  · exact u5051
  · exact u5052

def b7110 : PairBound 9 := { available := 213, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 35 13 104 213 245 213 213 469), lower := (rows 259 35 13 104 16 32 64 128 256), losses := [] }

theorem u7110 : Upper (D 3) (R 3) [258,33,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7110
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7111_5 : Upper (D 3) (R 3) [258,33,9,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5020

def r7111 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7111 : Upper (D 3) (R 3) [258,33,9,192] 13 := by
  apply FastRouting.sound _ _ [258,33,9,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r7111 c7111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7111_5
  · exact u5058
  · exact u5059
  · exact u5060
  · exact u5061
  · exact u5062
  · exact u5063

theorem m7112_9 : Upper (D 3) (R 3) [258,33,17,36,9] 13 :=
  permutation_upper _ _ _ [258,33,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5017

theorem m7112_65 : Upper (D 3) (R 3) [258,33,17,36,65] 13 :=
  permutation_upper _ _ _ [258,33,9,65,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5032

theorem m7112_72 : Upper (D 3) (R 3) [258,33,17,36,72] 13 :=
  permutation_upper _ _ _ [258,33,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5045

theorem m7112_192 : Upper (D 3) (R 3) [258,33,17,36,192] 13 :=
  permutation_upper _ _ _ [258,33,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5059

def r7112 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7112 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7112 : Upper (D 3) (R 3) [258,33,17,36] 13 := by
  apply FastRouting.sound _ _ [258,33,17,36] 13 (by decide) (choices 2) [9,65,72,192] r7112 c7112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7112_9
  · exact m7112_65
  · exact m7112_72
  · exact m7112_192

theorem m7113_12 : Upper (D 3) (R 3) [258,33,17,65,12] 13 :=
  permutation_upper _ _ _ [258,33,9,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5022

theorem m7113_36 : Upper (D 3) (R 3) [258,33,17,65,36] 13 :=
  permutation_upper _ _ _ [258,33,9,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5027

theorem m7113_40 : Upper (D 3) (R 3) [258,33,17,65,40] 13 :=
  permutation_upper _ _ _ [258,33,9,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5029

theorem m7113_68 : Upper (D 3) (R 3) [258,33,17,65,68] 13 :=
  permutation_upper _ _ _ [258,33,9,68,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5039

theorem m7113_72 : Upper (D 3) (R 3) [258,33,17,65,72] 13 :=
  permutation_upper _ _ _ [258,33,9,80,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5046

theorem m7113_96 : Upper (D 3) (R 3) [258,33,17,65,96] 13 :=
  permutation_upper _ _ _ [258,33,9,96,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5053

theorem m7113_132 : Upper (D 3) (R 3) [258,33,17,65,132] 13 :=
  permutation_upper _ _ _ [258,33,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5041

theorem m7113_136 : Upper (D 3) (R 3) [258,33,17,65,136] 13 :=
  permutation_upper _ _ _ [258,33,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5049

theorem m7113_160 : Upper (D 3) (R 3) [258,33,17,65,160] 13 :=
  permutation_upper _ _ _ [258,33,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5055

theorem m7113_192 : Upper (D 3) (R 3) [258,33,17,65,192] 13 :=
  permutation_upper _ _ _ [258,33,9,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5060

def r7113 : Route 9 := (fun mask => (mask,id))

def c7113 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7113 : Upper (D 3) (R 3) [258,33,17,65] 13 := by
  apply FastRouting.sound _ _ [258,33,17,65] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r7113 c7113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7113_12
  · exact m7113_36
  · exact m7113_40
  · exact m7113_68
  · exact m7113_72
  · exact m7113_96
  · exact m7113_132
  · exact m7113_136
  · exact m7113_160
  · exact m7113_192

theorem m7114_9 : Upper (D 3) (R 3) [258,33,17,68,9] 13 :=
  permutation_upper _ _ _ [258,33,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5018

theorem m7114_33 : Upper (D 3) (R 3) [258,33,17,68,33] 13 :=
  permutation_upper _ _ _ [258,33,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5025

theorem m7114_40 : Upper (D 3) (R 3) [258,33,17,68,40] 13 :=
  permutation_upper _ _ _ [258,33,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5030

theorem m7114_65 : Upper (D 3) (R 3) [258,33,17,68,65] 13 :=
  permutation_upper _ _ _ [258,33,9,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5033

theorem m7114_72 : Upper (D 3) (R 3) [258,33,17,68,72] 13 :=
  permutation_upper _ _ _ [258,33,9,80,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5047

theorem m7114_96 : Upper (D 3) (R 3) [258,33,17,68,96] 13 :=
  permutation_upper _ _ _ [258,33,9,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5054

theorem m7114_129 : Upper (D 3) (R 3) [258,33,17,68,129] 13 :=
  permutation_upper _ _ _ [258,33,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5035

theorem m7114_136 : Upper (D 3) (R 3) [258,33,17,68,136] 13 :=
  permutation_upper _ _ _ [258,33,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5050

theorem m7114_160 : Upper (D 3) (R 3) [258,33,17,68,160] 13 :=
  permutation_upper _ _ _ [258,33,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5056

theorem m7114_192 : Upper (D 3) (R 3) [258,33,17,68,192] 13 :=
  permutation_upper _ _ _ [258,33,9,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5061

def r7114 : Route 9 := (fun mask => (mask,id))

def c7114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7114 : Upper (D 3) (R 3) [258,33,17,68] 13 := by
  apply FastRouting.sound _ _ [258,33,17,68] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7114 c7114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7114_9
  · exact m7114_33
  · exact m7114_40
  · exact m7114_65
  · exact m7114_72
  · exact m7114_96
  · exact m7114_129
  · exact m7114_136
  · exact m7114_160
  · exact m7114_192

theorem m7115_5 : Upper (D 3) (R 3) [258,33,17,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5015

theorem m7115_9 : Upper (D 3) (R 3) [258,33,17,96,9] 13 :=
  permutation_upper _ _ _ [258,33,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5019

theorem m7115_12 : Upper (D 3) (R 3) [258,33,17,96,12] 13 :=
  permutation_upper _ _ _ [258,33,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5023

theorem m7115_65 : Upper (D 3) (R 3) [258,33,17,96,65] 13 :=
  permutation_upper _ _ _ [258,33,9,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5034

theorem m7115_68 : Upper (D 3) (R 3) [258,33,17,96,68] 13 :=
  permutation_upper _ _ _ [258,33,9,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5040

theorem m7115_72 : Upper (D 3) (R 3) [258,33,17,96,72] 13 :=
  permutation_upper _ _ _ [258,33,9,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5048

theorem m7115_129 : Upper (D 3) (R 3) [258,33,17,96,129] 13 :=
  permutation_upper _ _ _ [258,33,9,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5036

theorem m7115_132 : Upper (D 3) (R 3) [258,33,17,96,132] 13 :=
  permutation_upper _ _ _ [258,33,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5042

theorem m7115_136 : Upper (D 3) (R 3) [258,33,17,96,136] 13 :=
  permutation_upper _ _ _ [258,33,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5051

theorem m7115_192 : Upper (D 3) (R 3) [258,33,17,96,192] 13 :=
  permutation_upper _ _ _ [258,33,9,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5062

def r7115 : Route 9 := (fun mask => (mask,id))

def c7115 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7115 : Upper (D 3) (R 3) [258,33,17,96] 13 := by
  apply FastRouting.sound _ _ [258,33,17,96] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7115 c7115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7115_5
  · exact m7115_9
  · exact m7115_12
  · exact m7115_65
  · exact m7115_68
  · exact m7115_72
  · exact m7115_129
  · exact m7115_132
  · exact m7115_136
  · exact m7115_192

theorem m7116_5 : Upper (D 3) (R 3) [258,33,17,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,5,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5016

theorem m7116_9 : Upper (D 3) (R 3) [258,33,17,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5020

theorem m7116_12 : Upper (D 3) (R 3) [258,33,17,192,12] 13 :=
  permutation_upper _ _ _ [258,33,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5024

theorem m7116_33 : Upper (D 3) (R 3) [258,33,17,192,33] 13 :=
  permutation_upper _ _ _ [258,33,9,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5026

theorem m7116_36 : Upper (D 3) (R 3) [258,33,17,192,36] 13 :=
  permutation_upper _ _ _ [258,33,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5028

theorem m7116_40 : Upper (D 3) (R 3) [258,33,17,192,40] 13 :=
  permutation_upper _ _ _ [258,33,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5031

theorem m7116_65 : Upper (D 3) (R 3) [258,33,17,192,65] 13 :=
  permutation_upper _ _ _ [258,33,9,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5037

theorem m7116_68 : Upper (D 3) (R 3) [258,33,17,192,68] 13 :=
  permutation_upper _ _ _ [258,33,9,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5043

theorem m7116_72 : Upper (D 3) (R 3) [258,33,17,192,72] 13 :=
  permutation_upper _ _ _ [258,33,9,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5052

theorem m7116_96 : Upper (D 3) (R 3) [258,33,17,192,96] 13 :=
  permutation_upper _ _ _ [258,33,9,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5057

theorem m7116_192 : Upper (D 3) (R 3) [258,33,17,192,192] 13 :=
  permutation_upper _ _ _ [258,33,9,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5063

def r7116 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7116 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7116 : Upper (D 3) (R 3) [258,33,17,192] 13 := by
  apply FastRouting.sound _ _ [258,33,17,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,192] r7116 c7116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7116_5
  · exact m7116_9
  · exact m7116_12
  · exact m7116_33
  · exact m7116_36
  · exact m7116_40
  · exact m7116_65
  · exact m7116_68
  · exact m7116_72
  · exact m7116_96
  · exact m7116_192

def b7117 : PairBound 9 := { available := 197, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 213 229 197 197 453), lower := (rows 259 35 28 41 16 32 64 128 256), losses := [] }

theorem u7117 : Upper (D 3) (R 3) [258,33,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7118 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 28 44 209 225 193 193 449), lower := (rows 259 35 28 44 16 32 64 128 256), losses := [] }

theorem u7118 : Upper (D 3) (R 3) [258,33,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7118
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7119_5 : Upper (D 3) (R 3) [258,33,24,65,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5022

theorem m7119_33 : Upper (D 3) (R 3) [258,33,24,65,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5064

theorem m7119_36 : Upper (D 3) (R 3) [258,33,24,65,36] 13 :=
  permutation_upper _ _ _ [258,33,24,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5067

def r7119 : Route 9 := (fun mask => (mask,id))

def c7119 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7119 : Upper (D 3) (R 3) [258,33,24,65] 13 := by
  apply FastRouting.sound _ _ [258,33,24,65] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r7119 c7119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7119_5
  · exact m7119_33
  · exact m7119_36
  · exact u5069
  · exact u5070
  · exact u5071
  · exact u5072
  · exact u5073
  · exact u5074
  · exact u5075

theorem m7120_33 : Upper (D 3) (R 3) [258,33,24,68,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5065

theorem m7120_65 : Upper (D 3) (R 3) [258,33,24,68,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5070

theorem m7120_129 : Upper (D 3) (R 3) [258,33,24,68,129] 13 :=
  permutation_upper _ _ _ [258,33,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5073

def r7120 : Route 9 := (fun mask => (mask,id))

def c7120 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7120 : Upper (D 3) (R 3) [258,33,24,68] 13 := by
  apply FastRouting.sound _ _ [258,33,24,68] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7120 c7120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7120_33
  · exact m7120_65
  · exact u5076
  · exact m7120_129
  · exact u5077
  · exact u5078

theorem m7121_5 : Upper (D 3) (R 3) [258,33,24,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5023

theorem m7121_65 : Upper (D 3) (R 3) [258,33,24,96,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5071

theorem m7121_68 : Upper (D 3) (R 3) [258,33,24,96,68] 13 :=
  permutation_upper _ _ _ [258,33,24,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5076

theorem m7121_129 : Upper (D 3) (R 3) [258,33,24,96,129] 13 :=
  permutation_upper _ _ _ [258,33,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5074

theorem m7121_132 : Upper (D 3) (R 3) [258,33,24,96,132] 13 :=
  permutation_upper _ _ _ [258,33,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5077

def r7121 : Route 9 := (fun mask => (mask,id))

def c7121 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7121 : Upper (D 3) (R 3) [258,33,24,96] 13 := by
  apply FastRouting.sound _ _ [258,33,24,96] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7121 c7121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7121_5
  · exact m7121_65
  · exact m7121_68
  · exact m7121_129
  · exact m7121_132
  · exact u5079

theorem m7122_5 : Upper (D 3) (R 3) [258,33,24,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5024

theorem m7122_33 : Upper (D 3) (R 3) [258,33,24,192,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5066

theorem m7122_36 : Upper (D 3) (R 3) [258,33,24,192,36] 13 :=
  permutation_upper _ _ _ [258,33,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5068

theorem m7122_65 : Upper (D 3) (R 3) [258,33,24,192,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5075

theorem m7122_68 : Upper (D 3) (R 3) [258,33,24,192,68] 13 :=
  permutation_upper _ _ _ [258,33,24,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5078

theorem m7122_96 : Upper (D 3) (R 3) [258,33,24,192,96] 13 :=
  permutation_upper _ _ _ [258,33,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5079

def r7122 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7122 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7122 : Upper (D 3) (R 3) [258,33,24,192] 13 := by
  apply FastRouting.sound _ _ [258,33,24,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r7122 c7122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7122_5
  · exact m7122_33
  · exact m7122_36
  · exact m7122_65
  · exact m7122_68
  · exact m7122_96
  · exact u5080

def b7123 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 73 220 252 220 220 476), lower := (rows 259 35 37 73 16 32 64 128 256), losses := [] }

theorem u7123 : Upper (D 3) (R 3) [258,33,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7123
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7124 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 217 249 217 217 473), lower := (rows 259 35 37 76 16 32 64 128 256), losses := [] }

theorem u7124 : Upper (D 3) (R 3) [258,33,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7125 : PairBound 9 := { available := 221, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 200 221 253 221 221 477), lower := (rows 259 35 37 200 16 32 64 128 256), losses := [] }

theorem u7125 : Upper (D 3) (R 3) [258,33,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7125
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7126_5 : Upper (D 3) (R 3) [258,33,40,65,5] 13 :=
  permutation_upper _ _ _ [258,33,9,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5029

def r7126 : Route 9 := (fun mask => (mask,id))

def c7126 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7126 : Upper (D 3) (R 3) [258,33,40,65] 13 := by
  apply FastRouting.sound _ _ [258,33,40,65] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7126 c7126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7126_5
  · exact u5088
  · exact u5089
  · exact u5090
  · exact u5091
  · exact u5092

def b7127 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 259 35 44 76 209 241 209 209 465), lower := (rows 259 35 44 76 16 32 64 128 256), losses := [] }

theorem u7127 : Upper (D 3) (R 3) [258,33,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7127
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7128_5 : Upper (D 3) (R 3) [258,33,40,80,5] 13 :=
  permutation_upper _ _ _ [258,33,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5030

def r7128 : Route 9 := (fun mask => (mask,id))

def c7128 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7128 : Upper (D 3) (R 3) [258,33,40,80] 13 := by
  apply FastRouting.sound _ _ [258,33,40,80] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7128 c7128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7128_5
  · exact u5096
  · exact u5097
  · exact u5098
  · exact u5099
  · exact u5100

theorem m7129_5 : Upper (D 3) (R 3) [258,33,40,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5031

def r7129 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7129 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7129 : Upper (D 3) (R 3) [258,33,40,192] 13 := by
  apply FastRouting.sound _ _ [258,33,40,192] 13 (by decide) (choices 2) [5,65,68,192] r7129 c7129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7129_5
  · exact u5101
  · exact u5102
  · exact u5103

theorem m7130_5 : Upper (D 3) (R 3) [258,33,48,65,5] 13 :=
  permutation_upper _ _ _ [258,33,9,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5027

theorem m7130_9 : Upper (D 3) (R 3) [258,33,48,65,9] 13 :=
  permutation_upper _ _ _ [258,33,9,65,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5032

theorem m7130_12 : Upper (D 3) (R 3) [258,33,48,65,12] 13 :=
  permutation_upper _ _ _ [258,33,24,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5067

theorem m7130_65 : Upper (D 3) (R 3) [258,33,48,65,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5088

theorem m7130_68 : Upper (D 3) (R 3) [258,33,48,65,68] 13 :=
  permutation_upper _ _ _ [258,33,40,68,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5093

theorem m7130_72 : Upper (D 3) (R 3) [258,33,48,65,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5096

theorem m7130_129 : Upper (D 3) (R 3) [258,33,48,65,129] 13 :=
  permutation_upper _ _ _ [258,33,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5090

theorem m7130_132 : Upper (D 3) (R 3) [258,33,48,65,132] 13 :=
  permutation_upper _ _ _ [258,33,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5094

theorem m7130_136 : Upper (D 3) (R 3) [258,33,48,65,136] 13 :=
  permutation_upper _ _ _ [258,33,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5098

theorem m7130_192 : Upper (D 3) (R 3) [258,33,48,65,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5101

def r7130 : Route 9 := (fun mask => (mask,id))

def c7130 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7130 : Upper (D 3) (R 3) [258,33,48,65] 13 := by
  apply FastRouting.sound _ _ [258,33,48,65] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7130 c7130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7130_5
  · exact m7130_9
  · exact m7130_12
  · exact m7130_65
  · exact m7130_68
  · exact m7130_72
  · exact m7130_129
  · exact m7130_132
  · exact m7130_136
  · exact m7130_192

theorem m7131_9 : Upper (D 3) (R 3) [258,33,48,68,9] 13 :=
  permutation_upper _ _ _ [258,33,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5045

theorem m7131_65 : Upper (D 3) (R 3) [258,33,48,68,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5089

theorem m7131_72 : Upper (D 3) (R 3) [258,33,48,68,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5097

theorem m7131_129 : Upper (D 3) (R 3) [258,33,48,68,129] 13 :=
  permutation_upper _ _ _ [258,33,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5091

theorem m7131_136 : Upper (D 3) (R 3) [258,33,48,68,136] 13 :=
  permutation_upper _ _ _ [258,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5099

theorem m7131_192 : Upper (D 3) (R 3) [258,33,48,68,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5102

def r7131 : Route 9 := (fun mask => (mask,id))

def c7131 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7131 : Upper (D 3) (R 3) [258,33,48,68] 13 := by
  apply FastRouting.sound _ _ [258,33,48,68] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7131 c7131
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7131_9
  · exact m7131_65
  · exact m7131_72
  · exact m7131_129
  · exact m7131_136
  · exact m7131_192

theorem m7132_5 : Upper (D 3) (R 3) [258,33,48,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5028

theorem m7132_9 : Upper (D 3) (R 3) [258,33,48,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5059

theorem m7132_12 : Upper (D 3) (R 3) [258,33,48,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5068

theorem m7132_65 : Upper (D 3) (R 3) [258,33,48,192,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5092

theorem m7132_68 : Upper (D 3) (R 3) [258,33,48,192,68] 13 :=
  permutation_upper _ _ _ [258,33,40,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5095

theorem m7132_72 : Upper (D 3) (R 3) [258,33,48,192,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5100

theorem m7132_192 : Upper (D 3) (R 3) [258,33,48,192,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5103

def r7132 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7132 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7132 : Upper (D 3) (R 3) [258,33,48,192] 13 := by
  apply FastRouting.sound _ _ [258,33,48,192] 13 (by decide) (choices 2) [5,9,12,65,68,72,192] r7132 c7132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7132_5
  · exact m7132_9
  · exact m7132_12
  · exact m7132_65
  · exact m7132_68
  · exact m7132_72
  · exact m7132_192

def b7133 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 35 69 73 188 188 252 188 444), lower := (rows 259 35 69 73 16 32 64 128 256), losses := [] }

theorem u7133 : Upper (D 3) (R 3) [258,33,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7134 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 76 185 185 249 185 441), lower := (rows 259 35 69 76 16 32 64 128 256), losses := [] }

theorem u7134 : Upper (D 3) (R 3) [258,33,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7134
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7135_5 : Upper (D 3) (R 3) [258,33,65,80,5] 13 :=
  permutation_upper _ _ _ [258,33,9,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5033

theorem m7135_9 : Upper (D 3) (R 3) [258,33,65,80,9] 13 :=
  permutation_upper _ _ _ [258,33,9,68,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5039

theorem m7135_12 : Upper (D 3) (R 3) [258,33,65,80,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5070

theorem m7135_33 : Upper (D 3) (R 3) [258,33,65,80,33] 13 :=
  permutation_upper _ _ _ [258,33,33,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5081

theorem m7135_36 : Upper (D 3) (R 3) [258,33,65,80,36] 13 :=
  permutation_upper _ _ _ [258,33,40,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5089

theorem m7135_40 : Upper (D 3) (R 3) [258,33,65,80,40] 13 :=
  permutation_upper _ _ _ [258,33,40,68,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5093

def r7135 : Route 9 := (fun mask => (mask,id))

def c7135 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7135 : Upper (D 3) (R 3) [258,33,65,80] 13 := by
  apply FastRouting.sound _ _ [258,33,65,80] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r7135 c7135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7135_5
  · exact m7135_9
  · exact m7135_12
  · exact m7135_33
  · exact m7135_36
  · exact m7135_40
  · exact u5109
  · exact u5110
  · exact u5111
  · exact u5112

theorem m7136_5 : Upper (D 3) (R 3) [258,33,65,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5034

theorem m7136_9 : Upper (D 3) (R 3) [258,33,65,96,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5053

theorem m7136_12 : Upper (D 3) (R 3) [258,33,65,96,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5071

def r7136 : Route 9 := (fun mask => (mask,id))

def c7136 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7136 : Upper (D 3) (R 3) [258,33,65,96] 13 := by
  apply FastRouting.sound _ _ [258,33,65,96] 13 (by decide) (choices 2) [5,9,12,129,132,136] r7136 c7136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7136_5
  · exact m7136_9
  · exact m7136_12
  · exact u5113
  · exact u5114
  · exact u5115

theorem m7137_12 : Upper (D 3) (R 3) [258,33,65,129,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5072

theorem m7137_36 : Upper (D 3) (R 3) [258,33,65,129,36] 13 :=
  permutation_upper _ _ _ [258,33,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5090

theorem m7137_40 : Upper (D 3) (R 3) [258,33,65,129,40] 13 :=
  permutation_upper _ _ _ [258,33,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5090

theorem m7137_68 : Upper (D 3) (R 3) [258,33,65,129,68] 13 :=
  permutation_upper _ _ _ [258,33,65,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5106

theorem m7137_72 : Upper (D 3) (R 3) [258,33,65,129,72] 13 :=
  permutation_upper _ _ _ [258,33,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5109

theorem m7137_96 : Upper (D 3) (R 3) [258,33,65,129,96] 13 :=
  permutation_upper _ _ _ [258,33,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5113

theorem m7137_132 : Upper (D 3) (R 3) [258,33,65,129,132] 13 :=
  permutation_upper _ _ _ [258,33,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5109

theorem m7137_136 : Upper (D 3) (R 3) [258,33,65,129,136] 13 :=
  permutation_upper _ _ _ [258,33,65,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5106

theorem m7137_160 : Upper (D 3) (R 3) [258,33,65,129,160] 13 :=
  permutation_upper _ _ _ [258,33,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5113

def r7137 : Route 9 := (fun mask => (mask,id))

def c7137 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7137 : Upper (D 3) (R 3) [258,33,65,129] 13 := by
  apply FastRouting.sound _ _ [258,33,65,129] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r7137 c7137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7137_12
  · exact m7137_36
  · exact m7137_40
  · exact m7137_68
  · exact m7137_72
  · exact m7137_96
  · exact m7137_132
  · exact m7137_136
  · exact m7137_160
  · exact u5116

theorem m7138_9 : Upper (D 3) (R 3) [258,33,65,132,9] 13 :=
  permutation_upper _ _ _ [258,33,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5049

theorem m7138_33 : Upper (D 3) (R 3) [258,33,65,132,33] 13 :=
  permutation_upper _ _ _ [258,33,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5083

theorem m7138_40 : Upper (D 3) (R 3) [258,33,65,132,40] 13 :=
  permutation_upper _ _ _ [258,33,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5098

theorem m7138_65 : Upper (D 3) (R 3) [258,33,65,132,65] 13 :=
  permutation_upper _ _ _ [258,33,65,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5104

theorem m7138_72 : Upper (D 3) (R 3) [258,33,65,132,72] 13 :=
  permutation_upper _ _ _ [258,33,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5110

theorem m7138_96 : Upper (D 3) (R 3) [258,33,65,132,96] 13 :=
  permutation_upper _ _ _ [258,33,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5114

theorem m7138_129 : Upper (D 3) (R 3) [258,33,65,132,129] 13 :=
  permutation_upper _ _ _ [258,33,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5109

def r7138 : Route 9 := (fun mask => (mask,id))

def c7138 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7138 : Upper (D 3) (R 3) [258,33,65,132] 13 := by
  apply FastRouting.sound _ _ [258,33,65,132] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7138 c7138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7138_9
  · exact m7138_33
  · exact m7138_40
  · exact m7138_65
  · exact m7138_72
  · exact m7138_96
  · exact m7138_129
  · exact u5117
  · exact u5118
  · exact u5119

theorem m7139_5 : Upper (D 3) (R 3) [258,33,65,144,5] 13 :=
  permutation_upper _ _ _ [258,33,9,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5035

theorem m7139_9 : Upper (D 3) (R 3) [258,33,65,144,9] 13 :=
  permutation_upper _ _ _ [258,33,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5041

theorem m7139_12 : Upper (D 3) (R 3) [258,33,65,144,12] 13 :=
  permutation_upper _ _ _ [258,33,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5073

theorem m7139_33 : Upper (D 3) (R 3) [258,33,65,144,33] 13 :=
  permutation_upper _ _ _ [258,33,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5082

theorem m7139_36 : Upper (D 3) (R 3) [258,33,65,144,36] 13 :=
  permutation_upper _ _ _ [258,33,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5091

theorem m7139_40 : Upper (D 3) (R 3) [258,33,65,144,40] 13 :=
  permutation_upper _ _ _ [258,33,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5094

theorem m7139_65 : Upper (D 3) (R 3) [258,33,65,144,65] 13 :=
  permutation_upper _ _ _ [258,33,65,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5104

theorem m7139_68 : Upper (D 3) (R 3) [258,33,65,144,68] 13 :=
  permutation_upper _ _ _ [258,33,65,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5107

theorem m7139_72 : Upper (D 3) (R 3) [258,33,65,144,72] 13 :=
  permutation_upper _ _ _ [258,33,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5111

theorem m7139_96 : Upper (D 3) (R 3) [258,33,65,144,96] 13 :=
  permutation_upper _ _ _ [258,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5115

theorem m7139_129 : Upper (D 3) (R 3) [258,33,65,144,129] 13 :=
  permutation_upper _ _ _ [258,33,65,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5106

theorem m7139_132 : Upper (D 3) (R 3) [258,33,65,144,132] 13 :=
  permutation_upper _ _ _ [258,33,65,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5117

def r7139 : Route 9 := (fun mask => (mask,id))

def c7139 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7139 : Upper (D 3) (R 3) [258,33,65,144] 13 := by
  apply FastRouting.sound _ _ [258,33,65,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r7139 c7139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7139_5
  · exact m7139_9
  · exact m7139_12
  · exact m7139_33
  · exact m7139_36
  · exact m7139_40
  · exact m7139_65
  · exact m7139_68
  · exact m7139_72
  · exact m7139_96
  · exact m7139_129
  · exact m7139_132
  · exact u5120
  · exact u5121
  · exact u5122

#print axioms u7139
end Delivery.IrregularNine14.P03
