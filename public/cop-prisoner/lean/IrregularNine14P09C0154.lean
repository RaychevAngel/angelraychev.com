import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0132
import IrregularNine14P09C0133
import IrregularNine14P09C0134
import IrregularNine14P09C0135
import IrregularNine14P09C0136
import IrregularNine14P09C0137

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9240 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 74 401 433 465 401 401), lower := (rows 97 7 44 74 16 32 64 128 256), losses := [] }

theorem u9240 : Upper (D 9) (R 9) [96,5,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9240 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9241_3 : Upper (D 9) (R 9) [96,5,40,80,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7940

def r9241 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9241 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9241 : Upper (D 9) (R 9) [96,5,40,80] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80] 13 (by decide) (choices 2) [3,129,130,384] r9241 c9241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9241_3
  · exact u8053
  · exact u8054
  · exact u8055

def r9242 : Route 9 := (fun mask => (mask,id))

def c9242 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9242 : Upper (D 9) (R 9) [96,5,40,129] 13 := by
  apply FastRouting.sound _ _ [96,5,40,129] 13 (by decide) (choices 2) [66,130,192,258,320,384] r9242 c9242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8056
  · exact u8057
  · exact u8058
  · exact u8059
  · exact u8060
  · exact u8061

def r9243 : Route 9 := (fun mask => (mask,id))

def c9243 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9243 : Upper (D 9) (R 9) [96,5,40,130] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9243 c9243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8062
  · exact u8063
  · exact u8064
  · exact u8065
  · exact u8066
  · exact u8067

theorem m9244_3 : Upper (D 9) (R 9) [96,5,40,144,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7941

def r9244 : Route 9 := (fun mask => (mask,id))

def c9244 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9244 : Upper (D 9) (R 9) [96,5,40,144] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9244 c9244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9244_3
  · exact u8068
  · exact u8069
  · exact u8070
  · exact u8071
  · exact u8072
  · exact u8073
  · exact u8074
  · exact u8075
  · exact u8076

theorem m9245_3 : Upper (D 9) (R 9) [96,5,40,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7942

def r9245 : Route 9 := (fun mask => (mask,id))

def c9245 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9245 : Upper (D 9) (R 9) [96,5,40,192] 13 := by
  apply FastRouting.sound _ _ [96,5,40,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r9245 c9245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9245_3
  · exact u8077
  · exact u8078
  · exact u8079
  · exact u8080
  · exact u8081

theorem m9246_3 : Upper (D 9) (R 9) [96,5,40,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7943

def r9246 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9246 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9246 : Upper (D 9) (R 9) [96,5,40,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,384] 13 (by decide) (choices 2) [3,65,66,129,130,192,384] r9246 c9246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9246_3
  · exact u8082
  · exact u8083
  · exact u8084
  · exact u8085
  · exact u8086
  · exact u8087

theorem m9247_9 : Upper (D 9) (R 9) [96,5,48,66,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8041

theorem m9247_129 : Upper (D 9) (R 9) [96,5,48,66,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8056

theorem m9247_136 : Upper (D 9) (R 9) [96,5,48,66,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8069

theorem m9247_384 : Upper (D 9) (R 9) [96,5,48,66,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8083

def r9247 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9247 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9247 : Upper (D 9) (R 9) [96,5,48,66] 13 := by
  apply FastRouting.sound _ _ [96,5,48,66] 13 (by decide) (choices 2) [9,129,136,384] r9247 c9247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9247_9
  · exact m9247_129
  · exact m9247_136
  · exact m9247_384

theorem m9248_10 : Upper (D 9) (R 9) [96,5,48,129,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8046

theorem m9248_66 : Upper (D 9) (R 9) [96,5,48,129,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8051

theorem m9248_72 : Upper (D 9) (R 9) [96,5,48,129,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8053

theorem m9248_130 : Upper (D 9) (R 9) [96,5,48,129,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8063

theorem m9248_136 : Upper (D 9) (R 9) [96,5,48,129,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8070

theorem m9248_192 : Upper (D 9) (R 9) [96,5,48,129,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8077

theorem m9248_258 : Upper (D 9) (R 9) [96,5,48,129,258] 13 :=
  permutation_upper _ _ _ [96,5,40,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8065

theorem m9248_264 : Upper (D 9) (R 9) [96,5,48,129,264] 13 :=
  permutation_upper _ _ _ [96,5,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8073

theorem m9248_320 : Upper (D 9) (R 9) [96,5,48,129,320] 13 :=
  permutation_upper _ _ _ [96,5,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8079

theorem m9248_384 : Upper (D 9) (R 9) [96,5,48,129,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8084

def r9248 : Route 9 := (fun mask => (mask,id))

def c9248 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9248 : Upper (D 9) (R 9) [96,5,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,48,129] 13 (by decide) (choices 2) [10,66,72,130,136,192,258,264,320,384] r9248 c9248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9248_10
  · exact m9248_66
  · exact m9248_72
  · exact m9248_130
  · exact m9248_136
  · exact m9248_192
  · exact m9248_258
  · exact m9248_264
  · exact m9248_320
  · exact m9248_384

theorem m9249_9 : Upper (D 9) (R 9) [96,5,48,130,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8042

theorem m9249_65 : Upper (D 9) (R 9) [96,5,48,130,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8049

theorem m9249_72 : Upper (D 9) (R 9) [96,5,48,130,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8054

theorem m9249_129 : Upper (D 9) (R 9) [96,5,48,130,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8057

theorem m9249_136 : Upper (D 9) (R 9) [96,5,48,130,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8071

theorem m9249_192 : Upper (D 9) (R 9) [96,5,48,130,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8078

theorem m9249_257 : Upper (D 9) (R 9) [96,5,48,130,257] 13 :=
  permutation_upper _ _ _ [96,5,40,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8059

theorem m9249_264 : Upper (D 9) (R 9) [96,5,48,130,264] 13 :=
  permutation_upper _ _ _ [96,5,40,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8074

theorem m9249_320 : Upper (D 9) (R 9) [96,5,48,130,320] 13 :=
  permutation_upper _ _ _ [96,5,40,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8080

theorem m9249_384 : Upper (D 9) (R 9) [96,5,48,130,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8085

def r9249 : Route 9 := (fun mask => (mask,id))

def c9249 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9249 : Upper (D 9) (R 9) [96,5,48,130] 13 := by
  apply FastRouting.sound _ _ [96,5,48,130] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9249 c9249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9249_9
  · exact m9249_65
  · exact m9249_72
  · exact m9249_129
  · exact m9249_136
  · exact m9249_192
  · exact m9249_257
  · exact m9249_264
  · exact m9249_320
  · exact m9249_384

theorem m9250_3 : Upper (D 9) (R 9) [96,5,48,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7938

theorem m9250_9 : Upper (D 9) (R 9) [96,5,48,192,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8043

theorem m9250_10 : Upper (D 9) (R 9) [96,5,48,192,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8047

theorem m9250_129 : Upper (D 9) (R 9) [96,5,48,192,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8058

theorem m9250_130 : Upper (D 9) (R 9) [96,5,48,192,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8064

theorem m9250_136 : Upper (D 9) (R 9) [96,5,48,192,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8072

theorem m9250_257 : Upper (D 9) (R 9) [96,5,48,192,257] 13 :=
  permutation_upper _ _ _ [96,5,40,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8060

theorem m9250_258 : Upper (D 9) (R 9) [96,5,48,192,258] 13 :=
  permutation_upper _ _ _ [96,5,40,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8066

theorem m9250_264 : Upper (D 9) (R 9) [96,5,48,192,264] 13 :=
  permutation_upper _ _ _ [96,5,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8075

theorem m9250_384 : Upper (D 9) (R 9) [96,5,48,192,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8086

def r9250 : Route 9 := (fun mask => (mask,id))

def c9250 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9250 : Upper (D 9) (R 9) [96,5,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,48,192] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r9250 c9250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9250_3
  · exact m9250_9
  · exact m9250_10
  · exact m9250_129
  · exact m9250_130
  · exact m9250_136
  · exact m9250_257
  · exact m9250_258
  · exact m9250_264
  · exact m9250_384

theorem m9251_3 : Upper (D 9) (R 9) [96,5,48,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,34,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7939

theorem m9251_9 : Upper (D 9) (R 9) [96,5,48,384,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8044

theorem m9251_10 : Upper (D 9) (R 9) [96,5,48,384,10] 13 :=
  permutation_upper _ _ _ [96,5,40,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8048

theorem m9251_65 : Upper (D 9) (R 9) [96,5,48,384,65] 13 :=
  permutation_upper _ _ _ [96,5,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8050

theorem m9251_66 : Upper (D 9) (R 9) [96,5,48,384,66] 13 :=
  permutation_upper _ _ _ [96,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8052

theorem m9251_72 : Upper (D 9) (R 9) [96,5,48,384,72] 13 :=
  permutation_upper _ _ _ [96,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8055

theorem m9251_129 : Upper (D 9) (R 9) [96,5,48,384,129] 13 :=
  permutation_upper _ _ _ [96,5,40,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8061

theorem m9251_130 : Upper (D 9) (R 9) [96,5,48,384,130] 13 :=
  permutation_upper _ _ _ [96,5,40,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8067

theorem m9251_136 : Upper (D 9) (R 9) [96,5,48,384,136] 13 :=
  permutation_upper _ _ _ [96,5,40,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8076

theorem m9251_192 : Upper (D 9) (R 9) [96,5,48,384,192] 13 :=
  permutation_upper _ _ _ [96,5,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8081

theorem m9251_384 : Upper (D 9) (R 9) [96,5,48,384,384] 13 :=
  permutation_upper _ _ _ [96,5,40,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8087

def r9251 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9251 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9251 : Upper (D 9) (R 9) [96,5,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,48,384] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,384] r9251 c9251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9251_3
  · exact m9251_9
  · exact m9251_10
  · exact m9251_65
  · exact m9251_66
  · exact m9251_72
  · exact m9251_129
  · exact m9251_130
  · exact m9251_136
  · exact m9251_192
  · exact m9251_384

def b9252 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 26 409 425 457 393 393), lower := (rows 97 7 100 26 16 32 64 128 256), losses := [] }

theorem u9252 : Upper (D 9) (R 9) [96,5,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9252 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9253 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 137 410 442 474 410 410), lower := (rows 97 7 100 137 16 32 64 128 256), losses := [] }

theorem u9253 : Upper (D 9) (R 9) [96,5,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9254 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 138 409 441 473 409 409), lower := (rows 97 7 100 138 16 32 64 128 256), losses := [] }

theorem u9254 : Upper (D 9) (R 9) [96,5,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9255 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,5)], upper := (rows 97 7 100 392 411 443 475 411 411), lower := (rows 97 7 100 392 16 32 64 128 256), losses := [] }

theorem u9255 : Upper (D 9) (R 9) [96,5,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9256 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 26 504 488 488 488 488), lower := (rows 97 7 133 26 16 32 64 128 256), losses := [] }

theorem u9256 : Upper (D 9) (R 9) [96,5,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9257 : PairBound 9 := { available := 472, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 42 472 504 472 472 472), lower := (rows 97 7 133 42 16 32 64 128 256), losses := [] }

theorem u9257 : Upper (D 9) (R 9) [96,5,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9258 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 7 133 138 376 376 376 504 376), lower := (rows 97 7 133 138 16 32 64 128 256), losses := [] }

theorem u9258 : Upper (D 9) (R 9) [96,5,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9259 : PairBound 9 := { available := 346, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 168 346 378 346 474 346), lower := (rows 97 7 133 168 16 32 64 128 256), losses := [] }

theorem u9259 : Upper (D 9) (R 9) [96,5,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9259 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9260 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 266 504 504 504 504 504), lower := (rows 97 7 133 266 16 32 64 128 256), losses := [] }

theorem u9260 : Upper (D 9) (R 9) [96,5,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9260 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9261 : PairBound 9 := { available := 474, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 296 474 506 474 474 474), lower := (rows 97 7 133 296 16 32 64 128 256), losses := [] }

theorem u9261 : Upper (D 9) (R 9) [96,5,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9262 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 133 392 378 378 378 506 378), lower := (rows 97 7 133 392 16 32 64 128 256), losses := [] }

theorem u9262 : Upper (D 9) (R 9) [96,5,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9263_40 : Upper (D 9) (R 9) [96,5,130,17,40] 13 :=
  permutation_upper _ _ _ [96,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8028

theorem m9263_96 : Upper (D 9) (R 9) [96,5,130,17,96] 13 :=
  permutation_upper _ _ _ [96,5,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8089

def r9263 : Route 9 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9263 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9263 : Upper (D 9) (R 9) [96,5,130,17] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17] 13 (by decide) (choices 2) [40,96,136,160,264,288,384] r9263 c9263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9263_40
  · exact m9263_96
  · exact u8132
  · exact u8133
  · exact u8134
  · exact u8135
  · exact u8136

def b9264 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 134 41 472 504 472 472 472), lower := (rows 97 7 134 41 16 32 64 128 256), losses := [] }

theorem u9264 : Upper (D 9) (R 9) [96,5,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9265_9 : Upper (D 9) (R 9) [96,5,130,48,9] 13 :=
  permutation_upper _ _ _ [96,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8028

theorem m9265_65 : Upper (D 9) (R 9) [96,5,130,48,65] 13 :=
  permutation_upper _ _ _ [96,5,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8137

def r9265 : Route 9 := (fun mask => (mask,id))

def c9265 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9265 : Upper (D 9) (R 9) [96,5,130,48] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9265 c9265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9265_9
  · exact m9265_65
  · exact u8143
  · exact u8144
  · exact u8145
  · exact u8146
  · exact u8147
  · exact u8148
  · exact u8149
  · exact u8150

def b9266 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 134 104 409 441 473 409 409), lower := (rows 97 7 134 104 16 32 64 128 256), losses := [] }

theorem u9266 : Upper (D 9) (R 9) [96,5,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9267 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 134 137 376 376 376 504 376), lower := (rows 97 7 134 137 16 32 64 128 256), losses := [] }

theorem u9267 : Upper (D 9) (R 9) [96,5,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9267 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9268_9 : Upper (D 9) (R 9) [96,5,130,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8132

theorem m9268_33 : Upper (D 9) (R 9) [96,5,130,144,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8138

theorem m9268_40 : Upper (D 9) (R 9) [96,5,130,144,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8145

theorem m9268_96 : Upper (D 9) (R 9) [96,5,130,144,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8151

def r9268 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9268 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9268 : Upper (D 9) (R 9) [96,5,130,144] 13 := by
  apply FastRouting.sound _ _ [96,5,130,144] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9268 c9268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9268_9
  · exact m9268_33
  · exact m9268_40
  · exact m9268_96
  · exact u8157
  · exact u8158
  · exact u8159

theorem m9269_9 : Upper (D 9) (R 9) [96,5,130,160,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8133

theorem m9269_65 : Upper (D 9) (R 9) [96,5,130,160,65] 13 :=
  permutation_upper _ _ _ [96,5,130,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8139

theorem m9269_72 : Upper (D 9) (R 9) [96,5,130,160,72] 13 :=
  permutation_upper _ _ _ [96,5,130,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8146

def r9269 : Route 9 := (fun mask => (mask,id))

def c9269 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9269 : Upper (D 9) (R 9) [96,5,130,160] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9269 c9269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9269_9
  · exact m9269_65
  · exact m9269_72
  · exact u8160
  · exact u8161
  · exact u8162

theorem m9270_40 : Upper (D 9) (R 9) [96,5,130,257,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8147

theorem m9270_96 : Upper (D 9) (R 9) [96,5,130,257,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8152

theorem m9270_136 : Upper (D 9) (R 9) [96,5,130,257,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8157

theorem m9270_160 : Upper (D 9) (R 9) [96,5,130,257,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8160

def r9270 : Route 9 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9270 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9270 : Upper (D 9) (R 9) [96,5,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257] 13 (by decide) (choices 2) [40,96,136,160,264,288,384] r9270 c9270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9270_40
  · exact m9270_96
  · exact m9270_136
  · exact m9270_160
  · exact u8163
  · exact u8164
  · exact u8165

theorem m9271_9 : Upper (D 9) (R 9) [96,5,130,272,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8134

theorem m9271_33 : Upper (D 9) (R 9) [96,5,130,272,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8140

theorem m9271_40 : Upper (D 9) (R 9) [96,5,130,272,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8148

theorem m9271_96 : Upper (D 9) (R 9) [96,5,130,272,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8153

theorem m9271_129 : Upper (D 9) (R 9) [96,5,130,272,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8155

theorem m9271_136 : Upper (D 9) (R 9) [96,5,130,272,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8158

theorem m9271_160 : Upper (D 9) (R 9) [96,5,130,272,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8161

theorem m9271_257 : Upper (D 9) (R 9) [96,5,130,272,257] 13 :=
  permutation_upper _ _ _ [96,5,130,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8163

def r9271 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9271 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9271 : Upper (D 9) (R 9) [96,5,130,272] 13 := by
  apply FastRouting.sound _ _ [96,5,130,272] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r9271 c9271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9271_9
  · exact m9271_33
  · exact m9271_40
  · exact m9271_96
  · exact m9271_129
  · exact m9271_136
  · exact m9271_160
  · exact m9271_257
  · exact u8166
  · exact u8167
  · exact u8168

theorem m9272_9 : Upper (D 9) (R 9) [96,5,130,288,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8135

theorem m9272_65 : Upper (D 9) (R 9) [96,5,130,288,65] 13 :=
  permutation_upper _ _ _ [96,5,130,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8141

theorem m9272_72 : Upper (D 9) (R 9) [96,5,130,288,72] 13 :=
  permutation_upper _ _ _ [96,5,130,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8149

theorem m9272_129 : Upper (D 9) (R 9) [96,5,130,288,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8156

theorem m9272_136 : Upper (D 9) (R 9) [96,5,130,288,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8159

theorem m9272_192 : Upper (D 9) (R 9) [96,5,130,288,192] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8162

theorem m9272_257 : Upper (D 9) (R 9) [96,5,130,288,257] 13 :=
  permutation_upper _ _ _ [96,5,130,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8164

theorem m9272_264 : Upper (D 9) (R 9) [96,5,130,288,264] 13 :=
  permutation_upper _ _ _ [96,5,130,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8167

def r9272 : Route 9 := (fun mask => (mask,id))

def c9272 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9272 : Upper (D 9) (R 9) [96,5,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9272 c9272
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9272_9
  · exact m9272_65
  · exact m9272_72
  · exact m9272_129
  · exact m9272_136
  · exact m9272_192
  · exact m9272_257
  · exact m9272_264
  · exact u8169
  · exact u8170

theorem m9273_9 : Upper (D 9) (R 9) [96,5,130,384,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8136

theorem m9273_33 : Upper (D 9) (R 9) [96,5,130,384,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8142

theorem m9273_40 : Upper (D 9) (R 9) [96,5,130,384,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8150

theorem m9273_96 : Upper (D 9) (R 9) [96,5,130,384,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8154

theorem m9273_257 : Upper (D 9) (R 9) [96,5,130,384,257] 13 :=
  permutation_upper _ _ _ [96,5,130,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8165

theorem m9273_264 : Upper (D 9) (R 9) [96,5,130,384,264] 13 :=
  permutation_upper _ _ _ [96,5,130,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8168

theorem m9273_288 : Upper (D 9) (R 9) [96,5,130,384,288] 13 :=
  permutation_upper _ _ _ [96,5,130,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8170

def r9273 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9273 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9273 : Upper (D 9) (R 9) [96,5,130,384] 13 := by
  apply FastRouting.sound _ _ [96,5,130,384] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9273 c9273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9273_9
  · exact m9273_33
  · exact m9273_40
  · exact m9273_96
  · exact m9273_257
  · exact m9273_264
  · exact m9273_288

theorem m9274_34 : Upper (D 9) (R 9) [96,5,136,17,34] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8042

theorem m9274_96 : Upper (D 9) (R 9) [96,5,136,17,96] 13 :=
  permutation_upper _ _ _ [96,5,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8088

def r9274 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9274 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9274 : Upper (D 9) (R 9) [96,5,136,17] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r9274 c9274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9274_34
  · exact m9274_96
  · exact u8171
  · exact u8172
  · exact u8173
  · exact u8174
  · exact u8175

def r9275 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9275 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9275 : Upper (D 9) (R 9) [96,5,136,18] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r9275 c9275
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8176
  · exact u8177
  · exact u8178
  · exact u8179
  · exact u8180
  · exact u8181
  · exact u8182

def b9276 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 140 41 466 498 466 466 466), lower := (rows 97 7 140 41 16 32 64 128 256), losses := [] }

theorem u9276 : Upper (D 9) (R 9) [96,5,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9276 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9277 : Route 9 := (fun mask => (mask,id))

def c9277 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9277 : Upper (D 9) (R 9) [96,5,136,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9277 c9277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8189
  · exact u8190
  · exact u8191
  · exact u8192
  · exact u8193
  · exact u8194

theorem m9278_3 : Upper (D 9) (R 9) [96,5,136,48,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7947

def r9278 : Route 9 := (fun mask => (mask,id))

def c9278 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9278 : Upper (D 9) (R 9) [96,5,136,48] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9278 c9278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9278_3
  · exact u8195
  · exact u8196
  · exact u8197
  · exact u8198
  · exact u8199
  · exact u8200
  · exact u8201
  · exact u8202
  · exact u8203

def b9279 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 140 104 403 435 467 403 403), lower := (rows 97 7 140 104 16 32 64 128 256), losses := [] }

theorem u9279 : Upper (D 9) (R 9) [96,5,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9279 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9280 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 6, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 7 140 137 370 370 370 498 370), lower := (rows 97 7 140 137 16 32 64 128 256), losses := [] }

theorem u9280 : Upper (D 9) (R 9) [96,5,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9280 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9281 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 138 369 369 369 497 369), lower := (rows 97 7 140 138 16 32 64 128 256), losses := [] }

theorem u9281 : Upper (D 9) (R 9) [96,5,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9281 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9282 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 152 371 355 355 483 355), lower := (rows 97 7 140 152 16 32 64 128 256), losses := [] }

theorem u9282 : Upper (D 9) (R 9) [96,5,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9282 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9283 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 168 339 371 339 467 339), lower := (rows 97 7 140 168 16 32 64 128 256), losses := [] }

theorem u9283 : Upper (D 9) (R 9) [96,5,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9283 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9284 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9284 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9284 : Upper (D 9) (R 9) [96,5,136,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r9284 c9284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8222
  · exact u8223
  · exact u8224
  · exact u8225
  · exact u8226
  · exact u8227
  · exact u8228

def r9285 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9285 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9285 : Upper (D 9) (R 9) [96,5,136,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r9285 c9285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8229
  · exact u8230
  · exact u8231
  · exact u8232
  · exact u8233
  · exact u8234
  · exact u8235

theorem m9286_3 : Upper (D 9) (R 9) [96,5,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7948

def r9286 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9286 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9286 : Upper (D 9) (R 9) [96,5,136,272] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9286 c9286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9286_3
  · exact u8236
  · exact u8237
  · exact u8238
  · exact u8239
  · exact u8240
  · exact u8241
  · exact u8242
  · exact u8243
  · exact u8244
  · exact u8245

theorem m9287_3 : Upper (D 9) (R 9) [96,5,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7949

def r9287 : Route 9 := (fun mask => (mask,id))

def c9287 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9287 : Upper (D 9) (R 9) [96,5,136,288] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9287 c9287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9287_3
  · exact u8246
  · exact u8247
  · exact u8248
  · exact u8249
  · exact u8250
  · exact u8251
  · exact u8252
  · exact u8253
  · exact u8254

def b9288 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 7 140 392 371 371 371 499 371), lower := (rows 97 7 140 392 16 32 64 128 256), losses := [] }

theorem u9288 : Upper (D 9) (R 9) [96,5,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9288 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9289_9 : Upper (D 9) (R 9) [96,5,144,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8042

theorem m9289_65 : Upper (D 9) (R 9) [96,5,144,34,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8183

theorem m9289_72 : Upper (D 9) (R 9) [96,5,144,34,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8196

theorem m9289_129 : Upper (D 9) (R 9) [96,5,144,34,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8209

theorem m9289_136 : Upper (D 9) (R 9) [96,5,144,34,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8214

theorem m9289_192 : Upper (D 9) (R 9) [96,5,144,34,192] 13 :=
  permutation_upper _ _ _ [96,5,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8218

theorem m9289_257 : Upper (D 9) (R 9) [96,5,144,34,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8222

theorem m9289_264 : Upper (D 9) (R 9) [96,5,144,34,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8237

theorem m9289_320 : Upper (D 9) (R 9) [96,5,144,34,320] 13 :=
  permutation_upper _ _ _ [96,5,136,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8247

theorem m9289_384 : Upper (D 9) (R 9) [96,5,144,34,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8255

def r9289 : Route 9 := (fun mask => (mask,id))

def c9289 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9289 : Upper (D 9) (R 9) [96,5,144,34] 13 := by
  apply FastRouting.sound _ _ [96,5,144,34] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9289 c9289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9289_9
  · exact m9289_65
  · exact m9289_72
  · exact m9289_129
  · exact m9289_136
  · exact m9289_192
  · exact m9289_257
  · exact m9289_264
  · exact m9289_320
  · exact m9289_384

theorem m9290_10 : Upper (D 9) (R 9) [96,5,144,129,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8178

theorem m9290_34 : Upper (D 9) (R 9) [96,5,144,129,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8190

theorem m9290_40 : Upper (D 9) (R 9) [96,5,144,129,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8197

theorem m9290_96 : Upper (D 9) (R 9) [96,5,144,129,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8204

theorem m9290_258 : Upper (D 9) (R 9) [96,5,144,129,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8231

theorem m9290_264 : Upper (D 9) (R 9) [96,5,144,129,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8239

theorem m9290_288 : Upper (D 9) (R 9) [96,5,144,129,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8248

def r9290 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9290 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9290 : Upper (D 9) (R 9) [96,5,144,129] 13 := by
  apply FastRouting.sound _ _ [96,5,144,129] 13 (by decide) (choices 2) [10,34,40,96,258,264,288] r9290 c9290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9290_10
  · exact m9290_34
  · exact m9290_40
  · exact m9290_96
  · exact m9290_258
  · exact m9290_264
  · exact m9290_288

theorem m9291_9 : Upper (D 9) (R 9) [96,5,144,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8171

theorem m9291_33 : Upper (D 9) (R 9) [96,5,144,130,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8184

theorem m9291_40 : Upper (D 9) (R 9) [96,5,144,130,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8198

theorem m9291_96 : Upper (D 9) (R 9) [96,5,144,130,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8205

theorem m9291_257 : Upper (D 9) (R 9) [96,5,144,130,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8224

theorem m9291_264 : Upper (D 9) (R 9) [96,5,144,130,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8240

theorem m9291_288 : Upper (D 9) (R 9) [96,5,144,130,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8249

def r9291 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9291 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9291 : Upper (D 9) (R 9) [96,5,144,130] 13 := by
  apply FastRouting.sound _ _ [96,5,144,130] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9291 c9291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9291_9
  · exact m9291_33
  · exact m9291_40
  · exact m9291_96
  · exact m9291_257
  · exact m9291_264
  · exact m9291_288

theorem m9292_3 : Upper (D 9) (R 9) [96,5,144,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7944

theorem m9292_9 : Upper (D 9) (R 9) [96,5,144,160,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8172

theorem m9292_10 : Upper (D 9) (R 9) [96,5,144,160,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8179

theorem m9292_65 : Upper (D 9) (R 9) [96,5,144,160,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8185

theorem m9292_66 : Upper (D 9) (R 9) [96,5,144,160,66] 13 :=
  permutation_upper _ _ _ [96,5,136,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8191

theorem m9292_72 : Upper (D 9) (R 9) [96,5,144,160,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8199

theorem m9292_257 : Upper (D 9) (R 9) [96,5,144,160,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8225

theorem m9292_258 : Upper (D 9) (R 9) [96,5,144,160,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8232

theorem m9292_264 : Upper (D 9) (R 9) [96,5,144,160,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8241

theorem m9292_320 : Upper (D 9) (R 9) [96,5,144,160,320] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8250

def r9292 : Route 9 := (fun mask => (mask,id))

def c9292 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9292 : Upper (D 9) (R 9) [96,5,144,160] 13 := by
  apply FastRouting.sound _ _ [96,5,144,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r9292 c9292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9292_3
  · exact m9292_9
  · exact m9292_10
  · exact m9292_65
  · exact m9292_66
  · exact m9292_72
  · exact m9292_257
  · exact m9292_258
  · exact m9292_264
  · exact m9292_320

theorem m9293_10 : Upper (D 9) (R 9) [96,5,144,257,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8180

theorem m9293_34 : Upper (D 9) (R 9) [96,5,144,257,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8192

theorem m9293_40 : Upper (D 9) (R 9) [96,5,144,257,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8200

theorem m9293_96 : Upper (D 9) (R 9) [96,5,144,257,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8206

theorem m9293_130 : Upper (D 9) (R 9) [96,5,144,257,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8212

theorem m9293_136 : Upper (D 9) (R 9) [96,5,144,257,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8215

theorem m9293_160 : Upper (D 9) (R 9) [96,5,144,257,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8219

theorem m9293_258 : Upper (D 9) (R 9) [96,5,144,257,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8233

theorem m9293_264 : Upper (D 9) (R 9) [96,5,144,257,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8242

theorem m9293_288 : Upper (D 9) (R 9) [96,5,144,257,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8251

theorem m9293_384 : Upper (D 9) (R 9) [96,5,144,257,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8256

def r9293 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9293 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9293 : Upper (D 9) (R 9) [96,5,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,144,257] 13 (by decide) (choices 2) [10,34,40,96,130,136,160,258,264,288,384] r9293 c9293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9293_10
  · exact m9293_34
  · exact m9293_40
  · exact m9293_96
  · exact m9293_130
  · exact m9293_136
  · exact m9293_160
  · exact m9293_258
  · exact m9293_264
  · exact m9293_288
  · exact m9293_384

theorem m9294_9 : Upper (D 9) (R 9) [96,5,144,258,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8173

theorem m9294_33 : Upper (D 9) (R 9) [96,5,144,258,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8186

theorem m9294_40 : Upper (D 9) (R 9) [96,5,144,258,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8201

theorem m9294_96 : Upper (D 9) (R 9) [96,5,144,258,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8207

theorem m9294_129 : Upper (D 9) (R 9) [96,5,144,258,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8210

theorem m9294_136 : Upper (D 9) (R 9) [96,5,144,258,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8216

theorem m9294_160 : Upper (D 9) (R 9) [96,5,144,258,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8220

theorem m9294_257 : Upper (D 9) (R 9) [96,5,144,258,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8226

theorem m9294_264 : Upper (D 9) (R 9) [96,5,144,258,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8243

theorem m9294_288 : Upper (D 9) (R 9) [96,5,144,258,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8252

theorem m9294_384 : Upper (D 9) (R 9) [96,5,144,258,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8257

def r9294 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9294 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9294 : Upper (D 9) (R 9) [96,5,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,144,258] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r9294 c9294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9294_9
  · exact m9294_33
  · exact m9294_40
  · exact m9294_96
  · exact m9294_129
  · exact m9294_136
  · exact m9294_160
  · exact m9294_257
  · exact m9294_264
  · exact m9294_288
  · exact m9294_384

theorem m9295_3 : Upper (D 9) (R 9) [96,5,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7945

theorem m9295_9 : Upper (D 9) (R 9) [96,5,144,288,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8174

theorem m9295_10 : Upper (D 9) (R 9) [96,5,144,288,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8181

theorem m9295_65 : Upper (D 9) (R 9) [96,5,144,288,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8187

theorem m9295_66 : Upper (D 9) (R 9) [96,5,144,288,66] 13 :=
  permutation_upper _ _ _ [96,5,136,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8193

theorem m9295_72 : Upper (D 9) (R 9) [96,5,144,288,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8202

theorem m9295_129 : Upper (D 9) (R 9) [96,5,144,288,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8211

theorem m9295_130 : Upper (D 9) (R 9) [96,5,144,288,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8213

theorem m9295_136 : Upper (D 9) (R 9) [96,5,144,288,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8217

theorem m9295_192 : Upper (D 9) (R 9) [96,5,144,288,192] 13 :=
  permutation_upper _ _ _ [96,5,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8221

theorem m9295_257 : Upper (D 9) (R 9) [96,5,144,288,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8227

theorem m9295_258 : Upper (D 9) (R 9) [96,5,144,288,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8234

theorem m9295_264 : Upper (D 9) (R 9) [96,5,144,288,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8244

theorem m9295_320 : Upper (D 9) (R 9) [96,5,144,288,320] 13 :=
  permutation_upper _ _ _ [96,5,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8253

theorem m9295_384 : Upper (D 9) (R 9) [96,5,144,288,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8258

def r9295 : Route 9 := (fun mask => (mask,id))

def c9295 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9295 : Upper (D 9) (R 9) [96,5,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,144,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r9295 c9295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9295_3
  · exact m9295_9
  · exact m9295_10
  · exact m9295_65
  · exact m9295_66
  · exact m9295_72
  · exact m9295_129
  · exact m9295_130
  · exact m9295_136
  · exact m9295_192
  · exact m9295_257
  · exact m9295_258
  · exact m9295_264
  · exact m9295_320
  · exact m9295_384

theorem m9296_3 : Upper (D 9) (R 9) [96,5,144,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7946

theorem m9296_9 : Upper (D 9) (R 9) [96,5,144,384,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8175

theorem m9296_10 : Upper (D 9) (R 9) [96,5,144,384,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8182

theorem m9296_33 : Upper (D 9) (R 9) [96,5,144,384,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8188

theorem m9296_34 : Upper (D 9) (R 9) [96,5,144,384,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8194

theorem m9296_40 : Upper (D 9) (R 9) [96,5,144,384,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8203

theorem m9296_96 : Upper (D 9) (R 9) [96,5,144,384,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8208

theorem m9296_257 : Upper (D 9) (R 9) [96,5,144,384,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8228

theorem m9296_258 : Upper (D 9) (R 9) [96,5,144,384,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8235

theorem m9296_264 : Upper (D 9) (R 9) [96,5,144,384,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8245

theorem m9296_288 : Upper (D 9) (R 9) [96,5,144,384,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8254

def r9296 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9296 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9296 : Upper (D 9) (R 9) [96,5,144,384] 13 := by
  apply FastRouting.sound _ _ [96,5,144,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r9296 c9296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9296_3
  · exact m9296_9
  · exact m9296_10
  · exact m9296_33
  · exact m9296_34
  · exact m9296_40
  · exact m9296_96
  · exact m9296_257
  · exact m9296_258
  · exact m9296_264
  · exact m9296_288

theorem m9297_10 : Upper (D 9) (R 9) [96,5,160,17,10] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

theorem m9297_66 : Upper (D 9) (R 9) [96,5,160,17,66] 13 :=
  permutation_upper _ _ _ [96,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8043

theorem m9297_72 : Upper (D 9) (R 9) [96,5,160,17,72] 13 :=
  permutation_upper _ _ _ [96,5,34,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8029

theorem m9297_130 : Upper (D 9) (R 9) [96,5,160,17,130] 13 :=
  permutation_upper _ _ _ [96,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8172

theorem m9297_136 : Upper (D 9) (R 9) [96,5,160,17,136] 13 :=
  permutation_upper _ _ _ [96,5,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8133

theorem m9297_258 : Upper (D 9) (R 9) [96,5,160,17,258] 13 :=
  permutation_upper _ _ _ [96,5,136,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8174

theorem m9297_264 : Upper (D 9) (R 9) [96,5,160,17,264] 13 :=
  permutation_upper _ _ _ [96,5,130,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8135

def r9297 : Route 9 := (fun mask => (mask,id))

def c9297 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9297 : Upper (D 9) (R 9) [96,5,160,17] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17] 13 (by decide) (choices 2) [10,66,72,130,136,192,258,264,320,384] r9297 c9297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9297_10
  · exact m9297_66
  · exact m9297_72
  · exact m9297_130
  · exact m9297_136
  · exact u8259
  · exact m9297_258
  · exact m9297_264
  · exact u8260
  · exact u8261

theorem m9298_9 : Upper (D 9) (R 9) [96,5,160,18,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

def r9298 : Route 9 := (fun mask => (mask,id))

def c9298 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9298 : Upper (D 9) (R 9) [96,5,160,18] 13 := by
  apply FastRouting.sound _ _ [96,5,160,18] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9298 c9298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9298_9
  · exact u8262
  · exact u8263
  · exact u8264
  · exact u8265
  · exact u8266
  · exact u8267
  · exact u8268
  · exact u8269
  · exact u8270

def b9299 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 8, targets := 416 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(3,7),(3,8)], upper := (rows 97 7 164 73 410 442 474 410 410), lower := (rows 97 7 164 73 16 32 64 128 256), losses := [] }

theorem u9299 : Upper (D 9) (R 9) [96,5,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9299 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u9299
end Delivery.IrregularNine14.P09
