import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0582
import IrregularNine14P07C0583
import IrregularNine14P07C0584
import IrregularNine14P07C0585
import IrregularNine14P07C0586
import IrregularNine14P07C0587
import IrregularNine14P07C0588

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42240_3 : Upper (D 7) (R 7) [34,68,288,17,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34971

def r42240 : Route 9 := (fun mask => (mask,id))

def c42240 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42240 : Upper (D 7) (R 7) [34,68,288,17] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42240 c42240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42240_3
  · exact u34977
  · exact u34978
  · exact u34979
  · exact u34980
  · exact u34981
  · exact u34982
  · exact u34983
  · exact u34984
  · exact u34985

theorem m42241_9 : Upper (D 7) (R 7) [34,68,288,18,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34978

def r42241 : Route 9 := (fun mask => (mask,id))

def c42241 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42241 : Upper (D 7) (R 7) [34,68,288,18] 13 := by
  apply FastRouting.sound _ _ [34,68,288,18] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42241 c42241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42241_9
  · exact u34986
  · exact u34987
  · exact u34988
  · exact u34989
  · exact u34990

theorem m42242_3 : Upper (D 7) (R 7) [34,68,288,65,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34972

theorem m42242_9 : Upper (D 7) (R 7) [34,68,288,65,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34979

theorem m42242_10 : Upper (D 7) (R 7) [34,68,288,65,10] 13 :=
  permutation_upper _ _ _ [34,68,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34986

def r42242 : Route 9 := (fun mask => (mask,id))

def c42242 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42242 : Upper (D 7) (R 7) [34,68,288,65] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42242 c42242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42242_3
  · exact m42242_9
  · exact m42242_10
  · exact u34991
  · exact u34992
  · exact u34993

def b42243 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 292 74 153 185 217 153 409), lower := (rows 35 70 292 74 16 32 64 128 256), losses := [] }

theorem u42243 : Upper (D 7) (R 7) [34,68,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42244_3 : Upper (D 7) (R 7) [34,68,288,80,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34973

theorem m42244_9 : Upper (D 7) (R 7) [34,68,288,80,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34981

theorem m42244_10 : Upper (D 7) (R 7) [34,68,288,80,10] 13 :=
  permutation_upper _ _ _ [34,68,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34987

def r42244 : Route 9 := (fun mask => (mask,id))

def c42244 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42244 : Upper (D 7) (R 7) [34,68,288,80] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42244 c42244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42244_3
  · exact m42244_9
  · exact m42244_10
  · exact u34996
  · exact u34997
  · exact u34998

theorem m42245_3 : Upper (D 7) (R 7) [34,68,288,129,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34974

theorem m42245_9 : Upper (D 7) (R 7) [34,68,288,129,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34982

theorem m42245_10 : Upper (D 7) (R 7) [34,68,288,129,10] 13 :=
  permutation_upper _ _ _ [34,68,288,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34988

theorem m42245_65 : Upper (D 7) (R 7) [34,68,288,129,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34991

theorem m42245_66 : Upper (D 7) (R 7) [34,68,288,129,66] 13 :=
  permutation_upper _ _ _ [34,68,288,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34994

theorem m42245_72 : Upper (D 7) (R 7) [34,68,288,129,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34996

def r42245 : Route 9 := (fun mask => (mask,id))

def c42245 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42245 : Upper (D 7) (R 7) [34,68,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42245 c42245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42245_3
  · exact m42245_9
  · exact m42245_10
  · exact m42245_65
  · exact m42245_66
  · exact m42245_72
  · exact u34999
  · exact u35000
  · exact u35001
  · exact u35002

theorem m42246_9 : Upper (D 7) (R 7) [34,68,288,130,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34983

theorem m42246_65 : Upper (D 7) (R 7) [34,68,288,130,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34992

theorem m42246_72 : Upper (D 7) (R 7) [34,68,288,130,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34997

theorem m42246_129 : Upper (D 7) (R 7) [34,68,288,130,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35000

def r42246 : Route 9 := (fun mask => (mask,id))

def c42246 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42246 : Upper (D 7) (R 7) [34,68,288,130] 13 := by
  apply FastRouting.sound _ _ [34,68,288,130] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42246 c42246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42246_9
  · exact m42246_65
  · exact m42246_72
  · exact m42246_129
  · exact u35003
  · exact u35004

theorem m42247_3 : Upper (D 7) (R 7) [34,68,288,144,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34975

theorem m42247_9 : Upper (D 7) (R 7) [34,68,288,144,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34984

theorem m42247_10 : Upper (D 7) (R 7) [34,68,288,144,10] 13 :=
  permutation_upper _ _ _ [34,68,288,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34989

theorem m42247_65 : Upper (D 7) (R 7) [34,68,288,144,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34993

theorem m42247_66 : Upper (D 7) (R 7) [34,68,288,144,66] 13 :=
  permutation_upper _ _ _ [34,68,288,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34995

theorem m42247_72 : Upper (D 7) (R 7) [34,68,288,144,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34998

theorem m42247_129 : Upper (D 7) (R 7) [34,68,288,144,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35001

theorem m42247_130 : Upper (D 7) (R 7) [34,68,288,144,130] 13 :=
  permutation_upper _ _ _ [34,68,288,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35003

def r42247 : Route 9 := (fun mask => (mask,id))

def c42247 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42247 : Upper (D 7) (R 7) [34,68,288,144] 13 := by
  apply FastRouting.sound _ _ [34,68,288,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42247 c42247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42247_3
  · exact m42247_9
  · exact m42247_10
  · exact m42247_65
  · exact m42247_66
  · exact m42247_72
  · exact m42247_129
  · exact m42247_130
  · exact u35005
  · exact u35006

theorem m42248_3 : Upper (D 7) (R 7) [34,68,288,192,3] 13 :=
  permutation_upper _ _ _ [34,68,288,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34976

theorem m42248_9 : Upper (D 7) (R 7) [34,68,288,192,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34985

theorem m42248_10 : Upper (D 7) (R 7) [34,68,288,192,10] 13 :=
  permutation_upper _ _ _ [34,68,288,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34990

theorem m42248_129 : Upper (D 7) (R 7) [34,68,288,192,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35002

theorem m42248_130 : Upper (D 7) (R 7) [34,68,288,192,130] 13 :=
  permutation_upper _ _ _ [34,68,288,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35004

theorem m42248_136 : Upper (D 7) (R 7) [34,68,288,192,136] 13 :=
  permutation_upper _ _ _ [34,68,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35006

def r42248 : Route 9 := (fun mask => (mask,id))

def c42248 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42248 : Upper (D 7) (R 7) [34,68,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,192] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42248 c42248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42248_3
  · exact m42248_9
  · exact m42248_10
  · exact m42248_129
  · exact m42248_130
  · exact m42248_136

def b42249 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 388 11 249 249 249 249 505), lower := (rows 35 70 388 11 16 32 64 128 256), losses := [] }

theorem u42249 : Upper (D 7) (R 7) [34,68,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42250_3 : Upper (D 7) (R 7) [34,68,384,17,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35007

def r42250 : Route 9 := (fun mask => (mask,id))

def c42250 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42250 : Upper (D 7) (R 7) [34,68,384,17] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r42250 c42250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42250_3
  · exact u35016
  · exact u35017
  · exact u35018
  · exact u35019
  · exact u35020
  · exact u35021
  · exact u35022
  · exact u35023
  · exact u35024
  · exact u35025
  · exact u35026
  · exact u35027
  · exact u35028
  · exact u35029

theorem m42251_9 : Upper (D 7) (R 7) [34,68,384,18,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35017

def r42251 : Route 9 := (fun mask => (mask,id))

def c42251 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42251 : Upper (D 7) (R 7) [34,68,384,18] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42251 c42251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42251_9
  · exact u35030
  · exact u35031
  · exact u35032
  · exact u35033
  · exact u35034
  · exact u35035
  · exact u35036
  · exact u35037
  · exact u35038

def b42252 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 388 41 219 251 219 219 475), lower := (rows 35 70 388 41 16 32 64 128 256), losses := [] }

theorem u42252 : Upper (D 7) (R 7) [34,68,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42253 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 42 217 249 217 217 473), lower := (rows 35 70 388 42 16 32 64 128 256), losses := [] }

theorem u42253 : Upper (D 7) (R 7) [34,68,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42254_3 : Upper (D 7) (R 7) [34,68,384,48,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35008

theorem m42254_9 : Upper (D 7) (R 7) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35020

theorem m42254_10 : Upper (D 7) (R 7) [34,68,384,48,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35031

def r42254 : Route 9 := (fun mask => (mask,id))

def c42254 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42254 : Upper (D 7) (R 7) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42254 c42254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42254_3
  · exact m42254_9
  · exact m42254_10
  · exact u35050
  · exact u35051
  · exact u35052
  · exact u35053
  · exact u35054
  · exact u35055
  · exact u35056

theorem m42255_3 : Upper (D 7) (R 7) [34,68,384,65,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35009

theorem m42255_9 : Upper (D 7) (R 7) [34,68,384,65,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35021

theorem m42255_10 : Upper (D 7) (R 7) [34,68,384,65,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35032

theorem m42255_33 : Upper (D 7) (R 7) [34,68,384,65,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35039

theorem m42255_34 : Upper (D 7) (R 7) [34,68,384,65,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35045

theorem m42255_40 : Upper (D 7) (R 7) [34,68,384,65,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35050

def r42255 : Route 9 := (fun mask => (mask,id))

def c42255 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42255 : Upper (D 7) (R 7) [34,68,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42255 c42255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42255_3
  · exact m42255_9
  · exact m42255_10
  · exact m42255_33
  · exact m42255_34
  · exact m42255_40
  · exact u35057
  · exact u35058
  · exact u35059
  · exact u35060

def b42256 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 388 74 185 185 249 185 441), lower := (rows 35 70 388 74 16 32 64 128 256), losses := [] }

theorem u42256 : Upper (D 7) (R 7) [34,68,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42257_3 : Upper (D 7) (R 7) [34,68,384,80,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35010

theorem m42257_9 : Upper (D 7) (R 7) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35023

theorem m42257_10 : Upper (D 7) (R 7) [34,68,384,80,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35033

theorem m42257_33 : Upper (D 7) (R 7) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35040

theorem m42257_34 : Upper (D 7) (R 7) [34,68,384,80,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35046

theorem m42257_40 : Upper (D 7) (R 7) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35052

def r42257 : Route 9 := (fun mask => (mask,id))

def c42257 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42257 : Upper (D 7) (R 7) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42257 c42257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42257_3
  · exact m42257_9
  · exact m42257_10
  · exact m42257_33
  · exact m42257_34
  · exact m42257_40
  · exact u35064
  · exact u35065
  · exact u35066
  · exact u35067

theorem m42258_3 : Upper (D 7) (R 7) [34,68,384,96,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35011

theorem m42258_9 : Upper (D 7) (R 7) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35024

theorem m42258_10 : Upper (D 7) (R 7) [34,68,384,96,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35034

def r42258 : Route 9 := (fun mask => (mask,id))

def c42258 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42258 : Upper (D 7) (R 7) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42258 c42258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42258_3
  · exact m42258_9
  · exact m42258_10
  · exact u35068
  · exact u35069
  · exact u35070

theorem m42259_3 : Upper (D 7) (R 7) [34,68,384,129,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35012

theorem m42259_9 : Upper (D 7) (R 7) [34,68,384,129,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35025

theorem m42259_10 : Upper (D 7) (R 7) [34,68,384,129,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35035

theorem m42259_33 : Upper (D 7) (R 7) [34,68,384,129,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35041

theorem m42259_34 : Upper (D 7) (R 7) [34,68,384,129,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35047

theorem m42259_40 : Upper (D 7) (R 7) [34,68,384,129,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35053

theorem m42259_65 : Upper (D 7) (R 7) [34,68,384,129,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35057

theorem m42259_66 : Upper (D 7) (R 7) [34,68,384,129,66] 13 :=
  permutation_upper _ _ _ [34,68,384,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35061

theorem m42259_72 : Upper (D 7) (R 7) [34,68,384,129,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35064

theorem m42259_96 : Upper (D 7) (R 7) [34,68,384,129,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35068

def r42259 : Route 9 := (fun mask => (mask,id))

def c42259 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42259 : Upper (D 7) (R 7) [34,68,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42259 c42259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42259_3
  · exact m42259_9
  · exact m42259_10
  · exact m42259_33
  · exact m42259_34
  · exact m42259_40
  · exact m42259_65
  · exact m42259_66
  · exact m42259_72
  · exact m42259_96

theorem m42260_9 : Upper (D 7) (R 7) [34,68,384,130,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35026

theorem m42260_33 : Upper (D 7) (R 7) [34,68,384,130,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35042

theorem m42260_40 : Upper (D 7) (R 7) [34,68,384,130,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35054

theorem m42260_65 : Upper (D 7) (R 7) [34,68,384,130,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35058

theorem m42260_72 : Upper (D 7) (R 7) [34,68,384,130,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35065

theorem m42260_96 : Upper (D 7) (R 7) [34,68,384,130,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35069

def r42260 : Route 9 := (fun mask => (mask,id))

def c42260 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42260 : Upper (D 7) (R 7) [34,68,384,130] 13 := by
  apply FastRouting.sound _ _ [34,68,384,130] 13 (by decide) (choices 2) [9,33,40,65,72,96] r42260 c42260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42260_9
  · exact m42260_33
  · exact m42260_40
  · exact m42260_65
  · exact m42260_72
  · exact m42260_96

theorem m42261_3 : Upper (D 7) (R 7) [34,68,384,144,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35013

theorem m42261_9 : Upper (D 7) (R 7) [34,68,384,144,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35027

theorem m42261_10 : Upper (D 7) (R 7) [34,68,384,144,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35036

theorem m42261_33 : Upper (D 7) (R 7) [34,68,384,144,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35043

theorem m42261_34 : Upper (D 7) (R 7) [34,68,384,144,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35048

theorem m42261_40 : Upper (D 7) (R 7) [34,68,384,144,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35055

theorem m42261_65 : Upper (D 7) (R 7) [34,68,384,144,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35059

theorem m42261_66 : Upper (D 7) (R 7) [34,68,384,144,66] 13 :=
  permutation_upper _ _ _ [34,68,384,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35062

theorem m42261_72 : Upper (D 7) (R 7) [34,68,384,144,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35066

theorem m42261_96 : Upper (D 7) (R 7) [34,68,384,144,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35070

def r42261 : Route 9 := (fun mask => (mask,id))

def c42261 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42261 : Upper (D 7) (R 7) [34,68,384,144] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42261 c42261
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42261_3
  · exact m42261_9
  · exact m42261_10
  · exact m42261_33
  · exact m42261_34
  · exact m42261_40
  · exact m42261_65
  · exact m42261_66
  · exact m42261_72
  · exact m42261_96

theorem m42262_3 : Upper (D 7) (R 7) [34,68,384,160,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35014

theorem m42262_9 : Upper (D 7) (R 7) [34,68,384,160,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35028

theorem m42262_10 : Upper (D 7) (R 7) [34,68,384,160,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35037

theorem m42262_65 : Upper (D 7) (R 7) [34,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35060

theorem m42262_66 : Upper (D 7) (R 7) [34,68,384,160,66] 13 :=
  permutation_upper _ _ _ [34,68,384,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35063

theorem m42262_72 : Upper (D 7) (R 7) [34,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35067

def r42262 : Route 9 := (fun mask => (mask,id))

def c42262 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42262 : Upper (D 7) (R 7) [34,68,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r42262 c42262
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42262_3
  · exact m42262_9
  · exact m42262_10
  · exact m42262_65
  · exact m42262_66
  · exact m42262_72

theorem m42263_3 : Upper (D 7) (R 7) [34,68,384,192,3] 13 :=
  permutation_upper _ _ _ [34,68,384,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35015

theorem m42263_9 : Upper (D 7) (R 7) [34,68,384,192,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35029

theorem m42263_10 : Upper (D 7) (R 7) [34,68,384,192,10] 13 :=
  permutation_upper _ _ _ [34,68,384,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35038

theorem m42263_33 : Upper (D 7) (R 7) [34,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35044

theorem m42263_34 : Upper (D 7) (R 7) [34,68,384,192,34] 13 :=
  permutation_upper _ _ _ [34,68,384,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35049

theorem m42263_40 : Upper (D 7) (R 7) [34,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35056

def r42263 : Route 9 := (fun mask => (mask,id))

def c42263 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42263 : Upper (D 7) (R 7) [34,68,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r42263 c42263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42263_3
  · exact m42263_9
  · exact m42263_10
  · exact m42263_33
  · exact m42263_34
  · exact m42263_40

def b42264 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 7 13 504 504 504 504 504), lower := (rows 35 194 7 13 16 32 64 128 256), losses := [] }

theorem u42264 : Upper (D 7) (R 7) [34,192,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42265 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 28 505 489 489 489 489), lower := (rows 35 194 7 28 16 32 64 128 256), losses := [] }

theorem u42265 : Upper (D 7) (R 7) [34,192,3,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42266 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 7 44 473 505 473 473 473), lower := (rows 35 194 7 44 16 32 64 128 256), losses := [] }

theorem u42266 : Upper (D 7) (R 7) [34,192,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42267 : PairBound 9 := { available := 444, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 73 444 444 508 444 444), lower := (rows 35 194 7 73 16 32 64 128 256), losses := [] }

theorem u42267 : Upper (D 7) (R 7) [34,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42268 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 76 441 441 505 441 441), lower := (rows 35 194 7 76 16 32 64 128 256), losses := [] }

theorem u42268 : Upper (D 7) (R 7) [34,192,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42269 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 104 413 445 477 413 413), lower := (rows 35 194 7 104 16 32 64 128 256), losses := [] }

theorem u42269 : Upper (D 7) (R 7) [34,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42270 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 265 252 252 252 252 508), lower := (rows 35 194 7 265 16 32 64 128 256), losses := [] }

theorem u42270 : Upper (D 7) (R 7) [34,192,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42271 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 268 249 249 249 249 505), lower := (rows 35 194 7 268 16 32 64 128 256), losses := [] }

theorem u42271 : Upper (D 7) (R 7) [34,192,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42272 : PairBound 9 := { available := 221, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 296 221 253 221 221 477), lower := (rows 35 194 7 296 16 32 64 128 256), losses := [] }

theorem u42272 : Upper (D 7) (R 7) [34,192,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42273 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 504, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 194 7 328 189 189 253 189 445), lower := (rows 35 194 7 328 16 32 64 128 256), losses := [] }

theorem u42273 : Upper (D 7) (R 7) [34,192,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42274 : PairBound 9 := { available := 498, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 13 498 498 498 498 498), lower := (rows 35 194 13 13 16 32 64 128 256), losses := [] }

theorem u42274 : Upper (D 7) (R 7) [34,192,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42275 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 194 13 14 497 497 497 497 497), lower := (rows 35 194 13 14 16 32 64 128 256), losses := [] }

theorem u42275 : Upper (D 7) (R 7) [34,192,9,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42276 : PairBound 9 := { available := 486, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 25 502 486 486 486 486), lower := (rows 35 194 13 25 16 32 64 128 256), losses := [] }

theorem u42276 : Upper (D 7) (R 7) [34,192,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42277_5 : Upper (D 7) (R 7) [34,192,9,18,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35137

def r42277 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42277 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42277 : Upper (D 7) (R 7) [34,192,9,18] 13 := by
  apply FastRouting.sound _ _ [34,192,9,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r42277 c42277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42277_5
  · exact u35145
  · exact u35146
  · exact u35147
  · exact u35148
  · exact u35149
  · exact u35150
  · exact u35151
  · exact u35152
  · exact u35153
  · exact u35154

theorem m42278_3 : Upper (D 7) (R 7) [34,192,9,20,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35077

def r42278 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42278 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42278 : Upper (D 7) (R 7) [34,192,9,20] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r42278 c42278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42278_3
  · exact u35155
  · exact u35156
  · exact u35157
  · exact u35158
  · exact u35159
  · exact u35160
  · exact u35161
  · exact u35162
  · exact u35163
  · exact u35164

def b42279 : PairBound 9 := { available := 470, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 41 470 502 470 470 470), lower := (rows 35 194 13 41 16 32 64 128 256), losses := [] }

theorem u42279 : Upper (D 7) (R 7) [34,192,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42280 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 13 42 469 501 469 469 469), lower := (rows 35 194 13 42 16 32 64 128 256), losses := [] }

theorem u42280 : Upper (D 7) (R 7) [34,192,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42281 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 13 44 467 499 467 467 467), lower := (rows 35 194 13 44 16 32 64 128 256), losses := [] }

theorem u42281 : Upper (D 7) (R 7) [34,192,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42282_3 : Upper (D 7) (R 7) [34,192,9,48,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35078

theorem m42282_5 : Upper (D 7) (R 7) [34,192,9,48,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35138

def r42282 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42282 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42282 : Upper (D 7) (R 7) [34,192,9,48] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,192,257,258,260,320] r42282 c42282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42282_3
  · exact m42282_5
  · exact u35179
  · exact u35180
  · exact u35181
  · exact u35182
  · exact u35183
  · exact u35184
  · exact u35185
  · exact u35186
  · exact u35187

def b42283 : PairBound 9 := { available := 438, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 73 438 438 502 438 438), lower := (rows 35 194 13 73 16 32 64 128 256), losses := [] }

theorem u42283 : Upper (D 7) (R 7) [34,192,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42284 : PairBound 9 := { available := 437, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 194 13 74 437 437 501 437 437), lower := (rows 35 194 13 74 16 32 64 128 256), losses := [] }

theorem u42284 : Upper (D 7) (R 7) [34,192,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42285_3 : Upper (D 7) (R 7) [34,192,9,68,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35080

def r42285 : Route 9 := (fun mask => (mask,id))

def c42285 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42285 : Upper (D 7) (R 7) [34,192,9,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42285 c42285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42285_3
  · exact u35204
  · exact u35205
  · exact u35206
  · exact u35207
  · exact u35208
  · exact u35209
  · exact u35210
  · exact u35211
  · exact u35212

theorem m42286_3 : Upper (D 7) (R 7) [34,192,9,80,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35079

theorem m42286_5 : Upper (D 7) (R 7) [34,192,9,80,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35139

def r42286 : Route 9 := (fun mask => (mask,id))

def c42286 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42286 : Upper (D 7) (R 7) [34,192,9,80] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,257,258,260,288,384] r42286 c42286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42286_3
  · exact m42286_5
  · exact u35213
  · exact u35214
  · exact u35215
  · exact u35216
  · exact u35217
  · exact u35218
  · exact u35219
  · exact u35220
  · exact u35221
  · exact u35222
  · exact u35223
  · exact u35224
  · exact u35225

theorem m42287_3 : Upper (D 7) (R 7) [34,192,9,96,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35081

theorem m42287_5 : Upper (D 7) (R 7) [34,192,9,96,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35140

def r42287 : Route 9 := (fun mask => (mask,id))

def c42287 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42287 : Upper (D 7) (R 7) [34,192,9,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,257,258,260,384] r42287 c42287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42287_3
  · exact m42287_5
  · exact u35226
  · exact u35227
  · exact u35228
  · exact u35229
  · exact u35230
  · exact u35231
  · exact u35232
  · exact u35233

def b42288 : PairBound 9 := { available := 311, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 200 311 311 375 439 311), lower := (rows 35 194 13 200 16 32 64 128 256), losses := [] }

theorem u42288 : Upper (D 7) (R 7) [34,192,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42289 : PairBound 9 := { available := 246, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 194 13 265 246 246 246 246 502), lower := (rows 35 194 13 265 16 32 64 128 256), losses := [] }

theorem u42289 : Upper (D 7) (R 7) [34,192,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42290_5 : Upper (D 7) (R 7) [34,192,9,258,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35141

def r42290 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42290 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42290 : Upper (D 7) (R 7) [34,192,9,258] 13 := by
  apply FastRouting.sound _ _ [34,192,9,258] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r42290 c42290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42290_5
  · exact u35244
  · exact u35245
  · exact u35246
  · exact u35247
  · exact u35248
  · exact u35249

theorem m42291_3 : Upper (D 7) (R 7) [34,192,9,260,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35083

def r42291 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42291 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42291 : Upper (D 7) (R 7) [34,192,9,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r42291 c42291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42291_3
  · exact u35250
  · exact u35251
  · exact u35252
  · exact u35253
  · exact u35254
  · exact u35255

theorem m42292_3 : Upper (D 7) (R 7) [34,192,9,272,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35082

theorem m42292_5 : Upper (D 7) (R 7) [34,192,9,272,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35142

def r42292 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42292 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42292 : Upper (D 7) (R 7) [34,192,9,272] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r42292 c42292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42292_3
  · exact m42292_5
  · exact u35256
  · exact u35257
  · exact u35258
  · exact u35259
  · exact u35260
  · exact u35261
  · exact u35262
  · exact u35263
  · exact u35264

theorem m42293_3 : Upper (D 7) (R 7) [34,192,9,288,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35084

theorem m42293_5 : Upper (D 7) (R 7) [34,192,9,288,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35143

def r42293 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42293 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42293 : Upper (D 7) (R 7) [34,192,9,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288] 13 (by decide) (choices 2) [3,5,6,65,66,68,192] r42293 c42293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42293_3
  · exact m42293_5
  · exact u35265
  · exact u35266
  · exact u35267
  · exact u35268
  · exact u35269

theorem m42294_3 : Upper (D 7) (R 7) [34,192,9,320,3] 13 :=
  permutation_upper _ _ _ [34,192,3,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35085

theorem m42294_5 : Upper (D 7) (R 7) [34,192,9,320,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35144

def r42294 : Route 9 := (fun mask => (mask,id))

def c42294 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 257 => 8 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42294 : Upper (D 7) (R 7) [34,192,9,320] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r42294 c42294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42294_3
  · exact m42294_5
  · exact u35270
  · exact u35271
  · exact u35272
  · exact u35273
  · exact u35274
  · exact u35275
  · exact u35276
  · exact u35277

theorem m42295_5 : Upper (D 7) (R 7) [34,192,10,17,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35137

theorem m42295_33 : Upper (D 7) (R 7) [34,192,10,17,33] 13 :=
  permutation_upper _ _ _ [34,192,9,33,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35165

theorem m42295_36 : Upper (D 7) (R 7) [34,192,10,17,36] 13 :=
  permutation_upper _ _ _ [34,192,9,48,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35179

theorem m42295_65 : Upper (D 7) (R 7) [34,192,10,17,65] 13 :=
  permutation_upper _ _ _ [34,192,9,65,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35188

theorem m42295_68 : Upper (D 7) (R 7) [34,192,10,17,68] 13 :=
  permutation_upper _ _ _ [34,192,9,80,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35213

theorem m42295_96 : Upper (D 7) (R 7) [34,192,10,17,96] 13 :=
  permutation_upper _ _ _ [34,192,9,96,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35226

theorem m42295_192 : Upper (D 7) (R 7) [34,192,10,17,192] 13 :=
  permutation_upper _ _ _ [34,192,9,192,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35234

theorem m42295_257 : Upper (D 7) (R 7) [34,192,10,17,257] 13 :=
  permutation_upper _ _ _ [34,192,9,257,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35240

theorem m42295_260 : Upper (D 7) (R 7) [34,192,10,17,260] 13 :=
  permutation_upper _ _ _ [34,192,9,272,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35256

theorem m42295_288 : Upper (D 7) (R 7) [34,192,10,17,288] 13 :=
  permutation_upper _ _ _ [34,192,9,288,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35265

theorem m42295_320 : Upper (D 7) (R 7) [34,192,10,17,320] 13 :=
  permutation_upper _ _ _ [34,192,9,320,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35270

def r42295 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42295 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42295 : Upper (D 7) (R 7) [34,192,10,17] 13 := by
  apply FastRouting.sound _ _ [34,192,10,17] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r42295 c42295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42295_5
  · exact m42295_33
  · exact m42295_36
  · exact m42295_65
  · exact m42295_68
  · exact m42295_96
  · exact m42295_192
  · exact m42295_257
  · exact m42295_260
  · exact m42295_288
  · exact m42295_320

def r42296 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42296 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42296 : Upper (D 7) (R 7) [34,192,10,20] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r42296 c42296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35278
  · exact u35279
  · exact u35280
  · exact u35281
  · exact u35282
  · exact u35283
  · exact u35284

def b42297 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 41 469 501 469 469 469), lower := (rows 35 194 14 41 16 32 64 128 256), losses := [] }

theorem u42297 : Upper (D 7) (R 7) [34,192,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42298 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 194 14 44 465 497 465 465 465), lower := (rows 35 194 14 44 16 32 64 128 256), losses := [] }

theorem u42298 : Upper (D 7) (R 7) [34,192,10,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42299_5 : Upper (D 7) (R 7) [34,192,10,48,5] 13 :=
  permutation_upper _ _ _ [34,192,9,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35146

def r42299 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c42299 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42299 : Upper (D 7) (R 7) [34,192,10,48] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48] 13 (by decide) (choices 2) [5,65,68,192,257,260,320] r42299 c42299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42299_5
  · exact u35293
  · exact u35294
  · exact u35295
  · exact u35296
  · exact u35297
  · exact u35298

#print axioms u42299
end Delivery.IrregularNine14.P07
