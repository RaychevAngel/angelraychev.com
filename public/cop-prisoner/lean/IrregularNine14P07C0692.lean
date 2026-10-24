import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0534
import IrregularNine14P07C0535
import IrregularNine14P07C0536
import IrregularNine14P07C0537

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41520 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 290 13 73 242 242 242 242 498), lower := (rows 7 290 13 73 16 32 64 128 256), losses := [] }

theorem u41520 : Upper (D 7) (R 7) [6,288,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41521 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 290 13 74 241 241 241 241 497), lower := (rows 7 290 13 74 16 32 64 128 256), losses := [] }

theorem u41521 : Upper (D 7) (R 7) [6,288,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41522 : Route 9 := (fun mask => (mask,id))

def c41522 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41522 : Upper (D 7) (R 7) [6,288,9,80] 13 := by
  apply FastRouting.sound _ _ [6,288,9,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41522 c41522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32047
  · exact u32048
  · exact u32049
  · exact u32050
  · exact u32051
  · exact u32052
  · exact u32053
  · exact u32054
  · exact u32055
  · exact u32056

def r41523 : Route 9 := (fun mask => (mask,id))

def c41523 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41523 : Upper (D 7) (R 7) [6,288,9,96] 13 := by
  apply FastRouting.sound _ _ [6,288,9,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41523 c41523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32057
  · exact u32058
  · exact u32059
  · exact u32060
  · exact u32061
  · exact u32062

def r41524 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41524 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41524 : Upper (D 7) (R 7) [6,288,9,192] 13 := by
  apply FastRouting.sound _ _ [6,288,9,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41524 c41524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32063
  · exact u32064
  · exact u32065
  · exact u32066
  · exact u32067
  · exact u32068
  · exact u32069

def b41525 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 28 11 241 225 225 225 481), lower := (rows 7 290 28 11 16 32 64 128 256), losses := [] }

theorem u41525 : Upper (D 7) (R 7) [6,288,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41526_3 : Upper (D 7) (R 7) [6,288,24,33,3] 13 :=
  permutation_upper _ _ _ [6,288,24,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32070

def r41526 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41526 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41526 : Upper (D 7) (R 7) [6,288,24,33] 13 := by
  apply FastRouting.sound _ _ [6,288,24,33] 13 (by decide) (choices 2) [3,65,66,192] r41526 c41526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41526_3
  · exact u32074
  · exact u32075
  · exact u32076

def b41527 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 28 42 209 225 193 193 449), lower := (rows 7 290 28 42 16 32 64 128 256), losses := [] }

theorem u41527 : Upper (D 7) (R 7) [6,288,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41528_3 : Upper (D 7) (R 7) [6,288,24,65,3] 13 :=
  permutation_upper _ _ _ [6,288,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32071

theorem m41528_33 : Upper (D 7) (R 7) [6,288,24,65,33] 13 :=
  permutation_upper _ _ _ [6,288,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32074

theorem m41528_34 : Upper (D 7) (R 7) [6,288,24,65,34] 13 :=
  permutation_upper _ _ _ [6,288,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32077

def r41528 : Route 9 := (fun mask => (mask,id))

def c41528 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41528 : Upper (D 7) (R 7) [6,288,24,65] 13 := by
  apply FastRouting.sound _ _ [6,288,24,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41528 c41528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41528_3
  · exact m41528_33
  · exact m41528_34
  · exact u32079
  · exact u32080
  · exact u32081
  · exact u32082
  · exact u32083
  · exact u32084
  · exact u32085

theorem m41529_33 : Upper (D 7) (R 7) [6,288,24,66,33] 13 :=
  permutation_upper _ _ _ [6,288,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32075

theorem m41529_65 : Upper (D 7) (R 7) [6,288,24,66,65] 13 :=
  permutation_upper _ _ _ [6,288,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32080

theorem m41529_129 : Upper (D 7) (R 7) [6,288,24,66,129] 13 :=
  permutation_upper _ _ _ [6,288,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32083

def r41529 : Route 9 := (fun mask => (mask,id))

def c41529 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41529 : Upper (D 7) (R 7) [6,288,24,66] 13 := by
  apply FastRouting.sound _ _ [6,288,24,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41529 c41529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41529_33
  · exact m41529_65
  · exact u32086
  · exact m41529_129
  · exact u32087
  · exact u32088

theorem m41530_3 : Upper (D 7) (R 7) [6,288,24,96,3] 13 :=
  permutation_upper _ _ _ [6,288,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32072

theorem m41530_65 : Upper (D 7) (R 7) [6,288,24,96,65] 13 :=
  permutation_upper _ _ _ [6,288,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32081

theorem m41530_66 : Upper (D 7) (R 7) [6,288,24,96,66] 13 :=
  permutation_upper _ _ _ [6,288,24,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32086

theorem m41530_129 : Upper (D 7) (R 7) [6,288,24,96,129] 13 :=
  permutation_upper _ _ _ [6,288,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32084

theorem m41530_130 : Upper (D 7) (R 7) [6,288,24,96,130] 13 :=
  permutation_upper _ _ _ [6,288,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32087

def r41530 : Route 9 := (fun mask => (mask,id))

def c41530 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41530 : Upper (D 7) (R 7) [6,288,24,96] 13 := by
  apply FastRouting.sound _ _ [6,288,24,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41530 c41530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41530_3
  · exact m41530_65
  · exact m41530_66
  · exact m41530_129
  · exact m41530_130
  · exact u32089

theorem m41531_3 : Upper (D 7) (R 7) [6,288,24,192,3] 13 :=
  permutation_upper _ _ _ [6,288,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32073

theorem m41531_33 : Upper (D 7) (R 7) [6,288,24,192,33] 13 :=
  permutation_upper _ _ _ [6,288,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32076

theorem m41531_34 : Upper (D 7) (R 7) [6,288,24,192,34] 13 :=
  permutation_upper _ _ _ [6,288,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32078

theorem m41531_65 : Upper (D 7) (R 7) [6,288,24,192,65] 13 :=
  permutation_upper _ _ _ [6,288,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32085

theorem m41531_66 : Upper (D 7) (R 7) [6,288,24,192,66] 13 :=
  permutation_upper _ _ _ [6,288,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32088

theorem m41531_96 : Upper (D 7) (R 7) [6,288,24,192,96] 13 :=
  permutation_upper _ _ _ [6,288,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32089

def r41531 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41531 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41531 : Upper (D 7) (R 7) [6,288,24,192] 13 := by
  apply FastRouting.sound _ _ [6,288,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41531 c41531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41531_3
  · exact m41531_33
  · exact m41531_34
  · exact m41531_65
  · exact m41531_66
  · exact m41531_96
  · exact u32090

def b41532 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 290 44 11 209 241 209 209 465), lower := (rows 7 290 44 11 16 32 64 128 256), losses := [] }

theorem u41532 : Upper (D 7) (R 7) [6,288,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41533 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41533 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41533 : Upper (D 7) (R 7) [6,288,40,17] 13 := by
  apply FastRouting.sound _ _ [6,288,40,17] 13 (by decide) (choices 2) [3,65,66,192] r41533 c41533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32091
  · exact u32092
  · exact u32093
  · exact u32094

def r41534 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41534 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41534 : Upper (D 7) (R 7) [6,288,40,18] 13 := by
  apply FastRouting.sound _ _ [6,288,40,18] 13 (by decide) (choices 2) [65,192] r41534 c41534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u32095
  · exact u32096

def r41535 : Route 9 := (fun mask => (mask,id))

def c41535 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41535 : Upper (D 7) (R 7) [6,288,40,65] 13 := by
  apply FastRouting.sound _ _ [6,288,40,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41535 c41535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32097
  · exact u32098
  · exact u32099
  · exact u32100
  · exact u32101
  · exact u32102

def r41536 : Route 9 := (fun mask => (mask,id))

def c41536 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41536 : Upper (D 7) (R 7) [6,288,40,66] 13 := by
  apply FastRouting.sound _ _ [6,288,40,66] 13 (by decide) (choices 2) [65,129,192] r41536 c41536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32103
  · exact u32104
  · exact u32105

def r41537 : Route 9 := (fun mask => (mask,id))

def c41537 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41537 : Upper (D 7) (R 7) [6,288,40,80] 13 := by
  apply FastRouting.sound _ _ [6,288,40,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41537 c41537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32106
  · exact u32107
  · exact u32108
  · exact u32109
  · exact u32110
  · exact u32111

def r41538 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41538 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41538 : Upper (D 7) (R 7) [6,288,40,192] 13 := by
  apply FastRouting.sound _ _ [6,288,40,192] 13 (by decide) (choices 2) [3,65,66,192] r41538 c41538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32112
  · exact u32113
  · exact u32114
  · exact u32115

def b41539 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 290 69 11 248 248 248 248 504), lower := (rows 7 290 69 11 16 32 64 128 256), losses := [] }

theorem u41539 : Upper (D 7) (R 7) [6,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41540 : Route 9 := (fun mask => (mask,id))

def c41540 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41540 : Upper (D 7) (R 7) [6,288,65,17] 13 := by
  apply FastRouting.sound _ _ [6,288,65,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r41540 c41540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32122
  · exact u32123
  · exact u32124
  · exact u32125
  · exact u32126
  · exact u32127
  · exact u32128
  · exact u32129
  · exact u32130
  · exact u32131

theorem m41541_9 : Upper (D 7) (R 7) [6,288,65,18,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32122

def r41541 : Route 9 := (fun mask => (mask,id))

def c41541 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41541 : Upper (D 7) (R 7) [6,288,65,18] 13 := by
  apply FastRouting.sound _ _ [6,288,65,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r41541 c41541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41541_9
  · exact u32132
  · exact u32133
  · exact u32134
  · exact u32135
  · exact u32136
  · exact u32137
  · exact u32138
  · exact u32139
  · exact u32140

theorem m41542_10 : Upper (D 7) (R 7) [6,288,65,33,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32132

def r41542 : Route 9 := (fun mask => (mask,id))

def c41542 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41542 : Upper (D 7) (R 7) [6,288,65,33] 13 := by
  apply FastRouting.sound _ _ [6,288,65,33] 13 (by decide) (choices 2) [10,66,72,130,136,192] r41542 c41542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41542_10
  · exact u32141
  · exact u32142
  · exact u32143
  · exact u32144
  · exact u32145

def b41543 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 69 42 217 249 217 217 473), lower := (rows 7 290 69 42 16 32 64 128 256), losses := [] }

theorem u41543 : Upper (D 7) (R 7) [6,288,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41544_3 : Upper (D 7) (R 7) [6,288,65,48,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32116

theorem m41544_9 : Upper (D 7) (R 7) [6,288,65,48,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32124

theorem m41544_10 : Upper (D 7) (R 7) [6,288,65,48,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32133

def r41544 : Route 9 := (fun mask => (mask,id))

def c41544 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41544 : Upper (D 7) (R 7) [6,288,65,48] 13 := by
  apply FastRouting.sound _ _ [6,288,65,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41544 c41544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41544_3
  · exact m41544_9
  · exact m41544_10
  · exact u32150
  · exact u32151
  · exact u32152
  · exact u32153
  · exact u32154
  · exact u32155
  · exact u32156

def b41545 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 8, targets := 162 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,7)], upper := (rows 7 290 69 73 186 186 250 186 442), lower := (rows 7 290 69 73 16 32 64 128 256), losses := [] }

theorem u41545 : Upper (D 7) (R 7) [6,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41546 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 69 74 185 185 249 185 441), lower := (rows 7 290 69 74 16 32 64 128 256), losses := [] }

theorem u41546 : Upper (D 7) (R 7) [6,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41547_3 : Upper (D 7) (R 7) [6,288,65,80,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32117

theorem m41547_9 : Upper (D 7) (R 7) [6,288,65,80,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32126

theorem m41547_10 : Upper (D 7) (R 7) [6,288,65,80,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32135

theorem m41547_33 : Upper (D 7) (R 7) [6,288,65,80,33] 13 :=
  permutation_upper _ _ _ [6,288,65,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32142

theorem m41547_34 : Upper (D 7) (R 7) [6,288,65,80,34] 13 :=
  permutation_upper _ _ _ [6,288,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32146

theorem m41547_40 : Upper (D 7) (R 7) [6,288,65,80,40] 13 :=
  permutation_upper _ _ _ [6,288,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32152

def r41547 : Route 9 := (fun mask => (mask,id))

def c41547 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41547 : Upper (D 7) (R 7) [6,288,65,80] 13 := by
  apply FastRouting.sound _ _ [6,288,65,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41547 c41547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41547_3
  · exact m41547_9
  · exact m41547_10
  · exact m41547_33
  · exact m41547_34
  · exact m41547_40
  · exact u32163
  · exact u32164
  · exact u32165
  · exact u32166

theorem m41548_3 : Upper (D 7) (R 7) [6,288,65,96,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32118

theorem m41548_9 : Upper (D 7) (R 7) [6,288,65,96,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32127

theorem m41548_10 : Upper (D 7) (R 7) [6,288,65,96,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32136

def r41548 : Route 9 := (fun mask => (mask,id))

def c41548 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41548 : Upper (D 7) (R 7) [6,288,65,96] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41548 c41548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41548_3
  · exact m41548_9
  · exact m41548_10
  · exact u32167
  · exact u32168
  · exact u32169

theorem m41549_10 : Upper (D 7) (R 7) [6,288,65,129,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32137

theorem m41549_34 : Upper (D 7) (R 7) [6,288,65,129,34] 13 :=
  permutation_upper _ _ _ [6,288,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32147

theorem m41549_40 : Upper (D 7) (R 7) [6,288,65,129,40] 13 :=
  permutation_upper _ _ _ [6,288,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32153

theorem m41549_66 : Upper (D 7) (R 7) [6,288,65,129,66] 13 :=
  permutation_upper _ _ _ [6,288,65,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32160

theorem m41549_72 : Upper (D 7) (R 7) [6,288,65,129,72] 13 :=
  permutation_upper _ _ _ [6,288,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32163

theorem m41549_96 : Upper (D 7) (R 7) [6,288,65,129,96] 13 :=
  permutation_upper _ _ _ [6,288,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32167

def r41549 : Route 9 := (fun mask => (mask,id))

def c41549 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41549 : Upper (D 7) (R 7) [6,288,65,129] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r41549 c41549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41549_10
  · exact m41549_34
  · exact m41549_40
  · exact m41549_66
  · exact m41549_72
  · exact m41549_96
  · exact u32170
  · exact u32171
  · exact u32172
  · exact u32173

theorem m41550_9 : Upper (D 7) (R 7) [6,288,65,130,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32128

theorem m41550_33 : Upper (D 7) (R 7) [6,288,65,130,33] 13 :=
  permutation_upper _ _ _ [6,288,65,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32143

theorem m41550_40 : Upper (D 7) (R 7) [6,288,65,130,40] 13 :=
  permutation_upper _ _ _ [6,288,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32154

theorem m41550_65 : Upper (D 7) (R 7) [6,288,65,130,65] 13 :=
  permutation_upper _ _ _ [6,288,65,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32157

theorem m41550_72 : Upper (D 7) (R 7) [6,288,65,130,72] 13 :=
  permutation_upper _ _ _ [6,288,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32164

theorem m41550_96 : Upper (D 7) (R 7) [6,288,65,130,96] 13 :=
  permutation_upper _ _ _ [6,288,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32168

theorem m41550_129 : Upper (D 7) (R 7) [6,288,65,130,129] 13 :=
  permutation_upper _ _ _ [6,288,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32170

def r41550 : Route 9 := (fun mask => (mask,id))

def c41550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41550 : Upper (D 7) (R 7) [6,288,65,130] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r41550 c41550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41550_9
  · exact m41550_33
  · exact m41550_40
  · exact m41550_65
  · exact m41550_72
  · exact m41550_96
  · exact m41550_129
  · exact u32174
  · exact u32175
  · exact u32176

theorem m41551_3 : Upper (D 7) (R 7) [6,288,65,144,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32119

theorem m41551_9 : Upper (D 7) (R 7) [6,288,65,144,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32129

theorem m41551_10 : Upper (D 7) (R 7) [6,288,65,144,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32138

theorem m41551_33 : Upper (D 7) (R 7) [6,288,65,144,33] 13 :=
  permutation_upper _ _ _ [6,288,65,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32144

theorem m41551_34 : Upper (D 7) (R 7) [6,288,65,144,34] 13 :=
  permutation_upper _ _ _ [6,288,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32148

theorem m41551_40 : Upper (D 7) (R 7) [6,288,65,144,40] 13 :=
  permutation_upper _ _ _ [6,288,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32155

theorem m41551_65 : Upper (D 7) (R 7) [6,288,65,144,65] 13 :=
  permutation_upper _ _ _ [6,288,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32158

theorem m41551_66 : Upper (D 7) (R 7) [6,288,65,144,66] 13 :=
  permutation_upper _ _ _ [6,288,65,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32161

theorem m41551_72 : Upper (D 7) (R 7) [6,288,65,144,72] 13 :=
  permutation_upper _ _ _ [6,288,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32165

theorem m41551_96 : Upper (D 7) (R 7) [6,288,65,144,96] 13 :=
  permutation_upper _ _ _ [6,288,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32169

theorem m41551_129 : Upper (D 7) (R 7) [6,288,65,144,129] 13 :=
  permutation_upper _ _ _ [6,288,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32171

theorem m41551_130 : Upper (D 7) (R 7) [6,288,65,144,130] 13 :=
  permutation_upper _ _ _ [6,288,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32174

def r41551 : Route 9 := (fun mask => (mask,id))

def c41551 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41551 : Upper (D 7) (R 7) [6,288,65,144] 13 := by
  apply FastRouting.sound _ _ [6,288,65,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r41551 c41551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41551_3
  · exact m41551_9
  · exact m41551_10
  · exact m41551_33
  · exact m41551_34
  · exact m41551_40
  · exact m41551_65
  · exact m41551_66
  · exact m41551_72
  · exact m41551_96
  · exact m41551_129
  · exact m41551_130
  · exact u32177
  · exact u32178
  · exact u32179

theorem m41552_3 : Upper (D 7) (R 7) [6,288,65,160,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32120

theorem m41552_9 : Upper (D 7) (R 7) [6,288,65,160,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32130

theorem m41552_10 : Upper (D 7) (R 7) [6,288,65,160,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32139

theorem m41552_65 : Upper (D 7) (R 7) [6,288,65,160,65] 13 :=
  permutation_upper _ _ _ [6,288,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32159

theorem m41552_66 : Upper (D 7) (R 7) [6,288,65,160,66] 13 :=
  permutation_upper _ _ _ [6,288,65,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32162

theorem m41552_72 : Upper (D 7) (R 7) [6,288,65,160,72] 13 :=
  permutation_upper _ _ _ [6,288,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32166

theorem m41552_129 : Upper (D 7) (R 7) [6,288,65,160,129] 13 :=
  permutation_upper _ _ _ [6,288,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32172

theorem m41552_130 : Upper (D 7) (R 7) [6,288,65,160,130] 13 :=
  permutation_upper _ _ _ [6,288,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32175

theorem m41552_136 : Upper (D 7) (R 7) [6,288,65,160,136] 13 :=
  permutation_upper _ _ _ [6,288,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32178

def r41552 : Route 9 := (fun mask => (mask,id))

def c41552 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41552 : Upper (D 7) (R 7) [6,288,65,160] 13 := by
  apply FastRouting.sound _ _ [6,288,65,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41552 c41552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41552_3
  · exact m41552_9
  · exact m41552_10
  · exact m41552_65
  · exact m41552_66
  · exact m41552_72
  · exact m41552_129
  · exact m41552_130
  · exact m41552_136
  · exact u32180

theorem m41553_3 : Upper (D 7) (R 7) [6,288,65,192,3] 13 :=
  permutation_upper _ _ _ [6,288,65,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32121

theorem m41553_9 : Upper (D 7) (R 7) [6,288,65,192,9] 13 :=
  permutation_upper _ _ _ [6,288,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32131

theorem m41553_10 : Upper (D 7) (R 7) [6,288,65,192,10] 13 :=
  permutation_upper _ _ _ [6,288,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32140

theorem m41553_33 : Upper (D 7) (R 7) [6,288,65,192,33] 13 :=
  permutation_upper _ _ _ [6,288,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32145

theorem m41553_34 : Upper (D 7) (R 7) [6,288,65,192,34] 13 :=
  permutation_upper _ _ _ [6,288,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32149

theorem m41553_40 : Upper (D 7) (R 7) [6,288,65,192,40] 13 :=
  permutation_upper _ _ _ [6,288,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32156

theorem m41553_129 : Upper (D 7) (R 7) [6,288,65,192,129] 13 :=
  permutation_upper _ _ _ [6,288,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32173

theorem m41553_130 : Upper (D 7) (R 7) [6,288,65,192,130] 13 :=
  permutation_upper _ _ _ [6,288,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32176

theorem m41553_136 : Upper (D 7) (R 7) [6,288,65,192,136] 13 :=
  permutation_upper _ _ _ [6,288,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32179

theorem m41553_160 : Upper (D 7) (R 7) [6,288,65,192,160] 13 :=
  permutation_upper _ _ _ [6,288,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32180

def r41553 : Route 9 := (fun mask => (mask,id))

def c41553 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41553 : Upper (D 7) (R 7) [6,288,65,192] 13 := by
  apply FastRouting.sound _ _ [6,288,65,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r41553 c41553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41553_3
  · exact m41553_9
  · exact m41553_10
  · exact m41553_33
  · exact m41553_34
  · exact m41553_40
  · exact m41553_129
  · exact m41553_130
  · exact m41553_136
  · exact m41553_160

def b41554 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 76 11 241 241 241 241 497), lower := (rows 7 290 76 11 16 32 64 128 256), losses := [] }

theorem u41554 : Upper (D 7) (R 7) [6,288,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41555 : Route 9 := (fun mask => (mask,id))

def c41555 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41555 : Upper (D 7) (R 7) [6,288,72,17] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41555 c41555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32181
  · exact u32182
  · exact u32183
  · exact u32184
  · exact u32185
  · exact u32186
  · exact u32187
  · exact u32188
  · exact u32189
  · exact u32190

def r41556 : Route 9 := (fun mask => (mask,id))

def c41556 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41556 : Upper (D 7) (R 7) [6,288,72,18] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41556 c41556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32191
  · exact u32192
  · exact u32193
  · exact u32194
  · exact u32195
  · exact u32196

def r41557 : Route 9 := (fun mask => (mask,id))

def c41557 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41557 : Upper (D 7) (R 7) [6,288,72,33] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41557 c41557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32197
  · exact u32198
  · exact u32199
  · exact u32200
  · exact u32201
  · exact u32202

def b41558 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 290 76 42 209 241 209 209 465), lower := (rows 7 290 76 42 16 32 64 128 256), losses := [] }

theorem u41558 : Upper (D 7) (R 7) [6,288,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41559 : Route 9 := (fun mask => (mask,id))

def c41559 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41559 : Upper (D 7) (R 7) [6,288,72,48] 13 := by
  apply FastRouting.sound _ _ [6,288,72,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41559 c41559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32203
  · exact u32204
  · exact u32205
  · exact u32206
  · exact u32207
  · exact u32208

def b41560 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 73 179 179 243 179 435), lower := (rows 7 290 76 73 16 32 64 128 256), losses := [] }

theorem u41560 : Upper (D 7) (R 7) [6,288,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41561 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 74 177 177 241 177 433), lower := (rows 7 290 76 74 16 32 64 128 256), losses := [] }

theorem u41561 : Upper (D 7) (R 7) [6,288,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41562 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 88 179 163 227 163 419), lower := (rows 7 290 76 88 16 32 64 128 256), losses := [] }

theorem u41562 : Upper (D 7) (R 7) [6,288,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41563 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 104 147 179 211 147 403), lower := (rows 7 290 76 104 16 32 64 128 256), losses := [] }

theorem u41563 : Upper (D 7) (R 7) [6,288,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41564 : Route 9 := (fun mask => (mask,id))

def c41564 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41564 : Upper (D 7) (R 7) [6,288,72,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41564 c41564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32209
  · exact u32210
  · exact u32211
  · exact u32212
  · exact u32213
  · exact u32214
  · exact u32215
  · exact u32216
  · exact u32217
  · exact u32218

def r41565 : Route 9 := (fun mask => (mask,id))

def c41565 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41565 : Upper (D 7) (R 7) [6,288,72,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41565 c41565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32219
  · exact u32220
  · exact u32221
  · exact u32222
  · exact u32223
  · exact u32224

def r41566 : Route 9 := (fun mask => (mask,id))

def c41566 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41566 : Upper (D 7) (R 7) [6,288,72,144] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41566 c41566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32225
  · exact u32226
  · exact u32227
  · exact u32228
  · exact u32229
  · exact u32230
  · exact u32231
  · exact u32232
  · exact u32233
  · exact u32234

def r41567 : Route 9 := (fun mask => (mask,id))

def c41567 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41567 : Upper (D 7) (R 7) [6,288,72,160] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41567 c41567
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32235
  · exact u32236
  · exact u32237
  · exact u32238
  · exact u32239
  · exact u32240

def b41568 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 200 179 179 243 179 435), lower := (rows 7 290 76 200 16 32 64 128 256), losses := [] }

theorem u41568 : Upper (D 7) (R 7) [6,288,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41569 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 100 11 217 249 217 217 473), lower := (rows 7 290 100 11 16 32 64 128 256), losses := [] }

theorem u41569 : Upper (D 7) (R 7) [6,288,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41570_3 : Upper (D 7) (R 7) [6,288,96,17,3] 13 :=
  permutation_upper _ _ _ [6,288,96,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32241

def r41570 : Route 9 := (fun mask => (mask,id))

def c41570 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41570 : Upper (D 7) (R 7) [6,288,96,17] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41570 c41570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41570_3
  · exact u32246
  · exact u32247
  · exact u32248
  · exact u32249
  · exact u32250
  · exact u32251
  · exact u32252
  · exact u32253
  · exact u32254

theorem m41571_9 : Upper (D 7) (R 7) [6,288,96,18,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32247

def r41571 : Route 9 := (fun mask => (mask,id))

def c41571 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41571 : Upper (D 7) (R 7) [6,288,96,18] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18] 13 (by decide) (choices 2) [9,65,72,129,136,192] r41571 c41571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41571_9
  · exact u32255
  · exact u32256
  · exact u32257
  · exact u32258
  · exact u32259

def b41572 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 7 290 100 73 155 187 219 155 411), lower := (rows 7 290 100 73 16 32 64 128 256), losses := [] }

theorem u41572 : Upper (D 7) (R 7) [6,288,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41573_9 : Upper (D 7) (R 7) [6,288,96,66,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32249

def r41573 : Route 9 := (fun mask => (mask,id))

def c41573 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41573 : Upper (D 7) (R 7) [6,288,96,66] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66] 13 (by decide) (choices 2) [9,129,136] r41573 c41573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m41573_9
  · exact u32263
  · exact u32264

theorem m41574_3 : Upper (D 7) (R 7) [6,288,96,80,3] 13 :=
  permutation_upper _ _ _ [6,288,96,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32242

theorem m41574_9 : Upper (D 7) (R 7) [6,288,96,80,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32250

theorem m41574_10 : Upper (D 7) (R 7) [6,288,96,80,10] 13 :=
  permutation_upper _ _ _ [6,288,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32256

def r41574 : Route 9 := (fun mask => (mask,id))

def c41574 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41574 : Upper (D 7) (R 7) [6,288,96,80] 13 := by
  apply FastRouting.sound _ _ [6,288,96,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41574 c41574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41574_3
  · exact m41574_9
  · exact m41574_10
  · exact u32265
  · exact u32266
  · exact u32267

theorem m41575_3 : Upper (D 7) (R 7) [6,288,96,129,3] 13 :=
  permutation_upper _ _ _ [6,288,96,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32243

theorem m41575_9 : Upper (D 7) (R 7) [6,288,96,129,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32251

theorem m41575_10 : Upper (D 7) (R 7) [6,288,96,129,10] 13 :=
  permutation_upper _ _ _ [6,288,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32257

theorem m41575_65 : Upper (D 7) (R 7) [6,288,96,129,65] 13 :=
  permutation_upper _ _ _ [6,288,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32260

theorem m41575_66 : Upper (D 7) (R 7) [6,288,96,129,66] 13 :=
  permutation_upper _ _ _ [6,288,96,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32263

theorem m41575_72 : Upper (D 7) (R 7) [6,288,96,129,72] 13 :=
  permutation_upper _ _ _ [6,288,96,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32265

def r41575 : Route 9 := (fun mask => (mask,id))

def c41575 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41575 : Upper (D 7) (R 7) [6,288,96,129] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41575 c41575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41575_3
  · exact m41575_9
  · exact m41575_10
  · exact m41575_65
  · exact m41575_66
  · exact m41575_72
  · exact u32268
  · exact u32269
  · exact u32270
  · exact u32271

theorem m41576_9 : Upper (D 7) (R 7) [6,288,96,130,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32252

theorem m41576_65 : Upper (D 7) (R 7) [6,288,96,130,65] 13 :=
  permutation_upper _ _ _ [6,288,96,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32261

theorem m41576_72 : Upper (D 7) (R 7) [6,288,96,130,72] 13 :=
  permutation_upper _ _ _ [6,288,96,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32266

theorem m41576_129 : Upper (D 7) (R 7) [6,288,96,130,129] 13 :=
  permutation_upper _ _ _ [6,288,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32269

def r41576 : Route 9 := (fun mask => (mask,id))

def c41576 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41576 : Upper (D 7) (R 7) [6,288,96,130] 13 := by
  apply FastRouting.sound _ _ [6,288,96,130] 13 (by decide) (choices 2) [9,65,72,129,136,192] r41576 c41576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41576_9
  · exact m41576_65
  · exact m41576_72
  · exact m41576_129
  · exact u32272
  · exact u32273

theorem m41577_3 : Upper (D 7) (R 7) [6,288,96,144,3] 13 :=
  permutation_upper _ _ _ [6,288,96,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32244

theorem m41577_9 : Upper (D 7) (R 7) [6,288,96,144,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32253

theorem m41577_10 : Upper (D 7) (R 7) [6,288,96,144,10] 13 :=
  permutation_upper _ _ _ [6,288,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32258

theorem m41577_65 : Upper (D 7) (R 7) [6,288,96,144,65] 13 :=
  permutation_upper _ _ _ [6,288,96,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32262

theorem m41577_66 : Upper (D 7) (R 7) [6,288,96,144,66] 13 :=
  permutation_upper _ _ _ [6,288,96,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32264

theorem m41577_72 : Upper (D 7) (R 7) [6,288,96,144,72] 13 :=
  permutation_upper _ _ _ [6,288,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32267

theorem m41577_129 : Upper (D 7) (R 7) [6,288,96,144,129] 13 :=
  permutation_upper _ _ _ [6,288,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32270

theorem m41577_130 : Upper (D 7) (R 7) [6,288,96,144,130] 13 :=
  permutation_upper _ _ _ [6,288,96,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32272

def r41577 : Route 9 := (fun mask => (mask,id))

def c41577 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41577 : Upper (D 7) (R 7) [6,288,96,144] 13 := by
  apply FastRouting.sound _ _ [6,288,96,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41577 c41577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41577_3
  · exact m41577_9
  · exact m41577_10
  · exact m41577_65
  · exact m41577_66
  · exact m41577_72
  · exact m41577_129
  · exact m41577_130
  · exact u32274
  · exact u32275

theorem m41578_3 : Upper (D 7) (R 7) [6,288,96,192,3] 13 :=
  permutation_upper _ _ _ [6,288,96,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32245

theorem m41578_9 : Upper (D 7) (R 7) [6,288,96,192,9] 13 :=
  permutation_upper _ _ _ [6,288,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32254

theorem m41578_10 : Upper (D 7) (R 7) [6,288,96,192,10] 13 :=
  permutation_upper _ _ _ [6,288,96,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32259

theorem m41578_129 : Upper (D 7) (R 7) [6,288,96,192,129] 13 :=
  permutation_upper _ _ _ [6,288,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32271

theorem m41578_130 : Upper (D 7) (R 7) [6,288,96,192,130] 13 :=
  permutation_upper _ _ _ [6,288,96,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32273

theorem m41578_136 : Upper (D 7) (R 7) [6,288,96,192,136] 13 :=
  permutation_upper _ _ _ [6,288,96,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32275

def r41578 : Route 9 := (fun mask => (mask,id))

def c41578 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41578 : Upper (D 7) (R 7) [6,288,96,192] 13 := by
  apply FastRouting.sound _ _ [6,288,96,192] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41578 c41578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41578_3
  · exact m41578_9
  · exact m41578_10
  · exact m41578_129
  · exact m41578_130
  · exact m41578_136

def b41579 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 249 249 249 249 505), lower := (rows 7 290 196 11 16 32 64 128 256), losses := [] }

theorem u41579 : Upper (D 7) (R 7) [6,288,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41579
end Delivery.IrregularNine14.P07
