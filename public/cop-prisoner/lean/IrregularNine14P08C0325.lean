import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0151
import IrregularNine14P08C0152
import IrregularNine14P08C0153
import IrregularNine14P08C0154
import IrregularNine14P08C0155

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m19500_9 : Upper (D 8) (R 8) [34,68,160,257,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9070

theorem m19500_33 : Upper (D 8) (R 8) [34,68,160,257,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9078

theorem m19500_40 : Upper (D 8) (R 8) [34,68,160,257,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9087

theorem m19500_65 : Upper (D 8) (R 8) [34,68,160,257,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9092

theorem m19500_72 : Upper (D 8) (R 8) [34,68,160,257,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9099

theorem m19500_96 : Upper (D 8) (R 8) [34,68,160,257,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9105

theorem m19500_129 : Upper (D 8) (R 8) [34,68,160,257,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9108

theorem m19500_136 : Upper (D 8) (R 8) [34,68,160,257,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9112

theorem m19500_160 : Upper (D 8) (R 8) [34,68,160,257,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9116

theorem m19500_192 : Upper (D 8) (R 8) [34,68,160,257,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9119

def r19500 : Route 9 := (fun mask => (mask,id))

def c19500 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19500 : Upper (D 8) (R 8) [34,68,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19500 c19500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19500_9
  · exact m19500_33
  · exact m19500_40
  · exact m19500_65
  · exact m19500_72
  · exact m19500_96
  · exact m19500_129
  · exact m19500_136
  · exact m19500_160
  · exact m19500_192

theorem m19501_9 : Upper (D 8) (R 8) [34,68,160,272,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9071

theorem m19501_33 : Upper (D 8) (R 8) [34,68,160,272,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9079

theorem m19501_40 : Upper (D 8) (R 8) [34,68,160,272,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9088

theorem m19501_65 : Upper (D 8) (R 8) [34,68,160,272,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9093

theorem m19501_72 : Upper (D 8) (R 8) [34,68,160,272,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9100

theorem m19501_96 : Upper (D 8) (R 8) [34,68,160,272,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9106

theorem m19501_129 : Upper (D 8) (R 8) [34,68,160,272,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9109

theorem m19501_136 : Upper (D 8) (R 8) [34,68,160,272,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9113

theorem m19501_160 : Upper (D 8) (R 8) [34,68,160,272,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9117

theorem m19501_192 : Upper (D 8) (R 8) [34,68,160,272,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9120

def r19501 : Route 9 := (fun mask => (mask,id))

def c19501 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19501 : Upper (D 8) (R 8) [34,68,160,272] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19501 c19501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19501_9
  · exact m19501_33
  · exact m19501_40
  · exact m19501_65
  · exact m19501_72
  · exact m19501_96
  · exact m19501_129
  · exact m19501_136
  · exact m19501_160
  · exact m19501_192

theorem m19502_9 : Upper (D 8) (R 8) [34,68,160,288,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9072

theorem m19502_65 : Upper (D 8) (R 8) [34,68,160,288,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9094

theorem m19502_72 : Upper (D 8) (R 8) [34,68,160,288,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9101

theorem m19502_129 : Upper (D 8) (R 8) [34,68,160,288,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9110

theorem m19502_136 : Upper (D 8) (R 8) [34,68,160,288,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9114

theorem m19502_192 : Upper (D 8) (R 8) [34,68,160,288,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9121

def r19502 : Route 9 := (fun mask => (mask,id))

def c19502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19502 : Upper (D 8) (R 8) [34,68,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,160,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19502 c19502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19502_9
  · exact m19502_65
  · exact m19502_72
  · exact m19502_129
  · exact m19502_136
  · exact m19502_192

theorem m19503_9 : Upper (D 8) (R 8) [34,68,160,320,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9073

theorem m19503_33 : Upper (D 8) (R 8) [34,68,160,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9080

theorem m19503_40 : Upper (D 8) (R 8) [34,68,160,320,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9089

theorem m19503_129 : Upper (D 8) (R 8) [34,68,160,320,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9111

theorem m19503_136 : Upper (D 8) (R 8) [34,68,160,320,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9115

theorem m19503_160 : Upper (D 8) (R 8) [34,68,160,320,160] 13 :=
  permutation_upper _ _ _ [34,68,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9118

def r19503 : Route 9 := (fun mask => (mask,id))

def c19503 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19503 : Upper (D 8) (R 8) [34,68,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19503 c19503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19503_9
  · exact m19503_33
  · exact m19503_40
  · exact m19503_129
  · exact m19503_136
  · exact m19503_160

theorem m19504_9 : Upper (D 8) (R 8) [34,68,160,384,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9074

theorem m19504_33 : Upper (D 8) (R 8) [34,68,160,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9081

theorem m19504_40 : Upper (D 8) (R 8) [34,68,160,384,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9090

theorem m19504_65 : Upper (D 8) (R 8) [34,68,160,384,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9095

theorem m19504_72 : Upper (D 8) (R 8) [34,68,160,384,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9102

theorem m19504_96 : Upper (D 8) (R 8) [34,68,160,384,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9107

def r19504 : Route 9 := (fun mask => (mask,id))

def c19504 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19504 : Upper (D 8) (R 8) [34,68,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19504 c19504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19504_9
  · exact m19504_33
  · exact m19504_40
  · exact m19504_65
  · exact m19504_72
  · exact m19504_96

def b19505 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 25 248 232 232 232 488), lower := (rows 35 70 261 25 16 32 64 128 256), losses := [] }

theorem u19505 : Upper (D 8) (R 8) [34,68,257,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19506 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 41 248 248 248 248 504), lower := (rows 35 70 261 41 16 32 64 128 256), losses := [] }

theorem u19506 : Upper (D 8) (R 8) [34,68,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19507_9 : Upper (D 8) (R 8) [34,68,257,48,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9122

theorem m19507_33 : Upper (D 8) (R 8) [34,68,257,48,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9128

def r19507 : Route 9 := (fun mask => (mask,id))

def c19507 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19507 : Upper (D 8) (R 8) [34,68,257,48] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19507 c19507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19507_9
  · exact m19507_33
  · exact u9134
  · exact u9135
  · exact u9136
  · exact u9137
  · exact u9138
  · exact u9139
  · exact u9140
  · exact u9141

def b19508 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 184 184 248 184 440), lower := (rows 35 70 261 73 16 32 64 128 256), losses := [] }

theorem u19508 : Upper (D 8) (R 8) [34,68,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19509_9 : Upper (D 8) (R 8) [34,68,257,80,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9123

theorem m19509_33 : Upper (D 8) (R 8) [34,68,257,80,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9129

theorem m19509_40 : Upper (D 8) (R 8) [34,68,257,80,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9136

def r19509 : Route 9 := (fun mask => (mask,id))

def c19509 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19509 : Upper (D 8) (R 8) [34,68,257,80] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19509 c19509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19509_9
  · exact m19509_33
  · exact m19509_40
  · exact u9144
  · exact u9145
  · exact u9146

theorem m19510_9 : Upper (D 8) (R 8) [34,68,257,96,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9124

theorem m19510_33 : Upper (D 8) (R 8) [34,68,257,96,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9130

theorem m19510_40 : Upper (D 8) (R 8) [34,68,257,96,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9137

def r19510 : Route 9 := (fun mask => (mask,id))

def c19510 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19510 : Upper (D 8) (R 8) [34,68,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19510 c19510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19510_9
  · exact m19510_33
  · exact m19510_40
  · exact u9147
  · exact u9148
  · exact u9149

def b19511 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 261 137 248 248 248 248 504), lower := (rows 35 70 261 137 16 32 64 128 256), losses := [] }

theorem u19511 : Upper (D 8) (R 8) [34,68,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19512_9 : Upper (D 8) (R 8) [34,68,257,144,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9125

theorem m19512_33 : Upper (D 8) (R 8) [34,68,257,144,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9131

theorem m19512_40 : Upper (D 8) (R 8) [34,68,257,144,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9139

theorem m19512_65 : Upper (D 8) (R 8) [34,68,257,144,65] 13 :=
  permutation_upper _ _ _ [34,68,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9142

theorem m19512_72 : Upper (D 8) (R 8) [34,68,257,144,72] 13 :=
  permutation_upper _ _ _ [34,68,257,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9145

theorem m19512_96 : Upper (D 8) (R 8) [34,68,257,144,96] 13 :=
  permutation_upper _ _ _ [34,68,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9148

theorem m19512_129 : Upper (D 8) (R 8) [34,68,257,144,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9150

def r19512 : Route 9 := (fun mask => (mask,id))

def c19512 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19512 : Upper (D 8) (R 8) [34,68,257,144] 13 := by
  apply FastRouting.sound _ _ [34,68,257,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19512 c19512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19512_9
  · exact m19512_33
  · exact m19512_40
  · exact m19512_65
  · exact m19512_72
  · exact m19512_96
  · exact m19512_129
  · exact u9153
  · exact u9154
  · exact u9155

theorem m19513_9 : Upper (D 8) (R 8) [34,68,257,160,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9126

theorem m19513_33 : Upper (D 8) (R 8) [34,68,257,160,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9132

theorem m19513_40 : Upper (D 8) (R 8) [34,68,257,160,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9140

theorem m19513_65 : Upper (D 8) (R 8) [34,68,257,160,65] 13 :=
  permutation_upper _ _ _ [34,68,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9143

theorem m19513_72 : Upper (D 8) (R 8) [34,68,257,160,72] 13 :=
  permutation_upper _ _ _ [34,68,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9146

theorem m19513_96 : Upper (D 8) (R 8) [34,68,257,160,96] 13 :=
  permutation_upper _ _ _ [34,68,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9149

theorem m19513_129 : Upper (D 8) (R 8) [34,68,257,160,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9151

theorem m19513_136 : Upper (D 8) (R 8) [34,68,257,160,136] 13 :=
  permutation_upper _ _ _ [34,68,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9154

def r19513 : Route 9 := (fun mask => (mask,id))

def c19513 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19513 : Upper (D 8) (R 8) [34,68,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19513 c19513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19513_9
  · exact m19513_33
  · exact m19513_40
  · exact m19513_65
  · exact m19513_72
  · exact m19513_96
  · exact m19513_129
  · exact m19513_136
  · exact u9156
  · exact u9157

theorem m19514_9 : Upper (D 8) (R 8) [34,68,257,192,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9127

theorem m19514_33 : Upper (D 8) (R 8) [34,68,257,192,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9133

theorem m19514_40 : Upper (D 8) (R 8) [34,68,257,192,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9141

theorem m19514_129 : Upper (D 8) (R 8) [34,68,257,192,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9152

theorem m19514_136 : Upper (D 8) (R 8) [34,68,257,192,136] 13 :=
  permutation_upper _ _ _ [34,68,257,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9155

theorem m19514_160 : Upper (D 8) (R 8) [34,68,257,192,160] 13 :=
  permutation_upper _ _ _ [34,68,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9157

def r19514 : Route 9 := (fun mask => (mask,id))

def c19514 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19514 : Upper (D 8) (R 8) [34,68,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19514 c19514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19514_9
  · exact m19514_33
  · exact m19514_40
  · exact m19514_129
  · exact m19514_136
  · exact m19514_160

def r19515 : Route 9 := (fun mask => (mask,id))

def c19515 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19515 : Upper (D 8) (R 8) [34,68,264,17] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19515 c19515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9158
  · exact u9159
  · exact u9160
  · exact u9161
  · exact u9162
  · exact u9163

def b19516 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 268 41 241 241 241 241 497), lower := (rows 35 70 268 41 16 32 64 128 256), losses := [] }

theorem u19516 : Upper (D 8) (R 8) [34,68,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19517 : Route 9 := (fun mask => (mask,id))

def c19517 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19517 : Upper (D 8) (R 8) [34,68,264,48] 13 := by
  apply FastRouting.sound _ _ [34,68,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19517 c19517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9164
  · exact u9165
  · exact u9166
  · exact u9167
  · exact u9168
  · exact u9169

def b19518 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 73 177 177 241 177 433), lower := (rows 35 70 268 73 16 32 64 128 256), losses := [] }

theorem u19518 : Upper (D 8) (R 8) [34,68,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19519 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 88 177 161 225 161 417), lower := (rows 35 70 268 88 16 32 64 128 256), losses := [] }

theorem u19519 : Upper (D 8) (R 8) [34,68,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19520 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 104 177 177 241 177 433), lower := (rows 35 70 268 104 16 32 64 128 256), losses := [] }

theorem u19520 : Upper (D 8) (R 8) [34,68,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19521 : Route 9 := (fun mask => (mask,id))

def c19521 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19521 : Upper (D 8) (R 8) [34,68,264,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19521 c19521
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9170
  · exact u9171
  · exact u9172
  · exact u9173
  · exact u9174
  · exact u9175

def r19522 : Route 9 := (fun mask => (mask,id))

def c19522 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19522 : Upper (D 8) (R 8) [34,68,264,144] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19522 c19522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9176
  · exact u9177
  · exact u9178
  · exact u9179
  · exact u9180
  · exact u9181

def r19523 : Route 9 := (fun mask => (mask,id))

def c19523 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19523 : Upper (D 8) (R 8) [34,68,264,160] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19523 c19523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9182
  · exact u9183
  · exact u9184
  · exact u9185
  · exact u9186
  · exact u9187

def b19524 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 200 177 177 241 177 433), lower := (rows 35 70 268 200 16 32 64 128 256), losses := [] }

theorem u19524 : Upper (D 8) (R 8) [34,68,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19525 : Route 9 := (fun mask => (mask,id))

def c19525 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19525 : Upper (D 8) (R 8) [34,68,288,17] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19525 c19525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9188
  · exact u9189
  · exact u9190
  · exact u9191
  · exact u9192
  · exact u9193
  · exact u9194
  · exact u9195
  · exact u9196
  · exact u9197

def b19526 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 292 41 217 249 217 217 473), lower := (rows 35 70 292 41 16 32 64 128 256), losses := [] }

theorem u19526 : Upper (D 8) (R 8) [34,68,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19527_9 : Upper (D 8) (R 8) [34,68,288,48,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9190

def r19527 : Route 9 := (fun mask => (mask,id))

def c19527 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19527 : Upper (D 8) (R 8) [34,68,288,48] 13 := by
  apply FastRouting.sound _ _ [34,68,288,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19527 c19527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19527_9
  · exact u9202
  · exact u9203
  · exact u9204
  · exact u9205
  · exact u9206

def b19528 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 73 185 185 249 185 441), lower := (rows 35 70 292 73 16 32 64 128 256), losses := [] }

theorem u19528 : Upper (D 8) (R 8) [34,68,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19529_9 : Upper (D 8) (R 8) [34,68,288,80,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9192

theorem m19529_33 : Upper (D 8) (R 8) [34,68,288,80,33] 13 :=
  permutation_upper _ _ _ [34,68,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9198

theorem m19529_40 : Upper (D 8) (R 8) [34,68,288,80,40] 13 :=
  permutation_upper _ _ _ [34,68,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9203

def r19529 : Route 9 := (fun mask => (mask,id))

def c19529 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19529 : Upper (D 8) (R 8) [34,68,288,80] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19529 c19529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19529_9
  · exact m19529_33
  · exact m19529_40
  · exact u9210
  · exact u9211
  · exact u9212

theorem m19530_9 : Upper (D 8) (R 8) [34,68,288,96,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9193

def r19530 : Route 9 := (fun mask => (mask,id))

def c19530 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19530 : Upper (D 8) (R 8) [34,68,288,96] 13 := by
  apply FastRouting.sound _ _ [34,68,288,96] 13 (by decide) (choices 2) [9,129,136] r19530 c19530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19530_9
  · exact u9213
  · exact u9214

theorem m19531_9 : Upper (D 8) (R 8) [34,68,288,129,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9194

theorem m19531_33 : Upper (D 8) (R 8) [34,68,288,129,33] 13 :=
  permutation_upper _ _ _ [34,68,288,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9199

theorem m19531_40 : Upper (D 8) (R 8) [34,68,288,129,40] 13 :=
  permutation_upper _ _ _ [34,68,288,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9204

theorem m19531_65 : Upper (D 8) (R 8) [34,68,288,129,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9207

theorem m19531_72 : Upper (D 8) (R 8) [34,68,288,129,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9210

theorem m19531_96 : Upper (D 8) (R 8) [34,68,288,129,96] 13 :=
  permutation_upper _ _ _ [34,68,288,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9213

def r19531 : Route 9 := (fun mask => (mask,id))

def c19531 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19531 : Upper (D 8) (R 8) [34,68,288,129] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19531 c19531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19531_9
  · exact m19531_33
  · exact m19531_40
  · exact m19531_65
  · exact m19531_72
  · exact m19531_96
  · exact u9215
  · exact u9216
  · exact u9217
  · exact u9218

theorem m19532_9 : Upper (D 8) (R 8) [34,68,288,144,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9195

theorem m19532_33 : Upper (D 8) (R 8) [34,68,288,144,33] 13 :=
  permutation_upper _ _ _ [34,68,288,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9200

theorem m19532_40 : Upper (D 8) (R 8) [34,68,288,144,40] 13 :=
  permutation_upper _ _ _ [34,68,288,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9205

theorem m19532_65 : Upper (D 8) (R 8) [34,68,288,144,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9208

theorem m19532_72 : Upper (D 8) (R 8) [34,68,288,144,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9211

theorem m19532_96 : Upper (D 8) (R 8) [34,68,288,144,96] 13 :=
  permutation_upper _ _ _ [34,68,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9214

theorem m19532_129 : Upper (D 8) (R 8) [34,68,288,144,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9216

def r19532 : Route 9 := (fun mask => (mask,id))

def c19532 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19532 : Upper (D 8) (R 8) [34,68,288,144] 13 := by
  apply FastRouting.sound _ _ [34,68,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19532 c19532
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19532_9
  · exact m19532_33
  · exact m19532_40
  · exact m19532_65
  · exact m19532_72
  · exact m19532_96
  · exact m19532_129
  · exact u9219
  · exact u9220
  · exact u9221

theorem m19533_9 : Upper (D 8) (R 8) [34,68,288,160,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9196

theorem m19533_65 : Upper (D 8) (R 8) [34,68,288,160,65] 13 :=
  permutation_upper _ _ _ [34,68,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9209

theorem m19533_72 : Upper (D 8) (R 8) [34,68,288,160,72] 13 :=
  permutation_upper _ _ _ [34,68,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9212

theorem m19533_129 : Upper (D 8) (R 8) [34,68,288,160,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9217

theorem m19533_136 : Upper (D 8) (R 8) [34,68,288,160,136] 13 :=
  permutation_upper _ _ _ [34,68,288,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9220

def r19533 : Route 9 := (fun mask => (mask,id))

def c19533 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19533 : Upper (D 8) (R 8) [34,68,288,160] 13 := by
  apply FastRouting.sound _ _ [34,68,288,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r19533 c19533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19533_9
  · exact m19533_65
  · exact m19533_72
  · exact m19533_129
  · exact m19533_136
  · exact u9222

theorem m19534_9 : Upper (D 8) (R 8) [34,68,288,192,9] 13 :=
  permutation_upper _ _ _ [34,68,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9197

theorem m19534_33 : Upper (D 8) (R 8) [34,68,288,192,33] 13 :=
  permutation_upper _ _ _ [34,68,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9201

theorem m19534_40 : Upper (D 8) (R 8) [34,68,288,192,40] 13 :=
  permutation_upper _ _ _ [34,68,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9206

theorem m19534_129 : Upper (D 8) (R 8) [34,68,288,192,129] 13 :=
  permutation_upper _ _ _ [34,68,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9218

theorem m19534_136 : Upper (D 8) (R 8) [34,68,288,192,136] 13 :=
  permutation_upper _ _ _ [34,68,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9221

theorem m19534_160 : Upper (D 8) (R 8) [34,68,288,192,160] 13 :=
  permutation_upper _ _ _ [34,68,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9222

def r19534 : Route 9 := (fun mask => (mask,id))

def c19534 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19534 : Upper (D 8) (R 8) [34,68,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,288,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19534 c19534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19534_9
  · exact m19534_33
  · exact m19534_40
  · exact m19534_129
  · exact m19534_136
  · exact m19534_160

def r19535 : Route 9 := (fun mask => (mask,id))

def c19535 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19535 : Upper (D 8) (R 8) [34,68,384,17] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19535 c19535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9223
  · exact u9224
  · exact u9225
  · exact u9226
  · exact u9227
  · exact u9228
  · exact u9229
  · exact u9230
  · exact u9231
  · exact u9232

def b19536 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 388 41 249 249 249 249 505), lower := (rows 35 70 388 41 16 32 64 128 256), losses := [] }

theorem u19536 : Upper (D 8) (R 8) [34,68,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19537_9 : Upper (D 8) (R 8) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9225

theorem m19537_33 : Upper (D 8) (R 8) [34,68,384,48,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9233

def r19537 : Route 9 := (fun mask => (mask,id))

def c19537 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19537 : Upper (D 8) (R 8) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19537 c19537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19537_9
  · exact m19537_33
  · exact u9239
  · exact u9240
  · exact u9241
  · exact u9242
  · exact u9243
  · exact u9244
  · exact u9245
  · exact u9246

def b19538 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 185 185 249 185 441), lower := (rows 35 70 388 73 16 32 64 128 256), losses := [] }

theorem u19538 : Upper (D 8) (R 8) [34,68,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19539_9 : Upper (D 8) (R 8) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9227

theorem m19539_33 : Upper (D 8) (R 8) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9234

theorem m19539_40 : Upper (D 8) (R 8) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9241

def r19539 : Route 9 := (fun mask => (mask,id))

def c19539 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19539 : Upper (D 8) (R 8) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19539 c19539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19539_9
  · exact m19539_33
  · exact m19539_40
  · exact u9249
  · exact u9250
  · exact u9251

theorem m19540_9 : Upper (D 8) (R 8) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9228

theorem m19540_33 : Upper (D 8) (R 8) [34,68,384,96,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9235

theorem m19540_40 : Upper (D 8) (R 8) [34,68,384,96,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9242

def r19540 : Route 9 := (fun mask => (mask,id))

def c19540 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19540 : Upper (D 8) (R 8) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19540 c19540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19540_9
  · exact m19540_33
  · exact m19540_40
  · exact u9252
  · exact u9253
  · exact u9254

def b19541 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 388 137 121 121 121 249 377), lower := (rows 35 70 388 137 16 32 64 128 256), losses := [] }

theorem u19541 : Upper (D 8) (R 8) [34,68,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19542_9 : Upper (D 8) (R 8) [34,68,384,144,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9230

theorem m19542_33 : Upper (D 8) (R 8) [34,68,384,144,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9236

theorem m19542_40 : Upper (D 8) (R 8) [34,68,384,144,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9244

theorem m19542_65 : Upper (D 8) (R 8) [34,68,384,144,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9247

theorem m19542_72 : Upper (D 8) (R 8) [34,68,384,144,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9250

theorem m19542_96 : Upper (D 8) (R 8) [34,68,384,144,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9253

def r19542 : Route 9 := (fun mask => (mask,id))

def c19542 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19542 : Upper (D 8) (R 8) [34,68,384,144] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19542 c19542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19542_9
  · exact m19542_33
  · exact m19542_40
  · exact m19542_65
  · exact m19542_72
  · exact m19542_96

theorem m19543_9 : Upper (D 8) (R 8) [34,68,384,160,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9231

theorem m19543_33 : Upper (D 8) (R 8) [34,68,384,160,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9237

theorem m19543_40 : Upper (D 8) (R 8) [34,68,384,160,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9245

theorem m19543_65 : Upper (D 8) (R 8) [34,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9248

theorem m19543_72 : Upper (D 8) (R 8) [34,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9251

theorem m19543_96 : Upper (D 8) (R 8) [34,68,384,160,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9254

def r19543 : Route 9 := (fun mask => (mask,id))

def c19543 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19543 : Upper (D 8) (R 8) [34,68,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19543 c19543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19543_9
  · exact m19543_33
  · exact m19543_40
  · exact m19543_65
  · exact m19543_72
  · exact m19543_96

theorem m19544_9 : Upper (D 8) (R 8) [34,68,384,192,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9232

theorem m19544_33 : Upper (D 8) (R 8) [34,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9238

theorem m19544_40 : Upper (D 8) (R 8) [34,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9246

def r19544 : Route 9 := (fun mask => (mask,id))

def c19544 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19544 : Upper (D 8) (R 8) [34,68,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,192] 13 (by decide) (choices 2) [9,33,40] r19544 c19544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19544_9
  · exact m19544_33
  · exact m19544_40

def b19545 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 496 496 496 496 496), lower := (rows 35 194 13 13 16 32 64 128 256), losses := [] }

theorem u19545 : Upper (D 8) (R 8) [34,192,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19546 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 500 484 484 484 484), lower := (rows 35 194 13 25 16 32 64 128 256), losses := [] }

theorem u19546 : Upper (D 8) (R 8) [34,192,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19547 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19547 : Upper (D 8) (R 8) [34,192,9,20] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r19547 c19547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9264
  · exact u9265
  · exact u9266
  · exact u9267
  · exact u9268
  · exact u9269
  · exact u9270

def b19548 : PairBound 9 := { available := 500, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 500 500 500 500 500), lower := (rows 35 194 13 41 16 32 64 128 256), losses := [] }

theorem u19548 : Upper (D 8) (R 8) [34,192,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19549 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 497 497 497 497 497), lower := (rows 35 194 13 44 16 32 64 128 256), losses := [] }

theorem u19549 : Upper (D 8) (R 8) [34,192,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19550_5 : Upper (D 8) (R 8) [34,192,9,48,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9258

def r19550 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19550 : Upper (D 8) (R 8) [34,192,9,48] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r19550 c19550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19550_5
  · exact u9281
  · exact u9282
  · exact u9283
  · exact u9284
  · exact u9285
  · exact u9286
  · exact u9287
  · exact u9288
  · exact u9289
  · exact u9290

def b19551 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 73 436 436 500 436 436), lower := (rows 35 194 13 73 16 32 64 128 256), losses := [] }

theorem u19551 : Upper (D 8) (R 8) [34,192,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19552 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 433 433 497 433 433), lower := (rows 35 194 13 76 16 32 64 128 256), losses := [] }

theorem u19552 : Upper (D 8) (R 8) [34,192,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19553 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 437 421 485 421 421), lower := (rows 35 194 13 88 16 32 64 128 256), losses := [] }

theorem u19553 : Upper (D 8) (R 8) [34,192,9,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19554 : PairBound 9 := { available := 437, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 104 437 437 501 437 437), lower := (rows 35 194 13 104 16 32 64 128 256), losses := [] }

theorem u19554 : Upper (D 8) (R 8) [34,192,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19555 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 194 13 200 309 309 373 437 309), lower := (rows 35 194 13 200 16 32 64 128 256), losses := [] }

theorem u19555 : Upper (D 8) (R 8) [34,192,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19556 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 265 244 244 244 244 500), lower := (rows 35 194 13 265 16 32 64 128 256), losses := [] }

theorem u19556 : Upper (D 8) (R 8) [34,192,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19557 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19557 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19557 : Upper (D 8) (R 8) [34,192,9,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260] 13 (by decide) (choices 2) [33,65,96,192] r19557 c19557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9322
  · exact u9323
  · exact u9324
  · exact u9325

theorem m19558_5 : Upper (D 8) (R 8) [34,192,9,272,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9261

def r19558 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19558 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19558 : Upper (D 8) (R 8) [34,192,9,272] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r19558 c19558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19558_5
  · exact u9326
  · exact u9327
  · exact u9328
  · exact u9329
  · exact u9330
  · exact u9331

theorem m19559_5 : Upper (D 8) (R 8) [34,192,9,288,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9262

def r19559 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19559 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19559 : Upper (D 8) (R 8) [34,192,9,288] 13 := by
  apply FastRouting.sound _ _ [34,192,9,288] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r19559 c19559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19559_5
  · exact u9332
  · exact u9333
  · exact u9334
  · exact u9335
  · exact u9336
  · exact u9337

#print axioms u19559
end Delivery.IrregularNine14.P08
