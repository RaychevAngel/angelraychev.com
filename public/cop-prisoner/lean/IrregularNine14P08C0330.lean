import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0163
import IrregularNine14P08C0164
import IrregularNine14P08C0165
import IrregularNine14P08C0166
import IrregularNine14P08C0167

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m19800_9 : Upper (D 8) (R 8) [34,320,96,132,9] 13 :=
  permutation_upper _ _ _ [34,320,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9802

theorem m19800_33 : Upper (D 8) (R 8) [34,320,96,132,33] 13 :=
  permutation_upper _ _ _ [34,320,33,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9864

theorem m19800_40 : Upper (D 8) (R 8) [34,320,96,132,40] 13 :=
  permutation_upper _ _ _ [34,320,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9901

theorem m19800_129 : Upper (D 8) (R 8) [34,320,96,132,129] 13 :=
  permutation_upper _ _ _ [34,320,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9928

def r19800 : Route 9 := (fun mask => (mask,id))

def c19800 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19800 : Upper (D 8) (R 8) [34,320,96,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19800 c19800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19800_9
  · exact m19800_33
  · exact m19800_40
  · exact m19800_129
  · exact u9931
  · exact u9932

theorem m19801_5 : Upper (D 8) (R 8) [34,320,96,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9784

theorem m19801_9 : Upper (D 8) (R 8) [34,320,96,144,9] 13 :=
  permutation_upper _ _ _ [34,320,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9794

theorem m19801_12 : Upper (D 8) (R 8) [34,320,96,144,12] 13 :=
  permutation_upper _ _ _ [34,320,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9837

theorem m19801_33 : Upper (D 8) (R 8) [34,320,96,144,33] 13 :=
  permutation_upper _ _ _ [34,320,33,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9863

theorem m19801_36 : Upper (D 8) (R 8) [34,320,96,144,36] 13 :=
  permutation_upper _ _ _ [34,320,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9886

theorem m19801_40 : Upper (D 8) (R 8) [34,320,96,144,40] 13 :=
  permutation_upper _ _ _ [34,320,40,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9895

theorem m19801_129 : Upper (D 8) (R 8) [34,320,96,144,129] 13 :=
  permutation_upper _ _ _ [34,320,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9929

theorem m19801_132 : Upper (D 8) (R 8) [34,320,96,144,132] 13 :=
  permutation_upper _ _ _ [34,320,96,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9931

def r19801 : Route 9 := (fun mask => (mask,id))

def c19801 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19801 : Upper (D 8) (R 8) [34,320,96,144] 13 := by
  apply FastRouting.sound _ _ [34,320,96,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r19801 c19801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19801_5
  · exact m19801_9
  · exact m19801_12
  · exact m19801_33
  · exact m19801_36
  · exact m19801_40
  · exact m19801_129
  · exact m19801_132
  · exact u9933
  · exact u9934

theorem m19802_5 : Upper (D 8) (R 8) [34,320,96,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9785

theorem m19802_9 : Upper (D 8) (R 8) [34,320,96,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9811

theorem m19802_12 : Upper (D 8) (R 8) [34,320,96,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9838

theorem m19802_129 : Upper (D 8) (R 8) [34,320,96,160,129] 13 :=
  permutation_upper _ _ _ [34,320,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9930

theorem m19802_132 : Upper (D 8) (R 8) [34,320,96,160,132] 13 :=
  permutation_upper _ _ _ [34,320,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9932

theorem m19802_136 : Upper (D 8) (R 8) [34,320,96,160,136] 13 :=
  permutation_upper _ _ _ [34,320,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9934

def r19802 : Route 9 := (fun mask => (mask,id))

def c19802 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19802 : Upper (D 8) (R 8) [34,320,96,160] 13 := by
  apply FastRouting.sound _ _ [34,320,96,160] 13 (by decide) (choices 2) [5,9,12,129,132,136] r19802 c19802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19802_5
  · exact m19802_9
  · exact m19802_12
  · exact m19802_129
  · exact m19802_132
  · exact m19802_136

def b19803 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 322 133 137 124 124 124 252 380), lower := (rows 35 322 133 137 16 32 64 128 256), losses := [] }

theorem u19803 : Upper (D 8) (R 8) [34,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19804 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 133 140 121 121 121 249 377), lower := (rows 35 322 133 140 16 32 64 128 256), losses := [] }

theorem u19804 : Upper (D 8) (R 8) [34,320,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19805_5 : Upper (D 8) (R 8) [34,320,129,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9789

theorem m19805_9 : Upper (D 8) (R 8) [34,320,129,144,9] 13 :=
  permutation_upper _ _ _ [34,320,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9795

theorem m19805_12 : Upper (D 8) (R 8) [34,320,129,144,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9840

theorem m19805_33 : Upper (D 8) (R 8) [34,320,129,144,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9865

theorem m19805_36 : Upper (D 8) (R 8) [34,320,129,144,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9891

theorem m19805_40 : Upper (D 8) (R 8) [34,320,129,144,40] 13 :=
  permutation_upper _ _ _ [34,320,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9896

theorem m19805_65 : Upper (D 8) (R 8) [34,320,129,144,65] 13 :=
  permutation_upper _ _ _ [34,320,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9913

theorem m19805_68 : Upper (D 8) (R 8) [34,320,129,144,68] 13 :=
  permutation_upper _ _ _ [34,320,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9917

theorem m19805_72 : Upper (D 8) (R 8) [34,320,129,144,72] 13 :=
  permutation_upper _ _ _ [34,320,72,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9919

theorem m19805_96 : Upper (D 8) (R 8) [34,320,129,144,96] 13 :=
  permutation_upper _ _ _ [34,320,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9928

def r19805 : Route 9 := (fun mask => (mask,id))

def c19805 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19805 : Upper (D 8) (R 8) [34,320,129,144] 13 := by
  apply FastRouting.sound _ _ [34,320,129,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r19805 c19805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19805_5
  · exact m19805_9
  · exact m19805_12
  · exact m19805_33
  · exact m19805_36
  · exact m19805_40
  · exact m19805_65
  · exact m19805_68
  · exact m19805_72
  · exact m19805_96

theorem m19806_5 : Upper (D 8) (R 8) [34,320,129,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9790

theorem m19806_9 : Upper (D 8) (R 8) [34,320,129,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9812

theorem m19806_12 : Upper (D 8) (R 8) [34,320,129,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9841

theorem m19806_33 : Upper (D 8) (R 8) [34,320,129,160,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9866

theorem m19806_36 : Upper (D 8) (R 8) [34,320,129,160,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9892

theorem m19806_40 : Upper (D 8) (R 8) [34,320,129,160,40] 13 :=
  permutation_upper _ _ _ [34,320,40,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9907

theorem m19806_65 : Upper (D 8) (R 8) [34,320,129,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9914

theorem m19806_68 : Upper (D 8) (R 8) [34,320,129,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9918

theorem m19806_72 : Upper (D 8) (R 8) [34,320,129,160,72] 13 :=
  permutation_upper _ _ _ [34,320,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9924

theorem m19806_96 : Upper (D 8) (R 8) [34,320,129,160,96] 13 :=
  permutation_upper _ _ _ [34,320,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9930

def r19806 : Route 9 := (fun mask => (mask,id))

def c19806 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19806 : Upper (D 8) (R 8) [34,320,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,129,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r19806 c19806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19806_5
  · exact m19806_9
  · exact m19806_12
  · exact m19806_33
  · exact m19806_36
  · exact m19806_40
  · exact m19806_65
  · exact m19806_68
  · exact m19806_72
  · exact m19806_96

theorem m19807_5 : Upper (D 8) (R 8) [34,320,129,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9791

theorem m19807_9 : Upper (D 8) (R 8) [34,320,129,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9817

theorem m19807_12 : Upper (D 8) (R 8) [34,320,129,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9842

theorem m19807_33 : Upper (D 8) (R 8) [34,320,129,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9867

theorem m19807_36 : Upper (D 8) (R 8) [34,320,129,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9893

theorem m19807_40 : Upper (D 8) (R 8) [34,320,129,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9910

def r19807 : Route 9 := (fun mask => (mask,id))

def c19807 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19807 : Upper (D 8) (R 8) [34,320,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,129,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r19807 c19807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19807_5
  · exact m19807_9
  · exact m19807_12
  · exact m19807_33
  · exact m19807_36
  · exact m19807_40

def b19808 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 140 140 113 113 113 241 369), lower := (rows 35 322 140 140 16 32 64 128 256), losses := [] }

theorem u19808 : Upper (D 8) (R 8) [34,320,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19809 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 152 117 101 101 229 357), lower := (rows 35 322 140 152 16 32 64 128 256), losses := [] }

theorem u19809 : Upper (D 8) (R 8) [34,320,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19810 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 168 117 117 117 245 373), lower := (rows 35 322 140 168 16 32 64 128 256), losses := [] }

theorem u19810 : Upper (D 8) (R 8) [34,320,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19811 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 200 53 53 117 181 309), lower := (rows 35 322 140 200 16 32 64 128 256), losses := [] }

theorem u19811 : Upper (D 8) (R 8) [34,320,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19812_5 : Upper (D 8) (R 8) [34,320,144,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9796

theorem m19812_9 : Upper (D 8) (R 8) [34,320,144,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9813

theorem m19812_12 : Upper (D 8) (R 8) [34,320,144,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9843

theorem m19812_33 : Upper (D 8) (R 8) [34,320,144,160,33] 13 :=
  permutation_upper _ _ _ [34,320,33,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9868

theorem m19812_36 : Upper (D 8) (R 8) [34,320,144,160,36] 13 :=
  permutation_upper _ _ _ [34,320,40,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9897

theorem m19812_40 : Upper (D 8) (R 8) [34,320,144,160,40] 13 :=
  permutation_upper _ _ _ [34,320,40,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9908

theorem m19812_65 : Upper (D 8) (R 8) [34,320,144,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9915

theorem m19812_68 : Upper (D 8) (R 8) [34,320,144,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9920

theorem m19812_72 : Upper (D 8) (R 8) [34,320,144,160,72] 13 :=
  permutation_upper _ _ _ [34,320,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9925

theorem m19812_96 : Upper (D 8) (R 8) [34,320,144,160,96] 13 :=
  permutation_upper _ _ _ [34,320,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9932

def r19812 : Route 9 := (fun mask => (mask,id))

def c19812 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19812 : Upper (D 8) (R 8) [34,320,144,160] 13 := by
  apply FastRouting.sound _ _ [34,320,144,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r19812 c19812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19812_5
  · exact m19812_9
  · exact m19812_12
  · exact m19812_33
  · exact m19812_36
  · exact m19812_40
  · exact m19812_65
  · exact m19812_68
  · exact m19812_72
  · exact m19812_96

theorem m19813_5 : Upper (D 8) (R 8) [34,320,144,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9797

theorem m19813_9 : Upper (D 8) (R 8) [34,320,144,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9818

theorem m19813_12 : Upper (D 8) (R 8) [34,320,144,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9844

theorem m19813_33 : Upper (D 8) (R 8) [34,320,144,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9869

theorem m19813_36 : Upper (D 8) (R 8) [34,320,144,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9898

theorem m19813_40 : Upper (D 8) (R 8) [34,320,144,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9911

def r19813 : Route 9 := (fun mask => (mask,id))

def c19813 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19813 : Upper (D 8) (R 8) [34,320,144,192] 13 := by
  apply FastRouting.sound _ _ [34,320,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r19813 c19813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19813_5
  · exact m19813_9
  · exact m19813_12
  · exact m19813_33
  · exact m19813_36
  · exact m19813_40

def b19814 : PairBound 9 := { available := 93, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 164 168 93 125 93 221 349), lower := (rows 35 322 164 168 16 32 64 128 256), losses := [] }

theorem u19814 : Upper (D 8) (R 8) [34,320,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19815_5 : Upper (D 8) (R 8) [34,320,160,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9815

theorem m19815_9 : Upper (D 8) (R 8) [34,320,160,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9819

theorem m19815_12 : Upper (D 8) (R 8) [34,320,160,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9846

theorem m19815_33 : Upper (D 8) (R 8) [34,320,160,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9870

theorem m19815_36 : Upper (D 8) (R 8) [34,320,160,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9909

theorem m19815_40 : Upper (D 8) (R 8) [34,320,160,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9912

def r19815 : Route 9 := (fun mask => (mask,id))

def c19815 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19815 : Upper (D 8) (R 8) [34,320,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,160,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r19815 c19815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19815_5
  · exact m19815_9
  · exact m19815_12
  · exact m19815_33
  · exact m19815_36
  · exact m19815_40

def b19816 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 41 496 480 480 480 480), lower := (rows 67 7 28 41 16 32 64 128 256), losses := [] }

theorem u19816 : Upper (D 8) (R 8) [66,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19817 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 28 73 432 416 480 416 416), lower := (rows 67 7 28 73 16 32 64 128 256), losses := [] }

theorem u19817 : Upper (D 8) (R 8) [66,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19818 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 104 433 417 481 417 417), lower := (rows 67 7 28 104 16 32 64 128 256), losses := [] }

theorem u19818 : Upper (D 8) (R 8) [66,5,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19819 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 137 496 480 480 480 480), lower := (rows 67 7 28 137 16 32 64 128 256), losses := [] }

theorem u19819 : Upper (D 8) (R 8) [66,5,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19820_33 : Upper (D 8) (R 8) [66,5,24,160,33] 13 :=
  permutation_upper _ _ _ [66,5,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9935

theorem m19820_65 : Upper (D 8) (R 8) [66,5,24,160,65] 13 :=
  permutation_upper _ _ _ [66,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9938

theorem m19820_96 : Upper (D 8) (R 8) [66,5,24,160,96] 13 :=
  permutation_upper _ _ _ [66,5,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9941

theorem m19820_129 : Upper (D 8) (R 8) [66,5,24,160,129] 13 :=
  permutation_upper _ _ _ [66,5,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9944

def r19820 : Route 9 := (fun mask => (mask,id))

def c19820 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19820 : Upper (D 8) (R 8) [66,5,24,160] 13 := by
  apply FastRouting.sound _ _ [66,5,24,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19820 c19820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19820_33
  · exact m19820_65
  · exact m19820_96
  · exact m19820_129
  · exact u9947
  · exact u9948
  · exact u9949
  · exact u9950
  · exact u9951
  · exact u9952

def b19821 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 200 433 417 481 417 417), lower := (rows 67 7 28 200 16 32 64 128 256), losses := [] }

theorem u19821 : Upper (D 8) (R 8) [66,5,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19822 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 265 240 224 224 224 480), lower := (rows 67 7 28 265 16 32 64 128 256), losses := [] }

theorem u19822 : Upper (D 8) (R 8) [66,5,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19823_33 : Upper (D 8) (R 8) [66,5,24,288,33] 13 :=
  permutation_upper _ _ _ [66,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9936

theorem m19823_65 : Upper (D 8) (R 8) [66,5,24,288,65] 13 :=
  permutation_upper _ _ _ [66,5,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9939

theorem m19823_96 : Upper (D 8) (R 8) [66,5,24,288,96] 13 :=
  permutation_upper _ _ _ [66,5,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9942

theorem m19823_129 : Upper (D 8) (R 8) [66,5,24,288,129] 13 :=
  permutation_upper _ _ _ [66,5,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9945

theorem m19823_160 : Upper (D 8) (R 8) [66,5,24,288,160] 13 :=
  permutation_upper _ _ _ [66,5,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9950

theorem m19823_192 : Upper (D 8) (R 8) [66,5,24,288,192] 13 :=
  permutation_upper _ _ _ [66,5,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9953

def r19823 : Route 9 := (fun mask => (mask,id))

def c19823 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19823 : Upper (D 8) (R 8) [66,5,24,288] 13 := by
  apply FastRouting.sound _ _ [66,5,24,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19823 c19823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19823_33
  · exact m19823_65
  · exact m19823_96
  · exact m19823_129
  · exact m19823_160
  · exact m19823_192

def b19824 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 28 328 177 161 225 161 417), lower := (rows 67 7 28 328 16 32 64 128 256), losses := [] }

theorem u19824 : Upper (D 8) (R 8) [66,5,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19825_33 : Upper (D 8) (R 8) [66,5,24,384,33] 13 :=
  permutation_upper _ _ _ [66,5,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9937

theorem m19825_65 : Upper (D 8) (R 8) [66,5,24,384,65] 13 :=
  permutation_upper _ _ _ [66,5,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9940

theorem m19825_96 : Upper (D 8) (R 8) [66,5,24,384,96] 13 :=
  permutation_upper _ _ _ [66,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9943

theorem m19825_129 : Upper (D 8) (R 8) [66,5,24,384,129] 13 :=
  permutation_upper _ _ _ [66,5,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9946

theorem m19825_160 : Upper (D 8) (R 8) [66,5,24,384,160] 13 :=
  permutation_upper _ _ _ [66,5,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9952

theorem m19825_192 : Upper (D 8) (R 8) [66,5,24,384,192] 13 :=
  permutation_upper _ _ _ [66,5,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9954

def r19825 : Route 9 := (fun mask => (mask,id))

def c19825 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19825 : Upper (D 8) (R 8) [66,5,24,384] 13 := by
  apply FastRouting.sound _ _ [66,5,24,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19825 c19825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19825_33
  · exact m19825_65
  · exact m19825_96
  · exact m19825_129
  · exact m19825_160
  · exact m19825_192

def b19826 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 25 496 480 480 480 480), lower := (rows 67 7 44 25 16 32 64 128 256), losses := [] }

theorem u19826 : Upper (D 8) (R 8) [66,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19827 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 44 41 496 496 496 496 496), lower := (rows 67 7 44 41 16 32 64 128 256), losses := [] }

theorem u19827 : Upper (D 8) (R 8) [66,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19828 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 56 497 481 481 481 481), lower := (rows 67 7 44 56 16 32 64 128 256), losses := [] }

theorem u19828 : Upper (D 8) (R 8) [66,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19829 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 44 73 432 432 496 432 432), lower := (rows 67 7 44 73 16 32 64 128 256), losses := [] }

theorem u19829 : Upper (D 8) (R 8) [66,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19830 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 44 88 433 417 481 417 417), lower := (rows 67 7 44 88 16 32 64 128 256), losses := [] }

theorem u19830 : Upper (D 8) (R 8) [66,5,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19831 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 104 433 433 497 433 433), lower := (rows 67 7 44 104 16 32 64 128 256), losses := [] }

theorem u19831 : Upper (D 8) (R 8) [66,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19832 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 137 496 496 496 496 496), lower := (rows 67 7 44 137 16 32 64 128 256), losses := [] }

theorem u19832 : Upper (D 8) (R 8) [66,5,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19833 : Route 9 := (fun mask => (mask,id))

def c19833 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19833 : Upper (D 8) (R 8) [66,5,40,144] 13 := by
  apply FastRouting.sound _ _ [66,5,40,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19833 c19833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9955
  · exact u9956
  · exact u9957
  · exact u9958
  · exact u9959
  · exact u9960
  · exact u9961
  · exact u9962
  · exact u9963
  · exact u9964

def b19834 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 168 497 497 497 497 497), lower := (rows 67 7 44 168 16 32 64 128 256), losses := [] }

theorem u19834 : Upper (D 8) (R 8) [66,5,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19835 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 44 200 433 433 497 433 433), lower := (rows 67 7 44 200 16 32 64 128 256), losses := [] }

theorem u19835 : Upper (D 8) (R 8) [66,5,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19836 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 265 240 240 240 240 496), lower := (rows 67 7 44 265 16 32 64 128 256), losses := [] }

theorem u19836 : Upper (D 8) (R 8) [66,5,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19837 : Route 9 := (fun mask => (mask,id))

def c19837 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19837 : Upper (D 8) (R 8) [66,5,40,272] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19837 c19837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9965
  · exact u9966
  · exact u9967
  · exact u9968
  · exact u9969
  · exact u9970

def b19838 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 296 241 241 241 241 497), lower := (rows 67 7 44 296 16 32 64 128 256), losses := [] }

theorem u19838 : Upper (D 8) (R 8) [66,5,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19839 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 44 328 177 177 241 177 433), lower := (rows 67 7 44 328 16 32 64 128 256), losses := [] }

theorem u19839 : Upper (D 8) (R 8) [66,5,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19840 : Route 9 := (fun mask => (mask,id))

def c19840 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19840 : Upper (D 8) (R 8) [66,5,40,384] 13 := by
  apply FastRouting.sound _ _ [66,5,40,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19840 c19840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9971
  · exact u9972
  · exact u9973
  · exact u9974
  · exact u9975
  · exact u9976

def b19841 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 25 496 480 480 480 480), lower := (rows 67 7 140 25 16 32 64 128 256), losses := [] }

theorem u19841 : Upper (D 8) (R 8) [66,5,136,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19842 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 41 496 496 496 496 496), lower := (rows 67 7 140 41 16 32 64 128 256), losses := [] }

theorem u19842 : Upper (D 8) (R 8) [66,5,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19843 : Route 9 := (fun mask => (mask,id))

def c19843 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19843 : Upper (D 8) (R 8) [66,5,136,48] 13 := by
  apply FastRouting.sound _ _ [66,5,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19843 c19843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9977
  · exact u9978
  · exact u9979
  · exact u9980
  · exact u9981
  · exact u9982
  · exact u9983
  · exact u9984
  · exact u9985
  · exact u9986

def b19844 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 140 73 432 432 496 432 432), lower := (rows 67 7 140 73 16 32 64 128 256), losses := [] }

theorem u19844 : Upper (D 8) (R 8) [66,5,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19845 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 140 88 433 417 481 417 417), lower := (rows 67 7 140 88 16 32 64 128 256), losses := [] }

theorem u19845 : Upper (D 8) (R 8) [66,5,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19846 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 140 104 433 433 497 433 433), lower := (rows 67 7 140 104 16 32 64 128 256), losses := [] }

theorem u19846 : Upper (D 8) (R 8) [66,5,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19847 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 67 7 140 137 368 368 368 496 368), lower := (rows 67 7 140 137 16 32 64 128 256), losses := [] }

theorem u19847 : Upper (D 8) (R 8) [66,5,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19848 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 152 369 353 353 481 353), lower := (rows 67 7 140 152 16 32 64 128 256), losses := [] }

theorem u19848 : Upper (D 8) (R 8) [66,5,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19849 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 168 369 369 369 497 369), lower := (rows 67 7 140 168 16 32 64 128 256), losses := [] }

theorem u19849 : Upper (D 8) (R 8) [66,5,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19850 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 200 305 305 369 433 305), lower := (rows 67 7 140 200 16 32 64 128 256), losses := [] }

theorem u19850 : Upper (D 8) (R 8) [66,5,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19851 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 140 265 240 240 240 240 496), lower := (rows 67 7 140 265 16 32 64 128 256), losses := [] }

theorem u19851 : Upper (D 8) (R 8) [66,5,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19852 : Route 9 := (fun mask => (mask,id))

def c19852 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19852 : Upper (D 8) (R 8) [66,5,136,272] 13 := by
  apply FastRouting.sound _ _ [66,5,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19852 c19852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9987
  · exact u9988
  · exact u9989
  · exact u9990
  · exact u9991
  · exact u9992

def r19853 : Route 9 := (fun mask => (mask,id))

def c19853 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19853 : Upper (D 8) (R 8) [66,5,136,288] 13 := by
  apply FastRouting.sound _ _ [66,5,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19853 c19853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9993
  · exact u9994
  · exact u9995
  · exact u9996
  · exact u9997
  · exact u9998

def b19854 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 67 7 140 328 177 177 241 177 433), lower := (rows 67 7 140 328 16 32 64 128 256), losses := [] }

theorem u19854 : Upper (D 8) (R 8) [66,5,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19855 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 140 392 113 113 113 241 369), lower := (rows 67 7 140 392 16 32 64 128 256), losses := [] }

theorem u19855 : Upper (D 8) (R 8) [66,5,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19856 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 25 504 488 488 488 488), lower := (rows 67 7 164 25 16 32 64 128 256), losses := [] }

theorem u19856 : Upper (D 8) (R 8) [66,5,160,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19857 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 164 41 504 504 504 504 504), lower := (rows 67 7 164 41 16 32 64 128 256), losses := [] }

theorem u19857 : Upper (D 8) (R 8) [66,5,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19858_9 : Upper (D 8) (R 8) [66,5,160,48,9] 13 :=
  permutation_upper _ _ _ [66,5,160,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9999

theorem m19858_33 : Upper (D 8) (R 8) [66,5,160,48,33] 13 :=
  permutation_upper _ _ _ [66,5,160,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10008

def r19858 : Route 9 := (fun mask => (mask,id))

def c19858 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19858 : Upper (D 8) (R 8) [66,5,160,48] 13 := by
  apply FastRouting.sound _ _ [66,5,160,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r19858 c19858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19858_9
  · exact m19858_33
  · exact u10017
  · exact u10018
  · exact u10019
  · exact u10020
  · exact u10021
  · exact u10022
  · exact u10023
  · exact u10024
  · exact u10025
  · exact u10026
  · exact u10027
  · exact u10028
  · exact u10029

def b19859 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 7 164 73 440 440 504 440 440), lower := (rows 67 7 164 73 16 32 64 128 256), losses := [] }

theorem u19859 : Upper (D 8) (R 8) [66,5,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19859
end Delivery.IrregularNine14.P08
