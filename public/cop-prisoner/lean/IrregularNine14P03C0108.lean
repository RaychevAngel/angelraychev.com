import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0064
import IrregularNine14P03C0065
import IrregularNine14P03C0066

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6480 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 28 44 209 225 193 193 449), lower := (rows 35 322 28 44 16 32 64 128 256), losses := [] }

theorem u6480 : Upper (D 3) (R 3) [34,320,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6481 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 181 165 229 165 421), lower := (rows 35 322 28 73 16 32 64 128 256), losses := [] }

theorem u6481 : Upper (D 3) (R 3) [34,320,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6481
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 76 177 161 225 161 417), lower := (rows 35 322 28 76 16 32 64 128 256), losses := [] }

theorem u6482 : Upper (D 3) (R 3) [34,320,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6482
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6483_5 : Upper (D 3) (R 3) [34,320,24,96,5] 13 :=
  permutation_upper _ _ _ [34,320,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3891

def r6483 : Route 9 := (fun mask => (mask,id))

def c6483 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6483 : Upper (D 3) (R 3) [34,320,24,96] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96] 13 (by decide) (choices 2) [5,129,132] r6483 c6483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6483_5
  · exact u3957
  · exact u3958

theorem m6484_5 : Upper (D 3) (R 3) [34,320,24,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3892

theorem m6484_33 : Upper (D 3) (R 3) [34,320,24,129,33] 13 :=
  permutation_upper _ _ _ [34,320,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3947

theorem m6484_36 : Upper (D 3) (R 3) [34,320,24,129,36] 13 :=
  permutation_upper _ _ _ [34,320,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3950

theorem m6484_65 : Upper (D 3) (R 3) [34,320,24,129,65] 13 :=
  permutation_upper _ _ _ [34,320,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3952

theorem m6484_68 : Upper (D 3) (R 3) [34,320,24,129,68] 13 :=
  permutation_upper _ _ _ [34,320,24,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3955

theorem m6484_96 : Upper (D 3) (R 3) [34,320,24,129,96] 13 :=
  permutation_upper _ _ _ [34,320,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3957

def r6484 : Route 9 := (fun mask => (mask,id))

def c6484 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6484 : Upper (D 3) (R 3) [34,320,24,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,129] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6484 c6484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6484_5
  · exact m6484_33
  · exact m6484_36
  · exact m6484_65
  · exact m6484_68
  · exact m6484_96
  · exact u3959
  · exact u3960
  · exact u3961
  · exact u3962

theorem m6485_33 : Upper (D 3) (R 3) [34,320,24,132,33] 13 :=
  permutation_upper _ _ _ [34,320,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3948

theorem m6485_65 : Upper (D 3) (R 3) [34,320,24,132,65] 13 :=
  permutation_upper _ _ _ [34,320,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3953

theorem m6485_96 : Upper (D 3) (R 3) [34,320,24,132,96] 13 :=
  permutation_upper _ _ _ [34,320,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3958

theorem m6485_129 : Upper (D 3) (R 3) [34,320,24,132,129] 13 :=
  permutation_upper _ _ _ [34,320,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3960

def r6485 : Route 9 := (fun mask => (mask,id))

def c6485 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6485 : Upper (D 3) (R 3) [34,320,24,132] 13 := by
  apply FastRouting.sound _ _ [34,320,24,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6485 c6485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6485_33
  · exact m6485_65
  · exact m6485_96
  · exact m6485_129
  · exact u3963
  · exact u3964

theorem m6486_5 : Upper (D 3) (R 3) [34,320,24,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3893

theorem m6486_65 : Upper (D 3) (R 3) [34,320,24,160,65] 13 :=
  permutation_upper _ _ _ [34,320,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3954

theorem m6486_68 : Upper (D 3) (R 3) [34,320,24,160,68] 13 :=
  permutation_upper _ _ _ [34,320,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3956

theorem m6486_129 : Upper (D 3) (R 3) [34,320,24,160,129] 13 :=
  permutation_upper _ _ _ [34,320,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3961

theorem m6486_132 : Upper (D 3) (R 3) [34,320,24,160,132] 13 :=
  permutation_upper _ _ _ [34,320,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3963

def r6486 : Route 9 := (fun mask => (mask,id))

def c6486 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6486 : Upper (D 3) (R 3) [34,320,24,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,160] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6486 c6486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6486_5
  · exact m6486_65
  · exact m6486_68
  · exact m6486_129
  · exact m6486_132
  · exact u3965

theorem m6487_5 : Upper (D 3) (R 3) [34,320,24,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3894

theorem m6487_33 : Upper (D 3) (R 3) [34,320,24,192,33] 13 :=
  permutation_upper _ _ _ [34,320,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3949

theorem m6487_36 : Upper (D 3) (R 3) [34,320,24,192,36] 13 :=
  permutation_upper _ _ _ [34,320,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3951

theorem m6487_129 : Upper (D 3) (R 3) [34,320,24,192,129] 13 :=
  permutation_upper _ _ _ [34,320,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3962

theorem m6487_132 : Upper (D 3) (R 3) [34,320,24,192,132] 13 :=
  permutation_upper _ _ _ [34,320,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3964

theorem m6487_160 : Upper (D 3) (R 3) [34,320,24,192,160] 13 :=
  permutation_upper _ _ _ [34,320,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3965

def r6487 : Route 9 := (fun mask => (mask,id))

def c6487 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6487 : Upper (D 3) (R 3) [34,320,24,192] 13 := by
  apply FastRouting.sound _ _ [34,320,24,192] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6487 c6487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6487_5
  · exact m6487_33
  · exact m6487_36
  · exact m6487_129
  · exact m6487_132
  · exact m6487_160

def b6488 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 76 153 185 217 153 409), lower := (rows 35 322 37 76 16 32 64 128 256), losses := [] }

theorem u6488 : Upper (D 3) (R 3) [34,320,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6489 : PairBound 9 := { available := 221, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 137 221 253 221 221 477), lower := (rows 35 322 37 137 16 32 64 128 256), losses := [] }

theorem u6489 : Upper (D 3) (R 3) [34,320,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6490 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 140 217 249 217 217 473), lower := (rows 35 322 37 140 16 32 64 128 256), losses := [] }

theorem u6490 : Upper (D 3) (R 3) [34,320,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6491 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 37 200 157 189 221 157 413), lower := (rows 35 322 37 200 16 32 64 128 256), losses := [] }

theorem u6491 : Upper (D 3) (R 3) [34,320,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6492 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 73 149 181 213 149 405), lower := (rows 35 322 44 73 16 32 64 128 256), losses := [] }

theorem u6492 : Upper (D 3) (R 3) [34,320,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6492
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 76 145 177 209 145 401), lower := (rows 35 322 44 76 16 32 64 128 256), losses := [] }

theorem u6493 : Upper (D 3) (R 3) [34,320,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6493
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6494_5 : Upper (D 3) (R 3) [34,320,40,80,5] 13 :=
  permutation_upper _ _ _ [34,320,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3901

def r6494 : Route 9 := (fun mask => (mask,id))

def c6494 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6494 : Upper (D 3) (R 3) [34,320,40,80] 13 := by
  apply FastRouting.sound _ _ [34,320,40,80] 13 (by decide) (choices 2) [5,129,132] r6494 c6494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6494_5
  · exact u3976
  · exact u3977

theorem m6495_5 : Upper (D 3) (R 3) [34,320,40,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3902

def r6495 : Route 9 := (fun mask => (mask,id))

def c6495 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6495 : Upper (D 3) (R 3) [34,320,40,129] 13 := by
  apply FastRouting.sound _ _ [34,320,40,129] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6495 c6495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6495_5
  · exact u3978
  · exact u3979
  · exact u3980
  · exact u3981
  · exact u3982

def b6496 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 322 44 140 209 241 209 209 465), lower := (rows 35 322 44 140 16 32 64 128 256), losses := [] }

theorem u6496 : Upper (D 3) (R 3) [34,320,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6496
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6497_5 : Upper (D 3) (R 3) [34,320,40,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3903

def r6497 : Route 9 := (fun mask => (mask,id))

def c6497 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6497 : Upper (D 3) (R 3) [34,320,40,144] 13 := by
  apply FastRouting.sound _ _ [34,320,40,144] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6497 c6497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6497_5
  · exact u3985
  · exact u3986
  · exact u3987
  · exact u3988
  · exact u3989

theorem m6498_5 : Upper (D 3) (R 3) [34,320,40,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3904

def r6498 : Route 9 := (fun mask => (mask,id))

def c6498 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6498 : Upper (D 3) (R 3) [34,320,40,192] 13 := by
  apply FastRouting.sound _ _ [34,320,40,192] 13 (by decide) (choices 2) [5,129,132] r6498 c6498
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6498_5
  · exact u3990
  · exact u3991

theorem m6499_9 : Upper (D 3) (R 3) [34,320,48,68,9] 13 :=
  permutation_upper _ _ _ [34,320,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3911

theorem m6499_129 : Upper (D 3) (R 3) [34,320,48,68,129] 13 :=
  permutation_upper _ _ _ [34,320,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3979

theorem m6499_136 : Upper (D 3) (R 3) [34,320,48,68,136] 13 :=
  permutation_upper _ _ _ [34,320,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3986

def r6499 : Route 9 := (fun mask => (mask,id))

def c6499 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6499 : Upper (D 3) (R 3) [34,320,48,68] 13 := by
  apply FastRouting.sound _ _ [34,320,48,68] 13 (by decide) (choices 2) [9,129,136] r6499 c6499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6499_9
  · exact m6499_129
  · exact m6499_136

theorem m6500_5 : Upper (D 3) (R 3) [34,320,48,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3899

theorem m6500_9 : Upper (D 3) (R 3) [34,320,48,129,9] 13 :=
  permutation_upper _ _ _ [34,320,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3917

theorem m6500_12 : Upper (D 3) (R 3) [34,320,48,129,12] 13 :=
  permutation_upper _ _ _ [34,320,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3950

theorem m6500_65 : Upper (D 3) (R 3) [34,320,48,129,65] 13 :=
  permutation_upper _ _ _ [34,320,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3973

theorem m6500_68 : Upper (D 3) (R 3) [34,320,48,129,68] 13 :=
  permutation_upper _ _ _ [34,320,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3975

theorem m6500_72 : Upper (D 3) (R 3) [34,320,48,129,72] 13 :=
  permutation_upper _ _ _ [34,320,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3976

theorem m6500_129 : Upper (D 3) (R 3) [34,320,48,129,129] 13 :=
  permutation_upper _ _ _ [34,320,40,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3980

theorem m6500_132 : Upper (D 3) (R 3) [34,320,48,129,132] 13 :=
  permutation_upper _ _ _ [34,320,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3983

theorem m6500_136 : Upper (D 3) (R 3) [34,320,48,129,136] 13 :=
  permutation_upper _ _ _ [34,320,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3987

theorem m6500_192 : Upper (D 3) (R 3) [34,320,48,129,192] 13 :=
  permutation_upper _ _ _ [34,320,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3990

def r6500 : Route 9 := (fun mask => (mask,id))

def c6500 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6500 : Upper (D 3) (R 3) [34,320,48,129] 13 := by
  apply FastRouting.sound _ _ [34,320,48,129] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6500 c6500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6500_5
  · exact m6500_9
  · exact m6500_12
  · exact m6500_65
  · exact m6500_68
  · exact m6500_72
  · exact m6500_129
  · exact m6500_132
  · exact m6500_136
  · exact m6500_192

theorem m6501_9 : Upper (D 3) (R 3) [34,320,48,132,9] 13 :=
  permutation_upper _ _ _ [34,320,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3931

theorem m6501_65 : Upper (D 3) (R 3) [34,320,48,132,65] 13 :=
  permutation_upper _ _ _ [34,320,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3974

theorem m6501_72 : Upper (D 3) (R 3) [34,320,48,132,72] 13 :=
  permutation_upper _ _ _ [34,320,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3977

theorem m6501_129 : Upper (D 3) (R 3) [34,320,48,132,129] 13 :=
  permutation_upper _ _ _ [34,320,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3981

theorem m6501_136 : Upper (D 3) (R 3) [34,320,48,132,136] 13 :=
  permutation_upper _ _ _ [34,320,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3988

theorem m6501_192 : Upper (D 3) (R 3) [34,320,48,132,192] 13 :=
  permutation_upper _ _ _ [34,320,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3991

def r6501 : Route 9 := (fun mask => (mask,id))

def c6501 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6501 : Upper (D 3) (R 3) [34,320,48,132] 13 := by
  apply FastRouting.sound _ _ [34,320,48,132] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6501 c6501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6501_9
  · exact m6501_65
  · exact m6501_72
  · exact m6501_129
  · exact m6501_136
  · exact m6501_192

theorem m6502_5 : Upper (D 3) (R 3) [34,320,48,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3900

theorem m6502_9 : Upper (D 3) (R 3) [34,320,48,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3943

theorem m6502_12 : Upper (D 3) (R 3) [34,320,48,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3951

theorem m6502_129 : Upper (D 3) (R 3) [34,320,48,192,129] 13 :=
  permutation_upper _ _ _ [34,320,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3982

theorem m6502_132 : Upper (D 3) (R 3) [34,320,48,192,132] 13 :=
  permutation_upper _ _ _ [34,320,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3984

theorem m6502_136 : Upper (D 3) (R 3) [34,320,48,192,136] 13 :=
  permutation_upper _ _ _ [34,320,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3989

def r6502 : Route 9 := (fun mask => (mask,id))

def c6502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6502 : Upper (D 3) (R 3) [34,320,48,192] 13 := by
  apply FastRouting.sound _ _ [34,320,48,192] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6502 c6502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6502_5
  · exact m6502_9
  · exact m6502_12
  · exact m6502_129
  · exact m6502_132
  · exact m6502_136

def b6503 : PairBound 9 := { available := 189, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 137 189 189 253 189 445), lower := (rows 35 322 69 137 16 32 64 128 256), losses := [] }

theorem u6503 : Upper (D 3) (R 3) [34,320,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6503
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 140 185 185 249 185 441), lower := (rows 35 322 69 140 16 32 64 128 256), losses := [] }

theorem u6504 : Upper (D 3) (R 3) [34,320,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 168 157 189 221 157 413), lower := (rows 35 322 69 168 16 32 64 128 256), losses := [] }

theorem u6505 : Upper (D 3) (R 3) [34,320,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6505
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6506_5 : Upper (D 3) (R 3) [34,320,72,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3912

theorem m6506_33 : Upper (D 3) (R 3) [34,320,72,129,33] 13 :=
  permutation_upper _ _ _ [34,320,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3968

theorem m6506_36 : Upper (D 3) (R 3) [34,320,72,129,36] 13 :=
  permutation_upper _ _ _ [34,320,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3976

def r6506 : Route 9 := (fun mask => (mask,id))

def c6506 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6506 : Upper (D 3) (R 3) [34,320,72,129] 13 := by
  apply FastRouting.sound _ _ [34,320,72,129] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6506 c6506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6506_5
  · exact m6506_33
  · exact m6506_36
  · exact u3995
  · exact u3996
  · exact u3997

def b6507 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 140 177 177 241 177 433), lower := (rows 35 322 76 140 16 32 64 128 256), losses := [] }

theorem u6507 : Upper (D 3) (R 3) [34,320,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6507
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6508_5 : Upper (D 3) (R 3) [34,320,72,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3913

theorem m6508_33 : Upper (D 3) (R 3) [34,320,72,144,33] 13 :=
  permutation_upper _ _ _ [34,320,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3969

theorem m6508_36 : Upper (D 3) (R 3) [34,320,72,144,36] 13 :=
  permutation_upper _ _ _ [34,320,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3977

def r6508 : Route 9 := (fun mask => (mask,id))

def c6508 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6508 : Upper (D 3) (R 3) [34,320,72,144] 13 := by
  apply FastRouting.sound _ _ [34,320,72,144] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6508 c6508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6508_5
  · exact m6508_33
  · exact m6508_36
  · exact u4000
  · exact u4001
  · exact u4002

theorem m6509_5 : Upper (D 3) (R 3) [34,320,72,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3914

def r6509 : Route 9 := (fun mask => (mask,id))

def c6509 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6509 : Upper (D 3) (R 3) [34,320,72,160] 13 := by
  apply FastRouting.sound _ _ [34,320,72,160] 13 (by decide) (choices 2) [5,129,132] r6509 c6509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6509_5
  · exact u4003
  · exact u4004

theorem m6510_5 : Upper (D 3) (R 3) [34,320,80,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3909

theorem m6510_9 : Upper (D 3) (R 3) [34,320,80,129,9] 13 :=
  permutation_upper _ _ _ [34,320,9,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3918

theorem m6510_12 : Upper (D 3) (R 3) [34,320,80,129,12] 13 :=
  permutation_upper _ _ _ [34,320,24,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3955

theorem m6510_33 : Upper (D 3) (R 3) [34,320,80,129,33] 13 :=
  permutation_upper _ _ _ [34,320,33,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3966

theorem m6510_36 : Upper (D 3) (R 3) [34,320,80,129,36] 13 :=
  permutation_upper _ _ _ [34,320,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3975

theorem m6510_40 : Upper (D 3) (R 3) [34,320,80,129,40] 13 :=
  permutation_upper _ _ _ [34,320,40,129,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3979

theorem m6510_129 : Upper (D 3) (R 3) [34,320,80,129,129] 13 :=
  permutation_upper _ _ _ [34,320,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3995

theorem m6510_132 : Upper (D 3) (R 3) [34,320,80,129,132] 13 :=
  permutation_upper _ _ _ [34,320,72,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3998

theorem m6510_136 : Upper (D 3) (R 3) [34,320,80,129,136] 13 :=
  permutation_upper _ _ _ [34,320,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4000

theorem m6510_160 : Upper (D 3) (R 3) [34,320,80,129,160] 13 :=
  permutation_upper _ _ _ [34,320,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4003

def r6510 : Route 9 := (fun mask => (mask,id))

def c6510 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6510 : Upper (D 3) (R 3) [34,320,80,129] 13 := by
  apply FastRouting.sound _ _ [34,320,80,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6510 c6510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6510_5
  · exact m6510_9
  · exact m6510_12
  · exact m6510_33
  · exact m6510_36
  · exact m6510_40
  · exact m6510_129
  · exact m6510_132
  · exact m6510_136
  · exact m6510_160

theorem m6511_9 : Upper (D 3) (R 3) [34,320,80,132,9] 13 :=
  permutation_upper _ _ _ [34,320,9,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3933

theorem m6511_33 : Upper (D 3) (R 3) [34,320,80,132,33] 13 :=
  permutation_upper _ _ _ [34,320,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3967

theorem m6511_40 : Upper (D 3) (R 3) [34,320,80,132,40] 13 :=
  permutation_upper _ _ _ [34,320,40,144,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3986

theorem m6511_129 : Upper (D 3) (R 3) [34,320,80,132,129] 13 :=
  permutation_upper _ _ _ [34,320,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3996

theorem m6511_136 : Upper (D 3) (R 3) [34,320,80,132,136] 13 :=
  permutation_upper _ _ _ [34,320,72,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4001

theorem m6511_160 : Upper (D 3) (R 3) [34,320,80,132,160] 13 :=
  permutation_upper _ _ _ [34,320,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4004

def r6511 : Route 9 := (fun mask => (mask,id))

def c6511 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6511 : Upper (D 3) (R 3) [34,320,80,132] 13 := by
  apply FastRouting.sound _ _ [34,320,80,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6511 c6511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6511_9
  · exact m6511_33
  · exact m6511_40
  · exact m6511_129
  · exact m6511_136
  · exact m6511_160

theorem m6512_5 : Upper (D 3) (R 3) [34,320,80,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3910

theorem m6512_9 : Upper (D 3) (R 3) [34,320,80,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3939

theorem m6512_12 : Upper (D 3) (R 3) [34,320,80,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3956

theorem m6512_129 : Upper (D 3) (R 3) [34,320,80,160,129] 13 :=
  permutation_upper _ _ _ [34,320,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3997

theorem m6512_132 : Upper (D 3) (R 3) [34,320,80,160,132] 13 :=
  permutation_upper _ _ _ [34,320,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3999

theorem m6512_136 : Upper (D 3) (R 3) [34,320,80,160,136] 13 :=
  permutation_upper _ _ _ [34,320,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4002

def r6512 : Route 9 := (fun mask => (mask,id))

def c6512 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6512 : Upper (D 3) (R 3) [34,320,80,160] 13 := by
  apply FastRouting.sound _ _ [34,320,80,160] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6512 c6512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6512_5
  · exact m6512_9
  · exact m6512_12
  · exact m6512_129
  · exact m6512_132
  · exact m6512_136

theorem m6513_5 : Upper (D 3) (R 3) [34,320,96,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3915

theorem m6513_9 : Upper (D 3) (R 3) [34,320,96,129,9] 13 :=
  permutation_upper _ _ _ [34,320,9,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3919

theorem m6513_12 : Upper (D 3) (R 3) [34,320,96,129,12] 13 :=
  permutation_upper _ _ _ [34,320,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3957

def r6513 : Route 9 := (fun mask => (mask,id))

def c6513 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6513 : Upper (D 3) (R 3) [34,320,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,96,129] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6513 c6513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6513_5
  · exact m6513_9
  · exact m6513_12
  · exact u4005
  · exact u4006
  · exact u4007

theorem m6514_9 : Upper (D 3) (R 3) [34,320,96,132,9] 13 :=
  permutation_upper _ _ _ [34,320,9,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3934

theorem m6514_129 : Upper (D 3) (R 3) [34,320,96,132,129] 13 :=
  permutation_upper _ _ _ [34,320,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4006

def r6514 : Route 9 := (fun mask => (mask,id))

def c6514 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6514 : Upper (D 3) (R 3) [34,320,96,132] 13 := by
  apply FastRouting.sound _ _ [34,320,96,132] 13 (by decide) (choices 2) [9,129,136] r6514 c6514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6514_9
  · exact m6514_129
  · exact u4008

theorem m6515_5 : Upper (D 3) (R 3) [34,320,96,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3916

theorem m6515_9 : Upper (D 3) (R 3) [34,320,96,144,9] 13 :=
  permutation_upper _ _ _ [34,320,9,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3926

theorem m6515_12 : Upper (D 3) (R 3) [34,320,96,144,12] 13 :=
  permutation_upper _ _ _ [34,320,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3958

theorem m6515_129 : Upper (D 3) (R 3) [34,320,96,144,129] 13 :=
  permutation_upper _ _ _ [34,320,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4007

theorem m6515_132 : Upper (D 3) (R 3) [34,320,96,144,132] 13 :=
  permutation_upper _ _ _ [34,320,96,132,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4008

def r6515 : Route 9 := (fun mask => (mask,id))

def c6515 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6515 : Upper (D 3) (R 3) [34,320,96,144] 13 := by
  apply FastRouting.sound _ _ [34,320,96,144] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6515 c6515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6515_5
  · exact m6515_9
  · exact m6515_12
  · exact m6515_129
  · exact m6515_132
  · exact u4009

def b6516 : PairBound 9 := { available := 125, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 322 133 137 125 125 125 253 381), lower := (rows 35 322 133 137 16 32 64 128 256), losses := [] }

theorem u6516 : Upper (D 3) (R 3) [34,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6517 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 322 133 140 121 121 121 249 377), lower := (rows 35 322 133 140 16 32 64 128 256), losses := [] }

theorem u6517 : Upper (D 3) (R 3) [34,320,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6517
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6518_5 : Upper (D 3) (R 3) [34,320,129,144,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3921

theorem m6518_9 : Upper (D 3) (R 3) [34,320,129,144,9] 13 :=
  permutation_upper _ _ _ [34,320,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3927

theorem m6518_12 : Upper (D 3) (R 3) [34,320,129,144,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3960

theorem m6518_33 : Upper (D 3) (R 3) [34,320,129,144,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3970

theorem m6518_36 : Upper (D 3) (R 3) [34,320,129,144,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3981

theorem m6518_40 : Upper (D 3) (R 3) [34,320,129,144,40] 13 :=
  permutation_upper _ _ _ [34,320,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3983

theorem m6518_65 : Upper (D 3) (R 3) [34,320,129,144,65] 13 :=
  permutation_upper _ _ _ [34,320,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3992

theorem m6518_68 : Upper (D 3) (R 3) [34,320,129,144,68] 13 :=
  permutation_upper _ _ _ [34,320,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3996

theorem m6518_72 : Upper (D 3) (R 3) [34,320,129,144,72] 13 :=
  permutation_upper _ _ _ [34,320,72,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3998

theorem m6518_96 : Upper (D 3) (R 3) [34,320,129,144,96] 13 :=
  permutation_upper _ _ _ [34,320,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4006

def r6518 : Route 9 := (fun mask => (mask,id))

def c6518 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6518 : Upper (D 3) (R 3) [34,320,129,144] 13 := by
  apply FastRouting.sound _ _ [34,320,129,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r6518 c6518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6518_5
  · exact m6518_9
  · exact m6518_12
  · exact m6518_33
  · exact m6518_36
  · exact m6518_40
  · exact m6518_65
  · exact m6518_68
  · exact m6518_72
  · exact m6518_96

theorem m6519_5 : Upper (D 3) (R 3) [34,320,129,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3922

theorem m6519_9 : Upper (D 3) (R 3) [34,320,129,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3940

theorem m6519_12 : Upper (D 3) (R 3) [34,320,129,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3961

theorem m6519_65 : Upper (D 3) (R 3) [34,320,129,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3993

theorem m6519_68 : Upper (D 3) (R 3) [34,320,129,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3997

theorem m6519_72 : Upper (D 3) (R 3) [34,320,129,160,72] 13 :=
  permutation_upper _ _ _ [34,320,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4003

def r6519 : Route 9 := (fun mask => (mask,id))

def c6519 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6519 : Upper (D 3) (R 3) [34,320,129,160] 13 := by
  apply FastRouting.sound _ _ [34,320,129,160] 13 (by decide) (choices 2) [5,9,12,65,68,72] r6519 c6519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6519_5
  · exact m6519_9
  · exact m6519_12
  · exact m6519_65
  · exact m6519_68
  · exact m6519_72

theorem m6520_5 : Upper (D 3) (R 3) [34,320,129,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3923

theorem m6520_9 : Upper (D 3) (R 3) [34,320,129,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3944

theorem m6520_12 : Upper (D 3) (R 3) [34,320,129,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3962

theorem m6520_33 : Upper (D 3) (R 3) [34,320,129,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3971

theorem m6520_36 : Upper (D 3) (R 3) [34,320,129,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3982

theorem m6520_40 : Upper (D 3) (R 3) [34,320,129,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3990

def r6520 : Route 9 := (fun mask => (mask,id))

def c6520 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6520 : Upper (D 3) (R 3) [34,320,129,192] 13 := by
  apply FastRouting.sound _ _ [34,320,129,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r6520 c6520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6520_5
  · exact m6520_9
  · exact m6520_12
  · exact m6520_33
  · exact m6520_36
  · exact m6520_40

def b6521 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 140 140 113 113 113 241 369), lower := (rows 35 322 140 140 16 32 64 128 256), losses := [] }

theorem u6521 : Upper (D 3) (R 3) [34,320,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6522 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 152 117 101 101 229 357), lower := (rows 35 322 140 152 16 32 64 128 256), losses := [] }

theorem u6522 : Upper (D 3) (R 3) [34,320,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6523 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 168 85 117 85 213 341), lower := (rows 35 322 140 168 16 32 64 128 256), losses := [] }

theorem u6523 : Upper (D 3) (R 3) [34,320,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6524 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 140 200 53 53 117 181 309), lower := (rows 35 322 140 200 16 32 64 128 256), losses := [] }

theorem u6524 : Upper (D 3) (R 3) [34,320,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6524
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6525_5 : Upper (D 3) (R 3) [34,320,144,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3928

theorem m6525_9 : Upper (D 3) (R 3) [34,320,144,160,9] 13 :=
  permutation_upper _ _ _ [34,320,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3941

theorem m6525_12 : Upper (D 3) (R 3) [34,320,144,160,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3963

theorem m6525_65 : Upper (D 3) (R 3) [34,320,144,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3994

theorem m6525_68 : Upper (D 3) (R 3) [34,320,144,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3999

theorem m6525_72 : Upper (D 3) (R 3) [34,320,144,160,72] 13 :=
  permutation_upper _ _ _ [34,320,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4004

def r6525 : Route 9 := (fun mask => (mask,id))

def c6525 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6525 : Upper (D 3) (R 3) [34,320,144,160] 13 := by
  apply FastRouting.sound _ _ [34,320,144,160] 13 (by decide) (choices 2) [5,9,12,65,68,72] r6525 c6525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6525_5
  · exact m6525_9
  · exact m6525_12
  · exact m6525_65
  · exact m6525_68
  · exact m6525_72

theorem m6526_5 : Upper (D 3) (R 3) [34,320,144,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3929

theorem m6526_9 : Upper (D 3) (R 3) [34,320,144,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3945

theorem m6526_12 : Upper (D 3) (R 3) [34,320,144,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3964

theorem m6526_33 : Upper (D 3) (R 3) [34,320,144,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3972

theorem m6526_36 : Upper (D 3) (R 3) [34,320,144,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3984

theorem m6526_40 : Upper (D 3) (R 3) [34,320,144,192,40] 13 :=
  permutation_upper _ _ _ [34,320,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3991

def r6526 : Route 9 := (fun mask => (mask,id))

def c6526 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6526 : Upper (D 3) (R 3) [34,320,144,192] 13 := by
  apply FastRouting.sound _ _ [34,320,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r6526 c6526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6526_5
  · exact m6526_9
  · exact m6526_12
  · exact m6526_33
  · exact m6526_36
  · exact m6526_40

theorem m6527_5 : Upper (D 3) (R 3) [34,320,160,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3942

theorem m6527_9 : Upper (D 3) (R 3) [34,320,160,192,9] 13 :=
  permutation_upper _ _ _ [34,320,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3946

theorem m6527_12 : Upper (D 3) (R 3) [34,320,160,192,12] 13 :=
  permutation_upper _ _ _ [34,320,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3965

def r6527 : Route 9 := (fun mask => (mask,id))

def c6527 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6527 : Upper (D 3) (R 3) [34,320,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,160,192] 13 (by decide) (choices 2) [5,9,12] r6527 c6527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6527_5
  · exact m6527_9
  · exact m6527_12

def b6528 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 137 504 504 504 504 504), lower := (rows 97 7 7 137 16 32 64 128 256), losses := [] }

theorem u6528 : Upper (D 3) (R 3) [96,5,3,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6528
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6529 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 473 505 473 473 473), lower := (rows 97 7 7 168 16 32 64 128 256), losses := [] }

theorem u6529 : Upper (D 3) (R 3) [96,5,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6530 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 265 248 248 248 248 504), lower := (rows 97 7 7 265 16 32 64 128 256), losses := [] }

theorem u6530 : Upper (D 3) (R 3) [96,5,3,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6531 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 296 217 249 217 217 473), lower := (rows 97 7 7 296 16 32 64 128 256), losses := [] }

theorem u6531 : Upper (D 3) (R 3) [96,5,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6532 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 392 249 249 249 249 505), lower := (rows 97 7 7 392 16 32 64 128 256), losses := [] }

theorem u6532 : Upper (D 3) (R 3) [96,5,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6533 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 497 481 481 481 481), lower := (rows 97 7 13 26 16 32 64 128 256), losses := [] }

theorem u6533 : Upper (D 3) (R 3) [96,5,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6534 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 465 497 465 465 465), lower := (rows 97 7 13 42 16 32 64 128 256), losses := [] }

theorem u6534 : Upper (D 3) (R 3) [96,5,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6535 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 137 498 498 498 498 498), lower := (rows 97 7 13 137 16 32 64 128 256), losses := [] }

theorem u6535 : Upper (D 3) (R 3) [96,5,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6536 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 497 497 497 497 497), lower := (rows 97 7 13 138 16 32 64 128 256), losses := [] }

theorem u6536 : Upper (D 3) (R 3) [96,5,9,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6537 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 467 499 467 467 467), lower := (rows 97 7 13 168 16 32 64 128 256), losses := [] }

theorem u6537 : Upper (D 3) (R 3) [96,5,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6538 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 265 242 242 242 242 498), lower := (rows 97 7 13 265 16 32 64 128 256), losses := [] }

theorem u6538 : Upper (D 3) (R 3) [96,5,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6539 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 241 241 241 241 497), lower := (rows 97 7 13 266 16 32 64 128 256), losses := [] }

theorem u6539 : Upper (D 3) (R 3) [96,5,9,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6539
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6539
end Delivery.IrregularNine14.P03
