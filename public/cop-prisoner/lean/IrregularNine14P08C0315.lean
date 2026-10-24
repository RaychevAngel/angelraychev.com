import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0123
import IrregularNine14P08C0124
import IrregularNine14P08C0125

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18900 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 25 248 232 232 232 488), lower := (rows 7 35 324 25 16 32 64 128 256), losses := [] }

theorem u18900 : Upper (D 8) (R 8) [6,33,320,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18901 : PairBound 9 := { available := 248, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 248 248 248 248 504), lower := (rows 7 35 324 41 16 32 64 128 256), losses := [] }

theorem u18901 : Upper (D 8) (R 8) [6,33,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18902_9 : Upper (D 8) (R 8) [6,33,320,48,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7383

theorem m18902_33 : Upper (D 8) (R 8) [6,33,320,48,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7389

def r18902 : Route 9 := (fun mask => (mask,id))

def c18902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18902 : Upper (D 8) (R 8) [6,33,320,48] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r18902 c18902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18902_9
  · exact m18902_33
  · exact u7395
  · exact u7396
  · exact u7397
  · exact u7398
  · exact u7399
  · exact u7400
  · exact u7401
  · exact u7402

def b18903 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 73 184 184 248 184 440), lower := (rows 7 35 324 73 16 32 64 128 256), losses := [] }

theorem u18903 : Upper (D 8) (R 8) [6,33,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18904_9 : Upper (D 8) (R 8) [6,33,320,80,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7384

theorem m18904_33 : Upper (D 8) (R 8) [6,33,320,80,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7390

theorem m18904_40 : Upper (D 8) (R 8) [6,33,320,80,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7397

def r18904 : Route 9 := (fun mask => (mask,id))

def c18904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u18904 : Upper (D 8) (R 8) [6,33,320,80] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r18904 c18904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18904_9
  · exact m18904_33
  · exact m18904_40
  · exact u7405
  · exact u7406
  · exact u7407

theorem m18905_9 : Upper (D 8) (R 8) [6,33,320,96,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7385

theorem m18905_33 : Upper (D 8) (R 8) [6,33,320,96,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7391

theorem m18905_40 : Upper (D 8) (R 8) [6,33,320,96,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7398

def r18905 : Route 9 := (fun mask => (mask,id))

def c18905 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u18905 : Upper (D 8) (R 8) [6,33,320,96] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r18905 c18905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18905_9
  · exact m18905_33
  · exact m18905_40
  · exact u7408
  · exact u7409
  · exact u7410

def b18906 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 137 248 248 248 248 504), lower := (rows 7 35 324 137 16 32 64 128 256), losses := [] }

theorem u18906 : Upper (D 8) (R 8) [6,33,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18907_9 : Upper (D 8) (R 8) [6,33,320,144,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7386

theorem m18907_33 : Upper (D 8) (R 8) [6,33,320,144,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7392

theorem m18907_40 : Upper (D 8) (R 8) [6,33,320,144,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7400

theorem m18907_65 : Upper (D 8) (R 8) [6,33,320,144,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7403

theorem m18907_72 : Upper (D 8) (R 8) [6,33,320,144,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7406

theorem m18907_96 : Upper (D 8) (R 8) [6,33,320,144,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7409

theorem m18907_129 : Upper (D 8) (R 8) [6,33,320,144,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7411

def r18907 : Route 9 := (fun mask => (mask,id))

def c18907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18907 : Upper (D 8) (R 8) [6,33,320,144] 13 := by
  apply FastRouting.sound _ _ [6,33,320,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r18907 c18907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18907_9
  · exact m18907_33
  · exact m18907_40
  · exact m18907_65
  · exact m18907_72
  · exact m18907_96
  · exact m18907_129
  · exact u7414
  · exact u7415
  · exact u7416

theorem m18908_9 : Upper (D 8) (R 8) [6,33,320,160,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7387

theorem m18908_33 : Upper (D 8) (R 8) [6,33,320,160,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7393

theorem m18908_40 : Upper (D 8) (R 8) [6,33,320,160,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7401

theorem m18908_65 : Upper (D 8) (R 8) [6,33,320,160,65] 13 :=
  permutation_upper _ _ _ [6,33,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7404

theorem m18908_72 : Upper (D 8) (R 8) [6,33,320,160,72] 13 :=
  permutation_upper _ _ _ [6,33,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7407

theorem m18908_96 : Upper (D 8) (R 8) [6,33,320,160,96] 13 :=
  permutation_upper _ _ _ [6,33,320,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7410

theorem m18908_129 : Upper (D 8) (R 8) [6,33,320,160,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7412

theorem m18908_136 : Upper (D 8) (R 8) [6,33,320,160,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7415

def r18908 : Route 9 := (fun mask => (mask,id))

def c18908 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18908 : Upper (D 8) (R 8) [6,33,320,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r18908 c18908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18908_9
  · exact m18908_33
  · exact m18908_40
  · exact m18908_65
  · exact m18908_72
  · exact m18908_96
  · exact m18908_129
  · exact m18908_136
  · exact u7417
  · exact u7418

theorem m18909_9 : Upper (D 8) (R 8) [6,33,320,192,9] 13 :=
  permutation_upper _ _ _ [6,33,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7388

theorem m18909_33 : Upper (D 8) (R 8) [6,33,320,192,33] 13 :=
  permutation_upper _ _ _ [6,33,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7394

theorem m18909_40 : Upper (D 8) (R 8) [6,33,320,192,40] 13 :=
  permutation_upper _ _ _ [6,33,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7402

theorem m18909_129 : Upper (D 8) (R 8) [6,33,320,192,129] 13 :=
  permutation_upper _ _ _ [6,33,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7413

theorem m18909_136 : Upper (D 8) (R 8) [6,33,320,192,136] 13 :=
  permutation_upper _ _ _ [6,33,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7416

theorem m18909_160 : Upper (D 8) (R 8) [6,33,320,192,160] 13 :=
  permutation_upper _ _ _ [6,33,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7418

def r18909 : Route 9 := (fun mask => (mask,id))

def c18909 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u18909 : Upper (D 8) (R 8) [6,33,320,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r18909 c18909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18909_9
  · exact m18909_33
  · exact m18909_40
  · exact m18909_129
  · exact m18909_136
  · exact m18909_160

def b18910 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 41 465 481 449 449 449), lower := (rows 7 42 52 41 16 32 64 128 256), losses := [] }

theorem u18910 : Upper (D 8) (R 8) [6,40,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18911_33 : Upper (D 8) (R 8) [6,40,48,65,33] 13 :=
  permutation_upper _ _ _ [6,40,48,33,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7419

def r18911 : Route 9 := (fun mask => (mask,id))

def c18911 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18911 : Upper (D 8) (R 8) [6,40,48,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18911 c18911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18911_33
  · exact u7423
  · exact u7424
  · exact u7425
  · exact u7426
  · exact u7427
  · exact u7428
  · exact u7429
  · exact u7430
  · exact u7431

def b18912 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 104 465 481 449 449 449), lower := (rows 7 42 52 104 16 32 64 128 256), losses := [] }

theorem u18912 : Upper (D 8) (R 8) [6,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18913_33 : Upper (D 8) (R 8) [6,40,48,192,33] 13 :=
  permutation_upper _ _ _ [6,40,48,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7420

theorem m18913_65 : Upper (D 8) (R 8) [6,40,48,192,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7427

theorem m18913_96 : Upper (D 8) (R 8) [6,40,48,192,96] 13 :=
  permutation_upper _ _ _ [6,40,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7432

def r18913 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18913 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18913 : Upper (D 8) (R 8) [6,40,48,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18913 c18913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18913_33
  · exact m18913_65
  · exact m18913_96
  · exact u7436
  · exact u7437
  · exact u7438
  · exact u7439

theorem m18914_33 : Upper (D 8) (R 8) [6,40,48,257,33] 13 :=
  permutation_upper _ _ _ [6,40,48,33,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7421

theorem m18914_65 : Upper (D 8) (R 8) [6,40,48,257,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7428

theorem m18914_96 : Upper (D 8) (R 8) [6,40,48,257,96] 13 :=
  permutation_upper _ _ _ [6,40,48,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7433

theorem m18914_192 : Upper (D 8) (R 8) [6,40,48,257,192] 13 :=
  permutation_upper _ _ _ [6,40,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7437

def r18914 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18914 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18914 : Upper (D 8) (R 8) [6,40,48,257] 13 := by
  apply FastRouting.sound _ _ [6,40,48,257] 13 (by decide) (choices 2) [33,65,96,192] r18914 c18914
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18914_33
  · exact m18914_65
  · exact m18914_96
  · exact m18914_192

def b18915 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 296 209 225 193 193 449), lower := (rows 7 42 52 296 16 32 64 128 256), losses := [] }

theorem u18915 : Upper (D 8) (R 8) [6,40,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18916_33 : Upper (D 8) (R 8) [6,40,48,320,33] 13 :=
  permutation_upper _ _ _ [6,40,48,33,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7422

theorem m18916_65 : Upper (D 8) (R 8) [6,40,48,320,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7430

theorem m18916_96 : Upper (D 8) (R 8) [6,40,48,320,96] 13 :=
  permutation_upper _ _ _ [6,40,48,96,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7434

theorem m18916_129 : Upper (D 8) (R 8) [6,40,48,320,129] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7431

theorem m18916_160 : Upper (D 8) (R 8) [6,40,48,320,160] 13 :=
  permutation_upper _ _ _ [6,40,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7435

theorem m18916_192 : Upper (D 8) (R 8) [6,40,48,320,192] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7439

def r18916 : Route 9 := (fun mask => (mask,id))

def c18916 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18916 : Upper (D 8) (R 8) [6,40,48,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18916 c18916
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18916_33
  · exact m18916_65
  · exact m18916_96
  · exact m18916_129
  · exact m18916_160
  · exact m18916_192

def b18917 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 25 496 480 480 480 480), lower := (rows 7 42 69 25 16 32 64 128 256), losses := [] }

theorem u18917 : Upper (D 8) (R 8) [6,40,65,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18918 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 41 496 496 496 496 496), lower := (rows 7 42 69 41 16 32 64 128 256), losses := [] }

theorem u18918 : Upper (D 8) (R 8) [6,40,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18919 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 56 497 481 481 481 481), lower := (rows 7 42 69 56 16 32 64 128 256), losses := [] }

theorem u18919 : Upper (D 8) (R 8) [6,40,65,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18920 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 73 432 432 496 432 432), lower := (rows 7 42 69 73 16 32 64 128 256), losses := [] }

theorem u18920 : Upper (D 8) (R 8) [6,40,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18921 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 69 88 433 417 481 417 417), lower := (rows 7 42 69 88 16 32 64 128 256), losses := [] }

theorem u18921 : Upper (D 8) (R 8) [6,40,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18922 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 104 433 433 497 433 433), lower := (rows 7 42 69 104 16 32 64 128 256), losses := [] }

theorem u18922 : Upper (D 8) (R 8) [6,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18923 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 137 496 496 496 496 496), lower := (rows 7 42 69 137 16 32 64 128 256), losses := [] }

theorem u18923 : Upper (D 8) (R 8) [6,40,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18924 : Route 9 := (fun mask => (mask,id))

def c18924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18924 : Upper (D 8) (R 8) [6,40,65,144] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18924 c18924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7440
  · exact u7441
  · exact u7442
  · exact u7443
  · exact u7444
  · exact u7445
  · exact u7446
  · exact u7447
  · exact u7448
  · exact u7449

def b18925 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 168 497 497 497 497 497), lower := (rows 7 42 69 168 16 32 64 128 256), losses := [] }

theorem u18925 : Upper (D 8) (R 8) [6,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18926 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 69 200 433 433 497 433 433), lower := (rows 7 42 69 200 16 32 64 128 256), losses := [] }

theorem u18926 : Upper (D 8) (R 8) [6,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18927 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 265 240 240 240 240 496), lower := (rows 7 42 69 265 16 32 64 128 256), losses := [] }

theorem u18927 : Upper (D 8) (R 8) [6,40,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18928 : Route 9 := (fun mask => (mask,id))

def c18928 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18928 : Upper (D 8) (R 8) [6,40,65,272] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18928 c18928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7450
  · exact u7451
  · exact u7452
  · exact u7453
  · exact u7454
  · exact u7455

def b18929 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 296 241 241 241 241 497), lower := (rows 7 42 69 296 16 32 64 128 256), losses := [] }

theorem u18929 : Upper (D 8) (R 8) [6,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18930 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 69 328 177 177 241 177 433), lower := (rows 7 42 69 328 16 32 64 128 256), losses := [] }

theorem u18930 : Upper (D 8) (R 8) [6,40,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18931 : Route 9 := (fun mask => (mask,id))

def c18931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18931 : Upper (D 8) (R 8) [6,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18931 c18931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7456
  · exact u7457
  · exact u7458
  · exact u7459
  · exact u7460
  · exact u7461

def b18932 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 41 497 481 481 481 481), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u18932 : Upper (D 8) (R 8) [6,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18933 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 73 433 417 481 417 417), lower := (rows 7 42 84 73 16 32 64 128 256), losses := [] }

theorem u18933 : Upper (D 8) (R 8) [6,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18934 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 104 433 417 481 417 417), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u18934 : Upper (D 8) (R 8) [6,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18935 : Route 9 := (fun mask => (mask,id))

def c18935 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18935 : Upper (D 8) (R 8) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18935 c18935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7462
  · exact u7463
  · exact u7464
  · exact u7465
  · exact u7466
  · exact u7467
  · exact u7468
  · exact u7469
  · exact u7470
  · exact u7471

def b18936 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 168 497 481 481 481 481), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u18936 : Upper (D 8) (R 8) [6,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18937 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 433 417 481 417 417), lower := (rows 7 42 84 200 16 32 64 128 256), losses := [] }

theorem u18937 : Upper (D 8) (R 8) [6,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18938 : Route 9 := (fun mask => (mask,id))

def c18938 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18938 : Upper (D 8) (R 8) [6,40,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18938 c18938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7472
  · exact u7473
  · exact u7474
  · exact u7475
  · exact u7476
  · exact u7477

def b18939 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 296 241 225 225 225 481), lower := (rows 7 42 84 296 16 32 64 128 256), losses := [] }

theorem u18939 : Upper (D 8) (R 8) [6,40,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18940 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 328 177 161 225 161 417), lower := (rows 7 42 84 328 16 32 64 128 256), losses := [] }

theorem u18940 : Upper (D 8) (R 8) [6,40,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18941 : Route 9 := (fun mask => (mask,id))

def c18941 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18941 : Upper (D 8) (R 8) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18941 c18941
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7478
  · exact u7479
  · exact u7480
  · exact u7481
  · exact u7482
  · exact u7483

def r18942 : Route 9 := (fun mask => (mask,id))

def c18942 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18942 : Upper (D 8) (R 8) [6,40,96,17] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18942 c18942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7484
  · exact u7485
  · exact u7486
  · exact u7487
  · exact u7488
  · exact u7489
  · exact u7490
  · exact u7491
  · exact u7492
  · exact u7493

def b18943 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 41 465 497 465 465 465), lower := (rows 7 42 100 41 16 32 64 128 256), losses := [] }

theorem u18943 : Upper (D 8) (R 8) [6,40,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18944 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 56 465 481 449 449 449), lower := (rows 7 42 100 56 16 32 64 128 256), losses := [] }

theorem u18944 : Upper (D 8) (R 8) [6,40,96,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18945 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 11, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 73 433 433 497 433 433), lower := (rows 7 42 100 73 16 32 64 128 256), losses := [] }

theorem u18945 : Upper (D 8) (R 8) [6,40,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18946 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 88 433 417 481 417 417), lower := (rows 7 42 100 88 16 32 64 128 256), losses := [] }

theorem u18946 : Upper (D 8) (R 8) [6,40,96,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18947 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 104 401 433 465 401 401), lower := (rows 7 42 100 104 16 32 64 128 256), losses := [] }

theorem u18947 : Upper (D 8) (R 8) [6,40,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18948 : Route 9 := (fun mask => (mask,id))

def c18948 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18948 : Upper (D 8) (R 8) [6,40,96,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18948 c18948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7494
  · exact u7495
  · exact u7496
  · exact u7497
  · exact u7498
  · exact u7499
  · exact u7500
  · exact u7501
  · exact u7502
  · exact u7503

def r18949 : Route 9 := (fun mask => (mask,id))

def c18949 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18949 : Upper (D 8) (R 8) [6,40,96,144] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18949 c18949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7504
  · exact u7505
  · exact u7506
  · exact u7507
  · exact u7508
  · exact u7509
  · exact u7510
  · exact u7511
  · exact u7512
  · exact u7513

def b18950 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 168 465 497 465 465 465), lower := (rows 7 42 100 168 16 32 64 128 256), losses := [] }

theorem u18950 : Upper (D 8) (R 8) [6,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18951 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 200 433 433 497 433 433), lower := (rows 7 42 100 200 16 32 64 128 256), losses := [] }

theorem u18951 : Upper (D 8) (R 8) [6,40,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18952 : Route 9 := (fun mask => (mask,id))

def c18952 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18952 : Upper (D 8) (R 8) [6,40,96,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18952 c18952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7514
  · exact u7515
  · exact u7516
  · exact u7517
  · exact u7518
  · exact u7519

def r18953 : Route 9 := (fun mask => (mask,id))

def c18953 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18953 : Upper (D 8) (R 8) [6,40,96,272] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18953 c18953
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7520
  · exact u7521
  · exact u7522
  · exact u7523
  · exact u7524
  · exact u7525

def b18954 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 296 209 241 209 209 465), lower := (rows 7 42 100 296 16 32 64 128 256), losses := [] }

theorem u18954 : Upper (D 8) (R 8) [6,40,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18955 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 328 177 177 241 177 433), lower := (rows 7 42 100 328 16 32 64 128 256), losses := [] }

theorem u18955 : Upper (D 8) (R 8) [6,40,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18956 : Route 9 := (fun mask => (mask,id))

def c18956 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18956 : Upper (D 8) (R 8) [6,40,96,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18956 c18956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7526
  · exact u7527
  · exact u7528
  · exact u7529
  · exact u7530
  · exact u7531

def r18957 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18957 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18957 : Upper (D 8) (R 8) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18957 c18957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7532
  · exact u7533
  · exact u7534
  · exact u7535
  · exact u7536
  · exact u7537
  · exact u7538

def b18958 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 41 497 497 497 497 497), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u18958 : Upper (D 8) (R 8) [6,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18959 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 56 497 481 481 481 481), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u18959 : Upper (D 8) (R 8) [6,40,192,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18959
end Delivery.IrregularNine14.P08
