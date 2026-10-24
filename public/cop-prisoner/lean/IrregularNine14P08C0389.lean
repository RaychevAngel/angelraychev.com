import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0296
import IrregularNine14P08C0298
import IrregularNine14P08C0299
import IrregularNine14P08C0300
import IrregularNine14P08C0301

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23340 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 137 248 248 248 248 504), lower := (rows 321 7 38 137 16 32 64 128 256), losses := [] }

theorem u23340 : Upper (D 8) (R 8) [320,5,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23341_9 : Upper (D 8) (R 8) [320,5,34,144,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17908

theorem m23341_33 : Upper (D 8) (R 8) [320,5,34,144,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17914

theorem m23341_40 : Upper (D 8) (R 8) [320,5,34,144,40] 13 :=
  permutation_upper _ _ _ [320,5,34,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17922

theorem m23341_65 : Upper (D 8) (R 8) [320,5,34,144,65] 13 :=
  permutation_upper _ _ _ [320,5,34,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17925

theorem m23341_72 : Upper (D 8) (R 8) [320,5,34,144,72] 13 :=
  permutation_upper _ _ _ [320,5,34,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17928

theorem m23341_96 : Upper (D 8) (R 8) [320,5,34,144,96] 13 :=
  permutation_upper _ _ _ [320,5,34,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17931

theorem m23341_129 : Upper (D 8) (R 8) [320,5,34,144,129] 13 :=
  permutation_upper _ _ _ [320,5,34,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17933

def r23341 : Route 9 := (fun mask => (mask,id))

def c23341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23341 : Upper (D 8) (R 8) [320,5,34,144] 13 := by
  apply FastRouting.sound _ _ [320,5,34,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23341 c23341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23341_9
  · exact m23341_33
  · exact m23341_40
  · exact m23341_65
  · exact m23341_72
  · exact m23341_96
  · exact m23341_129
  · exact u17936
  · exact u17937
  · exact u17938

theorem m23342_9 : Upper (D 8) (R 8) [320,5,34,160,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17909

theorem m23342_33 : Upper (D 8) (R 8) [320,5,34,160,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17915

theorem m23342_40 : Upper (D 8) (R 8) [320,5,34,160,40] 13 :=
  permutation_upper _ _ _ [320,5,34,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17923

theorem m23342_65 : Upper (D 8) (R 8) [320,5,34,160,65] 13 :=
  permutation_upper _ _ _ [320,5,34,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17926

theorem m23342_72 : Upper (D 8) (R 8) [320,5,34,160,72] 13 :=
  permutation_upper _ _ _ [320,5,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17929

theorem m23342_96 : Upper (D 8) (R 8) [320,5,34,160,96] 13 :=
  permutation_upper _ _ _ [320,5,34,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17932

theorem m23342_129 : Upper (D 8) (R 8) [320,5,34,160,129] 13 :=
  permutation_upper _ _ _ [320,5,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17934

theorem m23342_136 : Upper (D 8) (R 8) [320,5,34,160,136] 13 :=
  permutation_upper _ _ _ [320,5,34,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17937

def r23342 : Route 9 := (fun mask => (mask,id))

def c23342 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23342 : Upper (D 8) (R 8) [320,5,34,160] 13 := by
  apply FastRouting.sound _ _ [320,5,34,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23342 c23342
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23342_9
  · exact m23342_33
  · exact m23342_40
  · exact m23342_65
  · exact m23342_72
  · exact m23342_96
  · exact m23342_129
  · exact m23342_136
  · exact u17939
  · exact u17940

theorem m23343_9 : Upper (D 8) (R 8) [320,5,34,192,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17910

theorem m23343_33 : Upper (D 8) (R 8) [320,5,34,192,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17916

theorem m23343_40 : Upper (D 8) (R 8) [320,5,34,192,40] 13 :=
  permutation_upper _ _ _ [320,5,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17924

theorem m23343_129 : Upper (D 8) (R 8) [320,5,34,192,129] 13 :=
  permutation_upper _ _ _ [320,5,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17935

theorem m23343_136 : Upper (D 8) (R 8) [320,5,34,192,136] 13 :=
  permutation_upper _ _ _ [320,5,34,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17938

theorem m23343_160 : Upper (D 8) (R 8) [320,5,34,192,160] 13 :=
  permutation_upper _ _ _ [320,5,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17940

def r23343 : Route 9 := (fun mask => (mask,id))

def c23343 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23343 : Upper (D 8) (R 8) [320,5,34,192] 13 := by
  apply FastRouting.sound _ _ [320,5,34,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23343 c23343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23343_9
  · exact m23343_33
  · exact m23343_40
  · exact m23343_129
  · exact m23343_136
  · exact m23343_160

def b23344 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 25 242 226 226 226 482), lower := (rows 321 7 44 25 16 32 64 128 256), losses := [] }

theorem u23344 : Upper (D 8) (R 8) [320,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23345 : Route 9 := (fun mask => (mask,id))

def c23345 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23345 : Upper (D 8) (R 8) [320,5,40,18] 13 := by
  apply FastRouting.sound _ _ [320,5,40,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23345 c23345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17947
  · exact u17948
  · exact u17949
  · exact u17950
  · exact u17951
  · exact u17952

def b23346 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 41 242 242 242 242 498), lower := (rows 321 7 44 41 16 32 64 128 256), losses := [] }

theorem u23346 : Upper (D 8) (R 8) [320,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23347 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 42 241 241 241 241 497), lower := (rows 321 7 44 42 16 32 64 128 256), losses := [] }

theorem u23347 : Upper (D 8) (R 8) [320,5,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23348 : PairBound 9 := { available := 227, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 56 243 227 227 227 483), lower := (rows 321 7 44 56 16 32 64 128 256), losses := [] }

theorem u23348 : Upper (D 8) (R 8) [320,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23349 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 44 73 178 178 242 178 434), lower := (rows 321 7 44 73 16 32 64 128 256), losses := [] }

theorem u23349 : Upper (D 8) (R 8) [320,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23350 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 74 177 177 241 177 433), lower := (rows 321 7 44 74 16 32 64 128 256), losses := [] }

theorem u23350 : Upper (D 8) (R 8) [320,5,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23351 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 88 179 163 227 163 419), lower := (rows 321 7 44 88 16 32 64 128 256), losses := [] }

theorem u23351 : Upper (D 8) (R 8) [320,5,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23352 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 104 179 179 243 179 435), lower := (rows 321 7 44 104 16 32 64 128 256), losses := [] }

theorem u23352 : Upper (D 8) (R 8) [320,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23353 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 44 137 242 242 242 242 498), lower := (rows 321 7 44 137 16 32 64 128 256), losses := [] }

theorem u23353 : Upper (D 8) (R 8) [320,5,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23354 : Route 9 := (fun mask => (mask,id))

def c23354 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23354 : Upper (D 8) (R 8) [320,5,40,130] 13 := by
  apply FastRouting.sound _ _ [320,5,40,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23354 c23354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17994
  · exact u17995
  · exact u17996
  · exact u17997
  · exact u17998
  · exact u17999

theorem m23355_3 : Upper (D 8) (R 8) [320,5,40,144,3] 13 :=
  permutation_upper _ _ _ [320,5,9,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17796

def r23355 : Route 9 := (fun mask => (mask,id))

def c23355 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23355 : Upper (D 8) (R 8) [320,5,40,144] 13 := by
  apply FastRouting.sound _ _ [320,5,40,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23355 c23355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23355_3
  · exact u18000
  · exact u18001
  · exact u18002
  · exact u18003
  · exact u18004
  · exact u18005
  · exact u18006
  · exact u18007
  · exact u18008

def b23356 : PairBound 9 := { available := 243, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 44 168 243 243 243 243 499), lower := (rows 321 7 44 168 16 32 64 128 256), losses := [] }

theorem u23356 : Upper (D 8) (R 8) [320,5,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23357 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 44 200 179 179 243 179 435), lower := (rows 321 7 44 200 16 32 64 128 256), losses := [] }

theorem u23357 : Upper (D 8) (R 8) [320,5,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23358_10 : Upper (D 8) (R 8) [320,5,48,33,10] 13 :=
  permutation_upper _ _ _ [320,5,40,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17947

theorem m23358_34 : Upper (D 8) (R 8) [320,5,48,33,34] 13 :=
  permutation_upper _ _ _ [320,5,40,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17959

theorem m23358_40 : Upper (D 8) (R 8) [320,5,48,33,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17964

theorem m23358_66 : Upper (D 8) (R 8) [320,5,48,33,66] 13 :=
  permutation_upper _ _ _ [320,5,40,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17975

theorem m23358_72 : Upper (D 8) (R 8) [320,5,48,33,72] 13 :=
  permutation_upper _ _ _ [320,5,40,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17978

theorem m23358_96 : Upper (D 8) (R 8) [320,5,48,33,96] 13 :=
  permutation_upper _ _ _ [320,5,40,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17983

theorem m23358_130 : Upper (D 8) (R 8) [320,5,48,33,130] 13 :=
  permutation_upper _ _ _ [320,5,40,130,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17994

theorem m23358_136 : Upper (D 8) (R 8) [320,5,48,33,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18000

theorem m23358_160 : Upper (D 8) (R 8) [320,5,48,33,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18009

theorem m23358_192 : Upper (D 8) (R 8) [320,5,48,33,192] 13 :=
  permutation_upper _ _ _ [320,5,40,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18017

def r23358 : Route 9 := (fun mask => (mask,id))

def c23358 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23358 : Upper (D 8) (R 8) [320,5,48,33] 13 := by
  apply FastRouting.sound _ _ [320,5,48,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23358 c23358
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23358_10
  · exact m23358_34
  · exact m23358_40
  · exact m23358_66
  · exact m23358_72
  · exact m23358_96
  · exact m23358_130
  · exact m23358_136
  · exact m23358_160
  · exact m23358_192

theorem m23359_9 : Upper (D 8) (R 8) [320,5,48,34,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17941

theorem m23359_33 : Upper (D 8) (R 8) [320,5,48,34,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17953

theorem m23359_40 : Upper (D 8) (R 8) [320,5,48,34,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17965

theorem m23359_65 : Upper (D 8) (R 8) [320,5,48,34,65] 13 :=
  permutation_upper _ _ _ [320,5,40,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17972

theorem m23359_72 : Upper (D 8) (R 8) [320,5,48,34,72] 13 :=
  permutation_upper _ _ _ [320,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17979

theorem m23359_96 : Upper (D 8) (R 8) [320,5,48,34,96] 13 :=
  permutation_upper _ _ _ [320,5,40,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17984

theorem m23359_129 : Upper (D 8) (R 8) [320,5,48,34,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17988

theorem m23359_136 : Upper (D 8) (R 8) [320,5,48,34,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18001

theorem m23359_160 : Upper (D 8) (R 8) [320,5,48,34,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18010

theorem m23359_192 : Upper (D 8) (R 8) [320,5,48,34,192] 13 :=
  permutation_upper _ _ _ [320,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18018

def r23359 : Route 9 := (fun mask => (mask,id))

def c23359 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23359 : Upper (D 8) (R 8) [320,5,48,34] 13 := by
  apply FastRouting.sound _ _ [320,5,48,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23359 c23359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23359_9
  · exact m23359_33
  · exact m23359_40
  · exact m23359_65
  · exact m23359_72
  · exact m23359_96
  · exact m23359_129
  · exact m23359_136
  · exact m23359_160
  · exact m23359_192

theorem m23360_9 : Upper (D 8) (R 8) [320,5,48,66,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17942

theorem m23360_33 : Upper (D 8) (R 8) [320,5,48,66,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17954

theorem m23360_40 : Upper (D 8) (R 8) [320,5,48,66,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17966

theorem m23360_129 : Upper (D 8) (R 8) [320,5,48,66,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17989

theorem m23360_136 : Upper (D 8) (R 8) [320,5,48,66,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18003

theorem m23360_160 : Upper (D 8) (R 8) [320,5,48,66,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18011

def r23360 : Route 9 := (fun mask => (mask,id))

def c23360 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23360 : Upper (D 8) (R 8) [320,5,48,66] 13 := by
  apply FastRouting.sound _ _ [320,5,48,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23360 c23360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23360_9
  · exact m23360_33
  · exact m23360_40
  · exact m23360_129
  · exact m23360_136
  · exact m23360_160

theorem m23361_3 : Upper (D 8) (R 8) [320,5,48,96,3] 13 :=
  permutation_upper _ _ _ [320,5,9,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17792

theorem m23361_9 : Upper (D 8) (R 8) [320,5,48,96,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17943

theorem m23361_10 : Upper (D 8) (R 8) [320,5,48,96,10] 13 :=
  permutation_upper _ _ _ [320,5,40,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17949

theorem m23361_33 : Upper (D 8) (R 8) [320,5,48,96,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17955

theorem m23361_34 : Upper (D 8) (R 8) [320,5,48,96,34] 13 :=
  permutation_upper _ _ _ [320,5,40,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17960

theorem m23361_40 : Upper (D 8) (R 8) [320,5,48,96,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17967

theorem m23361_129 : Upper (D 8) (R 8) [320,5,48,96,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17990

theorem m23361_130 : Upper (D 8) (R 8) [320,5,48,96,130] 13 :=
  permutation_upper _ _ _ [320,5,40,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17996

theorem m23361_136 : Upper (D 8) (R 8) [320,5,48,96,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18004

theorem m23361_160 : Upper (D 8) (R 8) [320,5,48,96,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18012

def r23361 : Route 9 := (fun mask => (mask,id))

def c23361 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23361 : Upper (D 8) (R 8) [320,5,48,96] 13 := by
  apply FastRouting.sound _ _ [320,5,48,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23361 c23361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23361_3
  · exact m23361_9
  · exact m23361_10
  · exact m23361_33
  · exact m23361_34
  · exact m23361_40
  · exact m23361_129
  · exact m23361_130
  · exact m23361_136
  · exact m23361_160

theorem m23362_10 : Upper (D 8) (R 8) [320,5,48,129,10] 13 :=
  permutation_upper _ _ _ [320,5,40,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17950

theorem m23362_34 : Upper (D 8) (R 8) [320,5,48,129,34] 13 :=
  permutation_upper _ _ _ [320,5,40,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17961

theorem m23362_40 : Upper (D 8) (R 8) [320,5,48,129,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17968

theorem m23362_66 : Upper (D 8) (R 8) [320,5,48,129,66] 13 :=
  permutation_upper _ _ _ [320,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17976

theorem m23362_72 : Upper (D 8) (R 8) [320,5,48,129,72] 13 :=
  permutation_upper _ _ _ [320,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17980

theorem m23362_96 : Upper (D 8) (R 8) [320,5,48,129,96] 13 :=
  permutation_upper _ _ _ [320,5,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17985

theorem m23362_130 : Upper (D 8) (R 8) [320,5,48,129,130] 13 :=
  permutation_upper _ _ _ [320,5,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17997

theorem m23362_136 : Upper (D 8) (R 8) [320,5,48,129,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18005

theorem m23362_160 : Upper (D 8) (R 8) [320,5,48,129,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18013

theorem m23362_192 : Upper (D 8) (R 8) [320,5,48,129,192] 13 :=
  permutation_upper _ _ _ [320,5,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18019

def r23362 : Route 9 := (fun mask => (mask,id))

def c23362 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23362 : Upper (D 8) (R 8) [320,5,48,129] 13 := by
  apply FastRouting.sound _ _ [320,5,48,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23362 c23362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23362_10
  · exact m23362_34
  · exact m23362_40
  · exact m23362_66
  · exact m23362_72
  · exact m23362_96
  · exact m23362_130
  · exact m23362_136
  · exact m23362_160
  · exact m23362_192

theorem m23363_9 : Upper (D 8) (R 8) [320,5,48,130,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17944

theorem m23363_33 : Upper (D 8) (R 8) [320,5,48,130,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17956

theorem m23363_40 : Upper (D 8) (R 8) [320,5,48,130,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17969

theorem m23363_65 : Upper (D 8) (R 8) [320,5,48,130,65] 13 :=
  permutation_upper _ _ _ [320,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17973

theorem m23363_72 : Upper (D 8) (R 8) [320,5,48,130,72] 13 :=
  permutation_upper _ _ _ [320,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17981

theorem m23363_96 : Upper (D 8) (R 8) [320,5,48,130,96] 13 :=
  permutation_upper _ _ _ [320,5,40,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17986

theorem m23363_129 : Upper (D 8) (R 8) [320,5,48,130,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17991

theorem m23363_136 : Upper (D 8) (R 8) [320,5,48,130,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18006

theorem m23363_160 : Upper (D 8) (R 8) [320,5,48,130,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18014

theorem m23363_192 : Upper (D 8) (R 8) [320,5,48,130,192] 13 :=
  permutation_upper _ _ _ [320,5,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18020

def r23363 : Route 9 := (fun mask => (mask,id))

def c23363 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23363 : Upper (D 8) (R 8) [320,5,48,130] 13 := by
  apply FastRouting.sound _ _ [320,5,48,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23363 c23363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23363_9
  · exact m23363_33
  · exact m23363_40
  · exact m23363_65
  · exact m23363_72
  · exact m23363_96
  · exact m23363_129
  · exact m23363_136
  · exact m23363_160
  · exact m23363_192

theorem m23364_3 : Upper (D 8) (R 8) [320,5,48,160,3] 13 :=
  permutation_upper _ _ _ [320,5,9,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17793

theorem m23364_9 : Upper (D 8) (R 8) [320,5,48,160,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17945

theorem m23364_10 : Upper (D 8) (R 8) [320,5,48,160,10] 13 :=
  permutation_upper _ _ _ [320,5,40,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17951

theorem m23364_33 : Upper (D 8) (R 8) [320,5,48,160,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17957

theorem m23364_34 : Upper (D 8) (R 8) [320,5,48,160,34] 13 :=
  permutation_upper _ _ _ [320,5,40,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17962

theorem m23364_40 : Upper (D 8) (R 8) [320,5,48,160,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17970

theorem m23364_65 : Upper (D 8) (R 8) [320,5,48,160,65] 13 :=
  permutation_upper _ _ _ [320,5,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17974

theorem m23364_66 : Upper (D 8) (R 8) [320,5,48,160,66] 13 :=
  permutation_upper _ _ _ [320,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17977

theorem m23364_72 : Upper (D 8) (R 8) [320,5,48,160,72] 13 :=
  permutation_upper _ _ _ [320,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17982

theorem m23364_96 : Upper (D 8) (R 8) [320,5,48,160,96] 13 :=
  permutation_upper _ _ _ [320,5,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17987

theorem m23364_129 : Upper (D 8) (R 8) [320,5,48,160,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17992

theorem m23364_130 : Upper (D 8) (R 8) [320,5,48,160,130] 13 :=
  permutation_upper _ _ _ [320,5,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17998

theorem m23364_136 : Upper (D 8) (R 8) [320,5,48,160,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18007

theorem m23364_160 : Upper (D 8) (R 8) [320,5,48,160,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18015

theorem m23364_192 : Upper (D 8) (R 8) [320,5,48,160,192] 13 :=
  permutation_upper _ _ _ [320,5,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18021

def r23364 : Route 9 := (fun mask => (mask,id))

def c23364 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23364 : Upper (D 8) (R 8) [320,5,48,160] 13 := by
  apply FastRouting.sound _ _ [320,5,48,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r23364 c23364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23364_3
  · exact m23364_9
  · exact m23364_10
  · exact m23364_33
  · exact m23364_34
  · exact m23364_40
  · exact m23364_65
  · exact m23364_66
  · exact m23364_72
  · exact m23364_96
  · exact m23364_129
  · exact m23364_130
  · exact m23364_136
  · exact m23364_160
  · exact m23364_192

theorem m23365_3 : Upper (D 8) (R 8) [320,5,48,192,3] 13 :=
  permutation_upper _ _ _ [320,5,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17794

theorem m23365_9 : Upper (D 8) (R 8) [320,5,48,192,9] 13 :=
  permutation_upper _ _ _ [320,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17946

theorem m23365_10 : Upper (D 8) (R 8) [320,5,48,192,10] 13 :=
  permutation_upper _ _ _ [320,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17952

theorem m23365_33 : Upper (D 8) (R 8) [320,5,48,192,33] 13 :=
  permutation_upper _ _ _ [320,5,40,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17958

theorem m23365_34 : Upper (D 8) (R 8) [320,5,48,192,34] 13 :=
  permutation_upper _ _ _ [320,5,40,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17963

theorem m23365_40 : Upper (D 8) (R 8) [320,5,48,192,40] 13 :=
  permutation_upper _ _ _ [320,5,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17971

theorem m23365_129 : Upper (D 8) (R 8) [320,5,48,192,129] 13 :=
  permutation_upper _ _ _ [320,5,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17993

theorem m23365_130 : Upper (D 8) (R 8) [320,5,48,192,130] 13 :=
  permutation_upper _ _ _ [320,5,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17999

theorem m23365_136 : Upper (D 8) (R 8) [320,5,48,192,136] 13 :=
  permutation_upper _ _ _ [320,5,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18008

theorem m23365_160 : Upper (D 8) (R 8) [320,5,48,192,160] 13 :=
  permutation_upper _ _ _ [320,5,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18016

def r23365 : Route 9 := (fun mask => (mask,id))

def c23365 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23365 : Upper (D 8) (R 8) [320,5,48,192] 13 := by
  apply FastRouting.sound _ _ [320,5,48,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23365 c23365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23365_3
  · exact m23365_9
  · exact m23365_10
  · exact m23365_33
  · exact m23365_34
  · exact m23365_40
  · exact m23365_129
  · exact m23365_130
  · exact m23365_136
  · exact m23365_160

def b23366 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 26 184 168 232 168 424), lower := (rows 321 7 69 26 16 32 64 128 256), losses := [] }

theorem u23366 : Upper (D 8) (R 8) [320,5,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23367 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 42 184 184 248 184 440), lower := (rows 321 7 69 42 16 32 64 128 256), losses := [] }

theorem u23367 : Upper (D 8) (R 8) [320,5,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23368 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 138 184 184 248 184 440), lower := (rows 321 7 69 138 16 32 64 128 256), losses := [] }

theorem u23368 : Upper (D 8) (R 8) [320,5,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23369 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 69 168 186 186 250 186 442), lower := (rows 321 7 69 168 16 32 64 128 256), losses := [] }

theorem u23369 : Upper (D 8) (R 8) [320,5,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23370 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 41 184 184 248 184 440), lower := (rows 321 7 70 41 16 32 64 128 256), losses := [] }

theorem u23370 : Upper (D 8) (R 8) [320,5,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23371 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 137 184 184 248 184 440), lower := (rows 321 7 70 137 16 32 64 128 256), losses := [] }

theorem u23371 : Upper (D 8) (R 8) [320,5,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23372 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 70 168 185 185 249 185 441), lower := (rows 321 7 70 168 16 32 64 128 256), losses := [] }

theorem u23372 : Upper (D 8) (R 8) [320,5,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23373 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 26 177 161 225 161 417), lower := (rows 321 7 76 26 16 32 64 128 256), losses := [] }

theorem u23373 : Upper (D 8) (R 8) [320,5,72,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23374 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 41 178 178 242 178 434), lower := (rows 321 7 76 41 16 32 64 128 256), losses := [] }

theorem u23374 : Upper (D 8) (R 8) [320,5,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23375 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 42 177 177 241 177 433), lower := (rows 321 7 76 42 16 32 64 128 256), losses := [] }

theorem u23375 : Upper (D 8) (R 8) [320,5,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23376 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 137 178 178 242 178 434), lower := (rows 321 7 76 137 16 32 64 128 256), losses := [] }

theorem u23376 : Upper (D 8) (R 8) [320,5,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23377 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 138 177 177 241 177 433), lower := (rows 321 7 76 138 16 32 64 128 256), losses := [] }

theorem u23377 : Upper (D 8) (R 8) [320,5,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23378 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 76 168 179 179 243 179 435), lower := (rows 321 7 76 168 16 32 64 128 256), losses := [] }

theorem u23378 : Upper (D 8) (R 8) [320,5,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23379 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 84 41 186 170 234 170 426), lower := (rows 321 7 84 41 16 32 64 128 256), losses := [] }

theorem u23379 : Upper (D 8) (R 8) [320,5,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23380 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 84 42 185 169 233 169 425), lower := (rows 321 7 84 42 16 32 64 128 256), losses := [] }

theorem u23380 : Upper (D 8) (R 8) [320,5,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23381 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 84 137 186 170 234 170 426), lower := (rows 321 7 84 137 16 32 64 128 256), losses := [] }

theorem u23381 : Upper (D 8) (R 8) [320,5,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23382 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 84 138 185 169 233 169 425), lower := (rows 321 7 84 138 16 32 64 128 256), losses := [] }

theorem u23382 : Upper (D 8) (R 8) [320,5,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23383 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 84 168 187 171 235 171 427), lower := (rows 321 7 84 168 16 32 64 128 256), losses := [] }

theorem u23383 : Upper (D 8) (R 8) [320,5,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23384 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 26 185 169 233 169 425), lower := (rows 321 7 100 26 16 32 64 128 256), losses := [] }

theorem u23384 : Upper (D 8) (R 8) [320,5,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23385 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 41 186 186 250 186 442), lower := (rows 321 7 100 41 16 32 64 128 256), losses := [] }

theorem u23385 : Upper (D 8) (R 8) [320,5,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23386 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 42 185 185 249 185 441), lower := (rows 321 7 100 42 16 32 64 128 256), losses := [] }

theorem u23386 : Upper (D 8) (R 8) [320,5,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23387 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 137 186 186 250 186 442), lower := (rows 321 7 100 137 16 32 64 128 256), losses := [] }

theorem u23387 : Upper (D 8) (R 8) [320,5,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23388 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 138 185 185 249 185 441), lower := (rows 321 7 100 138 16 32 64 128 256), losses := [] }

theorem u23388 : Upper (D 8) (R 8) [320,5,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23389 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 7 100 168 187 187 251 187 443), lower := (rows 321 7 100 168 16 32 64 128 256), losses := [] }

theorem u23389 : Upper (D 8) (R 8) [320,5,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23390 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 26 248 232 232 232 488), lower := (rows 321 7 133 26 16 32 64 128 256), losses := [] }

theorem u23390 : Upper (D 8) (R 8) [320,5,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23391 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 42 248 248 248 248 504), lower := (rows 321 7 133 42 16 32 64 128 256), losses := [] }

theorem u23391 : Upper (D 8) (R 8) [320,5,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23392 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 74 184 184 248 184 440), lower := (rows 321 7 133 74 16 32 64 128 256), losses := [] }

theorem u23392 : Upper (D 8) (R 8) [320,5,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23393 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 104 186 186 250 186 442), lower := (rows 321 7 133 104 16 32 64 128 256), losses := [] }

theorem u23393 : Upper (D 8) (R 8) [320,5,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23394 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 138 120 120 120 248 376), lower := (rows 321 7 133 138 16 32 64 128 256), losses := [] }

theorem u23394 : Upper (D 8) (R 8) [320,5,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23395 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 168 122 122 122 250 378), lower := (rows 321 7 133 168 16 32 64 128 256), losses := [] }

theorem u23395 : Upper (D 8) (R 8) [320,5,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23396 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 133 200 58 58 122 186 314), lower := (rows 321 7 133 200 16 32 64 128 256), losses := [] }

theorem u23396 : Upper (D 8) (R 8) [320,5,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23397 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 134 25 248 232 232 232 488), lower := (rows 321 7 134 25 16 32 64 128 256), losses := [] }

theorem u23397 : Upper (D 8) (R 8) [320,5,130,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23398 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 134 41 248 248 248 248 504), lower := (rows 321 7 134 41 16 32 64 128 256), losses := [] }

theorem u23398 : Upper (D 8) (R 8) [320,5,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23399_9 : Upper (D 8) (R 8) [320,5,130,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17908

theorem m23399_33 : Upper (D 8) (R 8) [320,5,130,48,33] 13 :=
  permutation_upper _ _ _ [320,5,130,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18105

def r23399 : Route 9 := (fun mask => (mask,id))

def c23399 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23399 : Upper (D 8) (R 8) [320,5,130,48] 13 := by
  apply FastRouting.sound _ _ [320,5,130,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23399 c23399
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23399_9
  · exact m23399_33
  · exact u18111
  · exact u18112
  · exact u18113
  · exact u18114
  · exact u18115
  · exact u18116
  · exact u18117
  · exact u18118

#print axioms u23399
end Delivery.IrregularNine14.P08
