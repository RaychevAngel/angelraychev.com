import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0267
import IrregularNine14P08C0268
import IrregularNine14P08C0269
import IrregularNine14P08C0270

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22500 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 41 240 224 224 224 480), lower := (rows 259 7 28 41 16 32 64 128 256), losses := [] }

theorem u22500 : Upper (D 8) (R 8) [258,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22501 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 28 73 240 224 224 224 480), lower := (rows 259 7 28 73 16 32 64 128 256), losses := [] }

theorem u22501 : Upper (D 8) (R 8) [258,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22502_33 : Upper (D 8) (R 8) [258,5,24,96,33] 13 :=
  permutation_upper _ _ _ [258,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16069

theorem m22502_65 : Upper (D 8) (R 8) [258,5,24,96,65] 13 :=
  permutation_upper _ _ _ [258,5,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16071

theorem m22502_129 : Upper (D 8) (R 8) [258,5,24,96,129] 13 :=
  permutation_upper _ _ _ [258,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16072

def r22502 : Route 9 := (fun mask => (mask,id))

def c22502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22502 : Upper (D 8) (R 8) [258,5,24,96] 13 := by
  apply FastRouting.sound _ _ [258,5,24,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22502 c22502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22502_33
  · exact m22502_65
  · exact u16074
  · exact m22502_129
  · exact u16075
  · exact u16076

theorem m22503_33 : Upper (D 8) (R 8) [258,5,24,192,33] 13 :=
  permutation_upper _ _ _ [258,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16070

theorem m22503_65 : Upper (D 8) (R 8) [258,5,24,192,65] 13 :=
  permutation_upper _ _ _ [258,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16073

theorem m22503_96 : Upper (D 8) (R 8) [258,5,24,192,96] 13 :=
  permutation_upper _ _ _ [258,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16076

def r22503 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22503 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22503 : Upper (D 8) (R 8) [258,5,24,192] 13 := by
  apply FastRouting.sound _ _ [258,5,24,192] 13 (by decide) (choices 2) [33,65,96,192] r22503 c22503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22503_33
  · exact m22503_65
  · exact m22503_96
  · exact u16077

def b22504 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 25 240 224 224 224 480), lower := (rows 259 7 44 25 16 32 64 128 256), losses := [] }

theorem u22504 : Upper (D 8) (R 8) [258,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22505 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 41 240 240 240 240 496), lower := (rows 259 7 44 41 16 32 64 128 256), losses := [] }

theorem u22505 : Upper (D 8) (R 8) [258,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22506 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 56 241 225 225 225 481), lower := (rows 259 7 44 56 16 32 64 128 256), losses := [] }

theorem u22506 : Upper (D 8) (R 8) [258,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22507 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 73 240 240 240 240 496), lower := (rows 259 7 44 73 16 32 64 128 256), losses := [] }

theorem u22507 : Upper (D 8) (R 8) [258,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22508 : Route 9 := (fun mask => (mask,id))

def c22508 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22508 : Upper (D 8) (R 8) [258,5,40,80] 13 := by
  apply FastRouting.sound _ _ [258,5,40,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22508 c22508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16078
  · exact u16079
  · exact u16080
  · exact u16081
  · exact u16082
  · exact u16083

def b22509 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 44 104 241 241 241 241 497), lower := (rows 259 7 44 104 16 32 64 128 256), losses := [] }

theorem u22509 : Upper (D 8) (R 8) [258,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22510 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22510 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22510 : Upper (D 8) (R 8) [258,5,40,192] 13 := by
  apply FastRouting.sound _ _ [258,5,40,192] 13 (by decide) (choices 2) [33,65,96,192] r22510 c22510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16084
  · exact u16085
  · exact u16086
  · exact u16087

def b22511 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 25 240 224 224 224 480), lower := (rows 259 7 76 25 16 32 64 128 256), losses := [] }

theorem u22511 : Upper (D 8) (R 8) [258,5,72,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22512 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 41 240 240 240 240 496), lower := (rows 259 7 76 41 16 32 64 128 256), losses := [] }

theorem u22512 : Upper (D 8) (R 8) [258,5,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22513 : Route 9 := (fun mask => (mask,id))

def c22513 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22513 : Upper (D 8) (R 8) [258,5,72,48] 13 := by
  apply FastRouting.sound _ _ [258,5,72,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22513 c22513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16088
  · exact u16089
  · exact u16090
  · exact u16091
  · exact u16092
  · exact u16093

def b22514 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 259 7 76 73 176 176 240 176 432), lower := (rows 259 7 76 73 16 32 64 128 256), losses := [] }

theorem u22514 : Upper (D 8) (R 8) [258,5,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22515 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 88 177 161 225 161 417), lower := (rows 259 7 76 88 16 32 64 128 256), losses := [] }

theorem u22515 : Upper (D 8) (R 8) [258,5,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22516 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 104 177 177 241 177 433), lower := (rows 259 7 76 104 16 32 64 128 256), losses := [] }

theorem u22516 : Upper (D 8) (R 8) [258,5,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22517 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 76 137 240 240 240 240 496), lower := (rows 259 7 76 137 16 32 64 128 256), losses := [] }

theorem u22517 : Upper (D 8) (R 8) [258,5,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22518 : Route 9 := (fun mask => (mask,id))

def c22518 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22518 : Upper (D 8) (R 8) [258,5,72,144] 13 := by
  apply FastRouting.sound _ _ [258,5,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22518 c22518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16094
  · exact u16095
  · exact u16096
  · exact u16097
  · exact u16098
  · exact u16099

def r22519 : Route 9 := (fun mask => (mask,id))

def c22519 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22519 : Upper (D 8) (R 8) [258,5,72,160] 13 := by
  apply FastRouting.sound _ _ [258,5,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22519 c22519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16100
  · exact u16101
  · exact u16102
  · exact u16103
  · exact u16104
  · exact u16105

def b22520 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 76 200 177 177 241 177 433), lower := (rows 259 7 76 200 16 32 64 128 256), losses := [] }

theorem u22520 : Upper (D 8) (R 8) [258,5,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22521 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 25 248 232 232 232 488), lower := (rows 259 7 100 25 16 32 64 128 256), losses := [] }

theorem u22521 : Upper (D 8) (R 8) [258,5,96,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22522 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 41 248 248 248 248 504), lower := (rows 259 7 100 41 16 32 64 128 256), losses := [] }

theorem u22522 : Upper (D 8) (R 8) [258,5,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22523_9 : Upper (D 8) (R 8) [258,5,96,48,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16106

theorem m22523_33 : Upper (D 8) (R 8) [258,5,96,48,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16111

def r22523 : Route 9 := (fun mask => (mask,id))

def c22523 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22523 : Upper (D 8) (R 8) [258,5,96,48] 13 := by
  apply FastRouting.sound _ _ [258,5,96,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22523 c22523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22523_9
  · exact m22523_33
  · exact u16116
  · exact u16117
  · exact u16118
  · exact u16119
  · exact u16120
  · exact u16121
  · exact u16122
  · exact u16123

def b22524 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 73 184 184 248 184 440), lower := (rows 259 7 100 73 16 32 64 128 256), losses := [] }

theorem u22524 : Upper (D 8) (R 8) [258,5,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22525_9 : Upper (D 8) (R 8) [258,5,96,80,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16107

theorem m22525_33 : Upper (D 8) (R 8) [258,5,96,80,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16112

theorem m22525_40 : Upper (D 8) (R 8) [258,5,96,80,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16118

def r22525 : Route 9 := (fun mask => (mask,id))

def c22525 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22525 : Upper (D 8) (R 8) [258,5,96,80] 13 := by
  apply FastRouting.sound _ _ [258,5,96,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22525 c22525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22525_9
  · exact m22525_33
  · exact m22525_40
  · exact u16126
  · exact u16127
  · exact u16128

def b22526 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 100 104 185 185 249 185 441), lower := (rows 259 7 100 104 16 32 64 128 256), losses := [] }

theorem u22526 : Upper (D 8) (R 8) [258,5,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22527 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 100 137 248 248 248 248 504), lower := (rows 259 7 100 137 16 32 64 128 256), losses := [] }

theorem u22527 : Upper (D 8) (R 8) [258,5,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22528_9 : Upper (D 8) (R 8) [258,5,96,144,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16108

theorem m22528_33 : Upper (D 8) (R 8) [258,5,96,144,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16113

theorem m22528_40 : Upper (D 8) (R 8) [258,5,96,144,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16121

theorem m22528_65 : Upper (D 8) (R 8) [258,5,96,144,65] 13 :=
  permutation_upper _ _ _ [258,5,96,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16124

theorem m22528_72 : Upper (D 8) (R 8) [258,5,96,144,72] 13 :=
  permutation_upper _ _ _ [258,5,96,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16127

theorem m22528_96 : Upper (D 8) (R 8) [258,5,96,144,96] 13 :=
  permutation_upper _ _ _ [258,5,96,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16129

theorem m22528_129 : Upper (D 8) (R 8) [258,5,96,144,129] 13 :=
  permutation_upper _ _ _ [258,5,96,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16131

def r22528 : Route 9 := (fun mask => (mask,id))

def c22528 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22528 : Upper (D 8) (R 8) [258,5,96,144] 13 := by
  apply FastRouting.sound _ _ [258,5,96,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22528 c22528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22528_9
  · exact m22528_33
  · exact m22528_40
  · exact m22528_65
  · exact m22528_72
  · exact m22528_96
  · exact m22528_129
  · exact u16134
  · exact u16135
  · exact u16136

theorem m22529_9 : Upper (D 8) (R 8) [258,5,96,160,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16109

theorem m22529_33 : Upper (D 8) (R 8) [258,5,96,160,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16114

theorem m22529_40 : Upper (D 8) (R 8) [258,5,96,160,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16122

theorem m22529_65 : Upper (D 8) (R 8) [258,5,96,160,65] 13 :=
  permutation_upper _ _ _ [258,5,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16125

theorem m22529_72 : Upper (D 8) (R 8) [258,5,96,160,72] 13 :=
  permutation_upper _ _ _ [258,5,96,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16128

theorem m22529_96 : Upper (D 8) (R 8) [258,5,96,160,96] 13 :=
  permutation_upper _ _ _ [258,5,96,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16130

theorem m22529_129 : Upper (D 8) (R 8) [258,5,96,160,129] 13 :=
  permutation_upper _ _ _ [258,5,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16132

theorem m22529_136 : Upper (D 8) (R 8) [258,5,96,160,136] 13 :=
  permutation_upper _ _ _ [258,5,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16135

def r22529 : Route 9 := (fun mask => (mask,id))

def c22529 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22529 : Upper (D 8) (R 8) [258,5,96,160] 13 := by
  apply FastRouting.sound _ _ [258,5,96,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22529 c22529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22529_9
  · exact m22529_33
  · exact m22529_40
  · exact m22529_65
  · exact m22529_72
  · exact m22529_96
  · exact m22529_129
  · exact m22529_136
  · exact u16137
  · exact u16138

theorem m22530_9 : Upper (D 8) (R 8) [258,5,96,192,9] 13 :=
  permutation_upper _ _ _ [258,5,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16110

theorem m22530_33 : Upper (D 8) (R 8) [258,5,96,192,33] 13 :=
  permutation_upper _ _ _ [258,5,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16115

theorem m22530_40 : Upper (D 8) (R 8) [258,5,96,192,40] 13 :=
  permutation_upper _ _ _ [258,5,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16123

theorem m22530_129 : Upper (D 8) (R 8) [258,5,96,192,129] 13 :=
  permutation_upper _ _ _ [258,5,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16133

theorem m22530_136 : Upper (D 8) (R 8) [258,5,96,192,136] 13 :=
  permutation_upper _ _ _ [258,5,96,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16136

theorem m22530_160 : Upper (D 8) (R 8) [258,5,96,192,160] 13 :=
  permutation_upper _ _ _ [258,5,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16138

def r22530 : Route 9 := (fun mask => (mask,id))

def c22530 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22530 : Upper (D 8) (R 8) [258,5,96,192] 13 := by
  apply FastRouting.sound _ _ [258,5,96,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22530 c22530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22530_9
  · exact m22530_33
  · exact m22530_40
  · exact m22530_129
  · exact m22530_136
  · exact m22530_160

def b22531 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 25 248 232 232 232 488), lower := (rows 259 7 196 25 16 32 64 128 256), losses := [] }

theorem u22531 : Upper (D 8) (R 8) [258,5,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22532 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 41 248 248 248 248 504), lower := (rows 259 7 196 41 16 32 64 128 256), losses := [] }

theorem u22532 : Upper (D 8) (R 8) [258,5,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22533_9 : Upper (D 8) (R 8) [258,5,192,48,9] 13 :=
  permutation_upper _ _ _ [258,5,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16139

theorem m22533_33 : Upper (D 8) (R 8) [258,5,192,48,33] 13 :=
  permutation_upper _ _ _ [258,5,192,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16142

def r22533 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22533 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22533 : Upper (D 8) (R 8) [258,5,192,48] 13 := by
  apply FastRouting.sound _ _ [258,5,192,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22533 c22533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22533_9
  · exact m22533_33
  · exact u16145
  · exact u16146
  · exact u16147
  · exact u16148
  · exact u16149

def b22534 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 7 196 73 184 184 248 184 440), lower := (rows 259 7 196 73 16 32 64 128 256), losses := [] }

theorem u22534 : Upper (D 8) (R 8) [258,5,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22535_9 : Upper (D 8) (R 8) [258,5,192,80,9] 13 :=
  permutation_upper _ _ _ [258,5,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16140

theorem m22535_33 : Upper (D 8) (R 8) [258,5,192,80,33] 13 :=
  permutation_upper _ _ _ [258,5,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16143

theorem m22535_40 : Upper (D 8) (R 8) [258,5,192,80,40] 13 :=
  permutation_upper _ _ _ [258,5,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16147

theorem m22535_129 : Upper (D 8) (R 8) [258,5,192,80,129] 13 :=
  permutation_upper _ _ _ [258,5,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16150

def r22535 : Route 9 := (fun mask => (mask,id))

def c22535 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22535 : Upper (D 8) (R 8) [258,5,192,80] 13 := by
  apply FastRouting.sound _ _ [258,5,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22535 c22535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22535_9
  · exact m22535_33
  · exact m22535_40
  · exact m22535_129
  · exact u16152
  · exact u16153

theorem m22536_9 : Upper (D 8) (R 8) [258,5,192,96,9] 13 :=
  permutation_upper _ _ _ [258,5,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16141

theorem m22536_33 : Upper (D 8) (R 8) [258,5,192,96,33] 13 :=
  permutation_upper _ _ _ [258,5,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16144

theorem m22536_40 : Upper (D 8) (R 8) [258,5,192,96,40] 13 :=
  permutation_upper _ _ _ [258,5,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16148

theorem m22536_129 : Upper (D 8) (R 8) [258,5,192,96,129] 13 :=
  permutation_upper _ _ _ [258,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16151

theorem m22536_136 : Upper (D 8) (R 8) [258,5,192,96,136] 13 :=
  permutation_upper _ _ _ [258,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16153

def r22536 : Route 9 := (fun mask => (mask,id))

def c22536 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22536 : Upper (D 8) (R 8) [258,5,192,96] 13 := by
  apply FastRouting.sound _ _ [258,5,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22536 c22536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22536_9
  · exact m22536_33
  · exact m22536_40
  · exact m22536_129
  · exact m22536_136
  · exact u16154

def b22537 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 7 196 200 57 57 121 185 313), lower := (rows 259 7 196 200 16 32 64 128 256), losses := [] }

theorem u22537 : Upper (D 8) (R 8) [258,5,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22538 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 21 41 240 224 224 224 480), lower := (rows 259 14 21 41 16 32 64 128 256), losses := [] }

theorem u22538 : Upper (D 8) (R 8) [258,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22539 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 21 73 240 224 224 224 480), lower := (rows 259 14 21 73 16 32 64 128 256), losses := [] }

theorem u22539 : Upper (D 8) (R 8) [258,12,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22540 : Route 9 := (fun mask => (mask,id))

def c22540 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22540 : Upper (D 8) (R 8) [258,12,17,96] 13 := by
  apply FastRouting.sound _ _ [258,12,17,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22540 c22540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16155
  · exact u16156
  · exact u16157
  · exact u16158
  · exact u16159
  · exact u16160

def r22541 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22541 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22541 : Upper (D 8) (R 8) [258,12,17,192] 13 := by
  apply FastRouting.sound _ _ [258,12,17,192] 13 (by decide) (choices 2) [33,65,96,192] r22541 c22541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16161
  · exact u16162
  · exact u16163
  · exact u16164

def b22542 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 259 14 37 41 240 240 240 240 496), lower := (rows 259 14 37 41 16 32 64 128 256), losses := [] }

theorem u22542 : Upper (D 8) (R 8) [258,12,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22543 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22543 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22543 : Upper (D 8) (R 8) [258,12,33,48] 13 := by
  apply FastRouting.sound _ _ [258,12,33,48] 13 (by decide) (choices 2) [33,65,96,192] r22543 c22543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16165
  · exact u16166
  · exact u16167
  · exact u16168

def b22544 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 37 73 240 240 240 240 496), lower := (rows 259 14 37 73 16 32 64 128 256), losses := [] }

theorem u22544 : Upper (D 8) (R 8) [258,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22545 : Route 9 := (fun mask => (mask,id))

def c22545 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22545 : Upper (D 8) (R 8) [258,12,33,80] 13 := by
  apply FastRouting.sound _ _ [258,12,33,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22545 c22545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16169
  · exact u16170
  · exact u16171
  · exact u16172
  · exact u16173
  · exact u16174

def r22546 : Route 9 := (fun mask => (mask,id))

def c22546 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22546 : Upper (D 8) (R 8) [258,12,33,96] 13 := by
  apply FastRouting.sound _ _ [258,12,33,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22546 c22546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16175
  · exact u16176
  · exact u16177
  · exact u16178
  · exact u16179
  · exact u16180

def r22547 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22547 : Upper (D 8) (R 8) [258,12,33,192] 13 := by
  apply FastRouting.sound _ _ [258,12,33,192] 13 (by decide) (choices 2) [33,65,96,192] r22547 c22547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16181
  · exact u16182
  · exact u16183
  · exact u16184

def r22548 : Route 9 := (fun mask => (mask,id))

def c22548 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22548 : Upper (D 8) (R 8) [258,12,48,65] 13 := by
  apply FastRouting.sound _ _ [258,12,48,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22548 c22548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16185
  · exact u16186
  · exact u16187
  · exact u16188
  · exact u16189
  · exact u16190

def r22549 : Route 9 := (fun mask => (mask,id))

def c22549 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22549 : Upper (D 8) (R 8) [258,12,48,96] 13 := by
  apply FastRouting.sound _ _ [258,12,48,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22549 c22549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16191
  · exact u16192
  · exact u16193
  · exact u16194
  · exact u16195
  · exact u16196

def r22550 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22550 : Upper (D 8) (R 8) [258,12,48,192] 13 := by
  apply FastRouting.sound _ _ [258,12,48,192] 13 (by decide) (choices 2) [33,65,96,192] r22550 c22550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16197
  · exact u16198
  · exact u16199
  · exact u16200

def b22551 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 259 14 69 73 176 176 240 176 432), lower := (rows 259 14 69 73 16 32 64 128 256), losses := [] }

theorem u22551 : Upper (D 8) (R 8) [258,12,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22552 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 69 88 177 161 225 161 417), lower := (rows 259 14 69 88 16 32 64 128 256), losses := [] }

theorem u22552 : Upper (D 8) (R 8) [258,12,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22553 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 69 104 177 177 241 177 433), lower := (rows 259 14 69 104 16 32 64 128 256), losses := [] }

theorem u22553 : Upper (D 8) (R 8) [258,12,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22554 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 259 14 69 137 240 240 240 240 496), lower := (rows 259 14 69 137 16 32 64 128 256), losses := [] }

theorem u22554 : Upper (D 8) (R 8) [258,12,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22555 : Route 9 := (fun mask => (mask,id))

def c22555 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22555 : Upper (D 8) (R 8) [258,12,65,144] 13 := by
  apply FastRouting.sound _ _ [258,12,65,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22555 c22555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16201
  · exact u16202
  · exact u16203
  · exact u16204
  · exact u16205
  · exact u16206

def r22556 : Route 9 := (fun mask => (mask,id))

def c22556 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22556 : Upper (D 8) (R 8) [258,12,65,160] 13 := by
  apply FastRouting.sound _ _ [258,12,65,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22556 c22556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16207
  · exact u16208
  · exact u16209
  · exact u16210
  · exact u16211
  · exact u16212

def b22557 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 69 200 177 177 241 177 433), lower := (rows 259 14 69 200 16 32 64 128 256), losses := [] }

theorem u22557 : Upper (D 8) (R 8) [258,12,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22558 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 84 104 177 161 225 161 417), lower := (rows 259 14 84 104 16 32 64 128 256), losses := [] }

theorem u22558 : Upper (D 8) (R 8) [258,12,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22559 : Route 9 := (fun mask => (mask,id))

def c22559 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22559 : Upper (D 8) (R 8) [258,12,80,160] 13 := by
  apply FastRouting.sound _ _ [258,12,80,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22559 c22559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16213
  · exact u16214
  · exact u16215
  · exact u16216
  · exact u16217
  · exact u16218

#print axioms u22559
end Delivery.IrregularNine14.P08
