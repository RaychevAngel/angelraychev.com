import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0270
import IrregularNine14P08C0271
import IrregularNine14P08C0272

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22560 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 84 200 177 161 225 161 417), lower := (rows 259 14 84 200 16 32 64 128 256), losses := [] }

theorem u22560 : Upper (D 8) (R 8) [258,12,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22561 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 100 104 177 177 241 177 433), lower := (rows 259 14 100 104 16 32 64 128 256), losses := [] }

theorem u22561 : Upper (D 8) (R 8) [258,12,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22562_129 : Upper (D 8) (R 8) [258,12,96,160,129] 13 :=
  permutation_upper _ _ _ [258,12,96,160,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16220

theorem m22562_160 : Upper (D 8) (R 8) [258,12,96,160,160] 13 :=
  permutation_upper _ _ _ [258,12,96,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16221

def r22562 : Route 9 := (fun mask => (mask,id))

def c22562 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22562 : Upper (D 8) (R 8) [258,12,96,160] 13 := by
  apply FastRouting.sound _ _ [258,12,96,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22562 c22562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16219
  · exact u16220
  · exact u16221
  · exact m22562_129
  · exact m22562_160
  · exact u16222

def b22563 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 14 100 200 177 177 241 177 433), lower := (rows 259 14 100 200 16 32 64 128 256), losses := [] }

theorem u22563 : Upper (D 8) (R 8) [258,12,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22564 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 259 14 196 200 49 49 113 177 305), lower := (rows 259 14 196 200 16 32 64 128 256), losses := [] }

theorem u22564 : Upper (D 8) (R 8) [258,12,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22565 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 28 240 224 224 224 480), lower := (rows 259 35 13 28 16 32 64 128 256), losses := [] }

theorem u22565 : Upper (D 8) (R 8) [258,33,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22566 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 13 44 240 240 240 240 496), lower := (rows 259 35 13 44 16 32 64 128 256), losses := [] }

theorem u22566 : Upper (D 8) (R 8) [258,33,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22567 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 76 240 240 240 240 496), lower := (rows 259 35 13 76 16 32 64 128 256), losses := [] }

theorem u22567 : Upper (D 8) (R 8) [258,33,9,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22568 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 104 244 244 244 244 500), lower := (rows 259 35 13 104 16 32 64 128 256), losses := [] }

theorem u22568 : Upper (D 8) (R 8) [258,33,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22569 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 200 244 244 244 244 500), lower := (rows 259 35 13 200 16 32 64 128 256), losses := [] }

theorem u22569 : Upper (D 8) (R 8) [258,33,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22570 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 21 44 248 232 232 232 488), lower := (rows 259 35 21 44 16 32 64 128 256), losses := [] }

theorem u22570 : Upper (D 8) (R 8) [258,33,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22571 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 21 76 248 232 232 232 488), lower := (rows 259 35 21 76 16 32 64 128 256), losses := [] }

theorem u22571 : Upper (D 8) (R 8) [258,33,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22572 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 21 104 252 236 236 236 492), lower := (rows 259 35 21 104 16 32 64 128 256), losses := [] }

theorem u22572 : Upper (D 8) (R 8) [258,33,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22573 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 21 200 252 236 236 236 492), lower := (rows 259 35 21 200 16 32 64 128 256), losses := [] }

theorem u22573 : Upper (D 8) (R 8) [258,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22574 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 259 35 28 41 244 228 228 228 484), lower := (rows 259 35 28 41 16 32 64 128 256), losses := [] }

theorem u22574 : Upper (D 8) (R 8) [258,33,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22575_33 : Upper (D 8) (R 8) [258,33,24,36,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16243

def r22575 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22575 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22575 : Upper (D 8) (R 8) [258,33,24,36] 13 := by
  apply FastRouting.sound _ _ [258,33,24,36] 13 (by decide) (choices 2) [33,65,96,192] r22575 c22575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22575_33
  · exact u16247
  · exact u16248
  · exact u16249

def b22576 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 28 73 244 228 228 228 484), lower := (rows 259 35 28 73 16 32 64 128 256), losses := [] }

theorem u22576 : Upper (D 8) (R 8) [258,33,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22577_33 : Upper (D 8) (R 8) [258,33,24,68,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16244

theorem m22577_65 : Upper (D 8) (R 8) [258,33,24,68,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16250

theorem m22577_129 : Upper (D 8) (R 8) [258,33,24,68,129] 13 :=
  permutation_upper _ _ _ [258,33,24,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16252

def r22577 : Route 9 := (fun mask => (mask,id))

def c22577 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22577 : Upper (D 8) (R 8) [258,33,24,68] 13 := by
  apply FastRouting.sound _ _ [258,33,24,68] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22577 c22577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22577_33
  · exact m22577_65
  · exact u16255
  · exact m22577_129
  · exact u16256
  · exact u16257

theorem m22578_5 : Upper (D 8) (R 8) [258,33,24,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16223

theorem m22578_33 : Upper (D 8) (R 8) [258,33,24,96,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16245

theorem m22578_36 : Upper (D 8) (R 8) [258,33,24,96,36] 13 :=
  permutation_upper _ _ _ [258,33,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16248

theorem m22578_65 : Upper (D 8) (R 8) [258,33,24,96,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16251

theorem m22578_68 : Upper (D 8) (R 8) [258,33,24,96,68] 13 :=
  permutation_upper _ _ _ [258,33,24,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16255

theorem m22578_129 : Upper (D 8) (R 8) [258,33,24,96,129] 13 :=
  permutation_upper _ _ _ [258,33,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16253

theorem m22578_132 : Upper (D 8) (R 8) [258,33,24,96,132] 13 :=
  permutation_upper _ _ _ [258,33,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16256

def r22578 : Route 9 := (fun mask => (mask,id))

def c22578 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22578 : Upper (D 8) (R 8) [258,33,24,96] 13 := by
  apply FastRouting.sound _ _ [258,33,24,96] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22578 c22578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22578_5
  · exact m22578_33
  · exact m22578_36
  · exact m22578_65
  · exact m22578_68
  · exact u16258
  · exact m22578_129
  · exact m22578_132
  · exact u16259
  · exact u16260

theorem m22579_5 : Upper (D 8) (R 8) [258,33,24,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16224

theorem m22579_33 : Upper (D 8) (R 8) [258,33,24,192,33] 13 :=
  permutation_upper _ _ _ [258,33,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16246

theorem m22579_36 : Upper (D 8) (R 8) [258,33,24,192,36] 13 :=
  permutation_upper _ _ _ [258,33,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16249

theorem m22579_65 : Upper (D 8) (R 8) [258,33,24,192,65] 13 :=
  permutation_upper _ _ _ [258,33,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16254

theorem m22579_68 : Upper (D 8) (R 8) [258,33,24,192,68] 13 :=
  permutation_upper _ _ _ [258,33,24,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16257

theorem m22579_96 : Upper (D 8) (R 8) [258,33,24,192,96] 13 :=
  permutation_upper _ _ _ [258,33,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16260

def r22579 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22579 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22579 : Upper (D 8) (R 8) [258,33,24,192] 13 := by
  apply FastRouting.sound _ _ [258,33,24,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r22579 c22579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22579_5
  · exact m22579_33
  · exact m22579_36
  · exact m22579_65
  · exact m22579_68
  · exact m22579_96
  · exact u16261

def b22580 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 44 216 248 216 216 472), lower := (rows 259 35 37 44 16 32 64 128 256), losses := [] }

theorem u22580 : Upper (D 8) (R 8) [258,33,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22581 : PairBound 9 := { available := 248, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 76 248 248 248 248 504), lower := (rows 259 35 37 76 16 32 64 128 256), losses := [] }

theorem u22581 : Upper (D 8) (R 8) [258,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22582 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 104 220 252 220 220 476), lower := (rows 259 35 37 104 16 32 64 128 256), losses := [] }

theorem u22582 : Upper (D 8) (R 8) [258,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22583 : PairBound 9 := { available := 252, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 200 252 252 252 252 508), lower := (rows 259 35 37 200 16 32 64 128 256), losses := [] }

theorem u22583 : Upper (D 8) (R 8) [258,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22584 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 44 209 241 209 209 465), lower := (rows 259 35 44 44 16 32 64 128 256), losses := [] }

theorem u22584 : Upper (D 8) (R 8) [258,33,40,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22585 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 56 213 229 197 197 453), lower := (rows 259 35 44 56 16 32 64 128 256), losses := [] }

theorem u22585 : Upper (D 8) (R 8) [258,33,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22586 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 73 244 244 244 244 500), lower := (rows 259 35 44 73 16 32 64 128 256), losses := [] }

theorem u22586 : Upper (D 8) (R 8) [258,33,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22587_33 : Upper (D 8) (R 8) [258,33,40,68,33] 13 :=
  permutation_upper _ _ _ [258,33,33,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16265

def r22587 : Route 9 := (fun mask => (mask,id))

def c22587 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22587 : Upper (D 8) (R 8) [258,33,40,68] 13 := by
  apply FastRouting.sound _ _ [258,33,40,68] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22587 c22587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22587_33
  · exact u16282
  · exact u16283
  · exact u16284
  · exact u16285
  · exact u16286

theorem m22588_5 : Upper (D 8) (R 8) [258,33,40,80,5] 13 :=
  permutation_upper _ _ _ [258,33,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16227

theorem m22588_33 : Upper (D 8) (R 8) [258,33,40,80,33] 13 :=
  permutation_upper _ _ _ [258,33,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16264

theorem m22588_36 : Upper (D 8) (R 8) [258,33,40,80,36] 13 :=
  permutation_upper _ _ _ [258,33,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16275

def r22588 : Route 9 := (fun mask => (mask,id))

def c22588 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22588 : Upper (D 8) (R 8) [258,33,40,80] 13 := by
  apply FastRouting.sound _ _ [258,33,40,80] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22588 c22588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22588_5
  · exact m22588_33
  · exact m22588_36
  · exact u16287
  · exact u16288
  · exact u16289
  · exact u16290
  · exact u16291
  · exact u16292
  · exact u16293

def b22589 : PairBound 9 := { available := 213, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 44 104 213 245 213 213 469), lower := (rows 259 35 44 104 16 32 64 128 256), losses := [] }

theorem u22589 : Upper (D 8) (R 8) [258,33,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22590_5 : Upper (D 8) (R 8) [258,33,40,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16228

theorem m22590_33 : Upper (D 8) (R 8) [258,33,40,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16266

theorem m22590_36 : Upper (D 8) (R 8) [258,33,40,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16276

def r22590 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22590 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22590 : Upper (D 8) (R 8) [258,33,40,192] 13 := by
  apply FastRouting.sound _ _ [258,33,40,192] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r22590 c22590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22590_5
  · exact m22590_33
  · exact m22590_36
  · exact u16297
  · exact u16298
  · exact u16299
  · exact u16300

theorem m22591_9 : Upper (D 8) (R 8) [258,33,48,68,9] 13 :=
  permutation_upper _ _ _ [258,33,9,80,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16232

theorem m22591_33 : Upper (D 8) (R 8) [258,33,48,68,33] 13 :=
  permutation_upper _ _ _ [258,33,33,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16262

theorem m22591_40 : Upper (D 8) (R 8) [258,33,48,68,40] 13 :=
  permutation_upper _ _ _ [258,33,40,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16275

theorem m22591_65 : Upper (D 8) (R 8) [258,33,48,68,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16277

theorem m22591_72 : Upper (D 8) (R 8) [258,33,48,68,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16288

theorem m22591_96 : Upper (D 8) (R 8) [258,33,48,68,96] 13 :=
  permutation_upper _ _ _ [258,33,40,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16294

theorem m22591_129 : Upper (D 8) (R 8) [258,33,48,68,129] 13 :=
  permutation_upper _ _ _ [258,33,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16279

theorem m22591_136 : Upper (D 8) (R 8) [258,33,48,68,136] 13 :=
  permutation_upper _ _ _ [258,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16291

theorem m22591_160 : Upper (D 8) (R 8) [258,33,48,68,160] 13 :=
  permutation_upper _ _ _ [258,33,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16295

theorem m22591_192 : Upper (D 8) (R 8) [258,33,48,68,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16298

def r22591 : Route 9 := (fun mask => (mask,id))

def c22591 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22591 : Upper (D 8) (R 8) [258,33,48,68] 13 := by
  apply FastRouting.sound _ _ [258,33,48,68] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r22591 c22591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22591_9
  · exact m22591_33
  · exact m22591_40
  · exact m22591_65
  · exact m22591_72
  · exact m22591_96
  · exact m22591_129
  · exact m22591_136
  · exact m22591_160
  · exact m22591_192

theorem m22592_5 : Upper (D 8) (R 8) [258,33,48,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16225

theorem m22592_9 : Upper (D 8) (R 8) [258,33,48,96,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16235

theorem m22592_12 : Upper (D 8) (R 8) [258,33,48,96,12] 13 :=
  permutation_upper _ _ _ [258,33,24,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16248

theorem m22592_65 : Upper (D 8) (R 8) [258,33,48,96,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16278

theorem m22592_68 : Upper (D 8) (R 8) [258,33,48,96,68] 13 :=
  permutation_upper _ _ _ [258,33,40,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16283

theorem m22592_72 : Upper (D 8) (R 8) [258,33,48,96,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16289

theorem m22592_129 : Upper (D 8) (R 8) [258,33,48,96,129] 13 :=
  permutation_upper _ _ _ [258,33,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16280

theorem m22592_132 : Upper (D 8) (R 8) [258,33,48,96,132] 13 :=
  permutation_upper _ _ _ [258,33,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16285

theorem m22592_136 : Upper (D 8) (R 8) [258,33,48,96,136] 13 :=
  permutation_upper _ _ _ [258,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16292

theorem m22592_192 : Upper (D 8) (R 8) [258,33,48,96,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16299

def r22592 : Route 9 := (fun mask => (mask,id))

def c22592 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22592 : Upper (D 8) (R 8) [258,33,48,96] 13 := by
  apply FastRouting.sound _ _ [258,33,48,96] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r22592 c22592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22592_5
  · exact m22592_9
  · exact m22592_12
  · exact m22592_65
  · exact m22592_68
  · exact m22592_72
  · exact m22592_129
  · exact m22592_132
  · exact m22592_136
  · exact m22592_192

theorem m22593_5 : Upper (D 8) (R 8) [258,33,48,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16226

theorem m22593_9 : Upper (D 8) (R 8) [258,33,48,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16240

theorem m22593_12 : Upper (D 8) (R 8) [258,33,48,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16249

theorem m22593_33 : Upper (D 8) (R 8) [258,33,48,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16263

theorem m22593_36 : Upper (D 8) (R 8) [258,33,48,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16274

theorem m22593_40 : Upper (D 8) (R 8) [258,33,48,192,40] 13 :=
  permutation_upper _ _ _ [258,33,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16276

theorem m22593_65 : Upper (D 8) (R 8) [258,33,48,192,65] 13 :=
  permutation_upper _ _ _ [258,33,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16281

theorem m22593_68 : Upper (D 8) (R 8) [258,33,48,192,68] 13 :=
  permutation_upper _ _ _ [258,33,40,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16286

theorem m22593_72 : Upper (D 8) (R 8) [258,33,48,192,72] 13 :=
  permutation_upper _ _ _ [258,33,40,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16293

theorem m22593_96 : Upper (D 8) (R 8) [258,33,48,192,96] 13 :=
  permutation_upper _ _ _ [258,33,40,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16296

theorem m22593_192 : Upper (D 8) (R 8) [258,33,48,192,192] 13 :=
  permutation_upper _ _ _ [258,33,40,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16300

def r22593 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22593 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22593 : Upper (D 8) (R 8) [258,33,48,192] 13 := by
  apply FastRouting.sound _ _ [258,33,48,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,192] r22593 c22593
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22593_5
  · exact m22593_9
  · exact m22593_12
  · exact m22593_33
  · exact m22593_36
  · exact m22593_40
  · exact m22593_65
  · exact m22593_68
  · exact m22593_72
  · exact m22593_96
  · exact m22593_192

def b22594 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 69 76 184 184 248 184 440), lower := (rows 259 35 69 76 16 32 64 128 256), losses := [] }

theorem u22594 : Upper (D 8) (R 8) [258,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22595 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 104 188 188 252 188 444), lower := (rows 259 35 69 104 16 32 64 128 256), losses := [] }

theorem u22595 : Upper (D 8) (R 8) [258,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22596 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 140 248 248 248 248 504), lower := (rows 259 35 69 140 16 32 64 128 256), losses := [] }

theorem u22596 : Upper (D 8) (R 8) [258,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22597 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 168 252 252 252 252 508), lower := (rows 259 35 69 168 16 32 64 128 256), losses := [] }

theorem u22597 : Upper (D 8) (R 8) [258,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22598 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 200 188 188 252 188 444), lower := (rows 259 35 69 200 16 32 64 128 256), losses := [] }

theorem u22598 : Upper (D 8) (R 8) [258,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22599 : PairBound 9 := { available := 177, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 35 76 76 177 177 241 177 433), lower := (rows 259 35 76 76 16 32 64 128 256), losses := [] }

theorem u22599 : Upper (D 8) (R 8) [258,33,72,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22600 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 88 181 165 229 165 421), lower := (rows 259 35 76 88 16 32 64 128 256), losses := [] }

theorem u22600 : Upper (D 8) (R 8) [258,33,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22601 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 104 181 181 245 181 437), lower := (rows 259 35 76 104 16 32 64 128 256), losses := [] }

theorem u22601 : Upper (D 8) (R 8) [258,33,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22602_33 : Upper (D 8) (R 8) [258,33,72,132,33] 13 :=
  permutation_upper _ _ _ [258,33,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16271

theorem m22602_65 : Upper (D 8) (R 8) [258,33,72,132,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16304

theorem m22602_129 : Upper (D 8) (R 8) [258,33,72,132,129] 13 :=
  permutation_upper _ _ _ [258,33,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16304

theorem m22602_160 : Upper (D 8) (R 8) [258,33,72,132,160] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16317

def r22602 : Route 9 := (fun mask => (mask,id))

def c22602 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22602 : Upper (D 8) (R 8) [258,33,72,132] 13 := by
  apply FastRouting.sound _ _ [258,33,72,132] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22602 c22602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22602_33
  · exact m22602_65
  · exact u16317
  · exact m22602_129
  · exact m22602_160
  · exact u16318

theorem m22603_5 : Upper (D 8) (R 8) [258,33,72,144,5] 13 :=
  permutation_upper _ _ _ [258,33,9,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16233

theorem m22603_33 : Upper (D 8) (R 8) [258,33,72,144,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16268

theorem m22603_36 : Upper (D 8) (R 8) [258,33,72,144,36] 13 :=
  permutation_upper _ _ _ [258,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16291

theorem m22603_65 : Upper (D 8) (R 8) [258,33,72,144,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16303

theorem m22603_68 : Upper (D 8) (R 8) [258,33,72,144,68] 13 :=
  permutation_upper _ _ _ [258,33,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16313

theorem m22603_129 : Upper (D 8) (R 8) [258,33,72,144,129] 13 :=
  permutation_upper _ _ _ [258,33,65,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16301

theorem m22603_132 : Upper (D 8) (R 8) [258,33,72,144,132] 13 :=
  permutation_upper _ _ _ [258,33,72,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16313

theorem m22603_160 : Upper (D 8) (R 8) [258,33,72,144,160] 13 :=
  permutation_upper _ _ _ [258,33,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16315

def r22603 : Route 9 := (fun mask => (mask,id))

def c22603 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22603 : Upper (D 8) (R 8) [258,33,72,144] 13 := by
  apply FastRouting.sound _ _ [258,33,72,144] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22603 c22603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22603_5
  · exact m22603_33
  · exact m22603_36
  · exact m22603_65
  · exact m22603_68
  · exact u16319
  · exact m22603_129
  · exact m22603_132
  · exact m22603_160
  · exact u16320

theorem m22604_5 : Upper (D 8) (R 8) [258,33,72,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16234

theorem m22604_33 : Upper (D 8) (R 8) [258,33,72,160,33] 13 :=
  permutation_upper _ _ _ [258,33,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16272

theorem m22604_36 : Upper (D 8) (R 8) [258,33,72,160,36] 13 :=
  permutation_upper _ _ _ [258,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16292

theorem m22604_65 : Upper (D 8) (R 8) [258,33,72,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16305

theorem m22604_68 : Upper (D 8) (R 8) [258,33,72,160,68] 13 :=
  permutation_upper _ _ _ [258,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16314

theorem m22604_129 : Upper (D 8) (R 8) [258,33,72,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16307

theorem m22604_132 : Upper (D 8) (R 8) [258,33,72,160,132] 13 :=
  permutation_upper _ _ _ [258,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16319

def r22604 : Route 9 := (fun mask => (mask,id))

def c22604 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22604 : Upper (D 8) (R 8) [258,33,72,160] 13 := by
  apply FastRouting.sound _ _ [258,33,72,160] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r22604 c22604
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22604_5
  · exact m22604_33
  · exact m22604_36
  · exact m22604_65
  · exact m22604_68
  · exact u16321
  · exact m22604_129
  · exact m22604_132
  · exact u16322
  · exact u16323

def b22605 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 259 35 76 200 181 181 245 181 437), lower := (rows 259 35 76 200 16 32 64 128 256), losses := [] }

theorem u22605 : Upper (D 8) (R 8) [258,33,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22606_5 : Upper (D 8) (R 8) [258,33,80,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16229

theorem m22606_9 : Upper (D 8) (R 8) [258,33,80,96,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16236

theorem m22606_12 : Upper (D 8) (R 8) [258,33,80,96,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16255

theorem m22606_33 : Upper (D 8) (R 8) [258,33,80,96,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16267

theorem m22606_36 : Upper (D 8) (R 8) [258,33,80,96,36] 13 :=
  permutation_upper _ _ _ [258,33,40,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16283

theorem m22606_40 : Upper (D 8) (R 8) [258,33,80,96,40] 13 :=
  permutation_upper _ _ _ [258,33,40,96,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16294

theorem m22606_129 : Upper (D 8) (R 8) [258,33,80,96,129] 13 :=
  permutation_upper _ _ _ [258,33,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16309

theorem m22606_132 : Upper (D 8) (R 8) [258,33,80,96,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16317

theorem m22606_136 : Upper (D 8) (R 8) [258,33,80,96,136] 13 :=
  permutation_upper _ _ _ [258,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16319

theorem m22606_160 : Upper (D 8) (R 8) [258,33,80,96,160] 13 :=
  permutation_upper _ _ _ [258,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16321

def r22606 : Route 9 := (fun mask => (mask,id))

def c22606 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22606 : Upper (D 8) (R 8) [258,33,80,96] 13 := by
  apply FastRouting.sound _ _ [258,33,80,96] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22606 c22606
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22606_5
  · exact m22606_9
  · exact m22606_12
  · exact m22606_33
  · exact m22606_36
  · exact m22606_40
  · exact m22606_129
  · exact m22606_132
  · exact m22606_136
  · exact m22606_160

theorem m22607_5 : Upper (D 8) (R 8) [258,33,80,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16230

theorem m22607_9 : Upper (D 8) (R 8) [258,33,80,160,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16237

theorem m22607_12 : Upper (D 8) (R 8) [258,33,80,160,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16256

theorem m22607_33 : Upper (D 8) (R 8) [258,33,80,160,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16269

theorem m22607_36 : Upper (D 8) (R 8) [258,33,80,160,36] 13 :=
  permutation_upper _ _ _ [258,33,40,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16285

theorem m22607_40 : Upper (D 8) (R 8) [258,33,80,160,40] 13 :=
  permutation_upper _ _ _ [258,33,40,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16295

theorem m22607_65 : Upper (D 8) (R 8) [258,33,80,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16302

theorem m22607_68 : Upper (D 8) (R 8) [258,33,80,160,68] 13 :=
  permutation_upper _ _ _ [258,33,72,68,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16312

theorem m22607_72 : Upper (D 8) (R 8) [258,33,80,160,72] 13 :=
  permutation_upper _ _ _ [258,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16314

theorem m22607_96 : Upper (D 8) (R 8) [258,33,80,160,96] 13 :=
  permutation_upper _ _ _ [258,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16316

theorem m22607_129 : Upper (D 8) (R 8) [258,33,80,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16306

theorem m22607_132 : Upper (D 8) (R 8) [258,33,80,160,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16317

theorem m22607_136 : Upper (D 8) (R 8) [258,33,80,160,136] 13 :=
  permutation_upper _ _ _ [258,33,72,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16315

theorem m22607_160 : Upper (D 8) (R 8) [258,33,80,160,160] 13 :=
  permutation_upper _ _ _ [258,33,72,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16322

theorem m22607_192 : Upper (D 8) (R 8) [258,33,80,160,192] 13 :=
  permutation_upper _ _ _ [258,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16324

def r22607 : Route 9 := (fun mask => (mask,id))

def c22607 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22607 : Upper (D 8) (R 8) [258,33,80,160] 13 := by
  apply FastRouting.sound _ _ [258,33,80,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r22607 c22607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22607_5
  · exact m22607_9
  · exact m22607_12
  · exact m22607_33
  · exact m22607_36
  · exact m22607_40
  · exact m22607_65
  · exact m22607_68
  · exact m22607_72
  · exact m22607_96
  · exact m22607_129
  · exact m22607_132
  · exact m22607_136
  · exact m22607_160
  · exact m22607_192

theorem m22608_5 : Upper (D 8) (R 8) [258,33,80,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16231

theorem m22608_9 : Upper (D 8) (R 8) [258,33,80,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16241

theorem m22608_12 : Upper (D 8) (R 8) [258,33,80,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16257

theorem m22608_33 : Upper (D 8) (R 8) [258,33,80,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16270

theorem m22608_36 : Upper (D 8) (R 8) [258,33,80,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,68,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16286

theorem m22608_40 : Upper (D 8) (R 8) [258,33,80,192,40] 13 :=
  permutation_upper _ _ _ [258,33,40,192,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16298

theorem m22608_129 : Upper (D 8) (R 8) [258,33,80,192,129] 13 :=
  permutation_upper _ _ _ [258,33,65,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16310

theorem m22608_132 : Upper (D 8) (R 8) [258,33,80,192,132] 13 :=
  permutation_upper _ _ _ [258,33,72,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16318

theorem m22608_136 : Upper (D 8) (R 8) [258,33,80,192,136] 13 :=
  permutation_upper _ _ _ [258,33,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16320

theorem m22608_160 : Upper (D 8) (R 8) [258,33,80,192,160] 13 :=
  permutation_upper _ _ _ [258,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16323

def r22608 : Route 9 := (fun mask => (mask,id))

def c22608 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22608 : Upper (D 8) (R 8) [258,33,80,192] 13 := by
  apply FastRouting.sound _ _ [258,33,80,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22608 c22608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22608_5
  · exact m22608_9
  · exact m22608_12
  · exact m22608_33
  · exact m22608_36
  · exact m22608_40
  · exact m22608_129
  · exact m22608_132
  · exact m22608_136
  · exact m22608_160

def b22609 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 100 104 157 189 221 157 413), lower := (rows 259 35 100 104 16 32 64 128 256), losses := [] }

theorem u22609 : Upper (D 8) (R 8) [258,33,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22610_5 : Upper (D 8) (R 8) [258,33,96,160,5] 13 :=
  permutation_upper _ _ _ [258,33,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16238

theorem m22610_9 : Upper (D 8) (R 8) [258,33,96,160,9] 13 :=
  permutation_upper _ _ _ [258,33,9,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16238

theorem m22610_12 : Upper (D 8) (R 8) [258,33,96,160,12] 13 :=
  permutation_upper _ _ _ [258,33,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16259

theorem m22610_65 : Upper (D 8) (R 8) [258,33,96,160,65] 13 :=
  permutation_upper _ _ _ [258,33,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16308

theorem m22610_68 : Upper (D 8) (R 8) [258,33,96,160,68] 13 :=
  permutation_upper _ _ _ [258,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16316

theorem m22610_72 : Upper (D 8) (R 8) [258,33,96,160,72] 13 :=
  permutation_upper _ _ _ [258,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16321

theorem m22610_129 : Upper (D 8) (R 8) [258,33,96,160,129] 13 :=
  permutation_upper _ _ _ [258,33,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16308

theorem m22610_132 : Upper (D 8) (R 8) [258,33,96,160,132] 13 :=
  permutation_upper _ _ _ [258,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16321

theorem m22610_136 : Upper (D 8) (R 8) [258,33,96,160,136] 13 :=
  permutation_upper _ _ _ [258,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16316

def r22610 : Route 9 := (fun mask => (mask,id))

def c22610 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22610 : Upper (D 8) (R 8) [258,33,96,160] 13 := by
  apply FastRouting.sound _ _ [258,33,96,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r22610 c22610
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22610_5
  · exact m22610_9
  · exact m22610_12
  · exact m22610_65
  · exact m22610_68
  · exact m22610_72
  · exact m22610_129
  · exact m22610_132
  · exact m22610_136
  · exact u16325

theorem m22611_5 : Upper (D 8) (R 8) [258,33,96,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16239

theorem m22611_9 : Upper (D 8) (R 8) [258,33,96,192,9] 13 :=
  permutation_upper _ _ _ [258,33,9,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16242

theorem m22611_12 : Upper (D 8) (R 8) [258,33,96,192,12] 13 :=
  permutation_upper _ _ _ [258,33,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16260

theorem m22611_33 : Upper (D 8) (R 8) [258,33,96,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16273

theorem m22611_36 : Upper (D 8) (R 8) [258,33,96,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16296

theorem m22611_40 : Upper (D 8) (R 8) [258,33,96,192,40] 13 :=
  permutation_upper _ _ _ [258,33,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16299

theorem m22611_129 : Upper (D 8) (R 8) [258,33,96,192,129] 13 :=
  permutation_upper _ _ _ [258,33,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16311

theorem m22611_132 : Upper (D 8) (R 8) [258,33,96,192,132] 13 :=
  permutation_upper _ _ _ [258,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16323

theorem m22611_136 : Upper (D 8) (R 8) [258,33,96,192,136] 13 :=
  permutation_upper _ _ _ [258,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16324

theorem m22611_160 : Upper (D 8) (R 8) [258,33,96,192,160] 13 :=
  permutation_upper _ _ _ [258,33,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16325

def r22611 : Route 9 := (fun mask => (mask,id))

def c22611 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22611 : Upper (D 8) (R 8) [258,33,96,192] 13 := by
  apply FastRouting.sound _ _ [258,33,96,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r22611 c22611
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22611_5
  · exact m22611_9
  · exact m22611_12
  · exact m22611_33
  · exact m22611_36
  · exact m22611_40
  · exact m22611_129
  · exact m22611_132
  · exact m22611_136
  · exact m22611_160

def b22612 : PairBound 9 := { available := 61, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 196 200 61 61 125 189 317), lower := (rows 259 35 196 200 16 32 64 128 256), losses := [] }

theorem u22612 : Upper (D 8) (R 8) [258,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22613 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 25 240 224 224 224 480), lower := (rows 259 38 13 25 16 32 64 128 256), losses := [] }

theorem u22613 : Upper (D 8) (R 8) [258,36,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22614 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 13 41 240 240 240 240 496), lower := (rows 259 38 13 41 16 32 64 128 256), losses := [] }

theorem u22614 : Upper (D 8) (R 8) [258,36,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22615 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22615 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22615 : Upper (D 8) (R 8) [258,36,9,48] 13 := by
  apply FastRouting.sound _ _ [258,36,9,48] 13 (by decide) (choices 2) [33,65,96,192] r22615 c22615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16326
  · exact u16327
  · exact u16328
  · exact u16329

def b22616 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 13 73 240 240 240 240 496), lower := (rows 259 38 13 73 16 32 64 128 256), losses := [] }

theorem u22616 : Upper (D 8) (R 8) [258,36,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22617 : Route 9 := (fun mask => (mask,id))

def c22617 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22617 : Upper (D 8) (R 8) [258,36,9,80] 13 := by
  apply FastRouting.sound _ _ [258,36,9,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22617 c22617
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16330
  · exact u16331
  · exact u16332
  · exact u16333
  · exact u16334
  · exact u16335

def r22618 : Route 9 := (fun mask => (mask,id))

def c22618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22618 : Upper (D 8) (R 8) [258,36,9,96] 13 := by
  apply FastRouting.sound _ _ [258,36,9,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r22618 c22618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u16336
  · exact u16337
  · exact u16338
  · exact u16339
  · exact u16340
  · exact u16341

def r22619 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22619 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22619 : Upper (D 8) (R 8) [258,36,9,192] 13 := by
  apply FastRouting.sound _ _ [258,36,9,192] 13 (by decide) (choices 2) [33,65,96,192] r22619 c22619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16342
  · exact u16343
  · exact u16344
  · exact u16345

#print axioms u22619
end Delivery.IrregularNine14.P08
