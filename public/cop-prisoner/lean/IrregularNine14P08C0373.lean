import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0253
import IrregularNine14P08C0254
import IrregularNine14P08C0255
import IrregularNine14P08C0256
import IrregularNine14P08C0257
import IrregularNine14P08C0258
import IrregularNine14P08C0260
import IrregularNine14P08C0261
import IrregularNine14P08C0263
import IrregularNine14P08C0264
import IrregularNine14P08C0265
import IrregularNine14P08C0266
import IrregularNine14P08C0267

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22380 : PairBound 9 := { available := 233, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 52 266 249 233 233 233 489), lower := (rows 193 38 52 266 16 32 64 128 256), losses := [] }

theorem u22380 : Upper (D 8) (R 8) [192,36,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22381 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 52 296 219 235 203 203 459), lower := (rows 193 38 52 296 16 32 64 128 256), losses := [] }

theorem u22381 : Upper (D 8) (R 8) [192,36,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22382 : PairBound 9 := { available := 171, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 52 328 187 171 235 171 427), lower := (rows 193 38 52 328 16 32 64 128 256), losses := [] }

theorem u22382 : Upper (D 8) (R 8) [192,36,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22383 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 138 313 313 377 441 313), lower := (rows 193 38 69 138 16 32 64 128 256), losses := [] }

theorem u22383 : Upper (D 8) (R 8) [192,36,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22384 : PairBound 9 := { available := 315, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 168 315 315 379 443 315), lower := (rows 193 38 69 168 16 32 64 128 256), losses := [] }

theorem u22384 : Upper (D 8) (R 8) [192,36,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22385 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 265 186 186 250 186 442), lower := (rows 193 38 69 265 16 32 64 128 256), losses := [] }

theorem u22385 : Upper (D 8) (R 8) [192,36,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22386 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 266 185 185 249 185 441), lower := (rows 193 38 69 266 16 32 64 128 256), losses := [] }

theorem u22386 : Upper (D 8) (R 8) [192,36,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22387 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 296 187 187 251 187 443), lower := (rows 193 38 69 296 16 32 64 128 256), losses := [] }

theorem u22387 : Upper (D 8) (R 8) [192,36,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22388 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 69 392 59 59 123 187 315), lower := (rows 193 38 69 392 16 32 64 128 256), losses := [] }

theorem u22388 : Upper (D 8) (R 8) [192,36,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22389 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 168 313 313 377 441 313), lower := (rows 193 38 70 168 16 32 64 128 256), losses := [] }

theorem u22389 : Upper (D 8) (R 8) [192,36,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22390 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 265 185 185 249 185 441), lower := (rows 193 38 70 265 16 32 64 128 256), losses := [] }

theorem u22390 : Upper (D 8) (R 8) [192,36,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22391 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 296 185 185 249 185 441), lower := (rows 193 38 70 296 16 32 64 128 256), losses := [] }

theorem u22391 : Upper (D 8) (R 8) [192,36,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22392 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 312, targets := 64 }], pairs := [(3,6)], upper := (rows 193 38 70 392 57 57 121 185 313), lower := (rows 193 38 70 392 16 32 64 128 256), losses := [] }

theorem u22392 : Upper (D 8) (R 8) [192,36,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22393_3 : Upper (D 8) (R 8) [192,36,72,48,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15256

theorem m22393_33 : Upper (D 8) (R 8) [192,36,72,48,33] 13 :=
  permutation_upper _ _ _ [192,33,34,48,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15807

theorem m22393_34 : Upper (D 8) (R 8) [192,36,72,48,34] 13 :=
  permutation_upper _ _ _ [192,36,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15952

theorem m22393_129 : Upper (D 8) (R 8) [192,36,72,48,129] 13 :=
  permutation_upper _ _ _ [192,36,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15978

def r22393 : Route 9 := (fun mask => (mask,id))

def c22393 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22393 : Upper (D 8) (R 8) [192,36,72,48] 13 := by
  apply FastRouting.sound _ _ [192,36,72,48] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r22393 c22393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22393_3
  · exact m22393_33
  · exact m22393_34
  · exact m22393_129
  · exact u16001
  · exact u16002
  · exact u16003
  · exact u16004
  · exact u16005
  · exact u16006

def b22394 : PairBound 9 := { available := 307, camps := [{ cop := 3, region := 374, targets := 128 }], pairs := [(1,7)], upper := (rows 193 38 76 137 307 307 371 435 307), lower := (rows 193 38 76 137 16 32 64 128 256), losses := [] }

theorem u22394 : Upper (D 8) (R 8) [192,36,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22395 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 138 305 305 369 433 305), lower := (rows 193 38 76 138 16 32 64 128 256), losses := [] }

theorem u22395 : Upper (D 8) (R 8) [192,36,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22396_3 : Upper (D 8) (R 8) [192,36,72,144,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15257

theorem m22396_33 : Upper (D 8) (R 8) [192,36,72,144,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15858

theorem m22396_34 : Upper (D 8) (R 8) [192,36,72,144,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15960

def r22396 : Route 9 := (fun mask => (mask,id))

def c22396 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22396 : Upper (D 8) (R 8) [192,36,72,144] 13 := by
  apply FastRouting.sound _ _ [192,36,72,144] 13 (by decide) (choices 2) [3,33,34,257,258,288] r22396 c22396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22396_3
  · exact m22396_33
  · exact m22396_34
  · exact u16012
  · exact u16013
  · exact u16014

theorem m22397_3 : Upper (D 8) (R 8) [192,36,72,160,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15258

theorem m22397_33 : Upper (D 8) (R 8) [192,36,72,160,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15860

theorem m22397_34 : Upper (D 8) (R 8) [192,36,72,160,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15961

def r22397 : Route 9 := (fun mask => (mask,id))

def c22397 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22397 : Upper (D 8) (R 8) [192,36,72,160] 13 := by
  apply FastRouting.sound _ _ [192,36,72,160] 13 (by decide) (choices 2) [3,33,34,257,258,288] r22397 c22397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22397_3
  · exact m22397_33
  · exact m22397_34
  · exact u16015
  · exact u16016
  · exact u16017

theorem m22398_3 : Upper (D 8) (R 8) [192,36,72,257,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15259

theorem m22398_33 : Upper (D 8) (R 8) [192,36,72,257,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15861

theorem m22398_34 : Upper (D 8) (R 8) [192,36,72,257,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15962

def r22398 : Route 9 := (fun mask => (mask,id))

def c22398 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22398 : Upper (D 8) (R 8) [192,36,72,257] 13 := by
  apply FastRouting.sound _ _ [192,36,72,257] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22398 c22398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22398_3
  · exact m22398_33
  · exact m22398_34
  · exact u16018
  · exact u16019
  · exact u16020

def b22399 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 76 266 177 177 241 177 433), lower := (rows 193 38 76 266 16 32 64 128 256), losses := [] }

theorem u22399 : Upper (D 8) (R 8) [192,36,72,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22400_3 : Upper (D 8) (R 8) [192,36,72,272,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15260

theorem m22400_33 : Upper (D 8) (R 8) [192,36,72,272,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15862

theorem m22400_34 : Upper (D 8) (R 8) [192,36,72,272,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15963

def r22400 : Route 9 := (fun mask => (mask,id))

def c22400 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22400 : Upper (D 8) (R 8) [192,36,72,272] 13 := by
  apply FastRouting.sound _ _ [192,36,72,272] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22400 c22400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22400_3
  · exact m22400_33
  · exact m22400_34
  · exact u16022
  · exact u16023
  · exact u16024

theorem m22401_3 : Upper (D 8) (R 8) [192,36,72,288,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15261

theorem m22401_33 : Upper (D 8) (R 8) [192,36,72,288,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15864

theorem m22401_34 : Upper (D 8) (R 8) [192,36,72,288,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15964

def r22401 : Route 9 := (fun mask => (mask,id))

def c22401 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22401 : Upper (D 8) (R 8) [192,36,72,288] 13 := by
  apply FastRouting.sound _ _ [192,36,72,288] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22401 c22401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22401_3
  · exact m22401_33
  · exact m22401_34
  · exact u16025
  · exact u16026
  · exact u16027

theorem m22402_3 : Upper (D 8) (R 8) [192,36,72,384,3] 13 :=
  permutation_upper _ _ _ [192,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15262

theorem m22402_33 : Upper (D 8) (R 8) [192,36,72,384,33] 13 :=
  permutation_upper _ _ _ [192,33,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15865

theorem m22402_34 : Upper (D 8) (R 8) [192,36,72,384,34] 13 :=
  permutation_upper _ _ _ [192,36,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15965

def r22402 : Route 9 := (fun mask => (mask,id))

def c22402 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22402 : Upper (D 8) (R 8) [192,36,72,384] 13 := by
  apply FastRouting.sound _ _ [192,36,72,384] 13 (by decide) (choices 2) [3,33,34] r22402 c22402
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m22402_3
  · exact m22402_33
  · exact m22402_34

theorem m22403_9 : Upper (D 8) (R 8) [192,36,80,130,9] 13 :=
  permutation_upper _ _ _ [192,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15351

theorem m22403_33 : Upper (D 8) (R 8) [192,36,80,130,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15845

theorem m22403_40 : Upper (D 8) (R 8) [192,36,80,130,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16001

theorem m22403_257 : Upper (D 8) (R 8) [192,36,80,130,257] 13 :=
  permutation_upper _ _ _ [192,36,72,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16019

theorem m22403_264 : Upper (D 8) (R 8) [192,36,80,130,264] 13 :=
  permutation_upper _ _ _ [192,36,72,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16023

theorem m22403_288 : Upper (D 8) (R 8) [192,36,80,130,288] 13 :=
  permutation_upper _ _ _ [192,36,72,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16026

def r22403 : Route 9 := (fun mask => (mask,id))

def c22403 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22403 : Upper (D 8) (R 8) [192,36,80,130] 13 := by
  apply FastRouting.sound _ _ [192,36,80,130] 13 (by decide) (choices 2) [9,33,40,257,264,288] r22403 c22403
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22403_9
  · exact m22403_33
  · exact m22403_40
  · exact m22403_257
  · exact m22403_264
  · exact m22403_288

theorem m22404_3 : Upper (D 8) (R 8) [192,36,80,160,3] 13 :=
  permutation_upper _ _ _ [192,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15251

theorem m22404_9 : Upper (D 8) (R 8) [192,36,80,160,9] 13 :=
  permutation_upper _ _ _ [192,5,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15407

theorem m22404_10 : Upper (D 8) (R 8) [192,36,80,160,10] 13 :=
  permutation_upper _ _ _ [192,12,48,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15666

theorem m22404_33 : Upper (D 8) (R 8) [192,36,80,160,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15846

theorem m22404_34 : Upper (D 8) (R 8) [192,36,80,160,34] 13 :=
  permutation_upper _ _ _ [192,36,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15956

theorem m22404_40 : Upper (D 8) (R 8) [192,36,80,160,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16002

theorem m22404_257 : Upper (D 8) (R 8) [192,36,80,160,257] 13 :=
  permutation_upper _ _ _ [192,36,72,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16020

theorem m22404_258 : Upper (D 8) (R 8) [192,36,80,160,258] 13 :=
  permutation_upper _ _ _ [192,36,72,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16021

theorem m22404_264 : Upper (D 8) (R 8) [192,36,80,160,264] 13 :=
  permutation_upper _ _ _ [192,36,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16024

theorem m22404_288 : Upper (D 8) (R 8) [192,36,80,160,288] 13 :=
  permutation_upper _ _ _ [192,36,72,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16027

def r22404 : Route 9 := (fun mask => (mask,id))

def c22404 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22404 : Upper (D 8) (R 8) [192,36,80,160] 13 := by
  apply FastRouting.sound _ _ [192,36,80,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r22404 c22404
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22404_3
  · exact m22404_9
  · exact m22404_10
  · exact m22404_33
  · exact m22404_34
  · exact m22404_40
  · exact m22404_257
  · exact m22404_258
  · exact m22404_264
  · exact m22404_288

theorem m22405_3 : Upper (D 8) (R 8) [192,36,80,257,3] 13 :=
  permutation_upper _ _ _ [192,5,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15252

theorem m22405_9 : Upper (D 8) (R 8) [192,36,80,257,9] 13 :=
  permutation_upper _ _ _ [192,5,257,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15440

theorem m22405_10 : Upper (D 8) (R 8) [192,36,80,257,10] 13 :=
  permutation_upper _ _ _ [192,12,48,257,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15677

theorem m22405_33 : Upper (D 8) (R 8) [192,36,80,257,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15847

theorem m22405_34 : Upper (D 8) (R 8) [192,36,80,257,34] 13 :=
  permutation_upper _ _ _ [192,36,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15957

theorem m22405_40 : Upper (D 8) (R 8) [192,36,80,257,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16003

theorem m22405_129 : Upper (D 8) (R 8) [192,36,80,257,129] 13 :=
  permutation_upper _ _ _ [192,36,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16007

theorem m22405_130 : Upper (D 8) (R 8) [192,36,80,257,130] 13 :=
  permutation_upper _ _ _ [192,36,72,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16010

theorem m22405_136 : Upper (D 8) (R 8) [192,36,80,257,136] 13 :=
  permutation_upper _ _ _ [192,36,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16012

theorem m22405_160 : Upper (D 8) (R 8) [192,36,80,257,160] 13 :=
  permutation_upper _ _ _ [192,36,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16015

def r22405 : Route 9 := (fun mask => (mask,id))

def c22405 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22405 : Upper (D 8) (R 8) [192,36,80,257] 13 := by
  apply FastRouting.sound _ _ [192,36,80,257] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22405 c22405
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22405_3
  · exact m22405_9
  · exact m22405_10
  · exact m22405_33
  · exact m22405_34
  · exact m22405_40
  · exact m22405_129
  · exact m22405_130
  · exact m22405_136
  · exact m22405_160

theorem m22406_9 : Upper (D 8) (R 8) [192,36,80,258,9] 13 :=
  permutation_upper _ _ _ [192,5,264,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15472

theorem m22406_33 : Upper (D 8) (R 8) [192,36,80,258,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15848

theorem m22406_40 : Upper (D 8) (R 8) [192,36,80,258,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16004

theorem m22406_129 : Upper (D 8) (R 8) [192,36,80,258,129] 13 :=
  permutation_upper _ _ _ [192,36,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16008

theorem m22406_136 : Upper (D 8) (R 8) [192,36,80,258,136] 13 :=
  permutation_upper _ _ _ [192,36,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16013

theorem m22406_160 : Upper (D 8) (R 8) [192,36,80,258,160] 13 :=
  permutation_upper _ _ _ [192,36,72,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16016

def r22406 : Route 9 := (fun mask => (mask,id))

def c22406 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22406 : Upper (D 8) (R 8) [192,36,80,258] 13 := by
  apply FastRouting.sound _ _ [192,36,80,258] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22406 c22406
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22406_9
  · exact m22406_33
  · exact m22406_40
  · exact m22406_129
  · exact m22406_136
  · exact m22406_160

theorem m22407_3 : Upper (D 8) (R 8) [192,36,80,288,3] 13 :=
  permutation_upper _ _ _ [192,5,40,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15253

theorem m22407_9 : Upper (D 8) (R 8) [192,36,80,288,9] 13 :=
  permutation_upper _ _ _ [192,5,288,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15509

theorem m22407_10 : Upper (D 8) (R 8) [192,36,80,288,10] 13 :=
  permutation_upper _ _ _ [192,12,48,288,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15687

theorem m22407_33 : Upper (D 8) (R 8) [192,36,80,288,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15849

theorem m22407_34 : Upper (D 8) (R 8) [192,36,80,288,34] 13 :=
  permutation_upper _ _ _ [192,36,40,66,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15958

theorem m22407_40 : Upper (D 8) (R 8) [192,36,80,288,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16005

theorem m22407_129 : Upper (D 8) (R 8) [192,36,80,288,129] 13 :=
  permutation_upper _ _ _ [192,36,72,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16009

theorem m22407_130 : Upper (D 8) (R 8) [192,36,80,288,130] 13 :=
  permutation_upper _ _ _ [192,36,72,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16011

theorem m22407_136 : Upper (D 8) (R 8) [192,36,80,288,136] 13 :=
  permutation_upper _ _ _ [192,36,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16014

theorem m22407_160 : Upper (D 8) (R 8) [192,36,80,288,160] 13 :=
  permutation_upper _ _ _ [192,36,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16017

def r22407 : Route 9 := (fun mask => (mask,id))

def c22407 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22407 : Upper (D 8) (R 8) [192,36,80,288] 13 := by
  apply FastRouting.sound _ _ [192,36,80,288] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22407 c22407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22407_3
  · exact m22407_9
  · exact m22407_10
  · exact m22407_33
  · exact m22407_34
  · exact m22407_40
  · exact m22407_129
  · exact m22407_130
  · exact m22407_136
  · exact m22407_160

theorem m22408_3 : Upper (D 8) (R 8) [192,36,80,384,3] 13 :=
  permutation_upper _ _ _ [192,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15254

theorem m22408_9 : Upper (D 8) (R 8) [192,36,80,384,9] 13 :=
  permutation_upper _ _ _ [192,5,320,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15530

theorem m22408_10 : Upper (D 8) (R 8) [192,36,80,384,10] 13 :=
  permutation_upper _ _ _ [192,12,48,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15693

theorem m22408_33 : Upper (D 8) (R 8) [192,36,80,384,33] 13 :=
  permutation_upper _ _ _ [192,33,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15850

theorem m22408_34 : Upper (D 8) (R 8) [192,36,80,384,34] 13 :=
  permutation_upper _ _ _ [192,36,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15959

theorem m22408_40 : Upper (D 8) (R 8) [192,36,80,384,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16006

def r22408 : Route 9 := (fun mask => (mask,id))

def c22408 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u22408 : Upper (D 8) (R 8) [192,36,80,384] 13 := by
  apply FastRouting.sound _ _ [192,36,80,384] 13 (by decide) (choices 2) [3,9,10,33,34,40] r22408 c22408
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22408_3
  · exact m22408_9
  · exact m22408_10
  · exact m22408_33
  · exact m22408_34
  · exact m22408_40

def b22409 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 138 313 313 377 441 313), lower := (rows 193 38 100 138 16 32 64 128 256), losses := [] }

theorem u22409 : Upper (D 8) (R 8) [192,36,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22410 : PairBound 9 := { available := 283, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 168 283 315 347 411 283), lower := (rows 193 38 100 168 16 32 64 128 256), losses := [] }

theorem u22410 : Upper (D 8) (R 8) [192,36,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22411 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 265 187 187 251 187 443), lower := (rows 193 38 100 265 16 32 64 128 256), losses := [] }

theorem u22411 : Upper (D 8) (R 8) [192,36,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22412 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 266 185 185 249 185 441), lower := (rows 193 38 100 266 16 32 64 128 256), losses := [] }

theorem u22412 : Upper (D 8) (R 8) [192,36,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22413 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 296 155 187 219 155 411), lower := (rows 193 38 100 296 16 32 64 128 256), losses := [] }

theorem u22413 : Upper (D 8) (R 8) [192,36,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22414 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 100 392 59 59 123 187 315), lower := (rows 193 38 100 392 16 32 64 128 256), losses := [] }

theorem u22414 : Upper (D 8) (R 8) [192,36,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22415 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 265 59 59 123 187 315), lower := (rows 193 38 196 265 16 32 64 128 256), losses := [] }

theorem u22415 : Upper (D 8) (R 8) [192,36,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22416 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 266 57 57 121 185 313), lower := (rows 193 38 196 266 16 32 64 128 256), losses := [] }

theorem u22416 : Upper (D 8) (R 8) [192,36,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22417 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 38 196 296 59 59 123 187 315), lower := (rows 193 38 196 296 16 32 64 128 256), losses := [] }

theorem u22417 : Upper (D 8) (R 8) [192,36,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22418_3 : Upper (D 8) (R 8) [192,36,257,48,3] 13 :=
  permutation_upper _ _ _ [192,5,40,257,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15276

theorem m22418_9 : Upper (D 8) (R 8) [192,36,257,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15190

theorem m22418_10 : Upper (D 8) (R 8) [192,36,257,48,10] 13 :=
  permutation_upper _ _ _ [192,12,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15625

theorem m22418_33 : Upper (D 8) (R 8) [192,36,257,48,33] 13 :=
  permutation_upper _ _ _ [192,33,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15808

theorem m22418_34 : Upper (D 8) (R 8) [192,36,257,48,34] 13 :=
  permutation_upper _ _ _ [192,36,40,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15953

theorem m22418_40 : Upper (D 8) (R 8) [192,36,257,48,40] 13 :=
  permutation_upper _ _ _ [192,36,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15942

theorem m22418_65 : Upper (D 8) (R 8) [192,36,257,48,65] 13 :=
  permutation_upper _ _ _ [192,36,65,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15979

theorem m22418_66 : Upper (D 8) (R 8) [192,36,257,48,66] 13 :=
  permutation_upper _ _ _ [192,36,72,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16003

theorem m22418_72 : Upper (D 8) (R 8) [192,36,257,48,72] 13 :=
  permutation_upper _ _ _ [192,36,66,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15993

theorem m22418_96 : Upper (D 8) (R 8) [192,36,257,48,96] 13 :=
  permutation_upper _ _ _ [192,36,96,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16028

theorem m22418_192 : Upper (D 8) (R 8) [192,36,257,48,192] 13 :=
  permutation_upper _ _ _ [192,36,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16041

def r22418 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22418 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22418 : Upper (D 8) (R 8) [192,36,257,48] 13 := by
  apply FastRouting.sound _ _ [192,36,257,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r22418 c22418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22418_3
  · exact m22418_9
  · exact m22418_10
  · exact m22418_33
  · exact m22418_34
  · exact m22418_40
  · exact m22418_65
  · exact m22418_66
  · exact m22418_72
  · exact m22418_96
  · exact m22418_192

def b22419 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 261 73 186 186 250 186 442), lower := (rows 193 38 261 73 16 32 64 128 256), losses := [] }

theorem u22419 : Upper (D 8) (R 8) [192,36,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22420_9 : Upper (D 8) (R 8) [192,36,257,66,9] 13 :=
  permutation_upper _ _ _ [192,5,72,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15352

theorem m22420_33 : Upper (D 8) (R 8) [192,36,257,66,33] 13 :=
  permutation_upper _ _ _ [192,33,40,257,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15877

theorem m22420_40 : Upper (D 8) (R 8) [192,36,257,66,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16003

theorem m22420_129 : Upper (D 8) (R 8) [192,36,257,66,129] 13 :=
  permutation_upper _ _ _ [192,36,257,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16044

def r22420 : Route 9 := (fun mask => (mask,id))

def c22420 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22420 : Upper (D 8) (R 8) [192,36,257,66] 13 := by
  apply FastRouting.sound _ _ [192,36,257,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22420 c22420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22420_9
  · exact m22420_33
  · exact m22420_40
  · exact m22420_129
  · exact u16047
  · exact u16048

theorem m22421_3 : Upper (D 8) (R 8) [192,36,257,80,3] 13 :=
  permutation_upper _ _ _ [192,5,40,257,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15277

theorem m22421_9 : Upper (D 8) (R 8) [192,36,257,80,9] 13 :=
  permutation_upper _ _ _ [192,5,66,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15325

theorem m22421_10 : Upper (D 8) (R 8) [192,36,257,80,10] 13 :=
  permutation_upper _ _ _ [192,12,48,66,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15661

theorem m22421_33 : Upper (D 8) (R 8) [192,36,257,80,33] 13 :=
  permutation_upper _ _ _ [192,33,40,257,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15876

theorem m22421_34 : Upper (D 8) (R 8) [192,36,257,80,34] 13 :=
  permutation_upper _ _ _ [192,36,40,257,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15970

theorem m22421_40 : Upper (D 8) (R 8) [192,36,257,80,40] 13 :=
  permutation_upper _ _ _ [192,36,66,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15993

theorem m22421_129 : Upper (D 8) (R 8) [192,36,257,80,129] 13 :=
  permutation_upper _ _ _ [192,36,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16045

theorem m22421_130 : Upper (D 8) (R 8) [192,36,257,80,130] 13 :=
  permutation_upper _ _ _ [192,36,257,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16047

def r22421 : Route 9 := (fun mask => (mask,id))

def c22421 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22421 : Upper (D 8) (R 8) [192,36,257,80] 13 := by
  apply FastRouting.sound _ _ [192,36,257,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22421 c22421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22421_3
  · exact m22421_9
  · exact m22421_10
  · exact m22421_33
  · exact m22421_34
  · exact m22421_40
  · exact m22421_129
  · exact m22421_130
  · exact u16049
  · exact u16050

theorem m22422_3 : Upper (D 8) (R 8) [192,36,257,96,3] 13 :=
  permutation_upper _ _ _ [192,5,40,257,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15278

theorem m22422_9 : Upper (D 8) (R 8) [192,36,257,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15408

theorem m22422_10 : Upper (D 8) (R 8) [192,36,257,96,10] 13 :=
  permutation_upper _ _ _ [192,12,48,96,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15668

theorem m22422_33 : Upper (D 8) (R 8) [192,36,257,96,33] 13 :=
  permutation_upper _ _ _ [192,33,40,257,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15878

theorem m22422_34 : Upper (D 8) (R 8) [192,36,257,96,34] 13 :=
  permutation_upper _ _ _ [192,36,40,257,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15971

theorem m22422_40 : Upper (D 8) (R 8) [192,36,257,96,40] 13 :=
  permutation_upper _ _ _ [192,36,96,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16028

theorem m22422_129 : Upper (D 8) (R 8) [192,36,257,96,129] 13 :=
  permutation_upper _ _ _ [192,36,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16046

theorem m22422_130 : Upper (D 8) (R 8) [192,36,257,96,130] 13 :=
  permutation_upper _ _ _ [192,36,257,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16048

theorem m22422_136 : Upper (D 8) (R 8) [192,36,257,96,136] 13 :=
  permutation_upper _ _ _ [192,36,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16050

def r22422 : Route 9 := (fun mask => (mask,id))

def c22422 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22422 : Upper (D 8) (R 8) [192,36,257,96] 13 := by
  apply FastRouting.sound _ _ [192,36,257,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22422 c22422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22422_3
  · exact m22422_9
  · exact m22422_10
  · exact m22422_33
  · exact m22422_34
  · exact m22422_40
  · exact m22422_129
  · exact m22422_130
  · exact m22422_136
  · exact u16051

def b22423 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 261 200 59 59 123 187 315), lower := (rows 193 38 261 200 16 32 64 128 256), losses := [] }

theorem u22423 : Upper (D 8) (R 8) [192,36,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22424_9 : Upper (D 8) (R 8) [192,36,258,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15191

theorem m22424_33 : Upper (D 8) (R 8) [192,36,258,48,33] 13 :=
  permutation_upper _ _ _ [192,33,34,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15810

theorem m22424_40 : Upper (D 8) (R 8) [192,36,258,48,40] 13 :=
  permutation_upper _ _ _ [192,36,34,48,264] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15943

theorem m22424_65 : Upper (D 8) (R 8) [192,36,258,48,65] 13 :=
  permutation_upper _ _ _ [192,36,65,48,264] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15981

theorem m22424_72 : Upper (D 8) (R 8) [192,36,258,48,72] 13 :=
  permutation_upper _ _ _ [192,36,66,48,264] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15994

theorem m22424_96 : Upper (D 8) (R 8) [192,36,258,48,96] 13 :=
  permutation_upper _ _ _ [192,36,96,48,264] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16030

theorem m22424_192 : Upper (D 8) (R 8) [192,36,258,48,192] 13 :=
  permutation_upper _ _ _ [192,36,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16043

def r22424 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22424 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22424 : Upper (D 8) (R 8) [192,36,258,48] 13 := by
  apply FastRouting.sound _ _ [192,36,258,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22424 c22424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22424_9
  · exact m22424_33
  · exact m22424_40
  · exact m22424_65
  · exact m22424_72
  · exact m22424_96
  · exact m22424_192

def b22425 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 262 73 185 185 249 185 441), lower := (rows 193 38 262 73 16 32 64 128 256), losses := [] }

theorem u22425 : Upper (D 8) (R 8) [192,36,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22426_9 : Upper (D 8) (R 8) [192,36,258,80,9] 13 :=
  permutation_upper _ _ _ [192,5,66,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15326

theorem m22426_33 : Upper (D 8) (R 8) [192,36,258,80,33] 13 :=
  permutation_upper _ _ _ [192,33,40,260,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15885

theorem m22426_40 : Upper (D 8) (R 8) [192,36,258,80,40] 13 :=
  permutation_upper _ _ _ [192,36,66,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15994

theorem m22426_129 : Upper (D 8) (R 8) [192,36,258,80,129] 13 :=
  permutation_upper _ _ _ [192,36,258,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16052

def r22426 : Route 9 := (fun mask => (mask,id))

def c22426 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22426 : Upper (D 8) (R 8) [192,36,258,80] 13 := by
  apply FastRouting.sound _ _ [192,36,258,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22426 c22426
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22426_9
  · exact m22426_33
  · exact m22426_40
  · exact m22426_129
  · exact u16054
  · exact u16055

theorem m22427_9 : Upper (D 8) (R 8) [192,36,258,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15410

theorem m22427_33 : Upper (D 8) (R 8) [192,36,258,96,33] 13 :=
  permutation_upper _ _ _ [192,33,40,260,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15886

theorem m22427_40 : Upper (D 8) (R 8) [192,36,258,96,40] 13 :=
  permutation_upper _ _ _ [192,36,96,48,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16030

theorem m22427_129 : Upper (D 8) (R 8) [192,36,258,96,129] 13 :=
  permutation_upper _ _ _ [192,36,258,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16053

theorem m22427_136 : Upper (D 8) (R 8) [192,36,258,96,136] 13 :=
  permutation_upper _ _ _ [192,36,258,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16055

def r22427 : Route 9 := (fun mask => (mask,id))

def c22427 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22427 : Upper (D 8) (R 8) [192,36,258,96] 13 := by
  apply FastRouting.sound _ _ [192,36,258,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22427 c22427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22427_9
  · exact m22427_33
  · exact m22427_40
  · exact m22427_129
  · exact m22427_136
  · exact u16056

def b22428 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 262 200 57 57 121 185 313), lower := (rows 193 38 262 200 16 32 64 128 256), losses := [] }

theorem u22428 : Upper (D 8) (R 8) [192,36,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22429_3 : Upper (D 8) (R 8) [192,36,264,48,3] 13 :=
  permutation_upper _ _ _ [192,5,40,272,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15284

theorem m22429_33 : Upper (D 8) (R 8) [192,36,264,48,33] 13 :=
  permutation_upper _ _ _ [192,33,34,48,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15809

theorem m22429_34 : Upper (D 8) (R 8) [192,36,264,48,34] 13 :=
  permutation_upper _ _ _ [192,36,40,48,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15954

theorem m22429_65 : Upper (D 8) (R 8) [192,36,264,48,65] 13 :=
  permutation_upper _ _ _ [192,36,65,48,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15980

theorem m22429_66 : Upper (D 8) (R 8) [192,36,264,48,66] 13 :=
  permutation_upper _ _ _ [192,36,72,48,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16004

theorem m22429_96 : Upper (D 8) (R 8) [192,36,264,48,96] 13 :=
  permutation_upper _ _ _ [192,36,96,48,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16029

theorem m22429_192 : Upper (D 8) (R 8) [192,36,264,48,192] 13 :=
  permutation_upper _ _ _ [192,36,192,48,258] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16042

def r22429 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22429 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22429 : Upper (D 8) (R 8) [192,36,264,48] 13 := by
  apply FastRouting.sound _ _ [192,36,264,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22429 c22429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22429_3
  · exact m22429_33
  · exact m22429_34
  · exact m22429_65
  · exact m22429_66
  · exact m22429_96
  · exact m22429_192

def b22430 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 38 268 73 179 179 243 179 435), lower := (rows 193 38 268 73 16 32 64 128 256), losses := [] }

theorem u22430 : Upper (D 8) (R 8) [192,36,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22431 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 38 268 74 177 177 241 177 433), lower := (rows 193 38 268 74 16 32 64 128 256), losses := [] }

theorem u22431 : Upper (D 8) (R 8) [192,36,264,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22432_3 : Upper (D 8) (R 8) [192,36,264,80,3] 13 :=
  permutation_upper _ _ _ [192,5,40,272,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15286

theorem m22432_33 : Upper (D 8) (R 8) [192,36,264,80,33] 13 :=
  permutation_upper _ _ _ [192,33,40,272,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15889

theorem m22432_34 : Upper (D 8) (R 8) [192,36,264,80,34] 13 :=
  permutation_upper _ _ _ [192,36,40,272,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15973

def r22432 : Route 9 := (fun mask => (mask,id))

def c22432 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22432 : Upper (D 8) (R 8) [192,36,264,80] 13 := by
  apply FastRouting.sound _ _ [192,36,264,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22432 c22432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22432_3
  · exact m22432_33
  · exact m22432_34
  · exact u16060
  · exact u16061
  · exact u16062

theorem m22433_3 : Upper (D 8) (R 8) [192,36,264,96,3] 13 :=
  permutation_upper _ _ _ [192,5,40,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15287

theorem m22433_33 : Upper (D 8) (R 8) [192,36,264,96,33] 13 :=
  permutation_upper _ _ _ [192,33,40,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15891

theorem m22433_34 : Upper (D 8) (R 8) [192,36,264,96,34] 13 :=
  permutation_upper _ _ _ [192,36,40,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15974

def r22433 : Route 9 := (fun mask => (mask,id))

def c22433 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22433 : Upper (D 8) (R 8) [192,36,264,96] 13 := by
  apply FastRouting.sound _ _ [192,36,264,96] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22433 c22433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22433_3
  · exact m22433_33
  · exact m22433_34
  · exact u16063
  · exact u16064
  · exact u16065

def b22434 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 38 268 200 51 51 115 179 307), lower := (rows 193 38 268 200 16 32 64 128 256), losses := [] }

theorem u22434 : Upper (D 8) (R 8) [192,36,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22435_9 : Upper (D 8) (R 8) [192,36,272,66,9] 13 :=
  permutation_upper _ _ _ [192,5,72,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15353

theorem m22435_33 : Upper (D 8) (R 8) [192,36,272,66,33] 13 :=
  permutation_upper _ _ _ [192,33,40,258,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15881

theorem m22435_40 : Upper (D 8) (R 8) [192,36,272,66,40] 13 :=
  permutation_upper _ _ _ [192,36,72,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16004

theorem m22435_129 : Upper (D 8) (R 8) [192,36,272,66,129] 13 :=
  permutation_upper _ _ _ [192,36,264,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16057

theorem m22435_136 : Upper (D 8) (R 8) [192,36,272,66,136] 13 :=
  permutation_upper _ _ _ [192,36,264,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16061

theorem m22435_160 : Upper (D 8) (R 8) [192,36,272,66,160] 13 :=
  permutation_upper _ _ _ [192,36,264,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16064

def r22435 : Route 9 := (fun mask => (mask,id))

def c22435 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22435 : Upper (D 8) (R 8) [192,36,272,66] 13 := by
  apply FastRouting.sound _ _ [192,36,272,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22435 c22435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22435_9
  · exact m22435_33
  · exact m22435_40
  · exact m22435_129
  · exact m22435_136
  · exact m22435_160

theorem m22436_3 : Upper (D 8) (R 8) [192,36,272,96,3] 13 :=
  permutation_upper _ _ _ [192,5,40,258,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15281

theorem m22436_9 : Upper (D 8) (R 8) [192,36,272,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15409

theorem m22436_10 : Upper (D 8) (R 8) [192,36,272,96,10] 13 :=
  permutation_upper _ _ _ [192,12,48,96,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15669

theorem m22436_33 : Upper (D 8) (R 8) [192,36,272,96,33] 13 :=
  permutation_upper _ _ _ [192,33,40,258,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15882

theorem m22436_34 : Upper (D 8) (R 8) [192,36,272,96,34] 13 :=
  permutation_upper _ _ _ [192,36,40,258,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15972

theorem m22436_40 : Upper (D 8) (R 8) [192,36,272,96,40] 13 :=
  permutation_upper _ _ _ [192,36,96,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16029

theorem m22436_129 : Upper (D 8) (R 8) [192,36,272,96,129] 13 :=
  permutation_upper _ _ _ [192,36,264,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16058

theorem m22436_130 : Upper (D 8) (R 8) [192,36,272,96,130] 13 :=
  permutation_upper _ _ _ [192,36,264,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16059

theorem m22436_136 : Upper (D 8) (R 8) [192,36,272,96,136] 13 :=
  permutation_upper _ _ _ [192,36,264,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16062

theorem m22436_160 : Upper (D 8) (R 8) [192,36,272,96,160] 13 :=
  permutation_upper _ _ _ [192,36,264,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16065

def r22436 : Route 9 := (fun mask => (mask,id))

def c22436 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22436 : Upper (D 8) (R 8) [192,36,272,96] 13 := by
  apply FastRouting.sound _ _ [192,36,272,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22436 c22436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22436_3
  · exact m22436_9
  · exact m22436_10
  · exact m22436_33
  · exact m22436_34
  · exact m22436_40
  · exact m22436_129
  · exact m22436_130
  · exact m22436_136
  · exact m22436_160

def b22437 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 292 74 185 185 249 185 441), lower := (rows 193 38 292 74 16 32 64 128 256), losses := [] }

theorem u22437 : Upper (D 8) (R 8) [192,36,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22438 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 38 292 104 155 187 219 155 411), lower := (rows 193 38 292 104 16 32 64 128 256), losses := [] }

theorem u22438 : Upper (D 8) (R 8) [192,36,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22439_3 : Upper (D 8) (R 8) [192,36,320,48,3] 13 :=
  permutation_upper _ _ _ [192,5,40,320,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15294

theorem m22439_9 : Upper (D 8) (R 8) [192,36,320,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15193

theorem m22439_10 : Upper (D 8) (R 8) [192,36,320,48,10] 13 :=
  permutation_upper _ _ _ [192,12,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15627

theorem m22439_33 : Upper (D 8) (R 8) [192,36,320,48,33] 13 :=
  permutation_upper _ _ _ [192,33,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15811

theorem m22439_34 : Upper (D 8) (R 8) [192,36,320,48,34] 13 :=
  permutation_upper _ _ _ [192,36,40,48,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15955

theorem m22439_40 : Upper (D 8) (R 8) [192,36,320,48,40] 13 :=
  permutation_upper _ _ _ [192,36,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15944

theorem m22439_129 : Upper (D 8) (R 8) [192,36,320,48,129] 13 :=
  permutation_upper _ _ _ [192,36,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15982

theorem m22439_130 : Upper (D 8) (R 8) [192,36,320,48,130] 13 :=
  permutation_upper _ _ _ [192,36,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16006

theorem m22439_136 : Upper (D 8) (R 8) [192,36,320,48,136] 13 :=
  permutation_upper _ _ _ [192,36,66,48,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15995

theorem m22439_160 : Upper (D 8) (R 8) [192,36,320,48,160] 13 :=
  permutation_upper _ _ _ [192,36,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16031

def r22439 : Route 9 := (fun mask => (mask,id))

def c22439 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22439 : Upper (D 8) (R 8) [192,36,320,48] 13 := by
  apply FastRouting.sound _ _ [192,36,320,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22439 c22439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22439_3
  · exact m22439_9
  · exact m22439_10
  · exact m22439_33
  · exact m22439_34
  · exact m22439_40
  · exact m22439_129
  · exact m22439_130
  · exact m22439_136
  · exact m22439_160

#print axioms u22439
end Delivery.IrregularNine14.P08
