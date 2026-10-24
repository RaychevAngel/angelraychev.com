import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0034

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5400 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,5)], upper := (rows 97 7 28 42 208 160 321 385 257), lower := (rows 97 7 28 42 208 160 64 128 256), losses := [] }

theorem u5400 : Upper (D 9) (R 9) [96,5,24,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5400 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5401 : Route 9 := (fun mask => (mask,id))

def c5401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5401 : Upper (D 9) (R 9) [96,5,24,34,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,192,256] 13 (by decide) (choices 1) [1,128,256] r5401 c5401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2052
  · exact u2053
  · exact u2054

def b5402 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 28 42 400 33 448 448 448), lower := (rows 97 7 28 42 400 33 64 128 256), losses := [] }

theorem u5402 : Upper (D 9) (R 9) [96,5,24,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5402 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 42 400 96 449 385 385), lower := (rows 97 7 28 42 400 96 64 128 256), losses := [] }

theorem u5403 : Upper (D 9) (R 9) [96,5,24,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5403 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5404 : Route 9 := (fun mask => (mask,id))

def c5404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5404 : Upper (D 9) (R 9) [96,5,24,34,384,128] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,384,128] 13 (by decide) (choices 1) [1,256] r5404 c5404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2055
  · exact u2056

def b5405 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 54, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 28 137 176 34 320 448 320), lower := (rows 97 7 28 137 176 34 64 128 256), losses := [] }

theorem u5405 : Upper (D 9) (R 9) [96,5,24,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5405 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 176 96 322 386 258), lower := (rows 97 7 28 137 176 96 64 128 256), losses := [] }

theorem u5406 : Upper (D 9) (R 9) [96,5,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5406 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5407 : Route 9 := (fun mask => (mask,id))

def c5407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5407 : Upper (D 9) (R 9) [96,5,24,129,160,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,160,256] 13 (by decide) (choices 1) [2,256] r5407 c5407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2057
  · exact u2058

def b5408 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 274 96 480 416 416), lower := (rows 97 7 28 137 274 96 64 128 256), losses := [] }

theorem u5408 : Upper (D 9) (R 9) [96,5,24,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5408 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 496, targets := 1 },{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,0),(4,7)], upper := (rows 97 7 28 137 274 160 352 480 352), lower := (rows 97 7 28 137 274 160 64 128 256), losses := [{ target := 7, region := (rows 33 10 12 8 26 32 97 0 289), good := (rows 353 343 30 351 274 353 64 0 256) }] }

theorem u5409 : Upper (D 9) (R 9) [96,5,24,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5409 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5410_32 : Upper (D 9) (R 9) [96,5,24,129,258,256,32] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2059

theorem m5410_128 : Upper (D 9) (R 9) [96,5,24,129,258,256,128] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2060

def r5410 : Route 9 := (fun mask => (mask,id))

def c5410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5410 : Upper (D 9) (R 9) [96,5,24,129,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,258,256] 13 (by decide) (choices 1) [32,128] r5410 c5410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5410_32
  · exact m5410_128

def r5411 : Route 9 := (fun mask => (mask,id))

def c5411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5411 : Upper (D 9) (R 9) [96,5,24,129,288,2] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,288,2] 13 (by decide) (choices 1) [128,256] r5411 c5411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2061
  · exact u2062

def b5412 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 304 96 450 386 386), lower := (rows 97 7 28 137 304 96 64 128 256), losses := [] }

theorem u5412 : Upper (D 9) (R 9) [96,5,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5412 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5413 : Route 9 := (fun mask => (mask,id))

def c5413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5413 : Upper (D 9) (R 9) [96,5,24,129,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,288,128] 13 (by decide) (choices 1) [2,256] r5413 c5413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2063
  · exact u2064

def b5414 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 28 137 304 288 194 194 450), lower := (rows 97 7 28 137 304 288 64 128 256), losses := [] }

theorem u5414 : Upper (D 9) (R 9) [96,5,24,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5414 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5415 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 97 7 28 137 400 34 352 480 352), lower := (rows 97 7 28 137 400 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 59 34 99 163 291), good := (rows 496 502 28 476 400 498 64 128 256) }] }

theorem u5415 : Upper (D 9) (R 9) [96,5,24,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5415 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5416 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 137 400 96 354 418 290), lower := (rows 97 7 28 137 400 96 64 128 256), losses := [] }

theorem u5416 : Upper (D 9) (R 9) [96,5,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5416 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5417_2 : Upper (D 9) (R 9) [96,5,24,129,384,256,2] 13 :=
  permutation_upper _ _ _ [96,5,24,129,384,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2065

theorem m5417_32 : Upper (D 9) (R 9) [96,5,24,129,384,256,32] 13 :=
  permutation_upper _ _ _ [96,5,24,129,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2066

def r5417 : Route 9 := (fun mask => (mask,id))

def c5417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5417 : Upper (D 9) (R 9) [96,5,24,129,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,384,256] 13 (by decide) (choices 1) [2,32] r5417 c5417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5417_2
  · exact m5417_32

def b5418 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 456, targets := 33 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(3,5),(4,0)], upper := (rows 97 7 28 138 176 33 320 448 320), lower := (rows 97 7 28 138 176 33 64 128 256), losses := [] }

theorem u5418 : Upper (D 9) (R 9) [96,5,24,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5418 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 138 176 96 321 385 257), lower := (rows 97 7 28 138 176 96 64 128 256), losses := [] }

theorem u5419 : Upper (D 9) (R 9) [96,5,24,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5419 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5420 : Route 9 := (fun mask => (mask,id))

def c5420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5420 : Upper (D 9) (R 9) [96,5,24,130,160,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,160,256] 13 (by decide) (choices 1) [1,256] r5420 c5420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2067
  · exact u2068

def b5421 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 456, targets := 33 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,0)], upper := (rows 97 7 28 138 304 33 448 448 448), lower := (rows 97 7 28 138 304 33 64 128 256), losses := [] }

theorem u5421 : Upper (D 9) (R 9) [96,5,24,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5421 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 138 304 96 449 385 385), lower := (rows 97 7 28 138 304 96 64 128 256), losses := [] }

theorem u5422 : Upper (D 9) (R 9) [96,5,24,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5422 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5423 : Route 9 := (fun mask => (mask,id))

def c5423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5423 : Upper (D 9) (R 9) [96,5,24,130,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,288,128] 13 (by decide) (choices 1) [1,256] r5423 c5423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2069
  · exact u2070

def b5424 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 28 138 304 288 193 193 449), lower := (rows 97 7 28 138 304 288 64 128 256), losses := [] }

theorem u5424 : Upper (D 9) (R 9) [96,5,24,130,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5424 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(4,0)], upper := (rows 97 7 28 138 400 33 352 480 352), lower := (rows 97 7 28 138 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 51 32 97 161 289), good := (rows 496 478 28 158 400 496 64 128 256) }] }

theorem u5425 : Upper (D 9) (R 9) [96,5,24,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 138 400 96 353 417 289), lower := (rows 97 7 28 138 400 96 64 128 256), losses := [] }

theorem u5426 : Upper (D 9) (R 9) [96,5,24,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5426 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5427_1 : Upper (D 9) (R 9) [96,5,24,130,384,256,1] 13 :=
  permutation_upper _ _ _ [96,5,24,130,384,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2071

theorem m5427_32 : Upper (D 9) (R 9) [96,5,24,130,384,256,32] 13 :=
  permutation_upper _ _ _ [96,5,24,130,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2072

def r5427 : Route 9 := (fun mask => (mask,id))

def c5427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5427 : Upper (D 9) (R 9) [96,5,24,130,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130,384,256] 13 (by decide) (choices 1) [1,32] r5427 c5427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5427_1
  · exact m5427_32

def b5428 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 28 168 208 33 322 386 258), lower := (rows 97 7 28 168 208 33 64 128 256), losses := [] }

theorem u5428 : Upper (D 9) (R 9) [96,5,24,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5428 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 28 168 208 34 321 385 257), lower := (rows 97 7 28 168 208 34 64 128 256), losses := [] }

theorem u5429 : Upper (D 9) (R 9) [96,5,24,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5429 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5430_1 : Upper (D 9) (R 9) [96,5,24,160,192,256,1] 13 :=
  permutation_upper _ _ _ [96,5,24,160,192,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2073

theorem m5430_2 : Upper (D 9) (R 9) [96,5,24,160,192,256,2] 13 :=
  permutation_upper _ _ _ [96,5,24,160,192,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2074

def r5430 : Route 9 := (fun mask => (mask,id))

def c5430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5430 : Upper (D 9) (R 9) [96,5,24,160,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,192,256] 13 (by decide) (choices 1) [1,2,256] r5430 c5430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5430_1
  · exact m5430_2
  · exact u2075

def b5431 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 33, targets := 384 },{ cop := 1, region := 424, targets := 64 }], pairs := [(0,7),(0,8),(3,6),(4,0),(4,5)], upper := (rows 97 7 28 168 336 33 450 386 386), lower := (rows 97 7 28 168 336 33 64 128 256), losses := [] }

theorem u5431 : Upper (D 9) (R 9) [96,5,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5432_1 : Upper (D 9) (R 9) [96,5,24,160,320,2,1] 13 :=
  permutation_upper _ _ _ [96,5,24,160,320,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2076

def r5432 : Route 9 := (fun mask => (mask,id))

def c5432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5432 : Upper (D 9) (R 9) [96,5,24,160,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,320,2] 13 (by decide) (choices 1) [1,128,256] r5432 c5432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5432_1
  · exact u2078
  · exact u2079

def b5433 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 7 28 168 336 160 323 387 259), lower := (rows 97 7 28 168 336 160 64 128 256), losses := [] }

theorem u5433 : Upper (D 9) (R 9) [96,5,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5433 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5434_1 : Upper (D 9) (R 9) [96,5,24,160,320,256,1] 13 :=
  permutation_upper _ _ _ [96,5,24,160,320,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2077

theorem m5434_2 : Upper (D 9) (R 9) [96,5,24,160,320,256,2] 13 :=
  permutation_upper _ _ _ [96,5,24,160,320,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2078

def r5434 : Route 9 := (fun mask => (mask,id))

def c5434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5434 : Upper (D 9) (R 9) [96,5,24,160,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160,320,256] 13 (by decide) (choices 1) [1,2,128] r5434 c5434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5434_1
  · exact m5434_2
  · exact u2080

def b5435 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,0),(4,5)], upper := (rows 97 7 28 168 400 33 322 450 322), lower := (rows 97 7 28 168 400 33 64 128 256), losses := [] }

theorem u5435 : Upper (D 9) (R 9) [96,5,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5435 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(4,5)], upper := (rows 97 7 28 168 400 34 321 449 321), lower := (rows 97 7 28 168 400 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 51 0 67 131 259), good := (rows 465 471 28 156 400 466 64 128 256) }] }

theorem u5436 : Upper (D 9) (R 9) [96,5,24,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5436 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5437 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 168 400 96 323 387 259), lower := (rows 97 7 28 168 400 96 64 128 256), losses := [] }

theorem u5437 : Upper (D 9) (R 9) [96,5,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5438 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 7 28 168 400 288 67 195 323), lower := (rows 97 7 28 168 400 288 64 128 256), losses := [] }

theorem u5438 : Upper (D 9) (R 9) [96,5,24,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 25 146 96 448 384 384), lower := (rows 97 7 44 25 146 96 64 128 256), losses := [] }

theorem u5439 : Upper (D 9) (R 9) [96,5,40,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5439 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 25 146 160 320 448 320), lower := (rows 97 7 44 25 146 160 64 128 256), losses := [] }

theorem u5440 : Upper (D 9) (R 9) [96,5,40,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5441 : Route 9 := (fun mask => (mask,id))

def c5441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5441 : Upper (D 9) (R 9) [96,5,40,17,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,17,130,256] 13 (by decide) (choices 1) [128,256] r5441 c5441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2081
  · exact u2082

def b5442 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6)], upper := (rows 97 7 44 25 400 34 448 448 448), lower := (rows 97 7 44 25 400 34 64 128 256), losses := [] }

theorem u5442 : Upper (D 9) (R 9) [96,5,40,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5442 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5443 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 25 400 96 450 386 386), lower := (rows 97 7 44 25 400 96 64 128 256), losses := [] }

theorem u5443 : Upper (D 9) (R 9) [96,5,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5443 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 25 400 160 322 450 322), lower := (rows 97 7 44 25 400 160 64 128 256), losses := [] }

theorem u5444 : Upper (D 9) (R 9) [96,5,40,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 26 145 96 448 384 384), lower := (rows 97 7 44 26 145 96 64 128 256), losses := [] }

theorem u5445 : Upper (D 9) (R 9) [96,5,40,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5445 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5446 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8),(3,6)], upper := (rows 97 7 44 26 145 160 320 448 320), lower := (rows 97 7 44 26 145 160 64 128 256), losses := [] }

theorem u5446 : Upper (D 9) (R 9) [96,5,40,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5446 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5447 : Route 9 := (fun mask => (mask,id))

def c5447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5447 : Upper (D 9) (R 9) [96,5,40,18,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,129,256] 13 (by decide) (choices 1) [128,256] r5447 c5447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2083
  · exact u2084

def b5448 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 44 26 208 33 448 384 384), lower := (rows 97 7 44 26 208 33 64 128 256), losses := [] }

theorem u5448 : Upper (D 9) (R 9) [96,5,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 26 208 160 321 385 257), lower := (rows 97 7 44 26 208 160 64 128 256), losses := [] }

theorem u5449 : Upper (D 9) (R 9) [96,5,40,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5449 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5450 : Route 9 := (fun mask => (mask,id))

def c5450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5450 : Upper (D 9) (R 9) [96,5,40,18,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,192,256] 13 (by decide) (choices 1) [1,128,256] r5450 c5450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2085
  · exact u2086
  · exact u2087

def b5451 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 26 400 33 448 448 448), lower := (rows 97 7 44 26 400 33 64 128 256), losses := [] }

theorem u5451 : Upper (D 9) (R 9) [96,5,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5451 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 44 26 400 96 449 385 385), lower := (rows 97 7 44 26 400 96 64 128 256), losses := [] }

theorem u5452 : Upper (D 9) (R 9) [96,5,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,5),(4,5)], upper := (rows 97 7 44 26 400 160 321 449 321), lower := (rows 97 7 44 26 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 6 44 62 432 160 64 160 256) }] }

theorem u5453 : Upper (D 9) (R 9) [96,5,40,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 88 145 34 448 384 384), lower := (rows 97 7 44 88 145 34 64 128 256), losses := [] }

theorem u5454 : Upper (D 9) (R 9) [96,5,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5454 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(1,7),(3,5),(4,5),(4,6)], upper := (rows 97 7 44 88 145 160 322 386 258), lower := (rows 97 7 44 88 145 160 64 128 256), losses := [] }

theorem u5455 : Upper (D 9) (R 9) [96,5,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5456 : Route 9 := (fun mask => (mask,id))

def c5456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5456 : Upper (D 9) (R 9) [96,5,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80,129,256] 13 (by decide) (choices 1) [2,128,256] r5456 c5456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2088
  · exact u2089
  · exact u2090

def b5457 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 44 88 146 33 448 384 384), lower := (rows 97 7 44 88 146 33 64 128 256), losses := [] }

theorem u5457 : Upper (D 9) (R 9) [96,5,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5458 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(1,7),(3,5),(4,5),(4,6)], upper := (rows 97 7 44 88 146 160 321 385 257), lower := (rows 97 7 44 88 146 160 64 128 256), losses := [] }

theorem u5458 : Upper (D 9) (R 9) [96,5,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5459 : Route 9 := (fun mask => (mask,id))

def c5459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5459 : Upper (D 9) (R 9) [96,5,40,80,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,40,80,130,256] 13 (by decide) (choices 1) [1,128,256] r5459 c5459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2091
  · exact u2092
  · exact u2093

#print axioms u5459
end Delivery.IrregularNine14.P09
