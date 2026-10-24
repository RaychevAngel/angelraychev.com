import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0068
import IrregularNine14P06C0069

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16380 : Route 9 := (fun mask => (mask,id))

def c16380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16380 : Upper (D 6) (R 6) [10,132,96,260,34,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,260,34,1] 13 (by decide) (choices 1) [1,16] r16380 c16380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4106
  · exact u4107

def b16381 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 100 268 50 48 65 193 321), lower := (rows 11 134 100 268 50 48 64 128 256), losses := [] }

theorem u16381 : Upper (D 6) (R 6) [10,132,96,260,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16381 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16382 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 268 50 96 81 145 273), lower := (rows 11 134 100 268 50 96 64 128 256), losses := [] }

theorem u16382 : Upper (D 6) (R 6) [10,132,96,260,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16383 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 100 280 21 33 98 226 354), lower := (rows 11 134 100 280 21 33 64 128 256), losses := [{ target := 0, region := (rows 0 54 36 24 16 32 100 164 292), good := (rows 10 454 486 282 478 486 64 128 256) }] }

theorem u16383 : Upper (D 6) (R 6) [10,132,96,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m16384_1 : Upper (D 6) (R 6) [10,132,96,272,5,2,1] 13 :=
  permutation_upper _ _ _ [10,132,96,272,5,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4108

def r16384 : Route 9 := (fun mask => (mask,id))

def c16384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16384 : Upper (D 6) (R 6) [10,132,96,272,5,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,272,5,2] 13 (by decide) (choices 1) [1,32] r16384 c16384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16384_1
  · exact u4109

def b16385 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 280 21 96 99 163 291), lower := (rows 11 134 100 280 21 96 64 128 256), losses := [] }

theorem u16385 : Upper (D 6) (R 6) [10,132,96,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16386 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 100 280 49 33 70 198 326), lower := (rows 11 134 100 280 49 33 64 128 256), losses := [] }

theorem u16386 : Upper (D 6) (R 6) [10,132,96,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16387 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 68, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 100 280 49 34 69 197 325), lower := (rows 11 134 100 280 49 34 64 128 256), losses := [] }

theorem u16387 : Upper (D 6) (R 6) [10,132,96,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16388 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 134 100 280 49 36 67 195 323), lower := (rows 11 134 100 280 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 68 8 17 102 64 128 256), good := (rows 57 164 100 280 49 36 100 128 256) }] }

theorem u16388 : Upper (D 6) (R 6) [10,132,96,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16389 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 280 49 96 71 135 263), lower := (rows 11 134 100 280 49 96 64 128 256), losses := [] }

theorem u16389 : Upper (D 6) (R 6) [10,132,96,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16390 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 100 280 50 33 69 197 325), lower := (rows 11 134 100 280 50 33 64 128 256), losses := [] }

theorem u16390 : Upper (D 6) (R 6) [10,132,96,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16391 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 100 280 50 36 65 193 321), lower := (rows 11 134 100 280 50 36 64 128 256), losses := [] }

theorem u16391 : Upper (D 6) (R 6) [10,132,96,272,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16392 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 280 50 96 69 133 261), lower := (rows 11 134 100 280 50 96 64 128 256), losses := [] }

theorem u16392 : Upper (D 6) (R 6) [10,132,96,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16393 : Route 9 := (fun mask => (mask,id))

def c16393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16393 : Upper (D 6) (R 6) [10,132,96,288,5,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,5,1] 13 (by decide) (choices 1) [2,16] r16393 c16393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4110
  · exact u4111

def r16394 : Route 9 := (fun mask => (mask,id))

def c16394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16394 : Upper (D 6) (R 6) [10,132,96,288,5,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,5,2] 13 (by decide) (choices 1) [1,16] r16394 c16394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4112
  · exact u4113

def b16395 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,2)], upper := (rows 11 134 100 296 21 48 67 195 323), lower := (rows 11 134 100 296 21 48 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 48 65 129 257), good := (rows 459 130 96 296 505 56 64 128 256) }] }

theorem u16395 : Upper (D 6) (R 6) [10,132,96,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16395 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16396 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 296 21 96 83 147 275), lower := (rows 11 134 100 296 21 96 64 128 256), losses := [] }

theorem u16396 : Upper (D 6) (R 6) [10,132,96,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16397 : Route 9 := (fun mask => (mask,id))

def c16397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16397 : Upper (D 6) (R 6) [10,132,96,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,65,1] 13 (by decide) (choices 1) [2,4,16] r16397 c16397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4114
  · exact u4115
  · exact u4116

def r16398 : Route 9 := (fun mask => (mask,id))

def c16398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16398 : Upper (D 6) (R 6) [10,132,96,288,65,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,65,2] 13 (by decide) (choices 1) [1,4,16] r16398 c16398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4117
  · exact u4118
  · exact u4119

def b16399 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 134 100 296 81 36 83 147 275), lower := (rows 11 134 100 296 81 36 64 128 256), losses := [] }

theorem u16399 : Upper (D 6) (R 6) [10,132,96,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16400 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 296 81 48 71 135 263), lower := (rows 11 134 100 296 81 48 64 128 256), losses := [] }

theorem u16400 : Upper (D 6) (R 6) [10,132,96,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16400 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16401 : Route 9 := (fun mask => (mask,id))

def c16401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16401 : Upper (D 6) (R 6) [10,132,96,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,66,1] 13 (by decide) (choices 1) [1,4,16] r16401 c16401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4120
  · exact u4121
  · exact u4122

def b16402 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 134 100 296 82 36 81 145 273), lower := (rows 11 134 100 296 82 36 64 128 256), losses := [] }

theorem u16402 : Upper (D 6) (R 6) [10,132,96,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16403 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 296 82 48 69 133 261), lower := (rows 11 134 100 296 82 48 64 128 256), losses := [] }

theorem u16403 : Upper (D 6) (R 6) [10,132,96,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16403 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16404 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 261 25 52 34 96 224 352), lower := (rows 11 134 261 25 52 34 64 128 256), losses := [] }

theorem u16404 : Upper (D 6) (R 6) [10,132,257,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16405 : Route 9 := (fun mask => (mask,id))

def c16405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16405 : Upper (D 6) (R 6) [10,132,257,17,36,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,36,64] 13 (by decide) (choices 1) [2,32] r16405 c16405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4123
  · exact u4124

def r16406 : Route 9 := (fun mask => (mask,id))

def c16406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16406 : Upper (D 6) (R 6) [10,132,257,17,96,2] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,96,2] 13 (by decide) (choices 1) [4,32] r16406 c16406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4125
  · exact u4126

theorem m16407_2 : Upper (D 6) (R 6) [10,132,257,17,96,4,2] 13 :=
  permutation_upper _ _ _ [10,132,257,17,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4125

def r16407 : Route 9 := (fun mask => (mask,id))

def c16407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16407 : Upper (D 6) (R 6) [10,132,257,17,96,4] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,96,4] 13 (by decide) (choices 1) [2,32] r16407 c16407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16407_2
  · exact u4127

def b16408 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 25 112 96 102 166 294), lower := (rows 11 134 261 25 112 96 64 128 256), losses := [] }

theorem u16408 : Upper (D 6) (R 6) [10,132,257,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16409 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 261 28 49 34 96 224 352), lower := (rows 11 134 261 28 49 34 64 128 256), losses := [] }

theorem u16409 : Upper (D 6) (R 6) [10,132,257,20,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16410 : Route 9 := (fun mask => (mask,id))

def c16410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16410 : Upper (D 6) (R 6) [10,132,257,20,33,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,33,64] 13 (by decide) (choices 1) [2,32] r16410 c16410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4128
  · exact u4129

def b16411 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 261 28 50 33 96 224 352), lower := (rows 11 134 261 28 50 33 64 128 256), losses := [] }

theorem u16411 : Upper (D 6) (R 6) [10,132,257,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16412 : Route 9 := (fun mask => (mask,id))

def c16412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16412 : Upper (D 6) (R 6) [10,132,257,20,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,34,64] 13 (by decide) (choices 1) [1,32] r16412 c16412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4130
  · exact u4131

def r16413 : Route 9 := (fun mask => (mask,id))

def c16413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16413 : Upper (D 6) (R 6) [10,132,257,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,96,1] 13 (by decide) (choices 1) [2,32] r16413 c16413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4132
  · exact u4133

theorem m16414_1 : Upper (D 6) (R 6) [10,132,257,20,96,2,1] 13 :=
  permutation_upper _ _ _ [10,132,257,20,96,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4132

def r16414 : Route 9 := (fun mask => (mask,id))

def c16414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16414 : Upper (D 6) (R 6) [10,132,257,20,96,2] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,96,2] 13 (by decide) (choices 1) [1,32] r16414 c16414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16414_1
  · exact u4134

def b16415 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 28 112 96 99 163 291), lower := (rows 11 134 261 28 112 96 64 128 256), losses := [] }

theorem u16415 : Upper (D 6) (R 6) [10,132,257,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16416 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 2, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 134 261 41 82 36 112 240 368), lower := (rows 11 134 261 41 82 36 64 128 256), losses := [] }

theorem u16416 : Upper (D 6) (R 6) [10,132,257,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16417 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 261 41 82 48 100 228 356), lower := (rows 11 134 261 41 82 48 64 128 256), losses := [] }

theorem u16417 : Upper (D 6) (R 6) [10,132,257,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16417 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16418 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 134 261 41 82 96 116 180 308), lower := (rows 11 134 261 41 82 96 64 128 256), losses := [] }

theorem u16418 : Upper (D 6) (R 6) [10,132,257,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16419 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 261 41 84 34 112 240 368), lower := (rows 11 134 261 41 84 34 64 128 256), losses := [] }

theorem u16419 : Upper (D 6) (R 6) [10,132,257,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16420 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 261 41 84 48 98 226 354), lower := (rows 11 134 261 41 84 48 64 128 256), losses := [] }

theorem u16420 : Upper (D 6) (R 6) [10,132,257,33,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16420 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16421 : Route 9 := (fun mask => (mask,id))

def c16421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16421 : Upper (D 6) (R 6) [10,132,257,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,33,68,64] 13 (by decide) (choices 1) [2,16,32] r16421 c16421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4135
  · exact u4136
  · exact u4137

def b16422 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 261 41 112 34 84 212 340), lower := (rows 11 134 261 41 112 34 64 128 256), losses := [] }

theorem u16422 : Upper (D 6) (R 6) [10,132,257,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16423 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 2, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 134 261 41 112 36 82 210 338), lower := (rows 11 134 261 41 112 36 64 128 256), losses := [] }

theorem u16423 : Upper (D 6) (R 6) [10,132,257,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16424 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 261 41 112 48 70 198 326), lower := (rows 11 134 261 41 112 48 64 128 256), losses := [] }

theorem u16424 : Upper (D 6) (R 6) [10,132,257,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16424 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16425 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 41 112 96 86 150 278), lower := (rows 11 134 261 41 112 96 64 128 256), losses := [] }

theorem u16425 : Upper (D 6) (R 6) [10,132,257,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16426 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 261 44 50 33 80 208 336), lower := (rows 11 134 261 44 50 33 64 128 256), losses := [] }

theorem u16426 : Upper (D 6) (R 6) [10,132,257,36,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16427 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 134 261 44 50 48 65 193 321), lower := (rows 11 134 261 44 50 48 64 128 256), losses := [] }

theorem u16427 : Upper (D 6) (R 6) [10,132,257,36,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16427 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16428 : Route 9 := (fun mask => (mask,id))

def c16428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16428 : Upper (D 6) (R 6) [10,132,257,36,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,34,64] 13 (by decide) (choices 1) [1,16] r16428 c16428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4138
  · exact u4139

def b16429 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 134 261 44 81 34 112 240 368), lower := (rows 11 134 261 44 81 34 64 128 256), losses := [] }

theorem u16429 : Upper (D 6) (R 6) [10,132,257,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16430 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 134 261 44 81 48 98 226 354), lower := (rows 11 134 261 44 81 48 64 128 256), losses := [] }

theorem u16430 : Upper (D 6) (R 6) [10,132,257,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16430 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16431 : Route 9 := (fun mask => (mask,id))

def c16431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16431 : Upper (D 6) (R 6) [10,132,257,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,65,64] 13 (by decide) (choices 1) [2,16,32] r16431 c16431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4140
  · exact u4141
  · exact u4142

def b16432 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 210, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 134 261 44 82 33 112 240 368), lower := (rows 11 134 261 44 82 33 64 128 256), losses := [] }

theorem u16432 : Upper (D 6) (R 6) [10,132,257,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16433 : Route 9 := (fun mask => (mask,id))

def c16433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16433 : Upper (D 6) (R 6) [10,132,257,36,66,16] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,66,16] 13 (by decide) (choices 1) [1,32] r16433 c16433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4143
  · exact u4144

def r16434 : Route 9 := (fun mask => (mask,id))

def c16434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16434 : Upper (D 6) (R 6) [10,132,257,36,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,66,64] 13 (by decide) (choices 1) [1,16,32] r16434 c16434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4145
  · exact u4146
  · exact u4147

def b16435 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 210, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 134 261 44 112 33 82 210 338), lower := (rows 11 134 261 44 112 33 64 128 256), losses := [] }

theorem u16435 : Upper (D 6) (R 6) [10,132,257,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16436 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 134 261 44 112 34 81 209 337), lower := (rows 11 134 261 44 112 34 64 128 256), losses := [] }

theorem u16436 : Upper (D 6) (R 6) [10,132,257,36,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16437 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 261 44 112 48 67 195 323), lower := (rows 11 134 261 44 112 48 64 128 256), losses := [] }

theorem u16437 : Upper (D 6) (R 6) [10,132,257,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16437 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16438 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 44 112 96 83 147 275), lower := (rows 11 134 261 44 112 96 64 128 256), losses := [] }

theorem u16438 : Upper (D 6) (R 6) [10,132,257,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16439 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 11 134 261 56 81 34 100 228 356), lower := (rows 11 134 261 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 70 134 262), good := (rows 490 486 486 56 120 482 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 64 128 256), good := (rows 43 162 289 56 121 34 64 128 256) }] }

theorem u16439 : Upper (D 6) (R 6) [10,132,257,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16439
end Delivery.IrregularNine14.P06
