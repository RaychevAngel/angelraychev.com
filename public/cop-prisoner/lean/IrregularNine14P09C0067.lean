import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0016
import IrregularNine14P09C0017

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4020 : Route 9 := (fun mask => (mask,id))

def c4020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4020 : Upper (D 9) (R 9) [34,65,24,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,192,256] 13 (by decide) (choices 1) [4,32,256] r4020 c4020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u996
  · exact u997
  · exact u998

def b4021 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 137 276 96 480 416 416), lower := (rows 35 67 28 137 276 96 64 128 256), losses := [] }

theorem u4021 : Upper (D 9) (R 9) [34,65,24,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4021 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4022 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,7),(4,0)], upper := (rows 35 67 28 137 276 160 352 480 352), lower := (rows 35 67 28 137 276 160 64 128 256), losses := [{ target := 7, region := (rows 33 43 12 8 24 32 97 0 289), good := (rows 355 323 30 351 276 355 64 0 256) }] }

theorem u4022 : Upper (D 9) (R 9) [34,65,24,129,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4022 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4023 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 203, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,0)], upper := (rows 35 67 28 137 276 288 224 224 480), lower := (rows 35 67 28 137 276 288 64 128 256), losses := [] }

theorem u4023 : Upper (D 9) (R 9) [34,65,24,129,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4023 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4024 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 372, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 35 67 28 137 304 36 448 448 448), lower := (rows 35 67 28 137 304 36 64 128 256), losses := [] }

theorem u4024 : Upper (D 9) (R 9) [34,65,24,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4024 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4025 : PairBound 9 := { available := 388, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 137 304 96 452 388 388), lower := (rows 35 67 28 137 304 96 64 128 256), losses := [] }

theorem u4025 : Upper (D 9) (R 9) [34,65,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4025 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4026 : Route 9 := (fun mask => (mask,id))

def c4026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4026 : Upper (D 9) (R 9) [34,65,24,129,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288,128] 13 (by decide) (choices 1) [4,256] r4026 c4026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u999
  · exact u1000

def b4027 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 28 137 304 288 196 196 452), lower := (rows 35 67 28 137 304 288 64 128 256), losses := [] }

theorem u4027 : Upper (D 9) (R 9) [34,65,24,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4027 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4028 : Route 9 := (fun mask => (mask,id))

def c4028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u4028 : Upper (D 9) (R 9) [34,65,24,129,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320,4] 13 (by decide) (choices 1) [32,128,256] r4028 c4028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1001
  · exact u1002
  · exact u1003

def r4029 : Route 9 := (fun mask => (mask,id))

def c4029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4029 : Upper (D 9) (R 9) [34,65,24,129,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320,128] 13 (by decide) (choices 1) [4,32,256] r4029 c4029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1004
  · exact u1005
  · exact u1006

def r4030 : Route 9 := (fun mask => (mask,id))

def c4030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4030 : Upper (D 9) (R 9) [34,65,24,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320,256] 13 (by decide) (choices 1) [4,32,128] r4030 c4030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1007
  · exact u1008
  · exact u1009

def b4031 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 28 137 400 36 352 480 352), lower := (rows 35 67 28 137 400 36 64 128 256), losses := [] }

theorem u4031 : Upper (D 9) (R 9) [34,65,24,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4031 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 137 400 96 356 420 292), lower := (rows 35 67 28 137 400 96 64 128 256), losses := [] }

theorem u4032 : Upper (D 9) (R 9) [34,65,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4033 : Route 9 := (fun mask => (mask,id))

def c4033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4033 : Upper (D 9) (R 9) [34,65,24,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,384,256] 13 (by decide) (choices 1) [4,32] r4033 c4033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1010
  · exact u1011

def b4034 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 204, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 28 140 304 33 448 448 448), lower := (rows 35 67 28 140 304 33 64 128 256), losses := [] }

theorem u4034 : Upper (D 9) (R 9) [34,65,24,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4035 : PairBound 9 := { available := 385, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 140 304 96 449 385 385), lower := (rows 35 67 28 140 304 96 64 128 256), losses := [] }

theorem u4035 : Upper (D 9) (R 9) [34,65,24,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4035 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4036 : Route 9 := (fun mask => (mask,id))

def c4036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4036 : Upper (D 9) (R 9) [34,65,24,132,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,288,128] 13 (by decide) (choices 1) [1,256] r4036 c4036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1012
  · exact u1013

def b4037 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 28 140 304 288 193 193 449), lower := (rows 35 67 28 140 304 288 64 128 256), losses := [] }

theorem u4037 : Upper (D 9) (R 9) [34,65,24,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4037 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 140 336 33 480 416 416), lower := (rows 35 67 28 140 336 33 64 128 256), losses := [] }

theorem u4038 : Upper (D 9) (R 9) [34,65,24,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4038 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4039 : Route 9 := (fun mask => (mask,id))

def c4039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4039 : Upper (D 9) (R 9) [34,65,24,132,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,320,128] 13 (by decide) (choices 1) [1,32,256] r4039 c4039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1014
  · exact u1015
  · exact u1016

def b4040 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 35, targets := 128 },{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 28 140 336 288 225 161 417), lower := (rows 35 67 28 140 336 288 64 128 256), losses := [] }

theorem u4040 : Upper (D 9) (R 9) [34,65,24,132,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 340, targets := 33 },{ cop := 4, region := 35, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 28 168 208 33 324 388 260), lower := (rows 35 67 28 168 208 33 64 128 256), losses := [] }

theorem u4041 : Upper (D 9) (R 9) [34,65,24,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4041 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 28 168 208 36 321 385 257), lower := (rows 35 67 28 168 208 36 64 128 256), losses := [] }

theorem u4042 : Upper (D 9) (R 9) [34,65,24,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4042 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4043 : Route 9 := (fun mask => (mask,id))

def c4043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4043 : Upper (D 9) (R 9) [34,65,24,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,192,256] 13 (by decide) (choices 1) [1,4,256] r4043 c4043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1017
  · exact u1018
  · exact u1019

def b4044 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 340, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 28 168 336 33 452 388 388), lower := (rows 35 67 28 168 336 33 64 128 256), losses := [] }

theorem u4044 : Upper (D 9) (R 9) [34,65,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4044 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4045 : Route 9 := (fun mask => (mask,id))

def c4045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4045 : Upper (D 9) (R 9) [34,65,24,160,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320,4] 13 (by decide) (choices 1) [1,128,256] r4045 c4045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1020
  · exact u1021
  · exact u1022

def b4046 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 28 168 336 160 325 389 261), lower := (rows 35 67 28 168 336 160 64 128 256), losses := [] }

theorem u4046 : Upper (D 9) (R 9) [34,65,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4046 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4047 : Route 9 := (fun mask => (mask,id))

def c4047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4047 : Upper (D 9) (R 9) [34,65,24,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320,256] 13 (by decide) (choices 1) [1,4,128] r4047 c4047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1023
  · exact u1024
  · exact u1025

def b4048 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 340, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 28 168 400 33 324 452 324), lower := (rows 35 67 28 168 400 33 64 128 256), losses := [] }

theorem u4048 : Upper (D 9) (R 9) [34,65,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4048 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4049 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 44, targets := 321 }], pairs := [(2,0),(2,6),(2,8),(3,0)], upper := (rows 35 67 28 168 400 36 321 449 321), lower := (rows 35 67 28 168 400 36 64 128 256), losses := [] }

theorem u4049 : Upper (D 9) (R 9) [34,65,24,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4049 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4050 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 28 168 400 96 325 389 261), lower := (rows 35 67 28 168 400 96 64 128 256), losses := [] }

theorem u4050 : Upper (D 9) (R 9) [34,65,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4050 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4051 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 44, targets := 65 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 28 168 400 288 69 197 325), lower := (rows 35 67 28 168 400 288 64 128 256), losses := [] }

theorem u4051 : Upper (D 9) (R 9) [34,65,24,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 200 400 33 356 420 292), lower := (rows 35 67 28 200 400 33 64 128 256), losses := [] }

theorem u4052 : Upper (D 9) (R 9) [34,65,24,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4053 : Route 9 := (fun mask => (mask,id))

def c4053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4053 : Upper (D 9) (R 9) [34,65,24,192,384,4] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,384,4] 13 (by decide) (choices 1) [1,32,256] r4053 c4053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1026
  · exact u1027
  · exact u1028

def r4054 : Route 9 := (fun mask => (mask,id))

def c4054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4054 : Upper (D 9) (R 9) [34,65,24,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,384,256] 13 (by decide) (choices 1) [1,4,32] r4054 c4054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1029
  · exact u1030
  · exact u1031

def b4055 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 88 145 36 448 384 384), lower := (rows 35 67 44 88 145 36 64 128 256), losses := [] }

theorem u4055 : Upper (D 9) (R 9) [34,65,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4055 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 364, targets := 1 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,0)], upper := (rows 35 67 44 88 145 160 324 388 260), lower := (rows 35 67 44 88 145 160 64 128 256), losses := [] }

theorem u4056 : Upper (D 9) (R 9) [34,65,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4056 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4057 : Route 9 := (fun mask => (mask,id))

def c4057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4057 : Upper (D 9) (R 9) [34,65,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129,256] 13 (by decide) (choices 1) [4,128,256] r4057 c4057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def b4058 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 44 88 148 33 448 384 384), lower := (rows 35 67 44 88 148 33 64 128 256), losses := [] }

theorem u4058 : Upper (D 9) (R 9) [34,65,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4058 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4059 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7),(2,0)], upper := (rows 35 67 44 88 148 160 321 385 257), lower := (rows 35 67 44 88 148 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 124 180 160 64 160 256) }] }

theorem u4059 : Upper (D 9) (R 9) [34,65,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4059 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4060 : Route 9 := (fun mask => (mask,id))

def c4060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4060 : Upper (D 9) (R 9) [34,65,40,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132,256] 13 (by decide) (choices 1) [1,128,256] r4060 c4060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def b4061 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 44 88 400 33 452 388 388), lower := (rows 35 67 44 88 400 33 64 128 256), losses := [] }

theorem u4061 : Upper (D 9) (R 9) [34,65,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4061 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4062 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 88 400 36 449 385 385), lower := (rows 35 67 44 88 400 36 64 128 256), losses := [] }

theorem u4062 : Upper (D 9) (R 9) [34,65,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4062 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4063 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,0),(2,6)], upper := (rows 35 67 44 88 400 160 325 389 261), lower := (rows 35 67 44 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 124 432 160 64 160 256) },{ target := 6, region := (rows 1 2 12 8 16 176 0 128 256), good := (rows 35 3 44 60 432 160 0 160 256) },{ target := 8, region := (rows 13 10 12 8 16 176 64 128 0), good := (rows 35 67 47 127 176 160 64 160 0) }] }

theorem u4063 : Upper (D 9) (R 9) [34,65,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4063 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 137 84 48 448 384 384), lower := (rows 35 67 44 137 84 48 64 128 256), losses := [] }

theorem u4064 : Upper (D 9) (R 9) [34,65,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4064 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,7)], upper := (rows 35 67 44 137 84 160 336 400 272), lower := (rows 35 67 44 137 84 160 64 128 256), losses := [] }

theorem u4065 : Upper (D 9) (R 9) [34,65,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4065 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4066 : Route 9 := (fun mask => (mask,id))

def c4066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u4066 : Upper (D 9) (R 9) [34,65,40,129,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,68,256] 13 (by decide) (choices 1) [16,128,256] r4066 c4066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1038
  · exact u1039
  · exact u1040

def b4067 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 44 137 208 36 336 400 272), lower := (rows 35 67 44 137 208 36 64 128 256), losses := [] }

theorem u4067 : Upper (D 9) (R 9) [34,65,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4067 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4068 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 44 137 208 48 324 388 260), lower := (rows 35 67 44 137 208 48 64 128 256), losses := [] }

theorem u4068 : Upper (D 9) (R 9) [34,65,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4068 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4069 : Route 9 := (fun mask => (mask,id))

def c4069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4069 : Upper (D 9) (R 9) [34,65,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,192,256] 13 (by decide) (choices 1) [4,16,256] r4069 c4069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1041
  · exact u1042
  · exact u1043

def b4070 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 372, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 35 67 44 137 276 48 448 448 448), lower := (rows 35 67 44 137 276 48 64 128 256), losses := [] }

theorem u4070 : Upper (D 9) (R 9) [34,65,40,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4070 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 44 137 276 96 464 400 400), lower := (rows 35 67 44 137 276 96 64 128 256), losses := [] }

theorem u4071 : Upper (D 9) (R 9) [34,65,40,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4072 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,7)], upper := (rows 35 67 44 137 276 160 336 464 336), lower := (rows 35 67 44 137 276 160 64 128 256), losses := [] }

theorem u4072 : Upper (D 9) (R 9) [34,65,40,129,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4073 : Route 9 := (fun mask => (mask,id))

def c4073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4073 : Upper (D 9) (R 9) [34,65,40,129,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260,256] 13 (by decide) (choices 1) [16,128] r4073 c4073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1044
  · exact u1045

def b4074 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 3, region := 36, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 67 44 137 336 36 464 400 400), lower := (rows 35 67 44 137 336 36 64 128 256), losses := [] }

theorem u4074 : Upper (D 9) (R 9) [34,65,40,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4074 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4075 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 137 336 48 452 388 388), lower := (rows 35 67 44 137 336 48 64 128 256), losses := [] }

theorem u4075 : Upper (D 9) (R 9) [34,65,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4075 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4076 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,7)], upper := (rows 35 67 44 137 336 160 340 404 276), lower := (rows 35 67 44 137 336 160 64 128 256), losses := [] }

theorem u4076 : Upper (D 9) (R 9) [34,65,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 35, targets := 128 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,5)], upper := (rows 35 67 44 137 336 288 212 148 404), lower := (rows 35 67 44 137 336 288 64 128 256), losses := [] }

theorem u4077 : Upper (D 9) (R 9) [34,65,40,129,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 3, region := 36, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 67 44 137 400 36 336 464 336), lower := (rows 35 67 44 137 400 36 64 128 256), losses := [] }

theorem u4078 : Upper (D 9) (R 9) [34,65,40,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4078 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 44 137 400 48 324 452 324), lower := (rows 35 67 44 137 400 48 64 128 256), losses := [] }

theorem u4079 : Upper (D 9) (R 9) [34,65,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4079 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P09
