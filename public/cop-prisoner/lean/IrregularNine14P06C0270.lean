import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0066
import IrregularNine14P06C0067

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16200 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 296 84 48 65 193 321), lower := (rows 11 134 38 296 84 48 64 128 256), losses := [] }

theorem u16200 : Upper (D 6) (R 6) [10,132,34,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16200 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16201 : Route 9 := (fun mask => (mask,id))

def c16201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16201 : Upper (D 6) (R 6) [10,132,34,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,288,68,64] 13 (by decide) (choices 1) [1,16] r16201 c16201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4007
  · exact u4008

def b16202 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 11 134 38 328 21 33 112 240 368), lower := (rows 11 134 38 328 21 33 64 128 256), losses := [] }

theorem u16202 : Upper (D 6) (R 6) [10,132,34,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16203 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 134 38 328 21 48 97 225 353), lower := (rows 11 134 38 328 21 48 64 128 256), losses := [] }

theorem u16203 : Upper (D 6) (R 6) [10,132,34,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16203 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16204 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(2,0),(3,1),(3,2)], upper := (rows 11 134 38 328 21 96 113 177 305), lower := (rows 11 134 38 328 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 360 20 96 96 128 256) }] }

theorem u16204 : Upper (D 6) (R 6) [10,132,34,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16205 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 38 328 49 33 84 212 340), lower := (rows 11 134 38 328 49 33 64 128 256), losses := [] }

theorem u16205 : Upper (D 6) (R 6) [10,132,34,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16206 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 328 49 36 81 209 337), lower := (rows 11 134 38 328 49 36 64 128 256), losses := [] }

theorem u16206 : Upper (D 6) (R 6) [10,132,34,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16207 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 328 49 48 69 197 325), lower := (rows 11 134 38 328 49 48 64 128 256), losses := [] }

theorem u16207 : Upper (D 6) (R 6) [10,132,34,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16207 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16208 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 134, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 134 38 328 49 96 85 149 277), lower := (rows 11 134 38 328 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 134 38 360 52 96 96 128 256) }] }

theorem u16208 : Upper (D 6) (R 6) [10,132,34,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16209 : Route 9 := (fun mask => (mask,id))

def c16209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16209 : Upper (D 6) (R 6) [10,132,34,320,65,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,65,1] 13 (by decide) (choices 1) [4,16,32] r16209 c16209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4009
  · exact u4010
  · exact u4011

def b16210 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 328 81 36 113 177 305), lower := (rows 11 134 38 328 81 36 64 128 256), losses := [] }

theorem u16210 : Upper (D 6) (R 6) [10,132,34,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16211 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 134 38 328 81 48 101 165 293), lower := (rows 11 134 38 328 81 48 64 128 256), losses := [] }

theorem u16211 : Upper (D 6) (R 6) [10,132,34,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16211 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16212 : Route 9 := (fun mask => (mask,id))

def c16212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16212 : Upper (D 6) (R 6) [10,132,34,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,68,1] 13 (by decide) (choices 1) [1,16,32] r16212 c16212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4012
  · exact u4013
  · exact u4014

def b16213 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 38 328 84 48 97 161 289), lower := (rows 11 134 38 328 84 48 64 128 256), losses := [] }

theorem u16213 : Upper (D 6) (R 6) [10,132,34,320,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16213 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16214 : Route 9 := (fun mask => (mask,id))

def c16214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16214 : Upper (D 6) (R 6) [10,132,34,320,96,1] 13 := by
  apply FastRouting.sound _ _ [10,132,34,320,96,1] 13 (by decide) (choices 1) [1,4,16] r16214 c16214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4015
  · exact u4016
  · exact u4017

def b16215 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 328 112 36 81 145 273), lower := (rows 11 134 38 328 112 36 64 128 256), losses := [] }

theorem u16215 : Upper (D 6) (R 6) [10,132,34,320,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16216 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 38 328 112 48 69 133 261), lower := (rows 11 134 38 328 112 48 64 128 256), losses := [] }

theorem u16216 : Upper (D 6) (R 6) [10,132,34,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16216 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16217 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 82 33 324 452 324), lower := (rows 11 134 52 41 82 33 64 128 256), losses := [] }

theorem u16217 : Upper (D 6) (R 6) [10,132,48,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16218 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 52 41 82 36 321 449 321), lower := (rows 11 134 52 41 82 36 64 128 256), losses := [] }

theorem u16218 : Upper (D 6) (R 6) [10,132,48,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16219 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 41 82 96 325 389 261), lower := (rows 11 134 52 41 82 96 64 128 256), losses := [] }

theorem u16219 : Upper (D 6) (R 6) [10,132,48,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16220 : Route 9 := (fun mask => (mask,id))

def c16220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16220 : Upper (D 6) (R 6) [10,132,48,33,66,256] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,66,256] 13 (by decide) (choices 1) [1,4] r16220 c16220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4018
  · exact u4019

def b16221 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 134 52 41 84 33 322 450 322), lower := (rows 11 134 52 41 84 33 64 128 256), losses := [] }

theorem u16221 : Upper (D 6) (R 6) [10,132,48,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16222 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 84 34 321 449 321), lower := (rows 11 134 52 41 84 34 64 128 256), losses := [] }

theorem u16222 : Upper (D 6) (R 6) [10,132,48,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16223 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 41 84 96 323 387 259), lower := (rows 11 134 52 41 84 96 64 128 256), losses := [] }

theorem u16223 : Upper (D 6) (R 6) [10,132,48,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16224 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 52 41 84 288 67 195 323), lower := (rows 11 134 52 41 84 288 64 128 256), losses := [] }

theorem u16224 : Upper (D 6) (R 6) [10,132,48,33,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16224 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16225 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 274 33 68 196 324), lower := (rows 11 134 52 41 274 33 64 128 256), losses := [] }

theorem u16225 : Upper (D 6) (R 6) [10,132,48,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16226 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 134 52 41 274 36 65 193 321), lower := (rows 11 134 52 41 274 36 64 128 256), losses := [] }

theorem u16226 : Upper (D 6) (R 6) [10,132,48,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16227 : Route 9 := (fun mask => (mask,id))

def c16227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16227 : Upper (D 6) (R 6) [10,132,48,33,258,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,258,64] 13 (by decide) (choices 1) [1,4] r16227 c16227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4020
  · exact u4021

def b16228 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 134 52 41 276 33 66 194 322), lower := (rows 11 134 52 41 276 33 64 128 256), losses := [] }

theorem u16228 : Upper (D 6) (R 6) [10,132,48,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16229 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 276 34 65 193 321), lower := (rows 11 134 52 41 276 34 64 128 256), losses := [] }

theorem u16229 : Upper (D 6) (R 6) [10,132,48,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16230 : Route 9 := (fun mask => (mask,id))

def c16230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16230 : Upper (D 6) (R 6) [10,132,48,33,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,33,260,64] 13 (by decide) (choices 1) [1,2] r16230 c16230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4022
  · exact u4023

def b16231 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 336 33 70 198 326), lower := (rows 11 134 52 41 336 33 64 128 256), losses := [] }

theorem u16231 : Upper (D 6) (R 6) [10,132,48,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16232 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 52 41 336 34 69 197 325), lower := (rows 11 134 52 41 336 34 64 128 256), losses := [] }

theorem u16232 : Upper (D 6) (R 6) [10,132,48,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16233 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 41 336 36 67 195 323), lower := (rows 11 134 52 41 336 36 64 128 256), losses := [] }

theorem u16233 : Upper (D 6) (R 6) [10,132,48,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16234 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 41 336 96 71 135 263), lower := (rows 11 134 52 41 336 96 64 128 256), losses := [] }

theorem u16234 : Upper (D 6) (R 6) [10,132,48,33,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16235 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 84 33 354 418 290), lower := (rows 11 134 52 73 84 33 64 128 256), losses := [] }

theorem u16235 : Upper (D 6) (R 6) [10,132,48,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16236 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 134 52 73 84 34 353 417 289), lower := (rows 11 134 52 73 84 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 13 8 24 35 64 128 256), good := (rows 62 166 52 124 84 34 64 128 256) }] }

theorem u16236 : Upper (D 6) (R 6) [10,132,48,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16237 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 134 52 73 84 288 99 163 291), lower := (rows 11 134 52 73 84 288 64 128 256), losses := [] }

theorem u16237 : Upper (D 6) (R 6) [10,132,48,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16237 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16238 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 134 52 73 273 34 100 228 356), lower := (rows 11 134 52 73 273 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 35 0 128 256), good := (rows 43 166 52 41 309 34 0 128 256) }] }

theorem u16238 : Upper (D 6) (R 6) [10,132,48,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16239 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 52 73 273 36 98 226 354), lower := (rows 11 134 52 73 273 36 64 128 256), losses := [] }

theorem u16239 : Upper (D 6) (R 6) [10,132,48,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16240 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 52 73 273 96 102 166 294), lower := (rows 11 134 52 73 273 96 64 128 256), losses := [] }

theorem u16240 : Upper (D 6) (R 6) [10,132,48,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16241 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 274 33 100 228 356), lower := (rows 11 134 52 73 274 33 64 128 256), losses := [] }

theorem u16241 : Upper (D 6) (R 6) [10,132,48,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16242 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 73 274 36 97 225 353), lower := (rows 11 134 52 73 274 36 64 128 256), losses := [] }

theorem u16242 : Upper (D 6) (R 6) [10,132,48,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16243 : Route 9 := (fun mask => (mask,id))

def c16243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16243 : Upper (D 6) (R 6) [10,132,48,65,258,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,258,64] 13 (by decide) (choices 1) [1,4,32] r16243 c16243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4024
  · exact u4025
  · exact u4026

def b16244 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 276 33 98 226 354), lower := (rows 11 134 52 73 276 33 64 128 256), losses := [] }

theorem u16244 : Upper (D 6) (R 6) [10,132,48,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16245 : Route 9 := (fun mask => (mask,id))

def c16245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16245 : Upper (D 6) (R 6) [10,132,48,65,260,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,260,2] 13 (by decide) (choices 1) [1,32] r16245 c16245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4027
  · exact u4028

def r16246 : Route 9 := (fun mask => (mask,id))

def c16246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16246 : Upper (D 6) (R 6) [10,132,48,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,260,64] 13 (by decide) (choices 1) [1,2,32] r16246 c16246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4029
  · exact u4030
  · exact u4031

def b16247 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 73 336 33 102 166 294), lower := (rows 11 134 52 73 336 33 64 128 256), losses := [] }

theorem u16247 : Upper (D 6) (R 6) [10,132,48,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16248 : Route 9 := (fun mask => (mask,id))

def c16248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16248 : Upper (D 6) (R 6) [10,132,48,65,320,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,65,320,2] 13 (by decide) (choices 1) [1,4,32] r16248 c16248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4032
  · exact u4033
  · exact u4034

def b16249 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 73 336 36 99 163 291), lower := (rows 11 134 52 73 336 36 64 128 256), losses := [] }

theorem u16249 : Upper (D 6) (R 6) [10,132,48,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16250 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 202, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 134 52 76 273 33 98 226 354), lower := (rows 11 134 52 76 273 33 64 128 256), losses := [] }

theorem u16250 : Upper (D 6) (R 6) [10,132,48,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16251 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(2,0),(2,6),(4,2)], upper := (rows 11 134 52 76 273 34 97 225 353), lower := (rows 11 134 52 76 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 64 128 256), good := (rows 42 166 52 76 308 34 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 35 0 128 256), good := (rows 43 166 52 12 309 34 0 128 256) }] }

theorem u16251 : Upper (D 6) (R 6) [10,132,48,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16252 : Route 9 := (fun mask => (mask,id))

def c16252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16252 : Upper (D 6) (R 6) [10,132,48,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68,257,64] 13 (by decide) (choices 1) [1,2,32] r16252 c16252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4035
  · exact u4036
  · exact u4037

def r16253 : Route 9 := (fun mask => (mask,id))

def c16253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16253 : Upper (D 6) (R 6) [10,132,48,68,258,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68,258,1] 13 (by decide) (choices 1) [1,32] r16253 c16253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4038
  · exact u4039

def r16254 : Route 9 := (fun mask => (mask,id))

def c16254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16254 : Upper (D 6) (R 6) [10,132,48,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,132,48,68,258,64] 13 (by decide) (choices 1) [1,32] r16254 c16254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4040
  · exact u4041

def b16255 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 134 52 104 81 33 326 390 262), lower := (rows 11 134 52 104 81 33 64 128 256), losses := [] }

theorem u16255 : Upper (D 6) (R 6) [10,132,48,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16256 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 134 52 104 81 34 325 389 261), lower := (rows 11 134 52 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 64 128 256), good := (rows 42 166 60 104 124 34 64 128 256) }] }

theorem u16256 : Upper (D 6) (R 6) [10,132,48,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16257 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 52 104 81 36 323 387 259), lower := (rows 11 134 52 104 81 36 64 128 256), losses := [] }

theorem u16257 : Upper (D 6) (R 6) [10,132,48,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16258 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 134 52 104 81 288 71 135 263), lower := (rows 11 134 52 104 81 288 64 128 256), losses := [] }

theorem u16258 : Upper (D 6) (R 6) [10,132,48,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16258 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16259 : Route 9 := (fun mask => (mask,id))

def c16259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16259 : Upper (D 6) (R 6) [10,132,48,96,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,66,1] 13 (by decide) (choices 1) [1,4,256] r16259 c16259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4042
  · exact u4043
  · exact u4044

#print axioms u16259
end Delivery.IrregularNine14.P06
