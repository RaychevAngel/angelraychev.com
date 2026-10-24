import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0049
import IrregularNine14P07C0050
import IrregularNine14P07C0051

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15240 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 69 104 145 34 216 152 408), lower := (rows 7 290 69 104 145 34 64 128 256), losses := [] }

theorem u15240 : Upper (D 7) (R 7) [6,288,65,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15241 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 69 104 145 40 210 146 402), lower := (rows 7 290 69 104 145 40 64 128 256), losses := [] }

theorem u15241 : Upper (D 7) (R 7) [6,288,65,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15241 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15242 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 290 69 104 145 48 202 138 394), lower := (rows 7 290 69 104 145 48 64 128 256), losses := [] }

theorem u15242 : Upper (D 7) (R 7) [6,288,65,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15242 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15243 : Route 9 := (fun mask => (mask,id))

def c15243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15243 : Upper (D 7) (R 7) [6,288,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,129,128] 13 (by decide) (choices 1) [2,8,16] r15243 c15243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2977
  · exact u2978
  · exact u2979

def b15244 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 290 69 104 146 33 216 152 408), lower := (rows 7 290 69 104 146 33 64 128 256), losses := [] }

theorem u15244 : Upper (D 7) (R 7) [6,288,65,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15245 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 69 104 146 40 209 145 401), lower := (rows 7 290 69 104 146 40 64 128 256), losses := [] }

theorem u15245 : Upper (D 7) (R 7) [6,288,65,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15245 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15246 : Route 9 := (fun mask => (mask,id))

def c15246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15246 : Upper (D 7) (R 7) [6,288,65,96,130,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,130,16] 13 (by decide) (choices 1) [1,8,128] r15246 c15246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2980
  · exact u2981
  · exact u2982

def r15247 : Route 9 := (fun mask => (mask,id))

def c15247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15247 : Upper (D 7) (R 7) [6,288,65,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,130,128] 13 (by decide) (choices 1) [1,8,16] r15247 c15247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2983
  · exact u2984
  · exact u2985

def b15248 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 40, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 290 69 104 152 33 210 146 402), lower := (rows 7 290 69 104 152 33 64 128 256), losses := [] }

theorem u15248 : Upper (D 7) (R 7) [6,288,65,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15249 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 290 69 104 152 34 209 145 401), lower := (rows 7 290 69 104 152 34 64 128 256), losses := [{ target := 0, region := (rows 0 258 4 12 16 291 64 128 256), good := (rows 46 290 108 104 152 34 64 128 290) }] }

theorem u15249 : Upper (D 7) (R 7) [6,288,65,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15250 : Route 9 := (fun mask => (mask,id))

def c15250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15250 : Upper (D 7) (R 7) [6,288,65,96,136,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,136,16] 13 (by decide) (choices 1) [1,2,128] r15250 c15250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2986
  · exact u2987
  · exact u2988

def r15251 : Route 9 := (fun mask => (mask,id))

def c15251 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15251 : Upper (D 7) (R 7) [6,288,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [6,288,65,96,136,128] 13 (by decide) (choices 1) [1,2,16] r15251 c15251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2989
  · exact u2990
  · exact u2991

def r15252 : Route 9 := (fun mask => (mask,id))

def c15252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15252 : Upper (D 7) (R 7) [6,288,65,129,130,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,130,8] 13 (by decide) (choices 1) [16,32] r15252 c15252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2992
  · exact u2993

def r15253 : Route 9 := (fun mask => (mask,id))

def c15253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15253 : Upper (D 7) (R 7) [6,288,65,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,130,16] 13 (by decide) (choices 1) [8,32] r15253 c15253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2994
  · exact u2995

def r15254 : Route 9 := (fun mask => (mask,id))

def c15254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15254 : Upper (D 7) (R 7) [6,288,65,129,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,130,64] 13 (by decide) (choices 1) [8,16,32] r15254 c15254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2996
  · exact u2997
  · exact u2998

def b15255 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 290 69 137 176 34 88 216 344), lower := (rows 7 290 69 137 176 34 64 128 256), losses := [] }

theorem u15255 : Upper (D 7) (R 7) [6,288,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15256 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 137 176 40 82 210 338), lower := (rows 7 290 69 137 176 40 64 128 256), losses := [] }

theorem u15256 : Upper (D 7) (R 7) [6,288,65,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15256 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15257 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 69 137 176 48 74 202 330), lower := (rows 7 290 69 137 176 48 64 128 256), losses := [] }

theorem u15257 : Upper (D 7) (R 7) [6,288,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15257 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15258 : Route 9 := (fun mask => (mask,id))

def c15258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15258 : Upper (D 7) (R 7) [6,288,65,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,160,64] 13 (by decide) (choices 1) [2,8,16] r15258 c15258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2999
  · exact u3000
  · exact u3001

def b15259 : PairBound 9 := { available := 56, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 7 290 69 137 208 34 120 184 312), lower := (rows 7 290 69 137 208 34 64 128 256), losses := [] }

theorem u15259 : Upper (D 7) (R 7) [6,288,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15260 : Route 9 := (fun mask => (mask,id))

def c15260 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15260 : Upper (D 7) (R 7) [6,288,65,129,192,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,192,8] 13 (by decide) (choices 1) [2,16,32] r15260 c15260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3002
  · exact u3003
  · exact u3004

def r15261 : Route 9 := (fun mask => (mask,id))

def c15261 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15261 : Upper (D 7) (R 7) [6,288,65,129,192,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,129,192,16] 13 (by decide) (choices 1) [2,8,32] r15261 c15261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3005
  · exact u3006
  · exact u3007

def r15262 : Route 9 := (fun mask => (mask,id))

def c15262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15262 : Upper (D 7) (R 7) [6,288,65,130,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,160,1] 13 (by decide) (choices 1) [8,16] r15262 c15262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3008
  · exact u3009

def b15263 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 290 69 138 176 40 81 209 337), lower := (rows 7 290 69 138 176 40 64 128 256), losses := [] }

theorem u15263 : Upper (D 7) (R 7) [6,288,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15263 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15264 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 69 138 176 48 73 201 329), lower := (rows 7 290 69 138 176 48 64 128 256), losses := [] }

theorem u15264 : Upper (D 7) (R 7) [6,288,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15264 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15265 : Route 9 := (fun mask => (mask,id))

def c15265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15265 : Upper (D 7) (R 7) [6,288,65,130,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,160,64] 13 (by decide) (choices 1) [1,8,16] r15265 c15265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3010
  · exact u3011
  · exact u3012

def r15266 : Route 9 := (fun mask => (mask,id))

def c15266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15266 : Upper (D 7) (R 7) [6,288,65,130,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,192,1] 13 (by decide) (choices 1) [8,16,32] r15266 c15266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3013
  · exact u3014
  · exact u3015

def r15267 : Route 9 := (fun mask => (mask,id))

def c15267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15267 : Upper (D 7) (R 7) [6,288,65,130,192,8] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,192,8] 13 (by decide) (choices 1) [1,16,32] r15267 c15267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3016
  · exact u3017
  · exact u3018

def r15268 : Route 9 := (fun mask => (mask,id))

def c15268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15268 : Upper (D 7) (R 7) [6,288,65,130,192,16] 13 := by
  apply FastRouting.sound _ _ [6,288,65,130,192,16] 13 (by decide) (choices 1) [1,8,32] r15268 c15268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3019
  · exact u3020
  · exact u3021

def r15269 : Route 9 := (fun mask => (mask,id))

def c15269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15269 : Upper (D 7) (R 7) [6,288,65,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,65,160,192,1] 13 (by decide) (choices 1) [2,8,16] r15269 c15269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3022
  · exact u3023
  · exact u3024

def r15270 : Route 9 := (fun mask => (mask,id))

def c15270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15270 : Upper (D 7) (R 7) [6,288,65,160,192,2] 13 := by
  apply FastRouting.sound _ _ [6,288,65,160,192,2] 13 (by decide) (choices 1) [1,8,16] r15270 c15270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3025
  · exact u3026
  · exact u3027

def b15271 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 69 168 208 40 83 147 275), lower := (rows 7 290 69 168 208 40 64 128 256), losses := [] }

theorem u15271 : Upper (D 7) (R 7) [6,288,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15271 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15272 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 168 208 48 75 139 267), lower := (rows 7 290 69 168 208 48 64 128 256), losses := [] }

theorem u15272 : Upper (D 7) (R 7) [6,288,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15272 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15273 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(4,0)], upper := (rows 7 290 76 25 112 33 194 130 386), lower := (rows 7 290 76 25 112 33 64 128 256), losses := [] }

theorem u15273 : Upper (D 7) (R 7) [6,288,72,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15274 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 76 25 112 34 193 129 385), lower := (rows 7 290 76 25 112 34 64 128 256), losses := [] }

theorem u15274 : Upper (D 7) (R 7) [6,288,72,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15275 : Route 9 := (fun mask => (mask,id))

def c15275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15275 : Upper (D 7) (R 7) [6,288,72,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,96,128] 13 (by decide) (choices 1) [1,2,128] r15275 c15275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3028
  · exact u3029
  · exact u3030

def r15276 : Route 9 := (fun mask => (mask,id))

def c15276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15276 : Upper (D 7) (R 7) [6,288,72,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,130,1] 13 (by decide) (choices 1) [32,128] r15276 c15276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3031
  · exact u3032

def r15277 : Route 9 := (fun mask => (mask,id))

def c15277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15277 : Upper (D 7) (R 7) [6,288,72,17,130,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,130,64] 13 (by decide) (choices 1) [1,32,128] r15277 c15277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3033
  · exact u3034
  · exact u3035

def r15278 : Route 9 := (fun mask => (mask,id))

def c15278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15278 : Upper (D 7) (R 7) [6,288,72,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,130,128] 13 (by decide) (choices 1) [1,32] r15278 c15278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3036
  · exact u3037

def b15279 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(4,0)], upper := (rows 7 290 76 25 176 33 194 194 450), lower := (rows 7 290 76 25 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 50 32 123 187 315), good := (rows 470 498 460 478 498 498 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 455 450 76 477 144 449 64 128 256) }] }

theorem u15279 : Upper (D 7) (R 7) [6,288,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15280 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 290 76 25 176 34 193 193 449), lower := (rows 7 290 76 25 176 34 64 128 256), losses := [] }

theorem u15280 : Upper (D 7) (R 7) [6,288,72,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15281 : Route 9 := (fun mask => (mask,id))

def c15281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15281 : Upper (D 7) (R 7) [6,288,72,17,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,160,64] 13 (by decide) (choices 1) [1,2,128] r15281 c15281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3038
  · exact u3039
  · exact u3040

def b15282 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 76 25 176 160 67 195 323), lower := (rows 7 290 76 25 176 160 64 128 256), losses := [] }

theorem u15282 : Upper (D 7) (R 7) [6,288,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15283 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(4,0)], upper := (rows 7 290 76 25 208 33 226 162 418), lower := (rows 7 290 76 25 208 33 64 128 256), losses := [] }

theorem u15283 : Upper (D 7) (R 7) [6,288,72,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15284 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(1,7)], upper := (rows 7 290 76 25 208 34 225 161 417), lower := (rows 7 290 76 25 208 34 64 128 256), losses := [] }

theorem u15284 : Upper (D 7) (R 7) [6,288,72,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15285 : Route 9 := (fun mask => (mask,id))

def c15285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15285 : Upper (D 7) (R 7) [6,288,72,17,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,17,192,128] 13 (by decide) (choices 1) [1,2,32] r15285 c15285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3041
  · exact u3042
  · exact u3043

def b15286 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 5, region := 450, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 290 76 26 145 33 224 224 480), lower := (rows 7 290 76 26 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 98 162 290), good := (rows 454 482 76 478 144 482 64 128 256) },{ target := 1, region := (rows 1 0 12 8 49 49 123 187 315), good := (rows 501 496 460 508 497 497 64 128 256) }] }

theorem u15286 : Upper (D 7) (R 7) [6,288,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15287 : Route 9 := (fun mask => (mask,id))

def c15287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15287 : Upper (D 7) (R 7) [6,288,72,18,129,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,129,64] 13 (by decide) (choices 1) [1,32,128] r15287 c15287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3044
  · exact u3045
  · exact u3046

def r15288 : Route 9 := (fun mask => (mask,id))

def c15288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15288 : Upper (D 7) (R 7) [6,288,72,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,129,128] 13 (by decide) (choices 1) [1,32] r15288 c15288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3047
  · exact u3048

def r15289 : Route 9 := (fun mask => (mask,id))

def c15289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15289 : Upper (D 7) (R 7) [6,288,72,18,160,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,160,1] 13 (by decide) (choices 1) [1,128] r15289 c15289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3049
  · exact u3050

def r15290 : Route 9 := (fun mask => (mask,id))

def c15290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15290 : Upper (D 7) (R 7) [6,288,72,18,160,64] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,160,64] 13 (by decide) (choices 1) [1,128] r15290 c15290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3051
  · exact u3052

def b15291 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 76 26 176 160 65 193 321), lower := (rows 7 290 76 26 176 160 64 128 256), losses := [] }

theorem u15291 : Upper (D 7) (R 7) [6,288,72,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15292 : Route 9 := (fun mask => (mask,id))

def c15292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15292 : Upper (D 7) (R 7) [6,288,72,18,192,1] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,192,1] 13 (by decide) (choices 1) [1,32,128] r15292 c15292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3053
  · exact u3054
  · exact u3055

def r15293 : Route 9 := (fun mask => (mask,id))

def c15293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15293 : Upper (D 7) (R 7) [6,288,72,18,192,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,18,192,128] 13 (by decide) (choices 1) [1,32] r15293 c15293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3056
  · exact u3057

def b15294 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 290 76 41 82 33 208 144 400), lower := (rows 7 290 76 41 82 33 64 128 256), losses := [] }

theorem u15294 : Upper (D 7) (R 7) [6,288,72,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15295 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 76 41 82 48 193 129 385), lower := (rows 7 290 76 41 82 48 64 128 256), losses := [] }

theorem u15295 : Upper (D 7) (R 7) [6,288,72,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15295 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15296 : Route 9 := (fun mask => (mask,id))

def c15296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15296 : Upper (D 7) (R 7) [6,288,72,33,66,128] 13 := by
  apply FastRouting.sound _ _ [6,288,72,33,66,128] 13 (by decide) (choices 1) [1,16,128] r15296 c15296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3058
  · exact u3059
  · exact u3060

def b15297 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 290 76 41 145 34 208 208 464), lower := (rows 7 290 76 41 145 34 64 128 256), losses := [] }

theorem u15297 : Upper (D 7) (R 7) [6,288,72,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15298 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 290 76 41 145 48 194 194 450), lower := (rows 7 290 76 41 145 48 64 128 256), losses := [] }

theorem u15298 : Upper (D 7) (R 7) [6,288,72,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15299 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 402, targets := 64 },{ cop := 0, region := 144, targets := 32 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(1,6),(4,5),(4,6)], upper := (rows 7 290 76 41 145 96 210 146 402), lower := (rows 7 290 76 41 145 96 64 128 256), losses := [] }

theorem u15299 : Upper (D 7) (R 7) [6,288,72,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15299
end Delivery.IrregularNine14.P07
