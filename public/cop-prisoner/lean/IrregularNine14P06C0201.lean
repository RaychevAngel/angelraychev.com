import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0036
import IrregularNine14P06C0037

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12060 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 69 140 52 34 336 464 336), lower := (rows 11 35 69 140 52 34 64 128 256), losses := [] }

theorem u12060 : Upper (D 6) (R 6) [10,33,65,132,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12061 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 140 52 48 322 450 322), lower := (rows 11 35 69 140 52 48 64 128 256), losses := [] }

theorem u12061 : Upper (D 6) (R 6) [10,33,65,132,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12061 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12062 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 69 140 52 96 338 402 274), lower := (rows 11 35 69 140 52 96 64 128 256), losses := [] }

theorem u12062 : Upper (D 6) (R 6) [10,33,65,132,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12063 : PairBound 9 := { available := 82, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 35 69 140 52 288 82 210 338), lower := (rows 11 35 69 140 52 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 295 65 129 257), good := (rows 506 482 508 188 60 288 64 128 288) }] }

theorem u12063 : Upper (D 6) (R 6) [10,33,65,132,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12063 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12064 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 140 82 36 368 432 304), lower := (rows 11 35 69 140 82 36 64 128 256), losses := [] }

theorem u12064 : Upper (D 6) (R 6) [10,33,65,132,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12065 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 69 140 82 48 356 420 292), lower := (rows 11 35 69 140 82 48 64 128 256), losses := [] }

theorem u12065 : Upper (D 6) (R 6) [10,33,65,132,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12065 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12066 : Route 9 := (fun mask => (mask,id))

def c12066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12066 : Upper (D 6) (R 6) [10,33,65,132,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,66,256] 13 (by decide) (choices 1) [4,16,32] r12066 c12066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2181
  · exact u2182
  · exact u2183

def b12067 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 140 112 34 340 404 276), lower := (rows 11 35 69 140 112 34 64 128 256), losses := [] }

theorem u12067 : Upper (D 6) (R 6) [10,33,65,132,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12068 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 140 112 36 338 402 274), lower := (rows 11 35 69 140 112 36 64 128 256), losses := [] }

theorem u12068 : Upper (D 6) (R 6) [10,33,65,132,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12069 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 140 112 48 326 390 262), lower := (rows 11 35 69 140 112 48 64 128 256), losses := [] }

theorem u12069 : Upper (D 6) (R 6) [10,33,65,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12069 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12070 : Route 9 := (fun mask => (mask,id))

def c12070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12070 : Upper (D 6) (R 6) [10,33,65,132,96,256] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,96,256] 13 (by decide) (choices 1) [2,4,16] r12070 c12070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2184
  · exact u2185
  · exact u2186

def b12071 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 140 274 36 112 240 368), lower := (rows 11 35 69 140 274 36 64 128 256), losses := [] }

theorem u12071 : Upper (D 6) (R 6) [10,33,65,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12072 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 69 140 274 48 100 228 356), lower := (rows 11 35 69 140 274 48 64 128 256), losses := [] }

theorem u12072 : Upper (D 6) (R 6) [10,33,65,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12072 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12073 : Route 9 := (fun mask => (mask,id))

def c12073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12073 : Upper (D 6) (R 6) [10,33,65,132,258,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,258,64] 13 (by decide) (choices 1) [4,16,32] r12073 c12073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2187
  · exact u2188
  · exact u2189

def b12074 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 140 276 34 112 240 368), lower := (rows 11 35 69 140 276 34 64 128 256), losses := [] }

theorem u12074 : Upper (D 6) (R 6) [10,33,65,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12075 : PairBound 9 := { available := 98, camps := [], pairs := [(3,0),(4,0)], upper := (rows 11 35 69 140 276 48 98 226 354), lower := (rows 11 35 69 140 276 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 60 67 131 259), good := (rows 490 482 508 188 316 48 64 128 256) }] }

theorem u12075 : Upper (D 6) (R 6) [10,33,65,132,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12075 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12076 : Route 9 := (fun mask => (mask,id))

def c12076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12076 : Upper (D 6) (R 6) [10,33,65,132,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,260,64] 13 (by decide) (choices 1) [2,16,32] r12076 c12076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2190
  · exact u2191
  · exact u2192

def b12077 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 140 304 34 84 212 340), lower := (rows 11 35 69 140 304 34 64 128 256), losses := [] }

theorem u12077 : Upper (D 6) (R 6) [10,33,65,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12078 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 140 304 36 82 210 338), lower := (rows 11 35 69 140 304 36 64 128 256), losses := [] }

theorem u12078 : Upper (D 6) (R 6) [10,33,65,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12079 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 69 140 304 48 70 198 326), lower := (rows 11 35 69 140 304 48 64 128 256), losses := [] }

theorem u12079 : Upper (D 6) (R 6) [10,33,65,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12079 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12080 : Route 9 := (fun mask => (mask,id))

def c12080 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12080 : Upper (D 6) (R 6) [10,33,65,132,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,288,64] 13 (by decide) (choices 1) [2,4,16] r12080 c12080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2193
  · exact u2194
  · exact u2195

def b12081 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 140 336 34 116 180 308), lower := (rows 11 35 69 140 336 34 64 128 256), losses := [] }

theorem u12081 : Upper (D 6) (R 6) [10,33,65,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12082 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 11 35 69 140 336 36 114 178 306), lower := (rows 11 35 69 140 336 36 64 128 256), losses := [] }

theorem u12082 : Upper (D 6) (R 6) [10,33,65,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12083 : Route 9 := (fun mask => (mask,id))

def c12083 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12083 : Upper (D 6) (R 6) [10,33,65,132,320,16] 13 := by
  apply FastRouting.sound _ _ [10,33,65,132,320,16] 13 (by decide) (choices 1) [2,4,32] r12083 c12083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2196
  · exact u2197
  · exact u2198

def b12084 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 152 52 34 324 452 324), lower := (rows 11 35 69 152 52 34 64 128 256), losses := [] }

theorem u12084 : Upper (D 6) (R 6) [10,33,65,144,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12085 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 69 152 52 36 322 450 322), lower := (rows 11 35 69 152 52 36 64 128 256), losses := [] }

theorem u12085 : Upper (D 6) (R 6) [10,33,65,144,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12086 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 69 152 52 96 326 390 262), lower := (rows 11 35 69 152 52 96 64 128 256), losses := [] }

theorem u12086 : Upper (D 6) (R 6) [10,33,65,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12087 : Route 9 := (fun mask => (mask,id))

def c12087 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12087 : Upper (D 6) (R 6) [10,33,65,144,36,256] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,36,256] 13 (by decide) (choices 1) [2,4] r12087 c12087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2199
  · exact u2200

def b12088 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 152 112 34 324 388 260), lower := (rows 11 35 69 152 112 34 64 128 256), losses := [] }

theorem u12088 : Upper (D 6) (R 6) [10,33,65,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12089 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 35 69 152 112 36 326 390 262), lower := (rows 11 35 69 152 112 36 64 128 256), losses := [] }

theorem u12089 : Upper (D 6) (R 6) [10,33,65,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12090 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,5)], upper := (rows 11 35 69 152 112 288 70 134 262), lower := (rows 11 35 69 152 112 288 64 128 256), losses := [] }

theorem u12090 : Upper (D 6) (R 6) [10,33,65,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12090 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12091 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 11 35 69 152 274 36 100 228 356), lower := (rows 11 35 69 152 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 100 164 292), good := (rows 26 506 484 152 282 484 64 128 256) }] }

theorem u12091 : Upper (D 6) (R 6) [10,33,65,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12092 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 35 69 152 274 96 100 164 292), lower := (rows 11 35 69 152 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 127 87 151 279), good := (rows 493 485 485 504 508 96 96 128 256) }] }

theorem u12092 : Upper (D 6) (R 6) [10,33,65,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12093 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 152 276 34 100 228 356), lower := (rows 11 35 69 152 276 34 64 128 256), losses := [] }

theorem u12093 : Upper (D 6) (R 6) [10,33,65,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12094 : Route 9 := (fun mask => (mask,id))

def c12094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12094 : Upper (D 6) (R 6) [10,33,65,144,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,260,4] 13 (by decide) (choices 1) [2,32] r12094 c12094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2201
  · exact u2202

def r12095 : Route 9 := (fun mask => (mask,id))

def c12095 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12095 : Upper (D 6) (R 6) [10,33,65,144,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,260,64] 13 (by decide) (choices 1) [2,4,32] r12095 c12095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2203
  · exact u2204
  · exact u2205

def b12096 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 152 304 34 68 196 324), lower := (rows 11 35 69 152 304 34 64 128 256), losses := [] }

theorem u12096 : Upper (D 6) (R 6) [10,33,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12097 : Route 9 := (fun mask => (mask,id))

def c12097 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12097 : Upper (D 6) (R 6) [10,33,65,144,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,288,4] 13 (by decide) (choices 1) [2,4] r12097 c12097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2206
  · exact u2207

def r12098 : Route 9 := (fun mask => (mask,id))

def c12098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12098 : Upper (D 6) (R 6) [10,33,65,144,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,288,64] 13 (by decide) (choices 1) [2,4] r12098 c12098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2208
  · exact u2209

def b12099 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 152 336 34 100 164 292), lower := (rows 11 35 69 152 336 34 64 128 256), losses := [] }

theorem u12099 : Upper (D 6) (R 6) [10,33,65,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12100 : Route 9 := (fun mask => (mask,id))

def c12100 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12100 : Upper (D 6) (R 6) [10,33,65,144,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,320,4] 13 (by decide) (choices 1) [2,4,32] r12100 c12100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2210
  · exact u2211
  · exact u2212

def b12101 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 200 52 34 340 404 276), lower := (rows 11 35 69 200 52 34 64 128 256), losses := [] }

theorem u12101 : Upper (D 6) (R 6) [10,33,65,192,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12102 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 69 200 52 36 338 402 274), lower := (rows 11 35 69 200 52 36 64 128 256), losses := [] }

theorem u12102 : Upper (D 6) (R 6) [10,33,65,192,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12103 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 200 52 48 326 390 262), lower := (rows 11 35 69 200 52 48 64 128 256), losses := [] }

theorem u12103 : Upper (D 6) (R 6) [10,33,65,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12103 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12104 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 35 69 200 52 288 86 150 278), lower := (rows 11 35 69 200 52 288 64 128 256), losses := [] }

theorem u12104 : Upper (D 6) (R 6) [10,33,65,192,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12104 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12105 : Route 9 := (fun mask => (mask,id))

def c12105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12105 : Upper (D 6) (R 6) [10,33,65,192,258,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,258,4] 13 (by decide) (choices 1) [4,16,32] r12105 c12105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2213
  · exact u2214
  · exact u2215

def b12106 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 69 200 274 48 100 164 292), lower := (rows 11 35 69 200 274 48 64 128 256), losses := [] }

theorem u12106 : Upper (D 6) (R 6) [10,33,65,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12106 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12107 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 200 276 34 116 180 308), lower := (rows 11 35 69 200 276 34 64 128 256), losses := [] }

theorem u12107 : Upper (D 6) (R 6) [10,33,65,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12108 : Route 9 := (fun mask => (mask,id))

def c12108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12108 : Upper (D 6) (R 6) [10,33,65,192,260,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,260,4] 13 (by decide) (choices 1) [2,16,32] r12108 c12108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2216
  · exact u2217
  · exact u2218

def b12109 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 35 69 200 276 48 102 166 294), lower := (rows 11 35 69 200 276 48 64 128 256), losses := [] }

theorem u12109 : Upper (D 6) (R 6) [10,33,65,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12109 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12110 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 200 304 34 84 148 276), lower := (rows 11 35 69 200 304 34 64 128 256), losses := [] }

theorem u12110 : Upper (D 6) (R 6) [10,33,65,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12111 : Route 9 := (fun mask => (mask,id))

def c12111 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12111 : Upper (D 6) (R 6) [10,33,65,192,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,65,192,288,4] 13 (by decide) (choices 1) [2,4,16] r12111 c12111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2219
  · exact u2220
  · exact u2221

def b12112 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 69 200 304 48 70 134 262), lower := (rows 11 35 69 200 304 48 64 128 256), losses := [] }

theorem u12112 : Upper (D 6) (R 6) [10,33,65,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12112 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12113 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 50, targets := 64 },{ cop := 4, region := 488, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 35 69 392 22 36 112 240 368), lower := (rows 11 35 69 392 22 36 64 128 256), losses := [] }

theorem u12113 : Upper (D 6) (R 6) [10,33,65,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12114 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 69 392 22 48 100 228 356), lower := (rows 11 35 69 392 22 48 64 128 256), losses := [] }

theorem u12114 : Upper (D 6) (R 6) [10,33,65,384,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12114 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12115 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 488, targets := 3 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 69 392 22 96 116 180 308), lower := (rows 11 35 69 392 22 96 64 128 256), losses := [] }

theorem u12115 : Upper (D 6) (R 6) [10,33,65,384,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12116 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 69 392 52 34 84 212 340), lower := (rows 11 35 69 392 52 34 64 128 256), losses := [] }

theorem u12116 : Upper (D 6) (R 6) [10,33,65,384,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12117 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 69 392 52 36 82 210 338), lower := (rows 11 35 69 392 52 36 64 128 256), losses := [] }

theorem u12117 : Upper (D 6) (R 6) [10,33,65,384,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12118 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 392 52 48 70 198 326), lower := (rows 11 35 69 392 52 48 64 128 256), losses := [] }

theorem u12118 : Upper (D 6) (R 6) [10,33,65,384,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12118 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12119 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 69 392 52 96 86 150 278), lower := (rows 11 35 69 392 52 96 64 128 256), losses := [] }

theorem u12119 : Upper (D 6) (R 6) [10,33,65,384,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12119
end Delivery.IrregularNine14.P06
