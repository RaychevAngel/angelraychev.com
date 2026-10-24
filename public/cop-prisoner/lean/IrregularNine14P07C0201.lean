import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0018

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12060 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,6),(2,1),(3,7),(4,1)], upper := (rows 7 35 28 74 400 160 97 225 353), lower := (rows 7 35 28 74 400 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 187 67 131 259), good := (rows 501 497 60 508 432 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 176 0 128 256), good := (rows 7 35 63 10 432 160 0 160 256) }] }

theorem u12060 : Upper (D 7) (R 7) [6,33,24,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12061 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 104 208 33 450 386 386), lower := (rows 7 35 28 104 208 33 64 128 256), losses := [] }

theorem u12061 : Upper (D 7) (R 7) [6,33,24,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12062 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 104 208 34 449 385 385), lower := (rows 7 35 28 104 208 34 64 128 256), losses := [] }

theorem u12062 : Upper (D 7) (R 7) [6,33,24,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12063 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 28 104 208 160 323 387 259), lower := (rows 7 35 28 104 208 160 64 128 256), losses := [] }

theorem u12063 : Upper (D 7) (R 7) [6,33,24,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12064 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 28 104 208 288 195 131 387), lower := (rows 7 35 28 104 208 288 64 128 256), losses := [] }

theorem u12064 : Upper (D 7) (R 7) [6,33,24,96,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12064 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12065 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 104 273 34 192 192 448), lower := (rows 7 35 28 104 273 34 64 128 256), losses := [] }

theorem u12065 : Upper (D 7) (R 7) [6,33,24,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12066 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 35 28 104 273 96 194 130 386), lower := (rows 7 35 28 104 273 96 64 128 256), losses := [] }

theorem u12066 : Upper (D 7) (R 7) [6,33,24,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12067 : Route 9 := (fun mask => (mask,id))

def c12067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12067 : Upper (D 7) (R 7) [6,33,24,96,257,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,257,128] 13 (by decide) (choices 1) [2,128] r12067 c12067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1090
  · exact u1091

def b12068 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 104 274 33 192 192 448), lower := (rows 7 35 28 104 274 33 64 128 256), losses := [] }

theorem u12068 : Upper (D 7) (R 7) [6,33,24,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12069 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 35 28 104 274 96 193 129 385), lower := (rows 7 35 28 104 274 96 64 128 256), losses := [] }

theorem u12069 : Upper (D 7) (R 7) [6,33,24,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12070 : Route 9 := (fun mask => (mask,id))

def c12070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12070 : Upper (D 7) (R 7) [6,33,24,96,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,258,128] 13 (by decide) (choices 1) [1,128] r12070 c12070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1092
  · exact u1093

def b12071 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 104 336 33 194 130 386), lower := (rows 7 35 28 104 336 33 64 128 256), losses := [] }

theorem u12071 : Upper (D 7) (R 7) [6,33,24,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12072 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 104 336 34 193 129 385), lower := (rows 7 35 28 104 336 34 64 128 256), losses := [] }

theorem u12072 : Upper (D 7) (R 7) [6,33,24,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12073 : Route 9 := (fun mask => (mask,id))

def c12073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12073 : Upper (D 7) (R 7) [6,33,24,96,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,320,128] 13 (by decide) (choices 1) [1,2,128] r12073 c12073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096

def b12074 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 104 400 33 194 194 450), lower := (rows 7 35 28 104 400 33 64 128 256), losses := [] }

theorem u12074 : Upper (D 7) (R 7) [6,33,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12075 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 104 400 34 193 193 449), lower := (rows 7 35 28 104 400 34 64 128 256), losses := [] }

theorem u12075 : Upper (D 7) (R 7) [6,33,24,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12076 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 35 28 104 400 96 195 131 387), lower := (rows 7 35 28 104 400 96 64 128 256), losses := [] }

theorem u12076 : Upper (D 7) (R 7) [6,33,24,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12077 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,6),(1,6),(3,7),(4,5)], upper := (rows 7 35 28 104 400 160 67 195 323), lower := (rows 7 35 28 104 400 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 176 0 128 256), good := (rows 7 35 63 40 432 160 0 160 256) }] }

theorem u12077 : Upper (D 7) (R 7) [6,33,24,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12078 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 200 273 34 224 224 480), lower := (rows 7 35 28 200 273 34 64 128 256), losses := [] }

theorem u12078 : Upper (D 7) (R 7) [6,33,24,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12079 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 232, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(2,0),(3,0),(4,6)], upper := (rows 7 35 28 200 273 96 226 162 418), lower := (rows 7 35 28 200 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 123 67 131 259), good := (rows 494 490 60 232 508 96 96 128 256) },{ target := 7, region := (rows 5 6 4 8 16 104 64 0 256), good := (rows 7 35 63 104 273 96 96 0 256) }] }

theorem u12079 : Upper (D 7) (R 7) [6,33,24,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12080 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 200 274 33 224 224 480), lower := (rows 7 35 28 200 274 33 64 128 256), losses := [] }

theorem u12080 : Upper (D 7) (R 7) [6,33,24,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12081 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(2,1),(3,1),(4,6)], upper := (rows 7 35 28 200 274 96 225 161 417), lower := (rows 7 35 28 200 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 27 16 123 67 131 259), good := (rows 493 489 60 232 508 96 96 128 256) },{ target := 7, region := (rows 5 6 4 8 16 104 64 0 256), good := (rows 7 35 63 104 274 96 96 0 256) }] }

theorem u12081 : Upper (D 7) (R 7) [6,33,24,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12082 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 200 304 33 194 194 450), lower := (rows 7 35 28 200 304 33 64 128 256), losses := [] }

theorem u12082 : Upper (D 7) (R 7) [6,33,24,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12083 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 200 304 34 193 193 449), lower := (rows 7 35 28 200 304 34 64 128 256), losses := [] }

theorem u12083 : Upper (D 7) (R 7) [6,33,24,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12084 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 1, region := 400, targets := 64 }], pairs := [(0,7),(1,7),(3,5),(4,6)], upper := (rows 7 35 28 200 304 96 195 131 387), lower := (rows 7 35 28 200 304 96 64 128 256), losses := [{ target := 7, region := (rows 5 6 4 8 16 104 64 0 256), good := (rows 7 35 63 104 304 96 96 0 256) }] }

theorem u12084 : Upper (D 7) (R 7) [6,33,24,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12085 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 28 200 336 33 226 162 418), lower := (rows 7 35 28 200 336 33 64 128 256), losses := [] }

theorem u12085 : Upper (D 7) (R 7) [6,33,24,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12086 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 28 200 336 34 225 161 417), lower := (rows 7 35 28 200 336 34 64 128 256), losses := [] }

theorem u12086 : Upper (D 7) (R 7) [6,33,24,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12087 : Route 9 := (fun mask => (mask,id))

def c12087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12087 : Upper (D 7) (R 7) [6,33,24,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192,320,128] 13 (by decide) (choices 1) [1,2,32] r12087 c12087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099

def b12088 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 26 208 40 480 416 416), lower := (rows 7 35 69 26 208 40 64 128 256), losses := [] }

theorem u12088 : Upper (D 7) (R 7) [6,33,65,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12088 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12089 : Route 9 := (fun mask => (mask,id))

def c12089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u12089 : Upper (D 7) (R 7) [6,33,65,18,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,192,128] 13 (by decide) (choices 1) [8,32,256] r12089 c12089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1100
  · exact u1101
  · exact u1102

def b12090 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 496, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 26 208 288 232 168 424), lower := (rows 7 35 69 26 208 288 64 128 256), losses := [] }

theorem u12090 : Upper (D 7) (R 7) [6,33,65,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12090 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12091 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 26 336 40 224 160 416), lower := (rows 7 35 69 26 336 40 64 128 256), losses := [] }

theorem u12091 : Upper (D 7) (R 7) [6,33,65,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12091 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12092 : Route 9 := (fun mask => (mask,id))

def c12092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12092 : Upper (D 7) (R 7) [6,33,65,18,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,320,128] 13 (by decide) (choices 1) [8,32,128] r12092 c12092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1103
  · exact u1104
  · exact u1105

def b12093 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 26 400 40 224 224 480), lower := (rows 7 35 69 26 400 40 64 128 256), losses := [] }

theorem u12093 : Upper (D 7) (R 7) [6,33,65,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12093 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12094 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 26 400 96 232 168 424), lower := (rows 7 35 69 26 400 96 64 128 256), losses := [] }

theorem u12094 : Upper (D 7) (R 7) [6,33,65,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12095 : Route 9 := (fun mask => (mask,id))

def c12095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12095 : Upper (D 7) (R 7) [6,33,65,18,384,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,384,128] 13 (by decide) (choices 1) [8,32] r12095 c12095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1106
  · exact u1107

def b12096 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 56 146 40 448 448 448), lower := (rows 7 35 69 56 146 40 64 128 256), losses := [] }

theorem u12096 : Upper (D 7) (R 7) [6,33,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12096 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12097 : PairBound 9 := { available := 392, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 146 96 456 392 392), lower := (rows 7 35 69 56 146 96 64 128 256), losses := [] }

theorem u12097 : Upper (D 7) (R 7) [6,33,65,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12098 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 146 160 328 456 328), lower := (rows 7 35 69 56 146 160 64 128 256), losses := [] }

theorem u12098 : Upper (D 7) (R 7) [6,33,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12099 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 56 146 288 200 200 456), lower := (rows 7 35 69 56 146 288 64 128 256), losses := [] }

theorem u12099 : Upper (D 7) (R 7) [6,33,65,48,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12099 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12100 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 56 208 34 456 392 392), lower := (rows 7 35 69 56 208 34 64 128 256), losses := [] }

theorem u12100 : Upper (D 7) (R 7) [6,33,65,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12101 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 56 208 40 450 386 386), lower := (rows 7 35 69 56 208 40 64 128 256), losses := [] }

theorem u12101 : Upper (D 7) (R 7) [6,33,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12101 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12102 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 208 160 330 394 266), lower := (rows 7 35 69 56 208 160 64 128 256), losses := [] }

theorem u12102 : Upper (D 7) (R 7) [6,33,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12103 : Route 9 := (fun mask => (mask,id))

def c12103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12103 : Upper (D 7) (R 7) [6,33,65,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192,256] 13 (by decide) (choices 1) [2,8,128] r12103 c12103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1108
  · exact u1109
  · exact u1110

def b12104 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 56 274 40 192 192 448), lower := (rows 7 35 69 56 274 40 64 128 256), losses := [] }

theorem u12104 : Upper (D 7) (R 7) [6,33,65,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12104 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12105 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 274 96 200 136 392), lower := (rows 7 35 69 56 274 96 64 128 256), losses := [] }

theorem u12105 : Upper (D 7) (R 7) [6,33,65,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12106 : Route 9 := (fun mask => (mask,id))

def c12106 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12106 : Upper (D 7) (R 7) [6,33,65,48,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,258,128] 13 (by decide) (choices 1) [8,128] r12106 c12106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1111
  · exact u1112

def b12107 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 56 336 34 200 136 392), lower := (rows 7 35 69 56 336 34 64 128 256), losses := [] }

theorem u12107 : Upper (D 7) (R 7) [6,33,65,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12108 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 56 336 40 194 130 386), lower := (rows 7 35 69 56 336 40 64 128 256), losses := [] }

theorem u12108 : Upper (D 7) (R 7) [6,33,65,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12108 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12109 : Route 9 := (fun mask => (mask,id))

def c12109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12109 : Upper (D 7) (R 7) [6,33,65,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,320,128] 13 (by decide) (choices 1) [2,8,128] r12109 c12109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1113
  · exact u1114
  · exact u1115

def b12110 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 56 400 34 200 200 456), lower := (rows 7 35 69 56 400 34 64 128 256), losses := [] }

theorem u12110 : Upper (D 7) (R 7) [6,33,65,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12111 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 69 56 400 40 194 194 450), lower := (rows 7 35 69 56 400 40 64 128 256), losses := [] }

theorem u12111 : Upper (D 7) (R 7) [6,33,65,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12111 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12112 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 400 96 202 138 394), lower := (rows 7 35 69 56 400 96 64 128 256), losses := [] }

theorem u12112 : Upper (D 7) (R 7) [6,33,65,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12113 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 56 400 160 74 202 330), lower := (rows 7 35 69 56 400 160 64 128 256), losses := [] }

theorem u12113 : Upper (D 7) (R 7) [6,33,65,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12114 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 146 40 480 416 416), lower := (rows 7 35 69 88 146 40 64 128 256), losses := [] }

theorem u12114 : Upper (D 7) (R 7) [6,33,65,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12114 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12115 : Route 9 := (fun mask => (mask,id))

def c12115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u12115 : Upper (D 7) (R 7) [6,33,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,130,128] 13 (by decide) (choices 1) [8,32,256] r12115 c12115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1116
  · exact u1117
  · exact u1118

def b12116 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 88 146 288 232 168 424), lower := (rows 7 35 69 88 146 288 64 128 256), losses := [] }

theorem u12116 : Upper (D 7) (R 7) [6,33,65,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12116 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12117 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 88 176 34 456 392 392), lower := (rows 7 35 69 88 176 34 64 128 256), losses := [] }

theorem u12117 : Upper (D 7) (R 7) [6,33,65,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12118 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 176 40 450 386 386), lower := (rows 7 35 69 88 176 40 64 128 256), losses := [] }

theorem u12118 : Upper (D 7) (R 7) [6,33,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12118 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12119 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 69 88 176 160 330 394 266), lower := (rows 7 35 69 88 176 160 64 128 256), losses := [] }

theorem u12119 : Upper (D 7) (R 7) [6,33,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12119
end Delivery.IrregularNine14.P07
