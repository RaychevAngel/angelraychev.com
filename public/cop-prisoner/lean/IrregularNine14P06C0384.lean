import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0117

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23040 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 134 76 56 81 36 323 387 259), lower := (rows 35 134 76 56 81 36 64 128 256), losses := [] }

theorem u23040 : Upper (D 6) (R 6) [34,132,72,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23041 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 56 81 288 71 135 263), lower := (rows 35 134 76 56 81 288 64 128 256), losses := [] }

theorem u23041 : Upper (D 6) (R 6) [34,132,72,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23041 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23042 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 76 56 273 33 70 198 326), lower := (rows 35 134 76 56 273 33 64 128 256), losses := [] }

theorem u23042 : Upper (D 6) (R 6) [34,132,72,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23043 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 56 273 34 69 197 325), lower := (rows 35 134 76 56 273 34 64 128 256), losses := [] }

theorem u23043 : Upper (D 6) (R 6) [34,132,72,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23044 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 76 56 273 36 67 195 323), lower := (rows 35 134 76 56 273 36 64 128 256), losses := [] }

theorem u23044 : Upper (D 6) (R 6) [34,132,72,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23045 : Route 9 := (fun mask => (mask,id))

def c23045 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23045 : Upper (D 6) (R 6) [34,132,72,48,257,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,257,64] 13 (by decide) (choices 1) [1,2,4] r23045 c23045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7061
  · exact u7062
  · exact u7063

def b23046 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 76 56 274 33 69 197 325), lower := (rows 35 134 76 56 274 33 64 128 256), losses := [] }

theorem u23046 : Upper (D 6) (R 6) [34,132,72,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23047 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 76 56 274 36 65 193 321), lower := (rows 35 134 76 56 274 36 64 128 256), losses := [] }

theorem u23047 : Upper (D 6) (R 6) [34,132,72,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23048 : Route 9 := (fun mask => (mask,id))

def c23048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23048 : Upper (D 6) (R 6) [34,132,72,48,258,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,258,64] 13 (by decide) (choices 1) [1,4] r23048 c23048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7064
  · exact u7065

def r23049 : Route 9 := (fun mask => (mask,id))

def c23049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23049 : Upper (D 6) (R 6) [34,132,72,48,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48,260,1] 13 (by decide) (choices 1) [1,2] r23049 c23049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7066
  · exact u7067

def b23050 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 56 276 34 65 193 321), lower := (rows 35 134 76 56 276 34 64 128 256), losses := [] }

theorem u23050 : Upper (D 6) (R 6) [34,132,72,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23051 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 134 76 56 276 96 67 131 259), lower := (rows 35 134 76 56 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 166 108 56 316 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 33 164 108 56 316 96 96 128 256) }] }

theorem u23051 : Upper (D 6) (R 6) [34,132,72,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23052 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 56 336 33 71 135 263), lower := (rows 35 134 76 56 336 33 64 128 256), losses := [] }

theorem u23052 : Upper (D 6) (R 6) [34,132,72,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23053 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 56 336 34 69 133 261), lower := (rows 35 134 76 56 336 34 64 128 256), losses := [] }

theorem u23053 : Upper (D 6) (R 6) [34,132,72,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23054 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 134 76 56 336 36 67 131 259), lower := (rows 35 134 76 56 336 36 64 128 256), losses := [] }

theorem u23054 : Upper (D 6) (R 6) [34,132,72,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23055 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 265 21 34 112 240 368), lower := (rows 35 134 76 265 21 34 64 128 256), losses := [] }

theorem u23055 : Upper (D 6) (R 6) [34,132,72,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23056 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 76 265 21 48 98 226 354), lower := (rows 35 134 76 265 21 48 64 128 256), losses := [] }

theorem u23056 : Upper (D 6) (R 6) [34,132,72,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23056 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23057 : Route 9 := (fun mask => (mask,id))

def c23057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23057 : Upper (D 6) (R 6) [34,132,72,257,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,5,64] 13 (by decide) (choices 1) [2,16,32] r23057 c23057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7068
  · exact u7069
  · exact u7070

def b23058 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 134 76 265 52 33 82 210 338), lower := (rows 35 134 76 265 52 33 64 128 256), losses := [] }

theorem u23058 : Upper (D 6) (R 6) [34,132,72,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23059 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 265 52 34 81 209 337), lower := (rows 35 134 76 265 52 34 64 128 256), losses := [] }

theorem u23059 : Upper (D 6) (R 6) [34,132,72,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23060 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 265 52 48 67 195 323), lower := (rows 35 134 76 265 52 48 64 128 256), losses := [] }

theorem u23060 : Upper (D 6) (R 6) [34,132,72,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23060 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23061 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 265 52 96 83 147 275), lower := (rows 35 134 76 265 52 96 64 128 256), losses := [] }

theorem u23061 : Upper (D 6) (R 6) [34,132,72,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23062 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 265 81 34 116 180 308), lower := (rows 35 134 76 265 81 34 64 128 256), losses := [] }

theorem u23062 : Upper (D 6) (R 6) [34,132,72,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23063 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 265 81 36 114 178 306), lower := (rows 35 134 76 265 81 36 64 128 256), losses := [] }

theorem u23063 : Upper (D 6) (R 6) [34,132,72,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23064 : Route 9 := (fun mask => (mask,id))

def c23064 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23064 : Upper (D 6) (R 6) [34,132,72,257,65,16] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,65,16] 13 (by decide) (choices 1) [2,4,32] r23064 c23064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7071
  · exact u7072
  · exact u7073

def r23065 : Route 9 := (fun mask => (mask,id))

def c23065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23065 : Upper (D 6) (R 6) [34,132,72,257,66,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257,66,1] 13 (by decide) (choices 1) [4,16,32] r23065 c23065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7074
  · exact u7075
  · exact u7076

def b23066 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 265 82 36 113 177 305), lower := (rows 35 134 76 265 82 36 64 128 256), losses := [] }

theorem u23066 : Upper (D 6) (R 6) [34,132,72,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23067 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 76 265 82 48 101 165 293), lower := (rows 35 134 76 265 82 48 64 128 256), losses := [] }

theorem u23067 : Upper (D 6) (R 6) [34,132,72,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23067 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23068 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 134 76 265 112 33 86 150 278), lower := (rows 35 134 76 265 112 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 64 128 256), good := (rows 33 148 124 297 112 33 64 128 256) }] }

theorem u23068 : Upper (D 6) (R 6) [34,132,72,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23069 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 265 112 34 85 149 277), lower := (rows 35 134 76 265 112 34 64 128 256), losses := [] }

theorem u23069 : Upper (D 6) (R 6) [34,132,72,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23070 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 76 265 112 36 83 147 275), lower := (rows 35 134 76 265 112 36 64 128 256), losses := [] }

theorem u23070 : Upper (D 6) (R 6) [34,132,72,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23071 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 265 112 48 71 135 263), lower := (rows 35 134 76 265 112 48 64 128 256), losses := [] }

theorem u23071 : Upper (D 6) (R 6) [34,132,72,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23071 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23072 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 76 266 21 33 112 240 368), lower := (rows 35 134 76 266 21 33 64 128 256), losses := [] }

theorem u23072 : Upper (D 6) (R 6) [34,132,72,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23073 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 76 266 21 48 97 225 353), lower := (rows 35 134 76 266 21 48 64 128 256), losses := [] }

theorem u23073 : Upper (D 6) (R 6) [34,132,72,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23073 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23074 : Route 9 := (fun mask => (mask,id))

def c23074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23074 : Upper (D 6) (R 6) [34,132,72,258,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258,5,64] 13 (by decide) (choices 1) [1,16,32] r23074 c23074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7077
  · exact u7078
  · exact u7079

def b23075 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 76 266 52 33 81 209 337), lower := (rows 35 134 76 266 52 33 64 128 256), losses := [] }

theorem u23075 : Upper (D 6) (R 6) [34,132,72,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23076 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 266 52 48 65 193 321), lower := (rows 35 134 76 266 52 48 64 128 256), losses := [] }

theorem u23076 : Upper (D 6) (R 6) [34,132,72,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23076 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23077 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 266 52 96 81 145 273), lower := (rows 35 134 76 266 52 96 64 128 256), losses := [] }

theorem u23077 : Upper (D 6) (R 6) [34,132,72,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23078 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 266 81 33 116 180 308), lower := (rows 35 134 76 266 81 33 64 128 256), losses := [{ target := 2, region := (rows 11 2 0 8 20 63 64 128 256), good := (rows 35 179 121 299 113 33 64 128 256) }] }

theorem u23078 : Upper (D 6) (R 6) [34,132,72,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23079 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 76 266 81 36 113 177 305), lower := (rows 35 134 76 266 81 36 64 128 256), losses := [] }

theorem u23079 : Upper (D 6) (R 6) [34,132,72,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23080 : PairBound 9 := { available := 37, camps := [], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 266 81 48 101 165 293), lower := (rows 35 134 76 266 81 48 64 128 256), losses := [{ target := 2, region := (rows 11 2 0 8 20 54 64 128 256), good := (rows 35 179 121 299 113 48 64 128 256) }] }

theorem u23080 : Upper (D 6) (R 6) [34,132,72,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23080 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23081 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 266 112 33 85 149 277), lower := (rows 35 134 76 266 112 33 64 128 256), losses := [{ target := 2, region := (rows 11 2 0 8 20 47 64 128 256), good := (rows 35 179 121 299 112 33 64 128 256) }] }

theorem u23081 : Upper (D 6) (R 6) [34,132,72,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23082 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 76 266 112 36 81 145 273), lower := (rows 35 134 76 266 112 36 64 128 256), losses := [] }

theorem u23082 : Upper (D 6) (R 6) [34,132,72,258,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23083 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 266 112 48 69 133 261), lower := (rows 35 134 76 266 112 48 64 128 256), losses := [] }

theorem u23083 : Upper (D 6) (R 6) [34,132,72,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23083 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23084 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 268 81 33 114 178 306), lower := (rows 35 134 76 268 81 33 64 128 256), losses := [] }

theorem u23084 : Upper (D 6) (R 6) [34,132,72,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23085 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 268 81 34 113 177 305), lower := (rows 35 134 76 268 81 34 64 128 256), losses := [] }

theorem u23085 : Upper (D 6) (R 6) [34,132,72,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23086 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 268 81 48 99 163 291), lower := (rows 35 134 76 268 81 48 64 128 256), losses := [] }

theorem u23086 : Upper (D 6) (R 6) [34,132,72,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23086 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23087 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 268 112 33 83 147 275), lower := (rows 35 134 76 268 112 33 64 128 256), losses := [] }

theorem u23087 : Upper (D 6) (R 6) [34,132,72,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23088 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 268 112 34 81 145 273), lower := (rows 35 134 76 268 112 34 64 128 256), losses := [] }

theorem u23088 : Upper (D 6) (R 6) [34,132,72,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23089 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 268 112 48 67 131 259), lower := (rows 35 134 76 268 112 48 64 128 256), losses := [] }

theorem u23089 : Upper (D 6) (R 6) [34,132,72,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23089 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23090 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 76 280 21 33 98 226 354), lower := (rows 35 134 76 280 21 33 64 128 256), losses := [] }

theorem u23090 : Upper (D 6) (R 6) [34,132,72,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23091 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 280 21 34 97 225 353), lower := (rows 35 134 76 280 21 34 64 128 256), losses := [] }

theorem u23091 : Upper (D 6) (R 6) [34,132,72,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23092 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(3,2)], upper := (rows 35 134 76 280 21 96 99 163 291), lower := (rows 35 134 76 280 21 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 119 67 131 259), good := (rows 483 483 104 312 505 96 96 128 256) },{ target := 6, region := (rows 1 18 4 24 16 32 0 129 257), good := (rows 419 134 12 282 415 32 0 128 256) }] }

theorem u23092 : Upper (D 6) (R 6) [34,132,72,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23093 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 76 280 52 33 67 195 323), lower := (rows 35 134 76 280 52 33 64 128 256), losses := [] }

theorem u23093 : Upper (D 6) (R 6) [34,132,72,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23094 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 280 52 34 65 193 321), lower := (rows 35 134 76 280 52 34 64 128 256), losses := [] }

theorem u23094 : Upper (D 6) (R 6) [34,132,72,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23095 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 280 52 96 67 131 259), lower := (rows 35 134 76 280 52 96 64 128 256), losses := [] }

theorem u23095 : Upper (D 6) (R 6) [34,132,72,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23096 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 280 81 33 102 166 294), lower := (rows 35 134 76 280 81 33 64 128 256), losses := [] }

theorem u23096 : Upper (D 6) (R 6) [34,132,72,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23097 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 280 81 34 101 165 293), lower := (rows 35 134 76 280 81 34 64 128 256), losses := [] }

theorem u23097 : Upper (D 6) (R 6) [34,132,72,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23098 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 280 81 36 99 163 291), lower := (rows 35 134 76 280 81 36 64 128 256), losses := [] }

theorem u23098 : Upper (D 6) (R 6) [34,132,72,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23099 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 280 112 33 71 135 263), lower := (rows 35 134 76 280 112 33 64 128 256), losses := [] }

theorem u23099 : Upper (D 6) (R 6) [34,132,72,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23099
end Delivery.IrregularNine14.P06
