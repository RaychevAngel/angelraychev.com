import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001
import IrregularNine14P06C0002

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 52 140 82 288 65 196 324), lower := (rows 11 35 52 140 82 288 65 128 256), losses := [] }

theorem u2160 : Upper (D 6) (R 6) [10,33,48,132,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2160 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 140 82 288 68 193 321), lower := (rows 11 35 52 140 82 288 68 128 256), losses := [] }

theorem u2161 : Upper (D 6) (R 6) [10,33,48,132,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2161 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 52 140 273 96 66 196 324), lower := (rows 11 35 52 140 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 115 67 144 272), good := (rows 106 98 444 140 508 96 98 128 256) }] }

theorem u2162 : Upper (D 6) (R 6) [10,33,48,132,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 140 273 96 68 194 322), lower := (rows 11 35 52 140 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 125 92 129 257), good := (rows 490 418 124 236 508 96 100 128 256) }] }

theorem u2163 : Upper (D 6) (R 6) [10,33,48,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 52 140 274 96 65 196 324), lower := (rows 11 35 52 140 274 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 115 67 144 272), good := (rows 105 97 444 140 508 96 97 128 256) }] }

theorem u2164 : Upper (D 6) (R 6) [10,33,48,132,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,5)], upper := (rows 11 35 52 140 274 96 68 193 321), lower := (rows 11 35 52 140 274 96 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 19 0 76 129 257), good := (rows 475 403 84 204 274 64 68 128 256) }] }

theorem u2165 : Upper (D 6) (R 6) [10,33,48,132,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2166 : Route 9 := (fun mask => (mask,id))

def c2166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2166 : Upper (D 6) (R 6) [10,33,48,132,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,260,64,1] 13 (by decide) (choices 1) [2,64] r2166 c2166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u116
  · exact u117

def r2167 : Route 9 := (fun mask => (mask,id))

def c2167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2167 : Upper (D 6) (R 6) [10,33,48,132,260,64,2] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,260,64,2] 13 (by decide) (choices 1) [1,64] r2167 c2167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u118
  · exact u119

def b2168 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 52 200 82 288 65 132 260), lower := (rows 11 35 52 200 82 288 65 128 256), losses := [] }

theorem u2168 : Upper (D 6) (R 6) [10,33,48,192,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2168 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 200 82 288 68 133 261), lower := (rows 11 35 52 200 82 288 68 128 256), losses := [] }

theorem u2169 : Upper (D 6) (R 6) [10,33,48,192,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2169 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 52 200 84 288 65 134 262), lower := (rows 11 35 52 200 84 288 65 128 256), losses := [] }

theorem u2170 : Upper (D 6) (R 6) [10,33,48,192,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2170 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 200 84 288 66 133 261), lower := (rows 11 35 52 200 84 288 66 128 256), losses := [] }

theorem u2171 : Upper (D 6) (R 6) [10,33,48,192,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2171 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 52 200 84 288 68 131 259), lower := (rows 11 35 52 200 84 288 68 128 256), losses := [] }

theorem u2172 : Upper (D 6) (R 6) [10,33,48,192,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2172 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 28 176 288 66 196 324), lower := (rows 11 35 69 28 176 288 66 128 256), losses := [] }

theorem u2173 : Upper (D 6) (R 6) [10,33,65,20,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2173 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 434, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 11 35 69 28 176 288 68 194 322), lower := (rows 11 35 69 28 176 288 68 128 256), losses := [] }

theorem u2174 : Upper (D 6) (R 6) [10,33,65,20,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2174 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 28 400 96 66 164 292), lower := (rows 11 35 69 28 400 96 66 128 256), losses := [] }

theorem u2175 : Upper (D 6) (R 6) [10,33,65,20,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 28 400 96 68 162 290), lower := (rows 11 35 69 28 400 96 68 128 256), losses := [] }

theorem u2176 : Upper (D 6) (R 6) [10,33,65,20,384,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 69 28 400 96 96 134 262), lower := (rows 11 35 69 28 400 96 96 128 256), losses := [] }

theorem u2177 : Upper (D 6) (R 6) [10,33,65,20,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 88 400 36 66 164 292), lower := (rows 11 35 69 88 400 36 66 128 256), losses := [] }

theorem u2178 : Upper (D 6) (R 6) [10,33,65,80,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 88 400 36 68 162 290), lower := (rows 11 35 69 88 400 36 68 128 256), losses := [] }

theorem u2179 : Upper (D 6) (R 6) [10,33,65,80,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 35 69 88 400 36 96 134 262), lower := (rows 11 35 69 88 400 36 96 128 256), losses := [] }

theorem u2180 : Upper (D 6) (R 6) [10,33,65,80,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 69 140 82 288 68 176 304), lower := (rows 11 35 69 140 82 288 68 128 256), losses := [] }

theorem u2181 : Upper (D 6) (R 6) [10,33,65,132,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2181 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 69 140 82 288 80 164 292), lower := (rows 11 35 69 140 82 288 80 128 256), losses := [] }

theorem u2182 : Upper (D 6) (R 6) [10,33,65,132,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2182 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 69 140 82 288 96 148 276), lower := (rows 11 35 69 140 82 288 96 128 256), losses := [] }

theorem u2183 : Upper (D 6) (R 6) [10,33,65,132,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2183 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 140 112 288 66 148 276), lower := (rows 11 35 69 140 112 288 66 128 256), losses := [] }

theorem u2184 : Upper (D 6) (R 6) [10,33,65,132,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2184 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 11 35 69 140 112 288 68 146 274), lower := (rows 11 35 69 140 112 288 68 128 256), losses := [] }

theorem u2185 : Upper (D 6) (R 6) [10,33,65,132,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2185 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 69 140 112 288 80 134 262), lower := (rows 11 35 69 140 112 288 80 128 256), losses := [] }

theorem u2186 : Upper (D 6) (R 6) [10,33,65,132,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2186 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 140 274 96 68 176 304), lower := (rows 11 35 69 140 274 96 68 128 256), losses := [] }

theorem u2187 : Upper (D 6) (R 6) [10,33,65,132,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 140 274 96 80 164 292), lower := (rows 11 35 69 140 274 96 80 128 256), losses := [] }

theorem u2188 : Upper (D 6) (R 6) [10,33,65,132,258,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2188 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 69 140 274 96 96 148 276), lower := (rows 11 35 69 140 274 96 96 128 256), losses := [] }

theorem u2189 : Upper (D 6) (R 6) [10,33,65,132,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 140 276 96 66 176 304), lower := (rows 11 35 69 140 276 96 66 128 256), losses := [] }

theorem u2190 : Upper (D 6) (R 6) [10,33,65,132,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 11 35 69 140 276 96 80 162 290), lower := (rows 11 35 69 140 276 96 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 125 92 131 259), good := (rows 490 418 508 252 380 96 112 128 256) }] }

theorem u2191 : Upper (D 6) (R 6) [10,33,65,132,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2191 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 69 140 276 96 96 146 274), lower := (rows 11 35 69 140 276 96 96 128 256), losses := [] }

theorem u2192 : Upper (D 6) (R 6) [10,33,65,132,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 140 304 96 66 148 276), lower := (rows 11 35 69 140 304 96 66 128 256), losses := [] }

theorem u2193 : Upper (D 6) (R 6) [10,33,65,132,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 140 304 96 68 146 274), lower := (rows 11 35 69 140 304 96 68 128 256), losses := [] }

theorem u2194 : Upper (D 6) (R 6) [10,33,65,132,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 69 140 304 96 80 134 262), lower := (rows 11 35 69 140 304 96 80 128 256), losses := [] }

theorem u2195 : Upper (D 6) (R 6) [10,33,65,132,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2195 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 140 336 48 66 164 292), lower := (rows 11 35 69 140 336 48 66 128 256), losses := [] }

theorem u2196 : Upper (D 6) (R 6) [10,33,65,132,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2196 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 11 35 69 140 336 48 68 162 290), lower := (rows 11 35 69 140 336 48 68 128 256), losses := [] }

theorem u2197 : Upper (D 6) (R 6) [10,33,65,132,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2197 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 69 140 336 48 96 134 262), lower := (rows 11 35 69 140 336 48 96 128 256), losses := [] }

theorem u2198 : Upper (D 6) (R 6) [10,33,65,132,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2198 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 152 52 288 66 196 324), lower := (rows 11 35 69 152 52 288 66 128 256), losses := [] }

theorem u2199 : Upper (D 6) (R 6) [10,33,65,144,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2199 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 69 152 52 288 68 194 322), lower := (rows 11 35 69 152 52 288 68 128 256), losses := [] }

theorem u2200 : Upper (D 6) (R 6) [10,33,65,144,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2200 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 152 276 36 66 224 352), lower := (rows 11 35 69 152 276 36 66 128 256), losses := [] }

theorem u2201 : Upper (D 6) (R 6) [10,33,65,144,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 11 35 69 152 276 36 96 194 322), lower := (rows 11 35 69 152 276 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 52 126 131 259), good := (rows 458 482 508 248 380 124 96 128 256) }] }

theorem u2202 : Upper (D 6) (R 6) [10,33,65,144,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 152 276 96 66 164 292), lower := (rows 11 35 69 152 276 96 66 128 256), losses := [] }

theorem u2203 : Upper (D 6) (R 6) [10,33,65,144,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 11 35 69 152 276 96 68 162 290), lower := (rows 11 35 69 152 276 96 68 128 256), losses := [] }

theorem u2204 : Upper (D 6) (R 6) [10,33,65,144,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 69 152 276 96 96 134 262), lower := (rows 11 35 69 152 276 96 96 128 256), losses := [] }

theorem u2205 : Upper (D 6) (R 6) [10,33,65,144,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 152 304 36 66 196 324), lower := (rows 11 35 69 152 304 36 66 128 256), losses := [] }

theorem u2206 : Upper (D 6) (R 6) [10,33,65,144,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 11 35 69 152 304 36 68 194 322), lower := (rows 11 35 69 152 304 36 68 128 256), losses := [] }

theorem u2207 : Upper (D 6) (R 6) [10,33,65,144,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 152 304 96 66 132 260), lower := (rows 11 35 69 152 304 96 66 128 256), losses := [] }

theorem u2208 : Upper (D 6) (R 6) [10,33,65,144,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 11 35 69 152 304 96 68 134 262), lower := (rows 11 35 69 152 304 96 68 128 256), losses := [] }

theorem u2209 : Upper (D 6) (R 6) [10,33,65,144,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 152 336 36 66 164 292), lower := (rows 11 35 69 152 336 36 66 128 256), losses := [] }

theorem u2210 : Upper (D 6) (R 6) [10,33,65,144,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 11 35 69 152 336 36 68 162 290), lower := (rows 11 35 69 152 336 36 68 128 256), losses := [] }

theorem u2211 : Upper (D 6) (R 6) [10,33,65,144,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2212 : Route 9 := (fun mask => (mask,id))

def c2212 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2212 : Upper (D 6) (R 6) [10,33,65,144,320,4,32] 13 := by
  apply FastRouting.sound _ _ [10,33,65,144,320,4,32] 13 (by decide) (choices 1) [2,4] r2212 c2212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u120
  · exact u121

def b2213 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 200 274 36 68 176 304), lower := (rows 11 35 69 200 274 36 68 128 256), losses := [] }

theorem u2213 : Upper (D 6) (R 6) [10,33,65,192,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 69 200 274 36 80 164 292), lower := (rows 11 35 69 200 274 36 80 128 256), losses := [] }

theorem u2214 : Upper (D 6) (R 6) [10,33,65,192,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2214 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 35 69 200 274 36 96 148 276), lower := (rows 11 35 69 200 274 36 96 128 256), losses := [] }

theorem u2215 : Upper (D 6) (R 6) [10,33,65,192,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 200 276 36 66 176 304), lower := (rows 11 35 69 200 276 36 66 128 256), losses := [] }

theorem u2216 : Upper (D 6) (R 6) [10,33,65,192,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 35 69 200 276 36 80 162 290), lower := (rows 11 35 69 200 276 36 80 128 256), losses := [] }

theorem u2217 : Upper (D 6) (R 6) [10,33,65,192,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2217 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 306, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 35 69 200 276 36 96 146 274), lower := (rows 11 35 69 200 276 36 96 128 256), losses := [] }

theorem u2218 : Upper (D 6) (R 6) [10,33,65,192,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 69 200 304 36 66 148 276), lower := (rows 11 35 69 200 304 36 66 128 256), losses := [] }

theorem u2219 : Upper (D 6) (R 6) [10,33,65,192,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P06
