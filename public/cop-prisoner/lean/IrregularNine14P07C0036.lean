import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 25 274 160 65 192 448), lower := (rows 7 98 44 25 274 160 65 128 256), losses := [] }

theorem u2160 : Upper (D 7) (R 7) [6,96,40,17,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2161 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 25 274 160 192 193 321), lower := (rows 7 98 44 25 274 160 192 128 256), losses := [] }

theorem u2161 : Upper (D 7) (R 7) [6,96,40,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 25 336 160 65 130 386), lower := (rows 7 98 44 25 336 160 65 128 256), losses := [] }

theorem u2162 : Upper (D 7) (R 7) [6,96,40,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 25 336 160 66 129 385), lower := (rows 7 98 44 25 336 160 66 128 256), losses := [] }

theorem u2163 : Upper (D 7) (R 7) [6,96,40,17,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 25 336 160 192 131 259), lower := (rows 7 98 44 25 336 160 192 128 256), losses := [] }

theorem u2164 : Upper (D 7) (R 7) [6,96,40,17,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 88 274 160 65 129 385), lower := (rows 7 98 44 88 274 160 65 128 256), losses := [] }

theorem u2165 : Upper (D 7) (R 7) [6,96,40,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 88 274 160 192 129 257), lower := (rows 7 98 44 88 274 160 192 128 256), losses := [] }

theorem u2166 : Upper (D 7) (R 7) [6,96,40,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2167 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 137 146 288 65 208 336), lower := (rows 7 98 44 137 146 288 65 128 256), losses := [] }

theorem u2167 : Upper (D 7) (R 7) [6,96,40,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2167 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2168 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 44 137 146 288 80 193 321), lower := (rows 7 98 44 137 146 288 80 128 256), losses := [] }

theorem u2168 : Upper (D 7) (R 7) [6,96,40,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2168 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 137 208 288 65 146 274), lower := (rows 7 98 44 137 208 288 65 128 256), losses := [] }

theorem u2169 : Upper (D 7) (R 7) [6,96,40,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2169 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 137 208 288 66 145 273), lower := (rows 7 98 44 137 208 288 66 128 256), losses := [] }

theorem u2170 : Upper (D 7) (R 7) [6,96,40,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2170 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 44 137 208 288 80 131 259), lower := (rows 7 98 44 137 208 288 80 128 256), losses := [] }

theorem u2171 : Upper (D 7) (R 7) [6,96,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2171 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 152 274 33 65 192 448), lower := (rows 7 98 44 152 274 33 65 128 256), losses := [] }

theorem u2172 : Upper (D 7) (R 7) [6,96,40,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2173 : Route 9 := (fun mask => (mask,id))

def c2173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2173 : Upper (D 7) (R 7) [6,96,40,144,258,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,258,1,128] 13 (by decide) (choices 1) [1,64] r2173 c2173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u120
  · exact u121

def b2174 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 152 336 33 65 130 386), lower := (rows 7 98 44 152 336 33 65 128 256), losses := [] }

theorem u2174 : Upper (D 7) (R 7) [6,96,40,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 152 336 33 66 129 385), lower := (rows 7 98 44 152 336 33 66 128 256), losses := [] }

theorem u2175 : Upper (D 7) (R 7) [6,96,40,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2176 : Route 9 := (fun mask => (mask,id))

def c2176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2176 : Upper (D 7) (R 7) [6,96,40,144,320,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144,320,1,128] 13 (by decide) (choices 1) [1,2] r2176 c2176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u122
  · exact u123

def b2177 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 44 265 81 160 66 144 400), lower := (rows 7 98 44 265 81 160 66 128 256), losses := [] }

theorem u2177 : Upper (D 7) (R 7) [6,96,40,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 265 81 160 80 130 386), lower := (rows 7 98 44 265 81 160 80 128 256), losses := [] }

theorem u2178 : Upper (D 7) (R 7) [6,96,40,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2178 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 265 81 160 192 146 274), lower := (rows 7 98 44 265 81 160 192 128 256), losses := [] }

theorem u2179 : Upper (D 7) (R 7) [6,96,40,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 265 145 160 66 208 336), lower := (rows 7 98 44 265 145 160 66 128 256), losses := [] }

theorem u2180 : Upper (D 7) (R 7) [6,96,40,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 44 265 145 160 80 194 322), lower := (rows 7 98 44 265 145 160 80 128 256), losses := [] }

theorem u2181 : Upper (D 7) (R 7) [6,96,40,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2181 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 265 146 160 65 208 336), lower := (rows 7 98 44 265 146 160 65 128 256), losses := [] }

theorem u2182 : Upper (D 7) (R 7) [6,96,40,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 44 265 146 160 80 193 321), lower := (rows 7 98 44 265 146 160 80 128 256), losses := [] }

theorem u2183 : Upper (D 7) (R 7) [6,96,40,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2183 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 265 208 160 65 146 274), lower := (rows 7 98 44 265 208 160 65 128 256), losses := [] }

theorem u2184 : Upper (D 7) (R 7) [6,96,40,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 265 208 160 66 145 273), lower := (rows 7 98 44 265 208 160 66 128 256), losses := [] }

theorem u2185 : Upper (D 7) (R 7) [6,96,40,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 265 208 160 80 131 259), lower := (rows 7 98 44 265 208 160 80 128 256), losses := [] }

theorem u2186 : Upper (D 7) (R 7) [6,96,40,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2186 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 83, targets := 128 },{ cop := 4, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 7 98 44 266 81 160 65 144 400), lower := (rows 7 98 44 266 81 160 65 128 256), losses := [] }

theorem u2187 : Upper (D 7) (R 7) [6,96,40,258,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 266 81 160 80 129 385), lower := (rows 7 98 44 266 81 160 80 128 256), losses := [] }

theorem u2188 : Upper (D 7) (R 7) [6,96,40,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2188 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 44 266 81 160 192 145 273), lower := (rows 7 98 44 266 81 160 192 128 256), losses := [] }

theorem u2189 : Upper (D 7) (R 7) [6,96,40,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 266 145 160 65 208 336), lower := (rows 7 98 44 266 145 160 65 128 256), losses := [] }

theorem u2190 : Upper (D 7) (R 7) [6,96,40,258,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 44 266 145 160 80 193 321), lower := (rows 7 98 44 266 145 160 80 128 256), losses := [] }

theorem u2191 : Upper (D 7) (R 7) [6,96,40,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2191 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 280 146 33 65 192 448), lower := (rows 7 98 44 280 146 33 65 128 256), losses := [] }

theorem u2192 : Upper (D 7) (R 7) [6,96,40,272,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2193 : Route 9 := (fun mask => (mask,id))

def c2193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2193 : Upper (D 7) (R 7) [6,96,40,272,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272,130,1,128] 13 (by decide) (choices 1) [1,64] r2193 c2193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u124
  · exact u125

def b2194 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 280 208 33 65 130 386), lower := (rows 7 98 44 280 208 33 65 128 256), losses := [] }

theorem u2194 : Upper (D 7) (R 7) [6,96,40,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 280 208 33 66 129 385), lower := (rows 7 98 44 280 208 33 66 128 256), losses := [] }

theorem u2195 : Upper (D 7) (R 7) [6,96,40,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 44 280 208 33 192 131 259), lower := (rows 7 98 44 280 208 33 192 128 256), losses := [] }

theorem u2196 : Upper (D 7) (R 7) [6,96,40,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 328 145 160 65 146 274), lower := (rows 7 98 44 328 145 160 65 128 256), losses := [] }

theorem u2197 : Upper (D 7) (R 7) [6,96,40,320,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,1),(4,5),(4,6)], upper := (rows 7 98 44 328 145 160 66 145 273), lower := (rows 7 98 44 328 145 160 66 128 256), losses := [] }

theorem u2198 : Upper (D 7) (R 7) [6,96,40,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 44 328 145 160 80 131 259), lower := (rows 7 98 44 328 145 160 80 128 256), losses := [] }

theorem u2199 : Upper (D 7) (R 7) [6,96,40,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2199 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 328 146 160 65 145 273), lower := (rows 7 98 44 328 146 160 65 128 256), losses := [] }

theorem u2200 : Upper (D 7) (R 7) [6,96,40,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 98 44 328 146 160 80 129 257), lower := (rows 7 98 44 328 146 160 80 128 256), losses := [] }

theorem u2201 : Upper (D 7) (R 7) [6,96,40,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2201 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 119, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 44 392 81 33 66 144 400), lower := (rows 7 98 44 392 81 33 66 128 256), losses := [] }

theorem u2202 : Upper (D 7) (R 7) [6,96,40,384,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 119, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 44 392 81 33 80 130 386), lower := (rows 7 98 44 392 81 33 80 128 256), losses := [] }

theorem u2203 : Upper (D 7) (R 7) [6,96,40,384,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2203 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 392 81 33 192 146 274), lower := (rows 7 98 44 392 81 33 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 32 200 128 256), good := (rows 6 98 110 456 80 32 192 192 256) }] }

theorem u2204 : Upper (D 7) (R 7) [6,96,40,384,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 392 145 33 66 208 336), lower := (rows 7 98 44 392 145 33 66 128 256), losses := [] }

theorem u2205 : Upper (D 7) (R 7) [6,96,40,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 396, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 44 392 145 33 80 194 322), lower := (rows 7 98 44 392 145 33 80 128 256), losses := [] }

theorem u2206 : Upper (D 7) (R 7) [6,96,40,384,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2206 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 392 146 33 65 208 336), lower := (rows 7 98 44 392 146 33 65 128 256), losses := [] }

theorem u2207 : Upper (D 7) (R 7) [6,96,40,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2208 : Route 9 := (fun mask => (mask,id))

def c2208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2208 : Upper (D 7) (R 7) [6,96,40,384,130,1,16] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384,130,1,16] 13 (by decide) (choices 1) [1,64] r2208 c2208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u126
  · exact u127

def b2209 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 44 392 208 33 65 146 274), lower := (rows 7 98 44 392 208 33 65 128 256), losses := [] }

theorem u2209 : Upper (D 7) (R 7) [6,96,40,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 392 208 33 66 145 273), lower := (rows 7 98 44 392 208 33 66 128 256), losses := [] }

theorem u2210 : Upper (D 7) (R 7) [6,96,40,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 392 208 33 80 131 259), lower := (rows 7 98 44 392 208 33 80 128 256), losses := [] }

theorem u2211 : Upper (D 7) (R 7) [6,96,40,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2211 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(4,0),(4,7)], upper := (rows 7 98 133 25 274 40 192 224 352), lower := (rows 7 98 133 25 274 40 192 128 256), losses := [] }

theorem u2212 : Upper (D 7) (R 7) [6,96,129,17,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2212 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2213 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 25 274 96 192 168 296), lower := (rows 7 98 133 25 274 96 192 128 256), losses := [] }

theorem u2213 : Upper (D 7) (R 7) [6,96,129,17,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 7 98 133 25 304 160 66 200 328), lower := (rows 7 98 133 25 304 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 67 136 264), good := (rows 71 66 197 477 272 128 66 128 256) }] }

theorem u2214 : Upper (D 7) (R 7) [6,96,129,17,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 25 304 160 72 194 322), lower := (rows 7 98 133 25 304 160 72 128 256), losses := [] }

theorem u2215 : Upper (D 7) (R 7) [6,96,129,17,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2215 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 7 98 133 25 400 34 72 224 352), lower := (rows 7 98 133 25 400 34 72 128 256), losses := [] }

theorem u2216 : Upper (D 7) (R 7) [6,96,129,17,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2216 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 133 25 400 34 96 200 328), lower := (rows 7 98 133 25 400 34 96 128 256), losses := [] }

theorem u2217 : Upper (D 7) (R 7) [6,96,129,17,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 26 176 288 65 200 328), lower := (rows 7 98 133 26 176 288 65 128 256), losses := [] }

theorem u2218 : Upper (D 7) (R 7) [6,96,129,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2218 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7)], upper := (rows 7 98 133 26 176 288 72 193 321), lower := (rows 7 98 133 26 176 288 72 128 256), losses := [] }

theorem u2219 : Upper (D 7) (R 7) [6,96,129,18,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2219 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P07
