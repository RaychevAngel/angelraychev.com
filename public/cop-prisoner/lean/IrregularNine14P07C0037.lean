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

def b2220 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 98 133 26 273 40 192 224 352), lower := (rows 7 98 133 26 273 40 192 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 40 239 170 298), good := (rows 469 480 213 504 341 488 192 192 256) }] }

theorem u2220 : Upper (D 7) (R 7) [6,96,129,18,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2220 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 273 96 192 168 296), lower := (rows 7 98 133 26 273 96 192 128 256), losses := [] }

theorem u2221 : Upper (D 7) (R 7) [6,96,129,18,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 26 280 33 192 224 352), lower := (rows 7 98 133 26 280 33 192 128 256), losses := [] }

theorem u2222 : Upper (D 7) (R 7) [6,96,129,18,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 26 280 96 192 161 289), lower := (rows 7 98 133 26 280 96 192 128 256), losses := [] }

theorem u2223 : Upper (D 7) (R 7) [6,96,129,18,264,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 26 304 160 65 200 328), lower := (rows 7 98 133 26 304 160 65 128 256), losses := [] }

theorem u2224 : Upper (D 7) (R 7) [6,96,129,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2225 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 26 304 160 72 193 321), lower := (rows 7 98 133 26 304 160 72 128 256), losses := [] }

theorem u2225 : Upper (D 7) (R 7) [6,96,129,18,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2225 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 26 400 33 72 224 352), lower := (rows 7 98 133 26 400 33 72 128 256), losses := [] }

theorem u2226 : Upper (D 7) (R 7) [6,96,129,18,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2226 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 133 26 400 33 96 200 328), lower := (rows 7 98 133 26 400 33 96 128 256), losses := [] }

theorem u2227 : Upper (D 7) (R 7) [6,96,129,18,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 26 400 40 96 193 321), lower := (rows 7 98 133 26 400 40 96 128 256), losses := [] }

theorem u2228 : Upper (D 7) (R 7) [6,96,129,18,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2228 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 82, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 41 88 288 66 144 400), lower := (rows 7 98 133 41 88 288 66 128 256), losses := [] }

theorem u2229 : Upper (D 7) (R 7) [6,96,129,33,72,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2229 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 41 88 288 80 130 386), lower := (rows 7 98 133 41 88 288 80 128 256), losses := [] }

theorem u2230 : Upper (D 7) (R 7) [6,96,129,33,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2230 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 41 88 288 192 146 274), lower := (rows 7 98 133 41 88 288 192 128 256), losses := [] }

theorem u2231 : Upper (D 7) (R 7) [6,96,129,33,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2231 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 41 208 288 66 152 280), lower := (rows 7 98 133 41 208 288 66 128 256), losses := [] }

theorem u2232 : Upper (D 7) (R 7) [6,96,129,33,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2232 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 149, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 41 208 288 72 146 274), lower := (rows 7 98 133 41 208 288 72 128 256), losses := [] }

theorem u2233 : Upper (D 7) (R 7) [6,96,129,33,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2233 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2234 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 41 208 288 80 138 266), lower := (rows 7 98 133 41 208 288 80 128 256), losses := [] }

theorem u2234 : Upper (D 7) (R 7) [6,96,129,33,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2234 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 208 288 65 138 266), lower := (rows 7 98 133 56 208 288 65 128 256), losses := [] }

theorem u2235 : Upper (D 7) (R 7) [6,96,129,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2235 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 56 208 288 66 137 265), lower := (rows 7 98 133 56 208 288 66 128 256), losses := [{ target := 0, region := (rows 0 298 4 8 20 288 363 128 256), good := (rows 86 98 212 122 208 354 66 128 354) }] }

theorem u2236 : Upper (D 7) (R 7) [6,96,129,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2236 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 56 208 288 72 131 259), lower := (rows 7 98 133 56 208 288 72 128 256), losses := [] }

theorem u2237 : Upper (D 7) (R 7) [6,96,129,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2237 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2238 : Route 9 := (fun mask => (mask,id))

def c2238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2238 : Upper (D 7) (R 7) [6,96,129,48,257,128,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,257,128,2] 13 (by decide) (choices 1) [8,64] r2238 c2238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u128
  · exact u129

def b2239 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 273 160 72 194 322), lower := (rows 7 98 133 56 273 160 72 128 256), losses := [] }

theorem u2239 : Upper (D 7) (R 7) [6,96,129,48,257,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2239 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 274 33 72 192 448), lower := (rows 7 98 133 56 274 33 72 128 256), losses := [] }

theorem u2240 : Upper (D 7) (R 7) [6,96,129,48,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2240 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 56 274 33 192 200 328), lower := (rows 7 98 133 56 274 33 192 128 256), losses := [] }

theorem u2241 : Upper (D 7) (R 7) [6,96,129,48,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 56 274 160 65 200 328), lower := (rows 7 98 133 56 274 160 65 128 256), losses := [] }

theorem u2242 : Upper (D 7) (R 7) [6,96,129,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 274 160 72 193 321), lower := (rows 7 98 133 56 274 160 72 128 256), losses := [] }

theorem u2243 : Upper (D 7) (R 7) [6,96,129,48,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2243 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 280 160 65 194 322), lower := (rows 7 98 133 56 280 160 65 128 256), losses := [] }

theorem u2244 : Upper (D 7) (R 7) [6,96,129,48,264,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 66, targets := 129 }], pairs := [(0,5),(1,0),(1,7),(2,5)], upper := (rows 7 98 133 56 280 160 66 193 321), lower := (rows 7 98 133 56 280 160 66 128 256), losses := [] }

theorem u2245 : Upper (D 7) (R 7) [6,96,129,48,264,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 408, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 56 336 33 66 136 392), lower := (rows 7 98 133 56 336 33 66 128 256), losses := [] }

theorem u2246 : Upper (D 7) (R 7) [6,96,129,48,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 336 33 72 130 386), lower := (rows 7 98 133 56 336 33 72 128 256), losses := [] }

theorem u2247 : Upper (D 7) (R 7) [6,96,129,48,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2247 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 56 336 33 192 138 266), lower := (rows 7 98 133 56 336 33 192 128 256), losses := [] }

theorem u2248 : Upper (D 7) (R 7) [6,96,129,48,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 280, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 98 133 56 336 160 65 138 266), lower := (rows 7 98 133 56 336 160 65 128 256), losses := [] }

theorem u2249 : Upper (D 7) (R 7) [6,96,129,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2250 : Route 9 := (fun mask => (mask,id))

def c2250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2250 : Upper (D 7) (R 7) [6,96,129,48,320,128,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320,128,2] 13 (by decide) (choices 1) [1,8] r2250 c2250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b2251 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 336 160 72 131 259), lower := (rows 7 98 133 56 336 160 72 128 256), losses := [] }

theorem u2251 : Upper (D 7) (R 7) [6,96,129,48,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2251 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 56 400 34 65 200 328), lower := (rows 7 98 133 56 400 34 65 128 256), losses := [] }

theorem u2252 : Upper (D 7) (R 7) [6,96,129,48,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 56 400 34 72 193 321), lower := (rows 7 98 133 56 400 34 72 128 256), losses := [] }

theorem u2253 : Upper (D 7) (R 7) [6,96,129,48,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2253 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 152 273 34 72 224 352), lower := (rows 7 98 133 152 273 34 72 128 256), losses := [] }

theorem u2254 : Upper (D 7) (R 7) [6,96,129,144,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2254 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 133 152 273 34 96 200 328), lower := (rows 7 98 133 152 273 34 96 128 256), losses := [] }

theorem u2255 : Upper (D 7) (R 7) [6,96,129,144,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 152 274 33 72 224 352), lower := (rows 7 98 133 152 274 33 72 128 256), losses := [] }

theorem u2256 : Upper (D 7) (R 7) [6,96,129,144,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2256 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 133 152 274 33 96 200 328), lower := (rows 7 98 133 152 274 33 96 128 256), losses := [] }

theorem u2257 : Upper (D 7) (R 7) [6,96,129,144,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 133 152 274 40 96 193 321), lower := (rows 7 98 133 152 274 40 96 128 256), losses := [] }

theorem u2258 : Upper (D 7) (R 7) [6,96,129,144,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2258 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 408, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 152 280 33 66 224 352), lower := (rows 7 98 133 152 280 33 66 128 256), losses := [] }

theorem u2259 : Upper (D 7) (R 7) [6,96,129,144,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 133 152 280 34 96 193 321), lower := (rows 7 98 133 152 280 34 96 128 256), losses := [] }

theorem u2260 : Upper (D 7) (R 7) [6,96,129,144,264,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 408, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 152 304 33 66 200 328), lower := (rows 7 98 133 152 304 33 66 128 256), losses := [] }

theorem u2261 : Upper (D 7) (R 7) [6,96,129,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 152 304 33 72 194 322), lower := (rows 7 98 133 152 304 33 72 128 256), losses := [] }

theorem u2262 : Upper (D 7) (R 7) [6,96,129,144,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2262 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 133 152 304 34 65 200 328), lower := (rows 7 98 133 152 304 34 65 128 256), losses := [] }

theorem u2263 : Upper (D 7) (R 7) [6,96,129,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 152 304 34 72 193 321), lower := (rows 7 98 133 152 304 34 72 128 256), losses := [] }

theorem u2264 : Upper (D 7) (R 7) [6,96,129,144,288,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2264 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 152 304 40 65 194 322), lower := (rows 7 98 133 152 304 40 65 128 256), losses := [] }

theorem u2265 : Upper (D 7) (R 7) [6,96,129,144,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2265 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 152 304 40 66 193 321), lower := (rows 7 98 133 152 304 40 66 128 256), losses := [] }

theorem u2266 : Upper (D 7) (R 7) [6,96,129,144,288,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2266 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 168 274 48 65 200 328), lower := (rows 7 98 133 168 274 48 65 128 256), losses := [] }

theorem u2267 : Upper (D 7) (R 7) [6,96,129,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2267 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 168 274 48 72 193 321), lower := (rows 7 98 133 168 274 48 72 128 256), losses := [] }

theorem u2268 : Upper (D 7) (R 7) [6,96,129,160,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2268 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 168 280 48 65 194 322), lower := (rows 7 98 133 168 280 48 65 128 256), losses := [] }

theorem u2269 : Upper (D 7) (R 7) [6,96,129,160,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2269 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 168 280 48 66 193 321), lower := (rows 7 98 133 168 280 48 66 128 256), losses := [] }

theorem u2270 : Upper (D 7) (R 7) [6,96,129,160,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2270 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 25 274 33 96 192 448), lower := (rows 7 98 140 25 274 33 96 128 256), losses := [] }

theorem u2271 : Upper (D 7) (R 7) [6,96,136,17,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 466, targets := 1 },{ cop := 1, region := 272, targets := 128 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(4,0),(4,7)], upper := (rows 7 98 140 25 274 33 192 224 352), lower := (rows 7 98 140 25 274 33 192 128 256), losses := [] }

theorem u2272 : Upper (D 7) (R 7) [6,96,136,17,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 25 274 96 192 161 289), lower := (rows 7 98 140 25 274 96 192 128 256), losses := [] }

theorem u2273 : Upper (D 7) (R 7) [6,96,136,17,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(2,5),(4,0),(4,7)], upper := (rows 7 98 140 25 304 160 65 194 322), lower := (rows 7 98 140 25 304 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 73 131 259), good := (rows 455 450 204 477 272 128 449 128 256) }] }

theorem u2274 : Upper (D 7) (R 7) [6,96,136,17,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2275 : Route 9 := (fun mask => (mask,id))

def c2275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2275 : Upper (D 7) (R 7) [6,96,136,17,288,128,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,288,128,2] 13 (by decide) (choices 1) [1,64] r2275 c2275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u132
  · exact u133

def b2276 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 140 25 400 33 66 224 352), lower := (rows 7 98 140 25 400 33 66 128 256), losses := [] }

theorem u2276 : Upper (D 7) (R 7) [6,96,136,17,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 25 400 34 96 193 321), lower := (rows 7 98 140 25 400 34 96 128 256), losses := [] }

theorem u2277 : Upper (D 7) (R 7) [6,96,136,17,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 98 140 26 273 33 192 224 352), lower := (rows 7 98 140 26 273 33 192 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 239 162 290), good := (rows 454 482 204 478 336 482 192 192 256) },{ target := 1, region := (rows 1 0 12 8 49 49 255 187 315), good := (rows 501 496 460 508 497 497 192 192 256) }] }

theorem u2278 : Upper (D 7) (R 7) [6,96,136,18,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 140 26 273 96 192 161 289), lower := (rows 7 98 140 26 273 96 192 128 256), losses := [] }

theorem u2279 : Upper (D 7) (R 7) [6,96,136,18,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P07
