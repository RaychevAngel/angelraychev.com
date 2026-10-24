import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0002

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 69 200 304 36 68 146 274), lower := (rows 11 35 69 200 304 36 68 128 256), losses := [] }

theorem u2220 : Upper (D 6) (R 6) [10,33,65,192,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 35 69 200 304 36 80 134 262), lower := (rows 11 35 69 200 304 36 80 128 256), losses := [] }

theorem u2221 : Upper (D 6) (R 6) [10,33,65,192,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2221 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 35 69 392 82 36 68 176 304), lower := (rows 11 35 69 392 82 36 68 128 256), losses := [] }

theorem u2222 : Upper (D 6) (R 6) [10,33,65,384,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 69 392 82 36 80 164 292), lower := (rows 11 35 69 392 82 36 80 128 256), losses := [] }

theorem u2223 : Upper (D 6) (R 6) [10,33,65,384,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2223 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 69 392 82 36 96 148 276), lower := (rows 11 35 69 392 82 36 96 128 256), losses := [] }

theorem u2224 : Upper (D 6) (R 6) [10,33,65,384,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2225 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 28 176 288 65 196 324), lower := (rows 11 35 70 28 176 288 65 128 256), losses := [] }

theorem u2225 : Upper (D 6) (R 6) [10,33,66,20,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2225 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 70 28 176 288 68 193 321), lower := (rows 11 35 70 28 176 288 68 128 256), losses := [] }

theorem u2226 : Upper (D 6) (R 6) [10,33,66,20,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2226 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 28 400 96 65 164 292), lower := (rows 11 35 70 28 400 96 65 128 256), losses := [] }

theorem u2227 : Upper (D 6) (R 6) [10,33,66,20,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 400, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 28 400 96 68 161 289), lower := (rows 11 35 70 28 400 96 68 128 256), losses := [] }

theorem u2228 : Upper (D 6) (R 6) [10,33,66,20,384,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 28 400 96 96 133 261), lower := (rows 11 35 70 28 400 96 96 128 256), losses := [] }

theorem u2229 : Upper (D 6) (R 6) [10,33,66,20,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 88 52 160 65 388 260), lower := (rows 11 35 70 88 52 160 65 128 256), losses := [] }

theorem u2230 : Upper (D 6) (R 6) [10,33,66,80,36,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2230 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 70 88 52 160 68 385 257), lower := (rows 11 35 70 88 52 160 68 128 256), losses := [] }

theorem u2231 : Upper (D 6) (R 6) [10,33,66,80,36,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2231 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5)], upper := (rows 11 35 70 88 52 160 320 133 261), lower := (rows 11 35 70 88 52 160 320 128 256), losses := [] }

theorem u2232 : Upper (D 6) (R 6) [10,33,66,80,36,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2232 [(5,7),(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 88 148 288 65 164 292), lower := (rows 11 35 70 88 148 288 65 128 256), losses := [] }

theorem u2233 : Upper (D 6) (R 6) [10,33,66,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2233 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2234 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 291, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 70 88 148 288 68 161 289), lower := (rows 11 35 70 88 148 288 68 128 256), losses := [] }

theorem u2234 : Upper (D 6) (R 6) [10,33,66,80,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2234 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 70 88 148 288 96 133 261), lower := (rows 11 35 70 88 148 288 96 128 256), losses := [] }

theorem u2235 : Upper (D 6) (R 6) [10,33,66,80,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2235 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 88 176 36 65 388 260), lower := (rows 11 35 70 88 176 36 65 128 256), losses := [] }

theorem u2236 : Upper (D 6) (R 6) [10,33,66,80,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 400, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 88 176 36 68 385 257), lower := (rows 11 35 70 88 176 36 68 128 256), losses := [] }

theorem u2237 : Upper (D 6) (R 6) [10,33,66,80,160,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2238 : Route 9 := (fun mask => (mask,id))

def c2238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2238 : Upper (D 6) (R 6) [10,33,66,80,160,4,256] 13 := by
  apply FastRouting.sound _ _ [10,33,66,80,160,4,256] 13 (by decide) (choices 1) [1,4] r2238 c2238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u122
  · exact u123

def b2239 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 88 176 288 65 132 260), lower := (rows 11 35 70 88 176 288 65 128 256), losses := [] }

theorem u2239 : Upper (D 6) (R 6) [10,33,66,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2239 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 70 88 176 288 68 133 261), lower := (rows 11 35 70 88 176 288 68 128 256), losses := [] }

theorem u2240 : Upper (D 6) (R 6) [10,33,66,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2240 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 88 400 36 65 164 292), lower := (rows 11 35 70 88 400 36 65 128 256), losses := [] }

theorem u2241 : Upper (D 6) (R 6) [10,33,66,80,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 400, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 88 400 36 68 161 289), lower := (rows 11 35 70 88 400 36 68 128 256), losses := [] }

theorem u2242 : Upper (D 6) (R 6) [10,33,66,80,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 88 400 36 96 133 261), lower := (rows 11 35 70 88 400 36 96 128 256), losses := [] }

theorem u2243 : Upper (D 6) (R 6) [10,33,66,80,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 140 52 288 65 208 336), lower := (rows 11 35 70 140 52 288 65 128 256), losses := [] }

theorem u2244 : Upper (D 6) (R 6) [10,33,66,132,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2244 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 11 35 70 140 52 288 80 193 321), lower := (rows 11 35 70 140 52 288 80 128 256), losses := [] }

theorem u2245 : Upper (D 6) (R 6) [10,33,66,132,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2245 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 70 140 81 288 68 176 304), lower := (rows 11 35 70 140 81 288 68 128 256), losses := [] }

theorem u2246 : Upper (D 6) (R 6) [10,33,66,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2246 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 70 140 81 288 80 164 292), lower := (rows 11 35 70 140 81 288 80 128 256), losses := [] }

theorem u2247 : Upper (D 6) (R 6) [10,33,66,132,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2247 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 70 140 81 288 96 148 276), lower := (rows 11 35 70 140 81 288 96 128 256), losses := [] }

theorem u2248 : Upper (D 6) (R 6) [10,33,66,132,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2248 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 140 112 288 65 148 276), lower := (rows 11 35 70 140 112 288 65 128 256), losses := [] }

theorem u2249 : Upper (D 6) (R 6) [10,33,66,132,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2249 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 70 140 112 288 68 145 273), lower := (rows 11 35 70 140 112 288 68 128 256), losses := [] }

theorem u2250 : Upper (D 6) (R 6) [10,33,66,132,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2250 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 70 140 112 288 80 133 261), lower := (rows 11 35 70 140 112 288 80 128 256), losses := [] }

theorem u2251 : Upper (D 6) (R 6) [10,33,66,132,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2251 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 140 273 96 68 176 304), lower := (rows 11 35 70 140 273 96 68 128 256), losses := [] }

theorem u2252 : Upper (D 6) (R 6) [10,33,66,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 140 273 96 80 164 292), lower := (rows 11 35 70 140 273 96 80 128 256), losses := [] }

theorem u2253 : Upper (D 6) (R 6) [10,33,66,132,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2253 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 140 273 96 96 148 276), lower := (rows 11 35 70 140 273 96 96 128 256), losses := [] }

theorem u2254 : Upper (D 6) (R 6) [10,33,66,132,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 140 276 96 65 176 304), lower := (rows 11 35 70 140 276 96 65 128 256), losses := [] }

theorem u2255 : Upper (D 6) (R 6) [10,33,66,132,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 33, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 35 70 140 276 96 80 161 289), lower := (rows 11 35 70 140 276 96 80 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 125 92 131 259), good := (rows 489 417 508 252 380 96 112 128 256) }] }

theorem u2256 : Upper (D 6) (R 6) [10,33,66,132,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2256 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 140 276 96 96 145 273), lower := (rows 11 35 70 140 276 96 96 128 256), losses := [] }

theorem u2257 : Upper (D 6) (R 6) [10,33,66,132,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 140 304 96 65 148 276), lower := (rows 11 35 70 140 304 96 65 128 256), losses := [] }

theorem u2258 : Upper (D 6) (R 6) [10,33,66,132,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 140 304 96 68 145 273), lower := (rows 11 35 70 140 304 96 68 128 256), losses := [] }

theorem u2259 : Upper (D 6) (R 6) [10,33,66,132,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 35 70 140 304 96 80 133 261), lower := (rows 11 35 70 140 304 96 80 128 256), losses := [] }

theorem u2260 : Upper (D 6) (R 6) [10,33,66,132,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2260 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 140 336 48 65 164 292), lower := (rows 11 35 70 140 336 48 65 128 256), losses := [] }

theorem u2261 : Upper (D 6) (R 6) [10,33,66,132,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2261 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 70 140 336 48 68 161 289), lower := (rows 11 35 70 140 336 48 68 128 256), losses := [] }

theorem u2262 : Upper (D 6) (R 6) [10,33,66,132,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2262 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 70 140 336 48 96 133 261), lower := (rows 11 35 70 140 336 48 96 128 256), losses := [] }

theorem u2263 : Upper (D 6) (R 6) [10,33,66,132,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2263 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 152 52 288 65 196 324), lower := (rows 11 35 70 152 52 288 65 128 256), losses := [] }

theorem u2264 : Upper (D 6) (R 6) [10,33,66,144,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2264 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 70 152 52 288 68 193 321), lower := (rows 11 35 70 152 52 288 68 128 256), losses := [] }

theorem u2265 : Upper (D 6) (R 6) [10,33,66,144,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2265 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 152 112 288 65 132 260), lower := (rows 11 35 70 152 112 288 65 128 256), losses := [] }

theorem u2266 : Upper (D 6) (R 6) [10,33,66,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2266 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 70 152 112 288 68 133 261), lower := (rows 11 35 70 152 112 288 68 128 256), losses := [] }

theorem u2267 : Upper (D 6) (R 6) [10,33,66,144,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2267 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 11 35 70 152 273 96 68 164 292), lower := (rows 11 35 70 152 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 127 87 215 343), good := (rows 494 486 486 504 508 480 484 128 256) }] }

theorem u2268 : Upper (D 6) (R 6) [10,33,66,144,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 152 273 96 96 132 260), lower := (rows 11 35 70 152 273 96 96 128 256), losses := [] }

theorem u2269 : Upper (D 6) (R 6) [10,33,66,144,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 152 276 96 65 164 292), lower := (rows 11 35 70 152 276 96 65 128 256), losses := [] }

theorem u2270 : Upper (D 6) (R 6) [10,33,66,144,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(3,1)], upper := (rows 11 35 70 152 276 96 68 161 289), lower := (rows 11 35 70 152 276 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 124 84 131 259), good := (rows 425 417 508 248 380 96 124 128 256) }] }

theorem u2271 : Upper (D 6) (R 6) [10,33,66,144,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 70 152 276 96 96 133 261), lower := (rows 11 35 70 152 276 96 96 128 256), losses := [] }

theorem u2272 : Upper (D 6) (R 6) [10,33,66,144,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 152 304 36 65 196 324), lower := (rows 11 35 70 152 304 36 65 128 256), losses := [] }

theorem u2273 : Upper (D 6) (R 6) [10,33,66,144,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(3,1)], upper := (rows 11 35 70 152 304 36 68 193 321), lower := (rows 11 35 70 152 304 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 22 100 100 130 258), good := (rows 409 505 508 152 368 124 124 128 256) }] }

theorem u2274 : Upper (D 6) (R 6) [10,33,66,144,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 152 304 96 65 132 260), lower := (rows 11 35 70 152 304 96 65 128 256), losses := [] }

theorem u2275 : Upper (D 6) (R 6) [10,33,66,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2276 : Route 9 := (fun mask => (mask,id))

def c2276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2276 : Upper (D 6) (R 6) [10,33,66,144,288,64,4] 13 := by
  apply FastRouting.sound _ _ [10,33,66,144,288,64,4] 13 (by decide) (choices 1) [1,4] r2276 c2276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u124
  · exact u125

def b2277 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 152 336 36 65 164 292), lower := (rows 11 35 70 152 336 36 65 128 256), losses := [] }

theorem u2277 : Upper (D 6) (R 6) [10,33,66,144,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,0),(2,5),(3,1)], upper := (rows 11 35 70 152 336 36 68 161 289), lower := (rows 11 35 70 152 336 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 22 100 100 130 258), good := (rows 409 505 508 152 368 124 124 128 256) }] }

theorem u2278 : Upper (D 6) (R 6) [10,33,66,144,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 152 336 36 96 133 261), lower := (rows 11 35 70 152 336 36 96 128 256), losses := [] }

theorem u2279 : Upper (D 6) (R 6) [10,33,66,144,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P06
