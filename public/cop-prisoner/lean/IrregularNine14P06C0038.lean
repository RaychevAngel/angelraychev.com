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

def b2280 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 200 52 288 65 148 276), lower := (rows 11 35 70 200 52 288 65 128 256), losses := [] }

theorem u2280 : Upper (D 6) (R 6) [10,33,66,192,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2280 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 70 200 52 288 68 145 273), lower := (rows 11 35 70 200 52 288 68 128 256), losses := [] }

theorem u2281 : Upper (D 6) (R 6) [10,33,66,192,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2281 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 11 35 70 200 52 288 80 133 261), lower := (rows 11 35 70 200 52 288 80 128 256), losses := [] }

theorem u2282 : Upper (D 6) (R 6) [10,33,66,192,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2282 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 200 273 36 68 176 304), lower := (rows 11 35 70 200 273 36 68 128 256), losses := [] }

theorem u2283 : Upper (D 6) (R 6) [10,33,66,192,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 200 273 36 80 164 292), lower := (rows 11 35 70 200 273 36 80 128 256), losses := [] }

theorem u2284 : Upper (D 6) (R 6) [10,33,66,192,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2284 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 200 273 36 96 148 276), lower := (rows 11 35 70 200 273 36 96 128 256), losses := [] }

theorem u2285 : Upper (D 6) (R 6) [10,33,66,192,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 200 276 36 65 176 304), lower := (rows 11 35 70 200 276 36 65 128 256), losses := [] }

theorem u2286 : Upper (D 6) (R 6) [10,33,66,192,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 33, camps := [], pairs := [(3,1),(4,1)], upper := (rows 11 35 70 200 276 36 80 161 289), lower := (rows 11 35 70 200 276 36 80 128 256), losses := [{ target := 1, region := (rows 1 0 4 14 20 52 116 130 258), good := (rows 393 489 508 200 380 124 112 128 256) }] }

theorem u2287 : Upper (D 6) (R 6) [10,33,66,192,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2287 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 200 276 36 96 145 273), lower := (rows 11 35 70 200 276 36 96 128 256), losses := [] }

theorem u2288 : Upper (D 6) (R 6) [10,33,66,192,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 70 200 276 48 65 164 292), lower := (rows 11 35 70 200 276 48 65 128 256), losses := [] }

theorem u2289 : Upper (D 6) (R 6) [10,33,66,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2289 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 70 200 276 48 68 161 289), lower := (rows 11 35 70 200 276 48 68 128 256), losses := [] }

theorem u2290 : Upper (D 6) (R 6) [10,33,66,192,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2290 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 70 200 276 48 96 133 261), lower := (rows 11 35 70 200 276 48 96 128 256), losses := [] }

theorem u2291 : Upper (D 6) (R 6) [10,33,66,192,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2291 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 200 304 36 65 148 276), lower := (rows 11 35 70 200 304 36 65 128 256), losses := [] }

theorem u2292 : Upper (D 6) (R 6) [10,33,66,192,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 70 200 304 36 68 145 273), lower := (rows 11 35 70 200 304 36 68 128 256), losses := [] }

theorem u2293 : Upper (D 6) (R 6) [10,33,66,192,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 70 200 304 36 80 133 261), lower := (rows 11 35 70 200 304 36 80 128 256), losses := [] }

theorem u2294 : Upper (D 6) (R 6) [10,33,66,192,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2294 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 35 70 392 81 36 68 176 304), lower := (rows 11 35 70 392 81 36 68 128 256), losses := [] }

theorem u2295 : Upper (D 6) (R 6) [10,33,66,384,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 70 392 81 36 80 164 292), lower := (rows 11 35 70 392 81 36 80 128 256), losses := [] }

theorem u2296 : Upper (D 6) (R 6) [10,33,66,384,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2296 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 35 70 392 81 36 96 148 276), lower := (rows 11 35 70 392 81 36 96 128 256), losses := [] }

theorem u2297 : Upper (D 6) (R 6) [10,33,66,384,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 35 70 392 112 36 65 148 276), lower := (rows 11 35 70 392 112 36 65 128 256), losses := [] }

theorem u2298 : Upper (D 6) (R 6) [10,33,66,384,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 70 392 112 36 68 145 273), lower := (rows 11 35 70 392 112 36 68 128 256), losses := [] }

theorem u2299 : Upper (D 6) (R 6) [10,33,66,384,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2300 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 70 392 112 36 80 133 261), lower := (rows 11 35 70 392 112 36 80 128 256), losses := [] }

theorem u2300 : Upper (D 6) (R 6) [10,33,66,384,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2300 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2301 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 84 73 400 36 66 164 292), lower := (rows 11 35 84 73 400 36 66 128 256), losses := [] }

theorem u2301 : Upper (D 6) (R 6) [10,33,80,65,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 1, region := 400, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 11 35 84 73 400 36 68 162 290), lower := (rows 11 35 84 73 400 36 68 128 256), losses := [] }

theorem u2302 : Upper (D 6) (R 6) [10,33,80,65,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 84 73 400 36 96 134 262), lower := (rows 11 35 84 73 400 36 96 128 256), losses := [] }

theorem u2303 : Upper (D 6) (R 6) [10,33,80,65,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 276 96 66 164 292), lower := (rows 11 35 84 137 276 96 66 128 256), losses := [] }

theorem u2304 : Upper (D 6) (R 6) [10,33,80,129,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 139, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 137 276 96 68 162 290), lower := (rows 11 35 84 137 276 96 68 128 256), losses := [] }

theorem u2305 : Upper (D 6) (R 6) [10,33,80,129,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 276 96 96 134 262), lower := (rows 11 35 84 137 276 96 96 128 256), losses := [] }

theorem u2306 : Upper (D 6) (R 6) [10,33,80,129,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 304 36 66 196 324), lower := (rows 11 35 84 137 304 36 66 128 256), losses := [] }

theorem u2307 : Upper (D 6) (R 6) [10,33,80,129,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 304 36 68 194 322), lower := (rows 11 35 84 137 304 36 68 128 256), losses := [] }

theorem u2308 : Upper (D 6) (R 6) [10,33,80,129,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 304 96 66 132 260), lower := (rows 11 35 84 137 304 96 66 128 256), losses := [] }

theorem u2309 : Upper (D 6) (R 6) [10,33,80,129,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 137 304 96 68 134 262), lower := (rows 11 35 84 137 304 96 68 128 256), losses := [] }

theorem u2310 : Upper (D 6) (R 6) [10,33,80,129,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 11 35 84 140 273 96 66 164 292), lower := (rows 11 35 84 140 273 96 66 128 256), losses := [] }

theorem u2311 : Upper (D 6) (R 6) [10,33,80,132,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 84 140 273 96 68 162 290), lower := (rows 11 35 84 140 273 96 68 128 256), losses := [] }

theorem u2312 : Upper (D 6) (R 6) [10,33,80,132,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 84 140 273 96 96 134 262), lower := (rows 11 35 84 140 273 96 96 128 256), losses := [] }

theorem u2313 : Upper (D 6) (R 6) [10,33,80,132,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 11 35 84 140 274 96 65 164 292), lower := (rows 11 35 84 140 274 96 65 128 256), losses := [] }

theorem u2314 : Upper (D 6) (R 6) [10,33,80,132,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 84 140 274 96 68 161 289), lower := (rows 11 35 84 140 274 96 68 128 256), losses := [] }

theorem u2315 : Upper (D 6) (R 6) [10,33,80,132,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 84 140 274 96 96 133 261), lower := (rows 11 35 84 140 274 96 96 128 256), losses := [] }

theorem u2316 : Upper (D 6) (R 6) [10,33,80,132,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2317 : Route 9 := (fun mask => (mask,id))

def c2317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2317 : Upper (D 6) (R 6) [10,33,80,132,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,260,64,1] 13 (by decide) (choices 1) [2,32] r2317 c2317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u126
  · exact u127

def b2318 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 84 140 276 96 66 161 289), lower := (rows 11 35 84 140 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 100 74 82 100 64 130 258), good := (rows 409 445 124 172 308 124 508 128 256) }] }

theorem u2318 : Upper (D 6) (R 6) [10,33,80,132,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 140 276 96 96 131 259), lower := (rows 11 35 84 140 276 96 96 128 256), losses := [] }

theorem u2319 : Upper (D 6) (R 6) [10,33,80,132,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2320 : Route 9 := (fun mask => (mask,id))

def c2320 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2320 : Upper (D 6) (R 6) [10,33,80,132,288,64,1] 13 := by
  apply FastRouting.sound _ _ [10,33,80,132,288,64,1] 13 (by decide) (choices 1) [2,4] r2320 c2320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u128
  · exact u129

def b2321 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 11 35 84 140 304 96 66 133 261), lower := (rows 11 35 84 140 304 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 100 74 82 100 64 130 258), good := (rows 409 445 124 172 308 124 508 128 256) }] }

theorem u2321 : Upper (D 6) (R 6) [10,33,80,132,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 140 304 96 68 131 259), lower := (rows 11 35 84 140 304 96 68 128 256), losses := [] }

theorem u2322 : Upper (D 6) (R 6) [10,33,80,132,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 84 200 21 288 66 164 292), lower := (rows 11 35 84 200 21 288 66 128 256), losses := [] }

theorem u2323 : Upper (D 6) (R 6) [10,33,80,192,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2323 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 84, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 11 35 84 200 21 288 68 162 290), lower := (rows 11 35 84 200 21 288 68 128 256), losses := [] }

theorem u2324 : Upper (D 6) (R 6) [10,33,80,192,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2324 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 84 200 21 288 96 134 262), lower := (rows 11 35 84 200 21 288 96 128 256), losses := [] }

theorem u2325 : Upper (D 6) (R 6) [10,33,80,192,5,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2325 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 35 84 200 22 288 65 164 292), lower := (rows 11 35 84 200 22 288 65 128 256), losses := [] }

theorem u2326 : Upper (D 6) (R 6) [10,33,80,192,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2326 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 11 35 84 200 22 288 68 161 289), lower := (rows 11 35 84 200 22 288 68 128 256), losses := [] }

theorem u2327 : Upper (D 6) (R 6) [10,33,80,192,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2327 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 200 22 288 96 133 261), lower := (rows 11 35 84 200 22 288 96 128 256), losses := [] }

theorem u2328 : Upper (D 6) (R 6) [10,33,80,192,6,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2328 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 84 200 52 288 65 134 262), lower := (rows 11 35 84 200 52 288 65 128 256), losses := [] }

theorem u2329 : Upper (D 6) (R 6) [10,33,80,192,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2329 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 84 200 52 288 66 133 261), lower := (rows 11 35 84 200 52 288 66 128 256), losses := [] }

theorem u2330 : Upper (D 6) (R 6) [10,33,80,192,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2330 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 84 200 52 288 68 131 259), lower := (rows 11 35 84 200 52 288 68 128 256), losses := [] }

theorem u2331 : Upper (D 6) (R 6) [10,33,80,192,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2331 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 84 200 273 36 66 164 292), lower := (rows 11 35 84 200 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 30 16 52 67 180 308), good := (rows 74 490 508 200 508 428 74 128 256) }] }

theorem u2332 : Upper (D 6) (R 6) [10,33,80,192,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 84 200 273 36 68 162 290), lower := (rows 11 35 84 200 273 36 68 128 256), losses := [] }

theorem u2333 : Upper (D 6) (R 6) [10,33,80,192,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2334 : Route 9 := (fun mask => (mask,id))

def c2334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2334 : Upper (D 6) (R 6) [10,33,80,192,257,4,32] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,257,4,32] 13 (by decide) (choices 1) [2,4] r2334 c2334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b2335 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 84 200 274 36 65 164 292), lower := (rows 11 35 84 200 274 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 19 108 64 236 364), good := (rows 442 434 508 492 274 428 508 128 256) }] }

theorem u2335 : Upper (D 6) (R 6) [10,33,80,192,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 11 35 84 200 274 36 68 161 289), lower := (rows 11 35 84 200 274 36 68 128 256), losses := [] }

theorem u2336 : Upper (D 6) (R 6) [10,33,80,192,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2337 : Route 9 := (fun mask => (mask,id))

def c2337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2337 : Upper (D 6) (R 6) [10,33,80,192,258,4,32] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,258,4,32] 13 (by decide) (choices 1) [1,4] r2337 c2337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u132
  · exact u133

def b2338 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 84 200 304 36 65 134 262), lower := (rows 11 35 84 200 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 83 109 64 129 257), good := (rows 446 434 124 252 304 36 508 128 256) }] }

theorem u2338 : Upper (D 6) (R 6) [10,33,80,192,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2339 : Route 9 := (fun mask => (mask,id))

def c2339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2339 : Upper (D 6) (R 6) [10,33,80,192,288,4,2] 13 := by
  apply FastRouting.sound _ _ [10,33,80,192,288,4,2] 13 (by decide) (choices 1) [1,4] r2339 c2339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u134
  · exact u135

#print axioms u2339
end Delivery.IrregularNine14.P06
