import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 81, targets := 128 },{ cop := 1, region := 336, targets := 32 }], pairs := [(0,7),(1,7),(4,5),(4,7)], upper := (rows 97 7 140 296 273 160 80 194 322), lower := (rows 97 7 140 296 273 160 80 128 256), losses := [{ target := 7, region := (rows 9 6 4 8 30 32 94 0 262), good := (rows 97 343 351 377 337 32 80 0 256) }] }

theorem u2280 : Upper (D 9) (R 9) [96,5,136,288,257,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2280 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(4,5),(4,7)], upper := (rows 97 7 140 296 274 160 65 208 336), lower := (rows 97 7 140 296 274 160 65 128 256), losses := [] }

theorem u2281 : Upper (D 9) (R 9) [96,5,136,288,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2281 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 264, targets := 128 },{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(3,7),(4,5),(4,7)], upper := (rows 97 7 140 296 274 160 80 193 321), lower := (rows 97 7 140 296 274 160 80 128 256), losses := [] }

theorem u2282 : Upper (D 9) (R 9) [96,5,136,288,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2282 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 140 296 336 34 65 144 400), lower := (rows 97 7 140 296 336 34 65 128 256), losses := [] }

theorem u2283 : Upper (D 9) (R 9) [96,5,136,288,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2283 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 336 34 80 129 385), lower := (rows 97 7 140 296 336 34 80 128 256), losses := [] }

theorem u2284 : Upper (D 9) (R 9) [96,5,136,288,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2284 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 296 336 34 192 145 273), lower := (rows 97 7 140 296 336 34 192 128 256), losses := [] }

theorem u2285 : Upper (D 9) (R 9) [96,5,136,288,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2285 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 3, region := 81, targets := 128 },{ cop := 1, region := 336, targets := 32 }], pairs := [(0,7),(0,8),(1,8),(4,5),(4,7)], upper := (rows 97 7 140 296 336 160 65 146 274), lower := (rows 97 7 140 296 336 160 65 128 256), losses := [] }

theorem u2286 : Upper (D 9) (R 9) [96,5,136,288,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2286 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 296 336 160 66 145 273), lower := (rows 97 7 140 296 336 160 66 128 256), losses := [] }

theorem u2287 : Upper (D 9) (R 9) [96,5,136,288,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2287 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 8, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 7 140 296 336 160 80 131 259), lower := (rows 97 7 140 296 336 160 80 128 256), losses := [] }

theorem u2288 : Upper (D 9) (R 9) [96,5,136,288,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2288 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 140 296 400 33 66 208 336), lower := (rows 97 7 140 296 400 33 66 128 256), losses := [] }

theorem u2289 : Upper (D 9) (R 9) [96,5,136,288,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2289 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 7 140 296 400 33 80 194 322), lower := (rows 97 7 140 296 400 33 80 128 256), losses := [] }

theorem u2290 : Upper (D 9) (R 9) [96,5,136,288,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2290 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 140 296 400 34 65 208 336), lower := (rows 97 7 140 296 400 34 65 128 256), losses := [] }

theorem u2291 : Upper (D 9) (R 9) [96,5,136,288,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2291 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2292 : Route 9 := (fun mask => (mask,id))

def c2292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2292 : Upper (D 9) (R 9) [96,5,136,288,384,2,16] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,384,2,16] 13 (by decide) (choices 1) [1,64] r2292 c2292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u134
  · exact u135

def b2293 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 25 208 34 320 392 264), lower := (rows 97 7 164 25 208 34 320 128 256), losses := [] }

theorem u2293 : Upper (D 9) (R 9) [96,5,160,17,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2293 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 25 208 40 320 386 258), lower := (rows 97 7 164 25 208 40 320 128 256), losses := [] }

theorem u2294 : Upper (D 9) (R 9) [96,5,160,17,192,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2294 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 25 208 288 320 138 266), lower := (rows 97 7 164 25 208 288 320 128 256), losses := [] }

theorem u2295 : Upper (D 9) (R 9) [96,5,160,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2295 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 25 400 34 72 448 320), lower := (rows 97 7 164 25 400 34 72 128 256), losses := [] }

theorem u2296 : Upper (D 9) (R 9) [96,5,160,17,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2296 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2297 : Route 9 := (fun mask => (mask,id))

def c2297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2297 : Upper (D 9) (R 9) [96,5,160,17,384,2,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,17,384,2,256] 13 (by decide) (choices 1) [8,64] r2297 c2297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u136
  · exact u137

def b2298 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 91, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 97 7 164 26 88 288 65 384 384), lower := (rows 97 7 164 26 88 288 65 128 256), losses := [] }

theorem u2298 : Upper (D 9) (R 9) [96,5,160,18,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2298 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 390, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 26 88 288 192 385 257), lower := (rows 97 7 164 26 88 288 192 128 256), losses := [] }

theorem u2299 : Upper (D 9) (R 9) [96,5,160,18,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2299 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2300 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8),(4,8)], upper := (rows 97 7 164 26 88 288 320 129 385), lower := (rows 97 7 164 26 88 288 320 128 256), losses := [] }

theorem u2300 : Upper (D 9) (R 9) [96,5,160,18,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2300 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2301 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 26 145 288 72 448 320), lower := (rows 97 7 164 26 145 288 72 128 256), losses := [] }

theorem u2301 : Upper (D 9) (R 9) [96,5,160,18,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2301 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 26 145 288 320 200 328), lower := (rows 97 7 164 26 145 288 320 128 256), losses := [] }

theorem u2302 : Upper (D 9) (R 9) [96,5,160,18,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 26 152 288 65 448 320), lower := (rows 97 7 164 26 152 288 65 128 256), losses := [] }

theorem u2303 : Upper (D 9) (R 9) [96,5,160,18,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2303 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 26 152 288 320 193 321), lower := (rows 97 7 164 26 152 288 320 128 256), losses := [] }

theorem u2304 : Upper (D 9) (R 9) [96,5,160,18,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 26 208 288 65 392 264), lower := (rows 97 7 164 26 208 288 65 128 256), losses := [] }

theorem u2305 : Upper (D 9) (R 9) [96,5,160,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 26 208 288 72 385 257), lower := (rows 97 7 164 26 208 288 72 128 256), losses := [] }

theorem u2306 : Upper (D 9) (R 9) [96,5,160,18,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2306 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 26 208 288 320 137 265), lower := (rows 97 7 164 26 208 288 320 128 256), losses := [] }

theorem u2307 : Upper (D 9) (R 9) [96,5,160,18,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2307 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 26 273 40 192 448 320), lower := (rows 97 7 164 26 273 40 192 128 256), losses := [] }

theorem u2308 : Upper (D 9) (R 9) [96,5,160,18,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2308 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 7 164 26 273 40 320 192 448), lower := (rows 97 7 164 26 273 40 320 128 256), losses := [] }

theorem u2309 : Upper (D 9) (R 9) [96,5,160,18,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2309 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 7 164 26 273 288 72 192 448), lower := (rows 97 7 164 26 273 288 72 128 256), losses := [] }

theorem u2310 : Upper (D 9) (R 9) [96,5,160,18,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2310 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 },{ cop := 3, region := 484, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,5),(4,5)], upper := (rows 97 7 164 26 273 288 192 200 328), lower := (rows 97 7 164 26 273 288 192 128 256), losses := [] }

theorem u2311 : Upper (D 9) (R 9) [96,5,160,18,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2311 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 164 26 336 288 65 136 392), lower := (rows 97 7 164 26 336 288 65 128 256), losses := [] }

theorem u2312 : Upper (D 9) (R 9) [96,5,160,18,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 26 336 288 72 129 385), lower := (rows 97 7 164 26 336 288 72 128 256), losses := [] }

theorem u2313 : Upper (D 9) (R 9) [96,5,160,18,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2313 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 26 336 288 192 137 265), lower := (rows 97 7 164 26 336 288 192 128 256), losses := [] }

theorem u2314 : Upper (D 9) (R 9) [96,5,160,18,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 74 145 288 72 400 272), lower := (rows 97 7 164 74 145 288 72 128 256), losses := [] }

theorem u2315 : Upper (D 9) (R 9) [96,5,160,66,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2315 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 74 145 288 80 392 264), lower := (rows 97 7 164 74 145 288 80 128 256), losses := [] }

theorem u2316 : Upper (D 9) (R 9) [96,5,160,66,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2316 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 74 145 288 320 152 280), lower := (rows 97 7 164 74 145 288 320 128 256), losses := [] }

theorem u2317 : Upper (D 9) (R 9) [96,5,160,66,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2317 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 97 7 164 74 152 288 65 400 272), lower := (rows 97 7 164 74 152 288 65 128 256), losses := [] }

theorem u2318 : Upper (D 9) (R 9) [96,5,160,66,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2318 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 74 152 288 80 385 257), lower := (rows 97 7 164 74 152 288 80 128 256), losses := [] }

theorem u2319 : Upper (D 9) (R 9) [96,5,160,66,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2319 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 74 152 288 320 145 273), lower := (rows 97 7 164 74 152 288 320 128 256), losses := [] }

theorem u2320 : Upper (D 9) (R 9) [96,5,160,66,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7)], upper := (rows 97 7 164 74 273 48 72 384 384), lower := (rows 97 7 164 74 273 48 72 128 256), losses := [] }

theorem u2321 : Upper (D 9) (R 9) [96,5,160,66,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2321 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 74 273 48 192 392 264), lower := (rows 97 7 164 74 273 48 192 128 256), losses := [] }

theorem u2322 : Upper (D 9) (R 9) [96,5,160,66,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2322 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 74 273 48 320 136 392), lower := (rows 97 7 164 74 273 48 320 128 256), losses := [] }

theorem u2323 : Upper (D 9) (R 9) [96,5,160,66,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2323 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 74 273 288 72 144 400), lower := (rows 97 7 164 74 273 288 72 128 256), losses := [] }

theorem u2324 : Upper (D 9) (R 9) [96,5,160,66,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2324 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 74 273 288 80 136 392), lower := (rows 97 7 164 74 273 288 80 128 256), losses := [] }

theorem u2325 : Upper (D 9) (R 9) [96,5,160,66,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2325 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 74 273 288 192 152 280), lower := (rows 97 7 164 74 273 288 192 128 256), losses := [] }

theorem u2326 : Upper (D 9) (R 9) [96,5,160,66,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 97 7 164 74 280 288 65 144 400), lower := (rows 97 7 164 74 280 288 65 128 256), losses := [] }

theorem u2327 : Upper (D 9) (R 9) [96,5,160,66,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2327 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 74 280 288 80 129 385), lower := (rows 97 7 164 74 280 288 80 128 256), losses := [] }

theorem u2328 : Upper (D 9) (R 9) [96,5,160,66,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2328 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 74 280 288 192 145 273), lower := (rows 97 7 164 74 280 288 192 128 256), losses := [] }

theorem u2329 : Upper (D 9) (R 9) [96,5,160,66,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 97 7 164 74 400 288 65 152 280), lower := (rows 97 7 164 74 400 288 65 128 256), losses := [] }

theorem u2330 : Upper (D 9) (R 9) [96,5,160,66,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2330 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 74 400 288 72 145 273), lower := (rows 97 7 164 74 400 288 72 128 256), losses := [] }

theorem u2331 : Upper (D 9) (R 9) [96,5,160,66,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2331 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 74 400 288 80 137 265), lower := (rows 97 7 164 74 400 288 80 128 256), losses := [] }

theorem u2332 : Upper (D 9) (R 9) [96,5,160,66,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2332 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 88 145 288 66 392 264), lower := (rows 97 7 164 88 145 288 66 128 256), losses := [] }

theorem u2333 : Upper (D 9) (R 9) [96,5,160,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2333 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 88 145 288 72 386 258), lower := (rows 97 7 164 88 145 288 72 128 256), losses := [] }

theorem u2334 : Upper (D 9) (R 9) [96,5,160,80,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2334 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 88 145 288 320 138 266), lower := (rows 97 7 164 88 145 288 320 128 256), losses := [] }

theorem u2335 : Upper (D 9) (R 9) [96,5,160,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2335 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 88 146 288 65 392 264), lower := (rows 97 7 164 88 146 288 65 128 256), losses := [] }

theorem u2336 : Upper (D 9) (R 9) [96,5,160,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 164 88 146 288 72 385 257), lower := (rows 97 7 164 88 146 288 72 128 256), losses := [] }

theorem u2337 : Upper (D 9) (R 9) [96,5,160,80,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2337 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 164 88 146 288 320 137 265), lower := (rows 97 7 164 88 146 288 320 128 256), losses := [] }

theorem u2338 : Upper (D 9) (R 9) [96,5,160,80,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2339 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 7 164 88 273 34 72 384 384), lower := (rows 97 7 164 88 273 34 72 128 256), losses := [] }

theorem u2339 : Upper (D 9) (R 9) [96,5,160,80,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2339 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P09
