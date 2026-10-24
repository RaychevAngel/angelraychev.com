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

def b2280 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 26 304 33 65 192 448), lower := (rows 7 98 140 26 304 33 65 128 256), losses := [] }

theorem u2280 : Upper (D 7) (R 7) [6,96,136,18,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2281 : Route 9 := (fun mask => (mask,id))

def c2281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2281 : Upper (D 7) (R 7) [6,96,136,18,288,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,288,1,128] 13 (by decide) (choices 1) [1,64] r2281 c2281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u134
  · exact u135

def b2282 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,5),(3,7),(4,1)], upper := (rows 7 98 140 26 304 160 65 193 321), lower := (rows 7 98 140 26 304 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 11 18 32 65 0 321), good := (rows 351 378 12 26 304 32 329 0 256) }] }

theorem u2282 : Upper (D 7) (R 7) [6,96,136,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 26 400 33 65 224 352), lower := (rows 7 98 140 26 400 33 65 128 256), losses := [] }

theorem u2283 : Upper (D 7) (R 7) [6,96,136,18,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 26 400 33 96 193 321), lower := (rows 7 98 140 26 400 33 96 128 256), losses := [] }

theorem u2284 : Upper (D 7) (R 7) [6,96,136,18,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 7 98 140 41 146 288 65 208 336), lower := (rows 7 98 140 41 146 288 65 128 256), losses := [] }

theorem u2285 : Upper (D 7) (R 7) [6,96,136,33,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2285 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(4,5)], upper := (rows 7 98 140 41 146 288 80 193 321), lower := (rows 7 98 140 41 146 288 80 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 288 85 128 256), good := (rows 86 98 222 106 210 288 80 128 288) }] }

theorem u2286 : Upper (D 7) (R 7) [6,96,136,33,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2286 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 7 98 140 41 208 288 65 146 274), lower := (rows 7 98 140 41 208 288 65 128 256), losses := [] }

theorem u2287 : Upper (D 7) (R 7) [6,96,136,33,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2287 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(1,7),(4,5)], upper := (rows 7 98 140 41 208 288 66 145 273), lower := (rows 7 98 140 41 208 288 66 128 256), losses := [] }

theorem u2288 : Upper (D 7) (R 7) [6,96,136,33,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2288 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 41 208 288 80 131 259), lower := (rows 7 98 140 41 208 288 80 128 256), losses := [] }

theorem u2289 : Upper (D 7) (R 7) [6,96,136,33,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2289 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 208 33 65 386 258), lower := (rows 7 98 140 56 208 33 65 128 256), losses := [] }

theorem u2290 : Upper (D 7) (R 7) [6,96,136,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 140 56 208 33 66 385 257), lower := (rows 7 98 140 56 208 33 66 128 256), losses := [] }

theorem u2291 : Upper (D 7) (R 7) [6,96,136,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(4,5)], upper := (rows 7 98 140 56 208 33 320 131 259), lower := (rows 7 98 140 56 208 33 320 128 256), losses := [] }

theorem u2292 : Upper (D 7) (R 7) [6,96,136,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2292 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 7 98 140 56 273 160 65 194 322), lower := (rows 7 98 140 56 273 160 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 24 16 231 64 194 322), good := (rows 422 482 172 56 312 160 482 160 256) }] }

theorem u2293 : Upper (D 7) (R 7) [6,96,136,48,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,0),(1,7),(4,5),(4,7)], upper := (rows 7 98 140 56 273 160 66 193 321), lower := (rows 7 98 140 56 273 160 66 128 256), losses := [] }

theorem u2294 : Upper (D 7) (R 7) [6,96,136,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 274 33 65 192 448), lower := (rows 7 98 140 56 274 33 65 128 256), losses := [] }

theorem u2295 : Upper (D 7) (R 7) [6,96,136,48,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2296 : Route 9 := (fun mask => (mask,id))

def c2296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2296 : Upper (D 7) (R 7) [6,96,136,48,258,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258,1,128] 13 (by decide) (choices 1) [1,64] r2296 c2296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u136
  · exact u137

def b2297 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(3,1),(3,7),(4,5),(4,7)], upper := (rows 7 98 140 56 274 160 65 193 321), lower := (rows 7 98 140 56 274 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 231 65 193 321), good := (rows 485 480 172 56 312 160 481 160 256) },{ target := 7, region := (rows 1 2 4 10 19 32 65 0 321), good := (rows 351 378 12 56 282 32 337 0 256) }] }

theorem u2297 : Upper (D 7) (R 7) [6,96,136,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 336 33 65 130 386), lower := (rows 7 98 140 56 336 33 65 128 256), losses := [] }

theorem u2298 : Upper (D 7) (R 7) [6,96,136,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 140 56 336 33 66 129 385), lower := (rows 7 98 140 56 336 33 66 128 256), losses := [] }

theorem u2299 : Upper (D 7) (R 7) [6,96,136,48,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2300 : Route 9 := (fun mask => (mask,id))

def c2300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2300 : Upper (D 7) (R 7) [6,96,136,48,320,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,320,1,128] 13 (by decide) (choices 1) [1,2] r2300 c2300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u138
  · exact u139

def b2301 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(3,6),(3,7),(4,5),(4,7)], upper := (rows 7 98 140 56 336 160 65 131 259), lower := (rows 7 98 140 56 336 160 65 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 229 0 129 257), good := (rows 423 34 172 56 312 160 417 160 256) },{ target := 7, region := (rows 1 2 4 10 81 32 65 0 257), good := (rows 351 122 12 56 336 32 337 0 256) }] }

theorem u2301 : Upper (D 7) (R 7) [6,96,136,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,0),(1,7),(4,5),(4,7)], upper := (rows 7 98 140 56 336 160 66 129 257), lower := (rows 7 98 140 56 336 160 66 128 256), losses := [] }

theorem u2302 : Upper (D 7) (R 7) [6,96,136,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 56 400 33 65 194 322), lower := (rows 7 98 140 56 400 33 65 128 256), losses := [] }

theorem u2303 : Upper (D 7) (R 7) [6,96,136,48,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 140 56 400 33 66 193 321), lower := (rows 7 98 140 56 400 33 66 128 256), losses := [] }

theorem u2304 : Upper (D 7) (R 7) [6,96,136,48,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 7 98 140 265 145 34 80 224 352), lower := (rows 7 98 140 265 145 34 80 128 256), losses := [] }

theorem u2305 : Upper (D 7) (R 7) [6,96,136,257,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2305 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 265 145 34 96 208 336), lower := (rows 7 98 140 265 145 34 96 128 256), losses := [] }

theorem u2306 : Upper (D 7) (R 7) [6,96,136,257,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 140 265 146 33 80 224 352), lower := (rows 7 98 140 265 146 33 80 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 41 80 130 258), good := (rows 429 480 172 301 464 45 80 128 256) }] }

theorem u2307 : Upper (D 7) (R 7) [6,96,136,257,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2307 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2308 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 265 146 33 96 208 336), lower := (rows 7 98 140 265 146 33 96 128 256), losses := [] }

theorem u2308 : Upper (D 7) (R 7) [6,96,136,257,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 265 146 48 96 193 321), lower := (rows 7 98 140 265 146 48 96 128 256), losses := [] }

theorem u2309 : Upper (D 7) (R 7) [6,96,136,257,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 7 98 140 265 176 34 65 208 336), lower := (rows 7 98 140 265 176 34 65 128 256), losses := [] }

theorem u2310 : Upper (D 7) (R 7) [6,96,136,257,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 265 176 34 80 193 321), lower := (rows 7 98 140 265 176 34 80 128 256), losses := [] }

theorem u2311 : Upper (D 7) (R 7) [6,96,136,257,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2311 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 266 176 33 65 208 336), lower := (rows 7 98 140 266 176 33 65 128 256), losses := [] }

theorem u2312 : Upper (D 7) (R 7) [6,96,136,258,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 140 266 176 33 80 193 321), lower := (rows 7 98 140 266 176 33 80 128 256), losses := [] }

theorem u2313 : Upper (D 7) (R 7) [6,96,136,258,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2313 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 280 146 33 65 224 352), lower := (rows 7 98 140 280 146 33 65 128 256), losses := [] }

theorem u2314 : Upper (D 7) (R 7) [6,96,136,272,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 140 280 146 33 96 193 321), lower := (rows 7 98 140 280 146 33 96 128 256), losses := [] }

theorem u2315 : Upper (D 7) (R 7) [6,96,136,272,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 280 176 33 65 194 322), lower := (rows 7 98 140 280 176 33 65 128 256), losses := [] }

theorem u2316 : Upper (D 7) (R 7) [6,96,136,272,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,5)], upper := (rows 7 98 140 280 176 33 66 193 321), lower := (rows 7 98 140 280 176 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 161 289), good := (rows 455 450 140 284 412 449 66 128 256) }] }

theorem u2317 : Upper (D 7) (R 7) [6,96,136,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,1)], upper := (rows 7 98 140 280 176 34 65 193 321), lower := (rows 7 98 140 280 176 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 71 11 18 32 65 193 321), good := (rows 477 508 140 280 176 60 461 128 256) }] }

theorem u2318 : Upper (D 7) (R 7) [6,96,136,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 140 296 81 33 66 144 400), lower := (rows 7 98 140 296 81 33 66 128 256), losses := [] }

theorem u2319 : Upper (D 7) (R 7) [6,96,136,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 296 81 33 80 130 386), lower := (rows 7 98 140 296 81 33 80 128 256), losses := [] }

theorem u2320 : Upper (D 7) (R 7) [6,96,136,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2320 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 7 98 140 296 81 33 192 146 274), lower := (rows 7 98 140 296 81 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 196 128 256), good := (rows 117 96 204 296 113 49 192 192 256) }] }

theorem u2321 : Upper (D 7) (R 7) [6,96,136,288,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 98 140 296 81 160 65 146 274), lower := (rows 7 98 140 296 81 160 65 128 256), losses := [] }

theorem u2322 : Upper (D 7) (R 7) [6,96,136,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 7 98 140 296 81 160 66 145 273), lower := (rows 7 98 140 296 81 160 66 128 256), losses := [] }

theorem u2323 : Upper (D 7) (R 7) [6,96,136,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 296 81 160 80 131 259), lower := (rows 7 98 140 296 81 160 80 128 256), losses := [] }

theorem u2324 : Upper (D 7) (R 7) [6,96,136,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2324 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 140 296 145 33 66 208 336), lower := (rows 7 98 140 296 145 33 66 128 256), losses := [] }

theorem u2325 : Upper (D 7) (R 7) [6,96,136,288,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 7 98 140 296 145 33 80 194 322), lower := (rows 7 98 140 296 145 33 80 128 256), losses := [] }

theorem u2326 : Upper (D 7) (R 7) [6,96,136,288,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2326 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 296 146 33 65 208 336), lower := (rows 7 98 140 296 146 33 65 128 256), losses := [] }

theorem u2327 : Upper (D 7) (R 7) [6,96,136,288,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2328 : Route 9 := (fun mask => (mask,id))

def c2328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2328 : Upper (D 7) (R 7) [6,96,136,288,130,1,16] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288,130,1,16] 13 (by decide) (choices 1) [1,64] r2328 c2328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u140
  · exact u141

def b2329 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 98 140 296 146 48 65 193 321), lower := (rows 7 98 140 296 146 48 65 128 256), losses := [{ target := 1, region := (rows 1 0 23 10 16 48 65 193 321), good := (rows 461 492 140 296 188 52 453 128 256) }] }

theorem u2329 : Upper (D 7) (R 7) [6,96,136,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2329 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 140 296 208 33 65 146 274), lower := (rows 7 98 140 296 208 33 65 128 256), losses := [] }

theorem u2330 : Upper (D 7) (R 7) [6,96,136,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,5)], upper := (rows 7 98 140 296 208 33 66 145 273), lower := (rows 7 98 140 296 208 33 66 128 256), losses := [] }

theorem u2331 : Upper (D 7) (R 7) [6,96,136,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 296 208 33 80 131 259), lower := (rows 7 98 140 296 208 33 80 128 256), losses := [] }

theorem u2332 : Upper (D 7) (R 7) [6,96,136,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2332 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(3,5),(4,0),(4,5)], upper := (rows 7 98 164 25 208 33 66 392 264), lower := (rows 7 98 164 25 208 33 66 128 256), losses := [] }

theorem u2333 : Upper (D 7) (R 7) [6,96,160,17,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 388, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 25 208 33 72 386 258), lower := (rows 7 98 164 25 208 33 72 128 256), losses := [] }

theorem u2334 : Upper (D 7) (R 7) [6,96,160,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2334 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 164 25 208 33 320 138 266), lower := (rows 7 98 164 25 208 33 320 128 256), losses := [] }

theorem u2335 : Upper (D 7) (R 7) [6,96,160,17,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2335 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 132, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 25 274 33 72 192 448), lower := (rows 7 98 164 25 274 33 72 128 256), losses := [] }

theorem u2336 : Upper (D 7) (R 7) [6,96,160,17,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2336 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 1 },{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,5),(4,5)], upper := (rows 7 98 164 25 274 33 192 200 328), lower := (rows 7 98 164 25 274 33 192 128 256), losses := [] }

theorem u2337 : Upper (D 7) (R 7) [6,96,160,17,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 66 136 392), lower := (rows 7 98 164 25 336 33 66 128 256), losses := [] }

theorem u2338 : Upper (D 7) (R 7) [6,96,160,17,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2339 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 132, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 72 130 386), lower := (rows 7 98 164 25 336 33 72 128 256), losses := [] }

theorem u2339 : Upper (D 7) (R 7) [6,96,160,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2339 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P07
