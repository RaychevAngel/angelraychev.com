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

def r2340 : Route 9 := (fun mask => (mask,id))

def c2340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2340 : Upper (D 7) (R 7) [6,96,160,17,320,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320,1,128] 13 (by decide) (choices 1) [2,8] r2340 c2340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u142
  · exact u143

def b2341 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 25 400 33 66 200 328), lower := (rows 7 98 164 25 400 33 66 128 256), losses := [] }

theorem u2341 : Upper (D 7) (R 7) [6,96,160,17,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 132, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 25 400 33 72 194 322), lower := (rows 7 98 164 25 400 33 72 128 256), losses := [] }

theorem u2342 : Upper (D 7) (R 7) [6,96,160,17,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2342 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 164 26 273 33 72 192 448), lower := (rows 7 98 164 26 273 33 72 128 256), losses := [] }

theorem u2343 : Upper (D 7) (R 7) [6,96,160,18,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2343 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(3,5),(4,5)], upper := (rows 7 98 164 26 273 33 192 200 328), lower := (rows 7 98 164 26 273 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 204 136 264), good := (rows 101 96 228 508 305 33 192 192 256) }] }

theorem u2344 : Upper (D 7) (R 7) [6,96,160,18,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 26 280 33 65 192 448), lower := (rows 7 98 164 26 280 33 65 128 256), losses := [] }

theorem u2345 : Upper (D 7) (R 7) [6,96,160,18,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(3,5),(4,5)], upper := (rows 7 98 164 26 280 33 192 193 321), lower := (rows 7 98 164 26 280 33 192 128 256), losses := [] }

theorem u2346 : Upper (D 7) (R 7) [6,96,160,18,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 26 400 33 65 200 328), lower := (rows 7 98 164 26 400 33 65 128 256), losses := [] }

theorem u2347 : Upper (D 7) (R 7) [6,96,160,18,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2348 : Route 9 := (fun mask => (mask,id))

def c2348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2348 : Upper (D 7) (R 7) [6,96,160,18,384,1,8] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18,384,1,8] 13 (by decide) (choices 1) [1,64] r2348 c2348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u144
  · exact u145

def b2349 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 98 164 73 146 288 65 152 280), lower := (rows 7 98 164 73 146 288 65 128 256), losses := [] }

theorem u2349 : Upper (D 7) (R 7) [6,96,160,65,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2349 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 73 146 288 72 145 273), lower := (rows 7 98 164 73 146 288 72 128 256), losses := [] }

theorem u2350 : Upper (D 7) (R 7) [6,96,160,65,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2350 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 146 288 80 137 265), lower := (rows 7 98 164 73 146 288 80 128 256), losses := [] }

theorem u2351 : Upper (D 7) (R 7) [6,96,160,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2351 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 98 164 73 152 288 65 146 274), lower := (rows 7 98 164 73 152 288 65 128 256), losses := [] }

theorem u2352 : Upper (D 7) (R 7) [6,96,160,65,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2352 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 98 164 73 152 288 66 145 273), lower := (rows 7 98 164 73 152 288 66 128 256), losses := [] }

theorem u2353 : Upper (D 7) (R 7) [6,96,160,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2353 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 73 152 288 80 131 259), lower := (rows 7 98 164 73 152 288 80 128 256), losses := [] }

theorem u2354 : Upper (D 7) (R 7) [6,96,160,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2354 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 98 164 73 273 48 66 136 392), lower := (rows 7 98 164 73 273 48 66 128 256), losses := [] }

theorem u2355 : Upper (D 7) (R 7) [6,96,160,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2355 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 73 273 48 72 130 386), lower := (rows 7 98 164 73 273 48 72 128 256), losses := [] }

theorem u2356 : Upper (D 7) (R 7) [6,96,160,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2356 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 306, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 164 73 273 48 192 138 266), lower := (rows 7 98 164 73 273 48 192 128 256), losses := [] }

theorem u2357 : Upper (D 7) (R 7) [6,96,160,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2357 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 274 33 72 144 400), lower := (rows 7 98 164 73 274 33 72 128 256), losses := [] }

theorem u2358 : Upper (D 7) (R 7) [6,96,160,65,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2358 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 164, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 164 73 274 33 80 136 392), lower := (rows 7 98 164 73 274 33 80 128 256), losses := [] }

theorem u2359 : Upper (D 7) (R 7) [6,96,160,65,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2359 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 306, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 73 274 33 192 152 280), lower := (rows 7 98 164 73 274 33 192 128 256), losses := [] }

theorem u2360 : Upper (D 7) (R 7) [6,96,160,65,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 164 73 280 33 66 144 400), lower := (rows 7 98 164 73 280 33 66 128 256), losses := [] }

theorem u2361 : Upper (D 7) (R 7) [6,96,160,65,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2362 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 73 280 33 80 130 386), lower := (rows 7 98 164 73 280 33 80 128 256), losses := [] }

theorem u2362 : Upper (D 7) (R 7) [6,96,160,65,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2362 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2363 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 306, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 73 280 33 192 146 274), lower := (rows 7 98 164 73 280 33 192 128 256), losses := [] }

theorem u2363 : Upper (D 7) (R 7) [6,96,160,65,264,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 7 98 164 73 400 33 66 152 280), lower := (rows 7 98 164 73 400 33 66 128 256), losses := [] }

theorem u2364 : Upper (D 7) (R 7) [6,96,160,65,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 73 400 33 72 146 274), lower := (rows 7 98 164 73 400 33 72 128 256), losses := [] }

theorem u2365 : Upper (D 7) (R 7) [6,96,160,65,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2365 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7),(3,5),(4,5)], upper := (rows 7 98 164 73 400 33 80 138 266), lower := (rows 7 98 164 73 400 33 80 128 256), losses := [] }

theorem u2366 : Upper (D 7) (R 7) [6,96,160,65,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2366 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 164 88 146 288 65 137 265), lower := (rows 7 98 164 88 146 288 65 128 256), losses := [] }

theorem u2367 : Upper (D 7) (R 7) [6,96,160,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2367 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 98 164 88 146 288 72 129 257), lower := (rows 7 98 164 88 146 288 72 128 256), losses := [] }

theorem u2368 : Upper (D 7) (R 7) [6,96,160,80,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2368 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 88 273 33 66 136 392), lower := (rows 7 98 164 88 273 33 66 128 256), losses := [] }

theorem u2369 : Upper (D 7) (R 7) [6,96,160,80,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 88 273 33 72 130 386), lower := (rows 7 98 164 88 273 33 72 128 256), losses := [] }

theorem u2370 : Upper (D 7) (R 7) [6,96,160,80,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2370 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 88 273 33 192 138 266), lower := (rows 7 98 164 88 273 33 192 128 256), losses := [{ target := 7, region := (rows 1 10 4 10 49 49 64 0 267), good := (rows 319 378 52 378 305 305 64 0 256) }] }

theorem u2371 : Upper (D 7) (R 7) [6,96,160,80,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 88 274 33 65 136 392), lower := (rows 7 98 164 88 274 33 65 128 256), losses := [] }

theorem u2372 : Upper (D 7) (R 7) [6,96,160,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 164 88 274 33 72 129 385), lower := (rows 7 98 164 88 274 33 72 128 256), losses := [] }

theorem u2373 : Upper (D 7) (R 7) [6,96,160,80,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2373 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2374 : Route 9 := (fun mask => (mask,id))

def c2374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2374 : Upper (D 7) (R 7) [6,96,160,80,258,1,128] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,258,1,128] 13 (by decide) (choices 1) [1,8] r2374 c2374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u146
  · exact u147

def b2375 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 88 400 33 65 138 266), lower := (rows 7 98 164 88 400 33 65 128 256), losses := [] }

theorem u2375 : Upper (D 7) (R 7) [6,96,160,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 88 400 33 66 137 265), lower := (rows 7 98 164 88 400 33 66 128 256), losses := [] }

theorem u2376 : Upper (D 7) (R 7) [6,96,160,80,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 98 164 88 400 33 72 131 259), lower := (rows 7 98 164 88 400 33 72 128 256), losses := [] }

theorem u2377 : Upper (D 7) (R 7) [6,96,160,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2377 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 140, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 138 273 48 65 200 328), lower := (rows 7 98 164 138 273 48 65 128 256), losses := [] }

theorem u2378 : Upper (D 7) (R 7) [6,96,160,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2378 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 98 164 138 273 48 72 193 321), lower := (rows 7 98 164 138 273 48 72 128 256), losses := [] }

theorem u2379 : Upper (D 7) (R 7) [6,96,160,130,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2379 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 152 274 33 65 200 328), lower := (rows 7 98 164 152 274 33 65 128 256), losses := [] }

theorem u2380 : Upper (D 7) (R 7) [6,96,160,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2381 : Route 9 := (fun mask => (mask,id))

def c2381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2381 : Upper (D 7) (R 7) [6,96,160,144,258,1,8] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144,258,1,8] 13 (by decide) (choices 1) [1,64] r2381 c2381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u148
  · exact u149

def b2382 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 152 336 33 65 138 266), lower := (rows 7 98 164 152 336 33 65 128 256), losses := [] }

theorem u2382 : Upper (D 7) (R 7) [6,96,160,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 164 152 336 33 66 137 265), lower := (rows 7 98 164 152 336 33 66 128 256), losses := [] }

theorem u2383 : Upper (D 7) (R 7) [6,96,160,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 152 336 33 72 131 259), lower := (rows 7 98 164 152 336 33 72 128 256), losses := [] }

theorem u2384 : Upper (D 7) (R 7) [6,96,160,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2384 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 74, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 7 98 164 200 273 33 66 152 280), lower := (rows 7 98 164 200 273 33 66 128 256), losses := [] }

theorem u2385 : Upper (D 7) (R 7) [6,96,160,192,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 200 273 33 72 146 274), lower := (rows 7 98 164 200 273 33 72 128 256), losses := [] }

theorem u2386 : Upper (D 7) (R 7) [6,96,160,192,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2386 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 140, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 200 273 33 80 138 266), lower := (rows 7 98 164 200 273 33 80 128 256), losses := [] }

theorem u2387 : Upper (D 7) (R 7) [6,96,160,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2387 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 140, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 98 164 200 273 48 65 138 266), lower := (rows 7 98 164 200 273 48 65 128 256), losses := [] }

theorem u2388 : Upper (D 7) (R 7) [6,96,160,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2388 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 164 200 273 48 66 137 265), lower := (rows 7 98 164 200 273 48 66 128 256), losses := [] }

theorem u2389 : Upper (D 7) (R 7) [6,96,160,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2389 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 200 273 48 72 131 259), lower := (rows 7 98 164 200 273 48 72 128 256), losses := [] }

theorem u2390 : Upper (D 7) (R 7) [6,96,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2390 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 200 274 33 65 152 280), lower := (rows 7 98 164 200 274 33 65 128 256), losses := [] }

theorem u2391 : Upper (D 7) (R 7) [6,96,160,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 164 200 274 33 72 145 273), lower := (rows 7 98 164 200 274 33 72 128 256), losses := [] }

theorem u2392 : Upper (D 7) (R 7) [6,96,160,192,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2392 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2393 : Route 9 := (fun mask => (mask,id))

def c2393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2393 : Upper (D 7) (R 7) [6,96,160,192,258,1,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,258,1,16] 13 (by decide) (choices 1) [1,8] r2393 c2393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u150
  · exact u151

def b2394 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,0),(3,5),(4,0)], upper := (rows 7 98 164 200 280 33 65 146 274), lower := (rows 7 98 164 200 280 33 65 128 256), losses := [] }

theorem u2394 : Upper (D 7) (R 7) [6,96,160,192,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 74, targets := 1 }], pairs := [(1,0),(3,0),(3,5),(4,5)], upper := (rows 7 98 164 200 280 33 66 145 273), lower := (rows 7 98 164 200 280 33 66 128 256), losses := [] }

theorem u2395 : Upper (D 7) (R 7) [6,96,160,192,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 164 200 280 33 80 131 259), lower := (rows 7 98 164 200 280 33 80 128 256), losses := [] }

theorem u2396 : Upper (D 7) (R 7) [6,96,160,192,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2396 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 98 261 25 146 40 192 224 352), lower := (rows 7 98 261 25 146 40 192 128 256), losses := [] }

theorem u2397 : Upper (D 7) (R 7) [6,96,257,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2397 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 25 146 96 192 168 296), lower := (rows 7 98 261 25 146 96 192 128 256), losses := [] }

theorem u2398 : Upper (D 7) (R 7) [6,96,257,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 261, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 98 261 26 145 40 192 224 352), lower := (rows 7 98 261 26 145 40 192 128 256), losses := [] }

theorem u2399 : Upper (D 7) (R 7) [6,96,257,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2399 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P07
