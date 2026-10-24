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

def b2340 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 84 200 304 36 68 131 259), lower := (rows 11 35 84 200 304 36 68 128 256), losses := [] }

theorem u2340 : Upper (D 6) (R 6) [10,33,80,192,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2341 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 424, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 35 84 392 21 96 66 164 292), lower := (rows 11 35 84 392 21 96 66 128 256), losses := [] }

theorem u2341 : Upper (D 6) (R 6) [10,33,80,384,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 21 96 68 162 290), lower := (rows 11 35 84 392 21 96 68 128 256), losses := [] }

theorem u2342 : Upper (D 6) (R 6) [10,33,80,384,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 35 84 392 21 96 96 134 262), lower := (rows 11 35 84 392 21 96 96 128 256), losses := [] }

theorem u2343 : Upper (D 6) (R 6) [10,33,80,384,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 424, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 35 84 392 22 96 65 164 292), lower := (rows 11 35 84 392 22 96 65 128 256), losses := [] }

theorem u2344 : Upper (D 6) (R 6) [10,33,80,384,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 84 392 22 96 68 161 289), lower := (rows 11 35 84 392 22 96 68 128 256), losses := [] }

theorem u2345 : Upper (D 6) (R 6) [10,33,80,384,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 84 392 22 96 96 133 261), lower := (rows 11 35 84 392 22 96 96 128 256), losses := [] }

theorem u2346 : Upper (D 6) (R 6) [10,33,80,384,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 68, targets := 2 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 88 148 288 65 134 262), lower := (rows 11 35 100 88 148 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 76 81 355 64 129 257), good := (rows 446 434 124 124 156 288 508 128 288) }] }

theorem u2347 : Upper (D 6) (R 6) [10,33,96,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2347 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2348 : Route 9 := (fun mask => (mask,id))

def c2348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2348 : Upper (D 6) (R 6) [10,33,96,80,132,256,2] 13 := by
  apply FastRouting.sound _ _ [10,33,96,80,132,256,2] 13 (by decide) (choices 1) [1,4] r2348 c2348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u136
  · exact u137

def b2349 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 291, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 35 100 88 148 288 68 131 259), lower := (rows 11 35 100 88 148 288 68 128 256), losses := [] }

theorem u2349 : Upper (D 6) (R 6) [10,33,96,80,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2349 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 88 400 36 65 134 262), lower := (rows 11 35 100 88 400 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 76 83 109 64 129 257), good := (rows 446 434 124 124 400 44 508 128 256) }] }

theorem u2350 : Upper (D 6) (R 6) [10,33,96,80,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 100 88 400 36 66 133 261), lower := (rows 11 35 100 88 400 36 66 128 256), losses := [{ target := 1, region := (rows 1 0 76 72 19 109 64 129 257), good := (rows 445 433 108 124 400 36 124 128 256) }] }

theorem u2351 : Upper (D 6) (R 6) [10,33,96,80,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 88 400 36 68 131 259), lower := (rows 11 35 100 88 400 36 68 128 256), losses := [] }

theorem u2352 : Upper (D 6) (R 6) [10,33,96,80,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 11 35 100 140 21 288 66 208 336), lower := (rows 11 35 100 140 21 288 66 128 256), losses := [] }

theorem u2353 : Upper (D 6) (R 6) [10,33,96,132,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2353 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1)], upper := (rows 11 35 100 140 21 288 80 194 322), lower := (rows 11 35 100 140 21 288 80 128 256), losses := [] }

theorem u2354 : Upper (D 6) (R 6) [10,33,96,132,5,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2354 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 140 81 288 66 148 276), lower := (rows 11 35 100 140 81 288 66 128 256), losses := [] }

theorem u2355 : Upper (D 6) (R 6) [10,33,96,132,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2355 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 100 140 81 288 68 146 274), lower := (rows 11 35 100 140 81 288 68 128 256), losses := [] }

theorem u2356 : Upper (D 6) (R 6) [10,33,96,132,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2356 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 2 }], pairs := [(4,1)], upper := (rows 11 35 100 140 81 288 80 134 262), lower := (rows 11 35 100 140 81 288 80 128 256), losses := [] }

theorem u2357 : Upper (D 6) (R 6) [10,33,96,132,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2357 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 140 82 288 65 148 276), lower := (rows 11 35 100 140 82 288 65 128 256), losses := [] }

theorem u2358 : Upper (D 6) (R 6) [10,33,96,132,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2358 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 100 140 82 288 68 145 273), lower := (rows 11 35 100 140 82 288 68 128 256), losses := [] }

theorem u2359 : Upper (D 6) (R 6) [10,33,96,132,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2359 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 100 140 82 288 80 133 261), lower := (rows 11 35 100 140 82 288 80 128 256), losses := [] }

theorem u2360 : Upper (D 6) (R 6) [10,33,96,132,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2360 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2361 : Route 9 := (fun mask => (mask,id))

def c2361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2361 : Upper (D 6) (R 6) [10,33,96,132,260,16,1] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,260,16,1] 13 (by decide) (choices 1) [2,64] r2361 c2361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u138
  · exact u139

def r2362 : Route 9 := (fun mask => (mask,id))

def c2362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2362 : Upper (D 6) (R 6) [10,33,96,132,260,16,2] 13 := by
  apply FastRouting.sound _ _ [10,33,96,132,260,16,2] 13 (by decide) (choices 1) [1,64] r2362 c2362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u140
  · exact u141

def r2363 : Route 9 := (fun mask => (mask,id))

def c2363 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2363 : Upper (D 6) (R 6) [10,33,96,144,320,4,1] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,320,4,1] 13 (by decide) (choices 1) [2,4] r2363 c2363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u142
  · exact u143

def r2364 : Route 9 := (fun mask => (mask,id))

def c2364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2364 : Upper (D 6) (R 6) [10,33,96,144,320,4,2] 13 := by
  apply FastRouting.sound _ _ [10,33,96,144,320,4,2] 13 (by decide) (choices 1) [1,4] r2364 c2364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u144
  · exact u145

def b2365 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 152 336 36 68 131 259), lower := (rows 11 35 100 152 336 36 68 128 256), losses := [] }

theorem u2365 : Upper (D 6) (R 6) [10,33,96,144,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 68, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,6),(2,0)], upper := (rows 11 35 100 200 21 288 66 148 276), lower := (rows 11 35 100 200 21 288 66 128 256), losses := [] }

theorem u2366 : Upper (D 6) (R 6) [10,33,96,192,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2366 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 35 100 200 21 288 68 146 274), lower := (rows 11 35 100 200 21 288 68 128 256), losses := [] }

theorem u2367 : Upper (D 6) (R 6) [10,33,96,192,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2367 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 84, targets := 2 }], pairs := [(2,1)], upper := (rows 11 35 100 200 21 288 80 134 262), lower := (rows 11 35 100 200 21 288 80 128 256), losses := [] }

theorem u2368 : Upper (D 6) (R 6) [10,33,96,192,5,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2368 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 200 273 36 66 148 276), lower := (rows 11 35 100 200 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 95 24 16 127 67 144 272), good := (rows 110 102 100 236 508 36 102 128 256) }] }

theorem u2369 : Upper (D 6) (R 6) [10,33,96,192,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 200 273 36 68 146 274), lower := (rows 11 35 100 200 273 36 68 128 256), losses := [] }

theorem u2370 : Upper (D 6) (R 6) [10,33,96,192,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 200 273 36 80 134 262), lower := (rows 11 35 100 200 273 36 80 128 256), losses := [] }

theorem u2371 : Upper (D 6) (R 6) [10,33,96,192,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2371 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 200 274 36 65 148 276), lower := (rows 11 35 100 200 274 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 76 19 109 64 193 321), good := (rows 446 434 492 492 274 44 508 128 256) }] }

theorem u2372 : Upper (D 6) (R 6) [10,33,96,192,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 200 274 36 68 145 273), lower := (rows 11 35 100 200 274 36 68 128 256), losses := [] }

theorem u2373 : Upper (D 6) (R 6) [10,33,96,192,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 200 274 36 80 133 261), lower := (rows 11 35 100 200 274 36 80 128 256), losses := [] }

theorem u2374 : Upper (D 6) (R 6) [10,33,96,192,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2374 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 200 276 36 65 146 274), lower := (rows 11 35 100 200 276 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 81 125 64 131 259), good := (rows 446 434 124 252 308 36 508 128 256) }] }

theorem u2375 : Upper (D 6) (R 6) [10,33,96,192,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 35 100 200 276 36 66 145 273), lower := (rows 11 35 100 200 276 36 66 128 256), losses := [{ target := 1, region := (rows 1 0 76 72 81 125 64 131 259), good := (rows 445 433 124 252 308 36 508 128 256) }] }

theorem u2376 : Upper (D 6) (R 6) [10,33,96,192,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 200 276 36 80 131 259), lower := (rows 11 35 100 200 276 36 80 128 256), losses := [] }

theorem u2377 : Upper (D 6) (R 6) [10,33,96,192,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2377 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 68, targets := 2 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 200 276 48 65 134 262), lower := (rows 11 35 100 200 276 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 81 127 64 129 257), good := (rows 446 434 124 252 308 48 508 128 256) }] }

theorem u2378 : Upper (D 6) (R 6) [10,33,96,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2378 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2379 : Route 9 := (fun mask => (mask,id))

def c2379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2379 : Upper (D 6) (R 6) [10,33,96,192,260,16,2] 13 := by
  apply FastRouting.sound _ _ [10,33,96,192,260,16,2] 13 (by decide) (choices 1) [1,4] r2379 c2379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u146
  · exact u147

def b2380 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 35 100 200 276 48 68 131 259), lower := (rows 11 35 100 200 276 48 68 128 256), losses := [] }

theorem u2380 : Upper (D 6) (R 6) [10,33,96,192,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2380 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 392 81 36 66 148 276), lower := (rows 11 35 100 392 81 36 66 128 256), losses := [] }

theorem u2381 : Upper (D 6) (R 6) [10,33,96,384,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 100 392 81 36 68 146 274), lower := (rows 11 35 100 392 81 36 68 128 256), losses := [] }

theorem u2382 : Upper (D 6) (R 6) [10,33,96,384,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 392 81 36 80 134 262), lower := (rows 11 35 100 392 81 36 80 128 256), losses := [] }

theorem u2383 : Upper (D 6) (R 6) [10,33,96,384,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2383 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 100 392 82 36 65 148 276), lower := (rows 11 35 100 392 82 36 65 128 256), losses := [] }

theorem u2384 : Upper (D 6) (R 6) [10,33,96,384,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 393, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 35 100 392 82 36 68 145 273), lower := (rows 11 35 100 392 82 36 68 128 256), losses := [] }

theorem u2385 : Upper (D 6) (R 6) [10,33,96,384,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 100 392 82 36 80 133 261), lower := (rows 11 35 100 392 82 36 80 128 256), losses := [] }

theorem u2386 : Upper (D 6) (R 6) [10,33,96,384,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2386 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 35 133 28 112 288 66 196 324), lower := (rows 11 35 133 28 112 288 66 128 256), losses := [] }

theorem u2387 : Upper (D 6) (R 6) [10,33,129,20,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2387 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0)], upper := (rows 11 35 133 28 112 288 68 194 322), lower := (rows 11 35 133 28 112 288 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 93 295 76 129 257), good := (rows 506 434 508 124 120 288 124 128 288) }] }

theorem u2388 : Upper (D 6) (R 6) [10,33,129,20,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2388 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 133 28 304 96 66 196 324), lower := (rows 11 35 133 28 304 96 66 128 256), losses := [] }

theorem u2389 : Upper (D 6) (R 6) [10,33,129,20,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 35 133 28 304 96 68 194 322), lower := (rows 11 35 133 28 304 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 23 109 76 129 257), good := (rows 506 434 508 124 304 104 124 128 256) }] }

theorem u2390 : Upper (D 6) (R 6) [10,33,129,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 76 82 288 68 176 304), lower := (rows 11 35 133 76 82 288 68 128 256), losses := [] }

theorem u2391 : Upper (D 6) (R 6) [10,33,129,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2391 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 35 133 76 82 288 80 164 292), lower := (rows 11 35 133 76 82 288 80 128 256), losses := [] }

theorem u2392 : Upper (D 6) (R 6) [10,33,129,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2392 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 133 76 82 288 96 148 276), lower := (rows 11 35 133 76 82 288 96 128 256), losses := [] }

theorem u2393 : Upper (D 6) (R 6) [10,33,129,68,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2393 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2394 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 35 133 76 112 288 66 148 276), lower := (rows 11 35 133 76 112 288 66 128 256), losses := [] }

theorem u2394 : Upper (D 6) (R 6) [10,33,129,68,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2394 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 76 112 288 68 146 274), lower := (rows 11 35 133 76 112 288 68 128 256), losses := [] }

theorem u2395 : Upper (D 6) (R 6) [10,33,129,68,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2395 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 133 76 112 288 80 134 262), lower := (rows 11 35 133 76 112 288 80 128 256), losses := [] }

theorem u2396 : Upper (D 6) (R 6) [10,33,129,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2396 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 133 76 336 48 66 164 292), lower := (rows 11 35 133 76 336 48 66 128 256), losses := [] }

theorem u2397 : Upper (D 6) (R 6) [10,33,129,68,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2397 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 76 336 48 68 162 290), lower := (rows 11 35 133 76 336 48 68 128 256), losses := [] }

theorem u2398 : Upper (D 6) (R 6) [10,33,129,68,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2398 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 133 76 336 48 96 134 262), lower := (rows 11 35 133 76 336 48 96 128 256), losses := [] }

theorem u2399 : Upper (D 6) (R 6) [10,33,129,68,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2399 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P06
