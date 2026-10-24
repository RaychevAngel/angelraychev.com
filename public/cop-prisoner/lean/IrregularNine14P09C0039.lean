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

def b2340 : PairBound 9 := { available := 264, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 280, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 88 273 34 192 392 264), lower := (rows 97 7 164 88 273 34 192 128 256), losses := [] }

theorem u2340 : Upper (D 9) (R 9) [96,5,160,80,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2340 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2341 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 88 273 34 320 136 392), lower := (rows 97 7 164 88 273 34 320 128 256), losses := [] }

theorem u2341 : Upper (D 9) (R 9) [96,5,160,80,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2341 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 88 273 288 66 136 392), lower := (rows 97 7 164 88 273 288 66 128 256), losses := [] }

theorem u2342 : Upper (D 9) (R 9) [96,5,160,80,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2342 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 5, region := 89, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 7 164 88 273 288 72 130 386), lower := (rows 97 7 164 88 273 288 72 128 256), losses := [] }

theorem u2343 : Upper (D 9) (R 9) [96,5,160,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2343 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 88 273 288 192 138 266), lower := (rows 97 7 164 88 273 288 192 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 16 304 64 0 256), good := (rows 97 7 36 121 305 288 64 0 288) }] }

theorem u2344 : Upper (D 9) (R 9) [96,5,160,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2344 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 164 88 274 288 65 136 392), lower := (rows 97 7 164 88 274 288 65 128 256), losses := [] }

theorem u2345 : Upper (D 9) (R 9) [96,5,160,80,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2345 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 0, region := 134, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(4,6)], upper := (rows 97 7 164 88 274 288 72 129 385), lower := (rows 97 7 164 88 274 288 72 128 256), losses := [] }

theorem u2346 : Upper (D 9) (R 9) [96,5,160,80,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2346 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 },{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 88 274 288 192 137 265), lower := (rows 97 7 164 88 274 288 192 128 256), losses := [] }

theorem u2347 : Upper (D 9) (R 9) [96,5,160,80,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2347 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2348 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 88 400 34 65 392 264), lower := (rows 97 7 164 88 400 34 65 128 256), losses := [] }

theorem u2348 : Upper (D 9) (R 9) [96,5,160,80,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2348 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 88 400 34 72 385 257), lower := (rows 97 7 164 88 400 34 72 128 256), losses := [] }

theorem u2349 : Upper (D 9) (R 9) [96,5,160,80,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2349 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 7 164 88 400 34 320 137 265), lower := (rows 97 7 164 88 400 34 320 128 256), losses := [] }

theorem u2350 : Upper (D 9) (R 9) [96,5,160,80,384,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2350 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 164 137 274 48 72 448 320), lower := (rows 97 7 164 137 274 48 72 128 256), losses := [] }

theorem u2351 : Upper (D 9) (R 9) [96,5,160,129,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2351 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 137 274 48 320 200 328), lower := (rows 97 7 164 137 274 48 320 128 256), losses := [] }

theorem u2352 : Upper (D 9) (R 9) [96,5,160,129,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2352 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 137 274 288 72 208 336), lower := (rows 97 7 164 137 274 288 72 128 256), losses := [] }

theorem u2353 : Upper (D 9) (R 9) [96,5,160,129,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2353 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 137 274 288 80 200 328), lower := (rows 97 7 164 137 274 288 80 128 256), losses := [] }

theorem u2354 : Upper (D 9) (R 9) [96,5,160,129,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2354 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 137 280 288 66 208 336), lower := (rows 97 7 164 137 280 288 66 128 256), losses := [] }

theorem u2355 : Upper (D 9) (R 9) [96,5,160,129,264,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2355 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 137 280 288 80 194 322), lower := (rows 97 7 164 137 280 288 80 128 256), losses := [] }

theorem u2356 : Upper (D 9) (R 9) [96,5,160,129,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2356 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 137 336 288 66 152 280), lower := (rows 97 7 164 137 336 288 66 128 256), losses := [] }

theorem u2357 : Upper (D 9) (R 9) [96,5,160,129,320,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2357 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 137 336 288 72 146 274), lower := (rows 97 7 164 137 336 288 72 128 256), losses := [] }

theorem u2358 : Upper (D 9) (R 9) [96,5,160,129,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2358 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 164 137 336 288 80 138 266), lower := (rows 97 7 164 137 336 288 80 128 256), losses := [] }

theorem u2359 : Upper (D 9) (R 9) [96,5,160,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2359 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 138 273 288 72 208 336), lower := (rows 97 7 164 138 273 288 72 128 256), losses := [] }

theorem u2360 : Upper (D 9) (R 9) [96,5,160,130,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2360 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 138 273 288 80 200 328), lower := (rows 97 7 164 138 273 288 80 128 256), losses := [] }

theorem u2361 : Upper (D 9) (R 9) [96,5,160,130,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2361 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2362 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 138 280 288 65 208 336), lower := (rows 97 7 164 138 280 288 65 128 256), losses := [] }

theorem u2362 : Upper (D 9) (R 9) [96,5,160,130,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2363 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 138 280 288 80 193 321), lower := (rows 97 7 164 138 280 288 80 128 256), losses := [] }

theorem u2363 : Upper (D 9) (R 9) [96,5,160,130,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2363 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 138 336 288 65 152 280), lower := (rows 97 7 164 138 336 288 65 128 256), losses := [] }

theorem u2364 : Upper (D 9) (R 9) [96,5,160,130,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 138 336 288 72 145 273), lower := (rows 97 7 164 138 336 288 72 128 256), losses := [] }

theorem u2365 : Upper (D 9) (R 9) [96,5,160,130,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2365 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 164 138 336 288 80 137 265), lower := (rows 97 7 164 138 336 288 80 128 256), losses := [] }

theorem u2366 : Upper (D 9) (R 9) [96,5,160,130,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2366 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 152 273 34 72 448 320), lower := (rows 97 7 164 152 273 34 72 128 256), losses := [] }

theorem u2367 : Upper (D 9) (R 9) [96,5,160,144,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2367 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2368 : Route 9 := (fun mask => (mask,id))

def c2368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2368 : Upper (D 9) (R 9) [96,5,160,144,257,2,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,257,2,256] 13 (by decide) (choices 1) [8,64] r2368 c2368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u138
  · exact u139

def b2369 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 152 273 288 66 200 328), lower := (rows 97 7 164 152 273 288 66 128 256), losses := [] }

theorem u2369 : Upper (D 9) (R 9) [96,5,160,144,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2369 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 7 164 152 273 288 72 194 322), lower := (rows 97 7 164 152 273 288 72 128 256), losses := [] }

theorem u2370 : Upper (D 9) (R 9) [96,5,160,144,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2370 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 152 336 34 65 392 264), lower := (rows 97 7 164 152 336 34 65 128 256), losses := [] }

theorem u2371 : Upper (D 9) (R 9) [96,5,160,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2371 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 152 336 34 72 385 257), lower := (rows 97 7 164 152 336 34 72 128 256), losses := [] }

theorem u2372 : Upper (D 9) (R 9) [96,5,160,144,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2372 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 152 336 34 320 137 265), lower := (rows 97 7 164 152 336 34 320 128 256), losses := [] }

theorem u2373 : Upper (D 9) (R 9) [96,5,160,144,320,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2373 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 164 200 273 48 66 392 264), lower := (rows 97 7 164 200 273 48 66 128 256), losses := [] }

theorem u2374 : Upper (D 9) (R 9) [96,5,160,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2374 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 273 48 72 386 258), lower := (rows 97 7 164 200 273 48 72 128 256), losses := [] }

theorem u2375 : Upper (D 9) (R 9) [96,5,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2375 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 200 273 48 320 138 266), lower := (rows 97 7 164 200 273 48 320 128 256), losses := [] }

theorem u2376 : Upper (D 9) (R 9) [96,5,160,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2376 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 200 273 288 66 152 280), lower := (rows 97 7 164 200 273 288 66 128 256), losses := [] }

theorem u2377 : Upper (D 9) (R 9) [96,5,160,192,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2377 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 73, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 273 288 72 146 274), lower := (rows 97 7 164 200 273 288 72 128 256), losses := [] }

theorem u2378 : Upper (D 9) (R 9) [96,5,160,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2378 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 200 273 288 80 138 266), lower := (rows 97 7 164 200 273 288 80 128 256), losses := [] }

theorem u2379 : Upper (D 9) (R 9) [96,5,160,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2379 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 396, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 97 7 164 200 274 48 65 392 264), lower := (rows 97 7 164 200 274 48 65 128 256), losses := [] }

theorem u2380 : Upper (D 9) (R 9) [96,5,160,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2380 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 274 48 72 385 257), lower := (rows 97 7 164 200 274 48 72 128 256), losses := [] }

theorem u2381 : Upper (D 9) (R 9) [96,5,160,192,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2381 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 200 274 48 320 137 265), lower := (rows 97 7 164 200 274 48 320 128 256), losses := [] }

theorem u2382 : Upper (D 9) (R 9) [96,5,160,192,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2382 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 200 274 288 65 152 280), lower := (rows 97 7 164 200 274 288 65 128 256), losses := [] }

theorem u2383 : Upper (D 9) (R 9) [96,5,160,192,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2383 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 73, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 274 288 72 145 273), lower := (rows 97 7 164 200 274 288 72 128 256), losses := [] }

theorem u2384 : Upper (D 9) (R 9) [96,5,160,192,258,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2384 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 164 200 274 288 80 137 265), lower := (rows 97 7 164 200 274 288 80 128 256), losses := [] }

theorem u2385 : Upper (D 9) (R 9) [96,5,160,192,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2385 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 97 7 164 200 280 288 65 146 274), lower := (rows 97 7 164 200 280 288 65 128 256), losses := [] }

theorem u2386 : Upper (D 9) (R 9) [96,5,160,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2386 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 97 7 164 200 280 288 66 145 273), lower := (rows 97 7 164 200 280 288 66 128 256), losses := [] }

theorem u2387 : Upper (D 9) (R 9) [96,5,160,192,264,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2387 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(1,8),(2,8),(3,8)], upper := (rows 97 7 164 200 280 288 80 131 259), lower := (rows 97 7 164 200 280 288 80 128 256), losses := [] }

theorem u2388 : Upper (D 9) (R 9) [96,5,160,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2388 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5)], upper := (rows 97 7 164 265 274 40 80 192 448), lower := (rows 97 7 164 265 274 40 80 128 256), losses := [] }

theorem u2389 : Upper (D 9) (R 9) [96,5,160,257,258,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2389 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 265 274 40 192 208 336), lower := (rows 97 7 164 265 274 40 192 128 256), losses := [] }

theorem u2390 : Upper (D 9) (R 9) [96,5,160,257,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2390 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5)], upper := (rows 97 7 164 265 274 48 72 192 448), lower := (rows 97 7 164 265 274 48 72 128 256), losses := [] }

theorem u2391 : Upper (D 9) (R 9) [96,5,160,257,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2391 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 265 274 48 192 200 328), lower := (rows 97 7 164 265 274 48 192 128 256), losses := [] }

theorem u2392 : Upper (D 9) (R 9) [96,5,160,257,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2392 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 265 336 34 72 144 400), lower := (rows 97 7 164 265 336 34 72 128 256), losses := [] }

theorem u2393 : Upper (D 9) (R 9) [96,5,160,257,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2393 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2394 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 7 164 265 336 34 80 136 392), lower := (rows 97 7 164 265 336 34 80 128 256), losses := [] }

theorem u2394 : Upper (D 9) (R 9) [96,5,160,257,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2394 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 280, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 265 336 34 192 152 280), lower := (rows 97 7 164 265 336 34 192 128 256), losses := [] }

theorem u2395 : Upper (D 9) (R 9) [96,5,160,257,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2395 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 404, targets := 1 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,0),(3,5),(4,0)], upper := (rows 97 7 164 265 400 34 72 208 336), lower := (rows 97 7 164 265 400 34 72 128 256), losses := [] }

theorem u2396 : Upper (D 9) (R 9) [96,5,160,257,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2396 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 265 400 34 80 200 328), lower := (rows 97 7 164 265 400 34 80 128 256), losses := [] }

theorem u2397 : Upper (D 9) (R 9) [96,5,160,257,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2397 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7)], upper := (rows 97 7 164 265 400 40 66 208 336), lower := (rows 97 7 164 265 400 40 66 128 256), losses := [] }

theorem u2398 : Upper (D 9) (R 9) [96,5,160,257,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2398 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5)], upper := (rows 97 7 164 265 400 40 80 194 322), lower := (rows 97 7 164 265 400 40 80 128 256), losses := [] }

theorem u2399 : Upper (D 9) (R 9) [96,5,160,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2399 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P09
