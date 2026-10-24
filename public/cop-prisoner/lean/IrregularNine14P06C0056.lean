import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 52 140 276 33 65 194 322), lower := (rows 11 98 52 140 276 33 65 128 256), losses := [] }

theorem u3360 : Upper (D 6) (R 6) [10,96,48,132,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 52 140 276 33 66 193 321), lower := (rows 11 98 52 140 276 33 66 128 256), losses := [] }

theorem u3361 : Upper (D 6) (R 6) [10,96,48,132,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 52 140 336 33 65 134 262), lower := (rows 11 98 52 140 336 33 65 128 256), losses := [] }

theorem u3362 : Upper (D 6) (R 6) [10,96,48,132,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3363 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 52 140 336 33 66 133 261), lower := (rows 11 98 52 140 336 33 66 128 256), losses := [] }

theorem u3363 : Upper (D 6) (R 6) [10,96,48,132,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3364 : Route 9 := (fun mask => (mask,id))

def c3364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3364 : Upper (D 6) (R 6) [10,96,48,132,320,1,4] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,320,1,4] 13 (by decide) (choices 1) [1,2] r3364 c3364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u242
  · exact u243

def b3365 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 98 133 28 273 34 68 224 352), lower := (rows 11 98 133 28 273 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 5 29 17 32 93 130 258), good := (rows 477 480 221 92 349 416 76 128 256) }] }

theorem u3365 : Upper (D 6) (R 6) [10,96,129,20,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 28 273 34 96 196 324), lower := (rows 11 98 133 28 273 34 96 128 256), losses := [] }

theorem u3366 : Upper (D 6) (R 6) [10,96,129,20,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 98 133 28 274 33 68 224 352), lower := (rows 11 98 133 28 274 33 68 128 256), losses := [] }

theorem u3367 : Upper (D 6) (R 6) [10,96,129,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 28 274 33 96 196 324), lower := (rows 11 98 133 28 274 33 96 128 256), losses := [] }

theorem u3368 : Upper (D 6) (R 6) [10,96,129,20,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 28 274 36 96 193 321), lower := (rows 11 98 133 28 274 36 96 128 256), losses := [] }

theorem u3369 : Upper (D 6) (R 6) [10,96,129,20,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 98 133 28 304 33 66 196 324), lower := (rows 11 98 133 28 304 33 66 128 256), losses := [] }

theorem u3370 : Upper (D 6) (R 6) [10,96,129,20,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 98 133 28 304 33 68 194 322), lower := (rows 11 98 133 28 304 33 68 128 256), losses := [] }

theorem u3371 : Upper (D 6) (R 6) [10,96,129,20,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 98 133 28 304 36 65 194 322), lower := (rows 11 98 133 28 304 36 65 128 256), losses := [] }

theorem u3372 : Upper (D 6) (R 6) [10,96,129,20,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 5 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(1,2),(2,5)], upper := (rows 11 98 133 28 304 36 66 193 321), lower := (rows 11 98 133 28 304 36 66 128 256), losses := [] }

theorem u3373 : Upper (D 6) (R 6) [10,96,129,20,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 265, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 98 133 265 22 36 80 224 352), lower := (rows 11 98 133 265 22 36 80 128 256), losses := [] }

theorem u3374 : Upper (D 6) (R 6) [10,96,129,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3374 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 265 22 36 96 208 336), lower := (rows 11 98 133 265 22 36 96 128 256), losses := [] }

theorem u3375 : Upper (D 6) (R 6) [10,96,129,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 96, camps := [], pairs := [(2,1),(3,0)], upper := (rows 11 98 133 268 22 33 80 224 352), lower := (rows 11 98 133 268 22 33 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 80 130 258), good := (rows 394 482 132 268 478 32 88 128 256) },{ target := 1, region := (rows 1 0 5 25 16 37 80 146 274), good := (rows 429 480 173 300 508 45 472 128 256) }] }

theorem u3376 : Upper (D 6) (R 6) [10,96,129,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3376 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 268 22 33 96 208 336), lower := (rows 11 98 133 268 22 33 96 128 256), losses := [] }

theorem u3377 : Upper (D 6) (R 6) [10,96,129,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 133 268 22 48 96 193 321), lower := (rows 11 98 133 268 22 48 96 128 256), losses := [] }

theorem u3378 : Upper (D 6) (R 6) [10,96,129,260,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3378 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 98 133 280 22 33 68 224 352), lower := (rows 11 98 133 280 22 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 84 130 258), good := (rows 394 482 196 344 478 32 68 128 256) },{ target := 1, region := (rows 1 0 37 24 16 37 119 247 375), good := (rows 493 484 485 472 508 485 484 128 256) }] }

theorem u3379 : Upper (D 6) (R 6) [10,96,129,272,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 280 22 33 96 196 324), lower := (rows 11 98 133 280 22 33 96 128 256), losses := [] }

theorem u3380 : Upper (D 6) (R 6) [10,96,129,272,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 133 280 22 36 96 193 321), lower := (rows 11 98 133 280 22 36 96 128 256), losses := [] }

theorem u3381 : Upper (D 6) (R 6) [10,96,129,272,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3382 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 133 296 22 36 65 208 336), lower := (rows 11 98 133 296 22 36 65 128 256), losses := [] }

theorem u3382 : Upper (D 6) (R 6) [10,96,129,288,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 133 296 22 36 80 193 321), lower := (rows 11 98 133 296 22 36 80 128 256), losses := [] }

theorem u3383 : Upper (D 6) (R 6) [10,96,129,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3383 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 133 296 81 36 66 148 276), lower := (rows 11 98 133 296 81 36 66 128 256), losses := [] }

theorem u3384 : Upper (D 6) (R 6) [10,96,129,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 133 296 81 36 68 146 274), lower := (rows 11 98 133 296 81 36 68 128 256), losses := [] }

theorem u3385 : Upper (D 6) (R 6) [10,96,129,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3386 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 133 296 81 36 80 134 262), lower := (rows 11 98 133 296 81 36 80 128 256), losses := [] }

theorem u3386 : Upper (D 6) (R 6) [10,96,129,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3386 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 98 134 25 52 288 65 196 324), lower := (rows 11 98 134 25 52 288 65 128 256), losses := [] }

theorem u3387 : Upper (D 6) (R 6) [10,96,130,17,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3387 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(2,5)], upper := (rows 11 98 134 25 52 288 68 193 321), lower := (rows 11 98 134 25 52 288 68 128 256), losses := [] }

theorem u3388 : Upper (D 6) (R 6) [10,96,130,17,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3388 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 134 25 276 33 68 224 352), lower := (rows 11 98 134 25 276 33 68 128 256), losses := [] }

theorem u3389 : Upper (D 6) (R 6) [10,96,130,17,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 134 25 276 36 96 193 321), lower := (rows 11 98 134 25 276 36 96 128 256), losses := [] }

theorem u3390 : Upper (D 6) (R 6) [10,96,130,17,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 134 25 304 36 65 196 324), lower := (rows 11 98 134 25 304 36 65 128 256), losses := [] }

theorem u3391 : Upper (D 6) (R 6) [10,96,130,17,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 25 304 36 68 193 321), lower := (rows 11 98 134 25 304 36 68 128 256), losses := [] }

theorem u3392 : Upper (D 6) (R 6) [10,96,130,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 98 134 28 273 33 68 224 352), lower := (rows 11 98 134 28 273 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 39 24 16 32 127 162 290), good := (rows 462 486 454 92 348 486 68 128 256) }] }

theorem u3393 : Upper (D 6) (R 6) [10,96,130,20,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 134 28 273 36 96 193 321), lower := (rows 11 98 134 28 273 36 96 128 256), losses := [] }

theorem u3394 : Upper (D 6) (R 6) [10,96,130,20,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 134 28 304 33 65 196 324), lower := (rows 11 98 134 28 304 33 65 128 256), losses := [] }

theorem u3395 : Upper (D 6) (R 6) [10,96,130,20,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3396 : Route 9 := (fun mask => (mask,id))

def c3396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3396 : Upper (D 6) (R 6) [10,96,130,20,288,1,4] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,288,1,4] 13 (by decide) (choices 1) [1,64] r3396 c3396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u244
  · exact u245

def b3397 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 98 134 28 304 36 65 193 321), lower := (rows 11 98 134 28 304 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 44 65 193 321), good := (rows 505 496 188 60 304 44 465 128 256) }] }

theorem u3397 : Upper (D 6) (R 6) [10,96,130,20,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 134 56 273 36 65 196 324), lower := (rows 11 98 134 56 273 36 65 128 256), losses := [] }

theorem u3398 : Upper (D 6) (R 6) [10,96,130,48,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 56 273 36 68 193 321), lower := (rows 11 98 134 56 273 36 68 128 256), losses := [] }

theorem u3399 : Upper (D 6) (R 6) [10,96,130,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 134 56 276 33 65 196 324), lower := (rows 11 98 134 56 276 33 65 128 256), losses := [] }

theorem u3400 : Upper (D 6) (R 6) [10,96,130,48,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 134 56 276 33 68 193 321), lower := (rows 11 98 134 56 276 33 68 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 84 128 256), good := (rows 10 98 198 122 340 32 68 128 256) }] }

theorem u3401 : Upper (D 6) (R 6) [10,96,130,48,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 265 49 36 68 208 336), lower := (rows 11 98 134 265 49 36 68 128 256), losses := [] }

theorem u3402 : Upper (D 6) (R 6) [10,96,130,257,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 134 265 49 36 80 196 324), lower := (rows 11 98 134 265 49 36 80 128 256), losses := [] }

theorem u3403 : Upper (D 6) (R 6) [10,96,130,257,33,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3403 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 98 134 268 21 33 80 224 352), lower := (rows 11 98 134 268 21 33 80 128 256), losses := [] }

theorem u3404 : Upper (D 6) (R 6) [10,96,130,260,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3404 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 134 268 21 33 96 208 336), lower := (rows 11 98 134 268 21 33 96 128 256), losses := [] }

theorem u3405 : Upper (D 6) (R 6) [10,96,130,260,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 134 268 52 33 65 208 336), lower := (rows 11 98 134 268 52 33 65 128 256), losses := [] }

theorem u3406 : Upper (D 6) (R 6) [10,96,130,260,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 98 134 268 52 33 80 193 321), lower := (rows 11 98 134 268 52 33 80 128 256), losses := [] }

theorem u3407 : Upper (D 6) (R 6) [10,96,130,260,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3407 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 98 134 280 21 33 68 224 352), lower := (rows 11 98 134 280 21 33 68 128 256), losses := [] }

theorem u3408 : Upper (D 6) (R 6) [10,96,130,272,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3409 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 134 280 21 36 96 193 321), lower := (rows 11 98 134 280 21 36 96 128 256), losses := [] }

theorem u3409 : Upper (D 6) (R 6) [10,96,130,272,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3410 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 98 134 280 49 36 65 196 324), lower := (rows 11 98 134 280 49 36 65 128 256), losses := [] }

theorem u3410 : Upper (D 6) (R 6) [10,96,130,272,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3411 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 280 49 36 68 193 321), lower := (rows 11 98 134 280 49 36 68 128 256), losses := [] }

theorem u3411 : Upper (D 6) (R 6) [10,96,130,272,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3412 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 134 280 52 33 65 196 324), lower := (rows 11 98 134 280 52 33 65 128 256), losses := [] }

theorem u3412 : Upper (D 6) (R 6) [10,96,130,272,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 98 134 280 52 33 68 193 321), lower := (rows 11 98 134 280 52 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 7 24 16 0 119 161 289), good := (rows 463 454 198 344 476 453 68 128 256) }] }

theorem u3413 : Upper (D 6) (R 6) [10,96,130,272,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 134 296 81 36 65 148 276), lower := (rows 11 98 134 296 81 36 65 128 256), losses := [] }

theorem u3414 : Upper (D 6) (R 6) [10,96,130,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3415 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 296 81 36 68 145 273), lower := (rows 11 98 134 296 81 36 68 128 256), losses := [] }

theorem u3415 : Upper (D 6) (R 6) [10,96,130,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3416 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 296 81 36 80 133 261), lower := (rows 11 98 134 296 81 36 80 128 256), losses := [] }

theorem u3416 : Upper (D 6) (R 6) [10,96,130,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3416 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 134 296 84 33 65 148 276), lower := (rows 11 98 134 296 84 33 65 128 256), losses := [] }

theorem u3417 : Upper (D 6) (R 6) [10,96,130,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 98 134 296 84 33 68 145 273), lower := (rows 11 98 134 296 84 33 68 128 256), losses := [] }

theorem u3418 : Upper (D 6) (R 6) [10,96,130,288,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3419 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 134 296 84 33 80 133 261), lower := (rows 11 98 134 296 84 33 80 128 256), losses := [] }

theorem u3419 : Upper (D 6) (R 6) [10,96,130,288,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3419 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P06
