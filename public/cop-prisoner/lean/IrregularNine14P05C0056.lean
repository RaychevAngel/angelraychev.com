import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0016

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 28 50 33 105 169 297), lower := (rows 7 74 388 28 50 33 64 128 256), losses := [] }

theorem u3360 : Upper (D 5) (R 5) [6,72,384,20,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 74 388 28 50 40 97 161 289), lower := (rows 7 74 388 28 50 40 64 128 256), losses := [] }

theorem u3361 : Upper (D 5) (R 5) [6,72,384,20,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 41 28 33 114 178 306), lower := (rows 7 74 388 41 28 33 64 128 256), losses := [] }

theorem u3362 : Upper (D 5) (R 5) [6,72,384,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3363 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 388 41 28 34 113 177 305), lower := (rows 7 74 388 41 28 34 64 128 256), losses := [] }

theorem u3363 : Upper (D 5) (R 5) [6,72,384,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3364 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 74 388 41 28 48 99 163 291), lower := (rows 7 74 388 41 28 48 64 128 256), losses := [] }

theorem u3364 : Upper (D 5) (R 5) [6,72,384,33,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3365 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 41 50 33 92 156 284), lower := (rows 7 74 388 41 50 33 64 128 256), losses := [] }

theorem u3365 : Upper (D 5) (R 5) [6,72,384,33,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 74 388 41 50 36 89 153 281), lower := (rows 7 74 388 41 50 36 64 128 256), losses := [] }

theorem u3366 : Upper (D 5) (R 5) [6,72,384,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 389, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 74 388 41 50 40 85 149 277), lower := (rows 7 74 388 41 50 40 64 128 256), losses := [] }

theorem u3367 : Upper (D 5) (R 5) [6,72,384,33,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 388 41 50 48 77 141 269), lower := (rows 7 74 388 41 50 48 64 128 256), losses := [] }

theorem u3368 : Upper (D 5) (R 5) [6,72,384,33,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 41 52 33 90 154 282), lower := (rows 7 74 388 41 52 33 64 128 256), losses := [] }

theorem u3369 : Upper (D 5) (R 5) [6,72,384,33,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 74 388 41 52 34 89 153 281), lower := (rows 7 74 388 41 52 34 64 128 256), losses := [] }

theorem u3370 : Upper (D 5) (R 5) [6,72,384,33,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 41 52 40 83 147 275), lower := (rows 7 74 388 41 52 40 64 128 256), losses := [] }

theorem u3371 : Upper (D 5) (R 5) [6,72,384,33,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 388 41 52 48 75 139 267), lower := (rows 7 74 388 41 52 48 64 128 256), losses := [] }

theorem u3372 : Upper (D 5) (R 5) [6,72,384,33,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3373 : Route 9 := (fun mask => (mask,id))

def c3373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3373 : Upper (D 5) (R 5) [6,72,384,34,12,1] 13 := by
  apply FastRouting.sound _ _ [6,72,384,34,12,1] 13 (by decide) (choices 1) [1,16,32] r3373 c3373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u992
  · exact u993
  · exact u994

def b3374 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 388 42 28 48 97 161 289), lower := (rows 7 74 388 42 28 48 64 128 256), losses := [] }

theorem u3374 : Upper (D 5) (R 5) [6,72,384,34,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 42 49 33 92 156 284), lower := (rows 7 74 388 42 49 33 64 128 256), losses := [] }

theorem u3375 : Upper (D 5) (R 5) [6,72,384,34,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 42 49 36 89 153 281), lower := (rows 7 74 388 42 49 36 64 128 256), losses := [] }

theorem u3376 : Upper (D 5) (R 5) [6,72,384,34,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 21, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 388 42 49 40 85 149 277), lower := (rows 7 74 388 42 49 40 64 128 256), losses := [] }

theorem u3377 : Upper (D 5) (R 5) [6,72,384,34,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 388 42 49 48 77 141 269), lower := (rows 7 74 388 42 49 48 64 128 256), losses := [] }

theorem u3378 : Upper (D 5) (R 5) [6,72,384,34,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 388 42 52 33 89 153 281), lower := (rows 7 74 388 42 52 33 64 128 256), losses := [] }

theorem u3379 : Upper (D 5) (R 5) [6,72,384,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 388 42 52 40 81 145 273), lower := (rows 7 74 388 42 52 40 64 128 256), losses := [] }

theorem u3380 : Upper (D 5) (R 5) [6,72,384,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 388 42 52 48 73 137 265), lower := (rows 7 74 388 42 52 48 64 128 256), losses := [] }

theorem u3381 : Upper (D 5) (R 5) [6,72,384,34,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3382 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 44 25 33 114 178 306), lower := (rows 7 74 388 44 25 33 64 128 256), losses := [] }

theorem u3382 : Upper (D 5) (R 5) [6,72,384,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 74 388 44 25 34 113 177 305), lower := (rows 7 74 388 44 25 34 64 128 256), losses := [] }

theorem u3383 : Upper (D 5) (R 5) [6,72,384,36,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 74 388 44 25 48 99 163 291), lower := (rows 7 74 388 44 25 48 64 128 256), losses := [] }

theorem u3384 : Upper (D 5) (R 5) [6,72,384,36,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 74 388 44 49 33 90 154 282), lower := (rows 7 74 388 44 49 33 64 128 256), losses := [] }

theorem u3385 : Upper (D 5) (R 5) [6,72,384,36,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3386 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 44 49 34 89 153 281), lower := (rows 7 74 388 44 49 34 64 128 256), losses := [] }

theorem u3386 : Upper (D 5) (R 5) [6,72,384,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 74 388 44 49 40 83 147 275), lower := (rows 7 74 388 44 49 40 64 128 256), losses := [] }

theorem u3387 : Upper (D 5) (R 5) [6,72,384,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 74 388 44 49 48 75 139 267), lower := (rows 7 74 388 44 49 48 64 128 256), losses := [] }

theorem u3388 : Upper (D 5) (R 5) [6,72,384,36,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 388 44 50 33 89 153 281), lower := (rows 7 74 388 44 50 33 64 128 256), losses := [] }

theorem u3389 : Upper (D 5) (R 5) [6,72,384,36,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 389, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 74 388 44 50 40 81 145 273), lower := (rows 7 74 388 44 50 40 64 128 256), losses := [] }

theorem u3390 : Upper (D 5) (R 5) [6,72,384,36,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 74 388 44 50 48 73 137 265), lower := (rows 7 74 388 44 50 48 64 128 256), losses := [] }

theorem u3391 : Upper (D 5) (R 5) [6,72,384,36,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 82 164 41 273 34 76 140 268), lower := (rows 7 82 164 41 273 34 64 128 256), losses := [] }

theorem u3392 : Upper (D 5) (R 5) [6,80,160,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 82 164 41 273 36 74 138 266), lower := (rows 7 82 164 41 273 36 64 128 256), losses := [] }

theorem u3393 : Upper (D 5) (R 5) [6,80,160,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 82 164 41 273 40 78 142 270), lower := (rows 7 82 164 41 273 40 64 128 256), losses := [] }

theorem u3394 : Upper (D 5) (R 5) [6,80,160,33,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 82 164 41 276 33 74 138 266), lower := (rows 7 82 164 41 276 33 64 128 256), losses := [] }

theorem u3395 : Upper (D 5) (R 5) [6,80,160,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3396 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 82 164 41 276 34 73 137 265), lower := (rows 7 82 164 41 276 34 64 128 256), losses := [] }

theorem u3396 : Upper (D 5) (R 5) [6,80,160,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3397 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 82 164 41 276 40 75 139 267), lower := (rows 7 82 164 41 276 40 64 128 256), losses := [] }

theorem u3397 : Upper (D 5) (R 5) [6,80,160,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 82 164 41 280 33 78 142 270), lower := (rows 7 82 164 41 280 33 64 128 256), losses := [] }

theorem u3398 : Upper (D 5) (R 5) [6,80,160,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 82 164 41 280 34 77 141 269), lower := (rows 7 82 164 41 280 34 64 128 256), losses := [] }

theorem u3399 : Upper (D 5) (R 5) [6,80,160,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 82 164 41 280 36 75 139 267), lower := (rows 7 82 164 41 280 36 64 128 256), losses := [] }

theorem u3400 : Upper (D 5) (R 5) [6,80,160,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 82 164 41 280 40 71 135 263), lower := (rows 7 82 164 41 280 40 64 128 256), losses := [] }

theorem u3401 : Upper (D 5) (R 5) [6,80,160,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 42 25 33 332 396 268), lower := (rows 7 82 164 42 25 33 64 128 256), losses := [] }

theorem u3402 : Upper (D 5) (R 5) [6,80,160,34,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 265, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 25 36 329 393 265), lower := (rows 7 82 164 42 25 36 64 128 256), losses := [] }

theorem u3403 : Upper (D 5) (R 5) [6,80,160,34,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 42 25 40 325 389 261), lower := (rows 7 82 164 42 25 40 64 128 256), losses := [] }

theorem u3404 : Upper (D 5) (R 5) [6,80,160,34,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 420, targets := 2 }], pairs := [(2,1)], upper := (rows 7 82 164 42 25 288 77 141 269), lower := (rows 7 82 164 42 25 288 64 128 256), losses := [] }

theorem u3405 : Upper (D 5) (R 5) [6,80,160,34,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 273 33 76 140 268), lower := (rows 7 82 164 42 273 33 64 128 256), losses := [] }

theorem u3406 : Upper (D 5) (R 5) [6,80,160,34,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 273 36 73 137 265), lower := (rows 7 82 164 42 273 36 64 128 256), losses := [] }

theorem u3407 : Upper (D 5) (R 5) [6,80,160,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 82 164 42 273 40 77 141 269), lower := (rows 7 82 164 42 273 40 64 128 256), losses := [] }

theorem u3408 : Upper (D 5) (R 5) [6,80,160,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3409 : Route 9 := (fun mask => (mask,id))

def c3409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3409 : Upper (D 5) (R 5) [6,80,160,34,260,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,260,1] 13 (by decide) (choices 1) [1,8] r3409 c3409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u995
  · exact u996

def b3410 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 82 164 42 276 40 73 137 265), lower := (rows 7 82 164 42 276 40 64 128 256), losses := [] }

theorem u3410 : Upper (D 5) (R 5) [6,80,160,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3411 : Route 9 := (fun mask => (mask,id))

def c3411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3411 : Upper (D 5) (R 5) [6,80,160,34,264,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,34,264,1] 13 (by decide) (choices 1) [1,4,8] r3411 c3411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u997
  · exact u998
  · exact u999

def b3412 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 42 280 36 73 137 265), lower := (rows 7 82 164 42 280 36 64 128 256), losses := [] }

theorem u3412 : Upper (D 5) (R 5) [6,80,160,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 82 164 42 280 40 69 133 261), lower := (rows 7 82 164 42 280 40 64 128 256), losses := [] }

theorem u3413 : Upper (D 5) (R 5) [6,80,160,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 82 164 265 28 33 106 170 298), lower := (rows 7 82 164 265 28 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 41 16 41 81 145 273), good := (rows 491 466 168 489 506 489 64 128 256) }] }

theorem u3414 : Upper (D 5) (R 5) [6,80,160,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3415 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 82 164 265 28 34 105 169 297), lower := (rows 7 82 164 265 28 34 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 9 16 51 73 137 265), good := (rows 491 114 160 489 506 34 64 128 256) }] }

theorem u3415 : Upper (D 5) (R 5) [6,80,160,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3416 : Route 9 := (fun mask => (mask,id))

def c3416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3416 : Upper (D 5) (R 5) [6,80,160,257,12,8] 13 := by
  apply FastRouting.sound _ _ [6,80,160,257,12,8] 13 (by decide) (choices 1) [1,2,32] r3416 c3416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1000
  · exact u1001
  · exact u1002

def b3417 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 82 164 265 56 33 78 142 270), lower := (rows 7 82 164 265 56 33 64 128 256), losses := [] }

theorem u3417 : Upper (D 5) (R 5) [6,80,160,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 82 164 265 56 34 77 141 269), lower := (rows 7 82 164 265 56 34 64 128 256), losses := [] }

theorem u3418 : Upper (D 5) (R 5) [6,80,160,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3419 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 265 56 36 75 139 267), lower := (rows 7 82 164 265 56 36 64 128 256), losses := [] }

theorem u3419 : Upper (D 5) (R 5) [6,80,160,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3419
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P05
