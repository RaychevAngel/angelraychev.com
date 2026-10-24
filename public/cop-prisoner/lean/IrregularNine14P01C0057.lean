import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0013
import IrregularNine14P01C0014

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 196 265 24 162 226 162 418), lower := (rows 53 82 196 265 24 32 64 128 256), losses := [] }

theorem u3420 : Upper (D 1) (R 1) [52,80,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3421 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 265 48 170 202 138 394), lower := (rows 53 82 196 265 48 32 64 128 256), losses := [] }

theorem u3421 : Upper (D 1) (R 1) [52,80,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 196 265 144 42 106 170 298), lower := (rows 53 82 196 265 144 32 64 128 256), losses := [] }

theorem u3422 : Upper (D 1) (R 1) [52,80,192,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3423 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 82 196 266 17 170 234 170 426), lower := (rows 53 82 196 266 17 32 64 128 256), losses := [] }

theorem u3423 : Upper (D 1) (R 1) [52,80,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3424 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 266 18 169 233 169 425), lower := (rows 53 82 196 266 18 32 64 128 256), losses := [] }

theorem u3424 : Upper (D 1) (R 1) [52,80,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3425 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 82 196 266 24 163 227 163 419), lower := (rows 53 82 196 266 24 32 64 128 256), losses := [] }

theorem u3425 : Upper (D 1) (R 1) [52,80,192,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3426 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 266 48 171 203 139 395), lower := (rows 53 82 196 266 48 32 64 128 256), losses := [] }

theorem u3426 : Upper (D 1) (R 1) [52,80,192,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 196 266 144 43 107 171 299), lower := (rows 53 82 196 266 144 32 64 128 256), losses := [] }

theorem u3427 : Upper (D 1) (R 1) [52,80,192,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3428 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 196 296 17 170 202 138 394), lower := (rows 53 82 196 296 17 32 64 128 256), losses := [] }

theorem u3428 : Upper (D 1) (R 1) [52,80,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3429 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 296 18 171 203 139 395), lower := (rows 53 82 196 296 18 32 64 128 256), losses := [] }

theorem u3429 : Upper (D 1) (R 1) [52,80,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3430 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 196 296 24 163 195 131 387), lower := (rows 53 82 196 296 24 32 64 128 256), losses := [] }

theorem u3430 : Upper (D 1) (R 1) [52,80,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3431 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 196 296 144 43 75 139 267), lower := (rows 53 82 196 296 144 32 64 128 256), losses := [] }

theorem u3431 : Upper (D 1) (R 1) [52,80,192,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3431
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3432 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 82 196 392 17 42 106 170 298), lower := (rows 53 82 196 392 17 32 64 128 256), losses := [] }

theorem u3432 : Upper (D 1) (R 1) [52,80,192,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 392 18 43 107 171 299), lower := (rows 53 82 196 392 18 32 64 128 256), losses := [] }

theorem u3433 : Upper (D 1) (R 1) [52,80,192,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 82 196 392 24 35 99 163 291), lower := (rows 53 82 196 392 24 32 64 128 256), losses := [] }

theorem u3434 : Upper (D 1) (R 1) [52,80,192,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 392 48 43 75 139 267), lower := (rows 53 82 196 392 48 32 64 128 256), losses := [] }

theorem u3435 : Upper (D 1) (R 1) [52,80,192,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 53 82 262 42 17 232 200 200 456), lower := (rows 53 82 262 42 17 32 64 128 256), losses := [] }

theorem u3436 : Upper (D 1) (R 1) [52,80,258,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3436
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 53 82 262 42 24 225 193 193 449), lower := (rows 53 82 262 42 24 32 64 128 256), losses := [] }

theorem u3437 : Upper (D 1) (R 1) [52,80,258,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 262 42 80 169 201 137 393), lower := (rows 53 82 262 42 80 32 64 128 256), losses := [] }

theorem u3438 : Upper (D 1) (R 1) [52,80,258,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3439 : Route 9 := (fun mask => (mask,id))

def c3439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3439 : Upper (D 1) (R 1) [52,80,258,34,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,34,128] 13 (by decide) (choices 1) [1,8,64,128] r3439 c3439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u834
  · exact u835
  · exact u836
  · exact u837

def b3440 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 73 18 168 232 168 424), lower := (rows 53 82 262 73 18 32 64 128 256), losses := [] }

theorem u3440 : Upper (D 1) (R 1) [52,80,258,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 262 73 24 162 226 162 418), lower := (rows 53 82 262 73 24 32 64 128 256), losses := [] }

theorem u3441 : Upper (D 1) (R 1) [52,80,258,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3441
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 262 73 48 170 202 138 394), lower := (rows 53 82 262 73 48 32 64 128 256), losses := [] }

theorem u3442 : Upper (D 1) (R 1) [52,80,258,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3443 : Route 9 := (fun mask => (mask,id))

def c3443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3443 : Upper (D 1) (R 1) [52,80,258,65,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,65,128] 13 (by decide) (choices 1) [2,8,128] r3443 c3443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u838
  · exact u839
  · exact u840

def b3444 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 262 104 17 170 202 138 394), lower := (rows 53 82 262 104 17 32 64 128 256), losses := [] }

theorem u3444 : Upper (D 1) (R 1) [52,80,258,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 104 18 169 201 137 393), lower := (rows 53 82 262 104 18 32 64 128 256), losses := [] }

theorem u3445 : Upper (D 1) (R 1) [52,80,258,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3446 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 262 104 24 163 195 131 387), lower := (rows 53 82 262 104 24 32 64 128 256), losses := [] }

theorem u3446 : Upper (D 1) (R 1) [52,80,258,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3446
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3447 : Route 9 := (fun mask => (mask,id))

def c3447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3447 : Upper (D 1) (R 1) [52,80,258,96,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,96,128] 13 (by decide) (choices 1) [1,2,8,128] r3447 c3447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u841
  · exact u842
  · exact u843
  · exact u844

def b3448 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 137 18 232 232 232 488), lower := (rows 53 82 262 137 18 32 64 128 256), losses := [] }

theorem u3448 : Upper (D 1) (R 1) [52,80,258,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3449 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 82 262 137 24 226 226 226 482), lower := (rows 53 82 262 137 24 32 64 128 256), losses := [] }

theorem u3449 : Upper (D 1) (R 1) [52,80,258,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 262 137 48 234 202 202 458), lower := (rows 53 82 262 137 48 32 64 128 256), losses := [] }

theorem u3450 : Upper (D 1) (R 1) [52,80,258,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 262 137 80 170 234 170 426), lower := (rows 53 82 262 137 80 32 64 128 256), losses := [] }

theorem u3451 : Upper (D 1) (R 1) [52,80,258,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3451
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3452 : Route 9 := (fun mask => (mask,id))

def c3452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3452 : Upper (D 1) (R 1) [52,80,258,129,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,129,128] 13 (by decide) (choices 1) [2,8,64] r3452 c3452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u845
  · exact u846
  · exact u847

def b3453 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 53 82 262 138 17 232 232 232 488), lower := (rows 53 82 262 138 17 32 64 128 256), losses := [] }

theorem u3453 : Upper (D 1) (R 1) [52,80,258,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 53 82 262 138 24 225 225 225 481), lower := (rows 53 82 262 138 24 32 64 128 256), losses := [] }

theorem u3454 : Upper (D 1) (R 1) [52,80,258,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 262 138 48 233 201 201 457), lower := (rows 53 82 262 138 48 32 64 128 256), losses := [] }

theorem u3455 : Upper (D 1) (R 1) [52,80,258,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 262 138 80 169 233 169 425), lower := (rows 53 82 262 138 80 32 64 128 256), losses := [] }

theorem u3456 : Upper (D 1) (R 1) [52,80,258,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3457 : Route 9 := (fun mask => (mask,id))

def c3457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3457 : Upper (D 1) (R 1) [52,80,258,130,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,130,128] 13 (by decide) (choices 1) [1,8,64] r3457 c3457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u848
  · exact u849
  · exact u850

def b3458 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 53 82 262 168 17 234 202 202 458), lower := (rows 53 82 262 168 17 32 64 128 256), losses := [] }

theorem u3458 : Upper (D 1) (R 1) [52,80,258,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 168 18 233 201 201 457), lower := (rows 53 82 262 168 18 32 64 128 256), losses := [] }

theorem u3459 : Upper (D 1) (R 1) [52,80,258,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 82 262 168 24 227 195 195 451), lower := (rows 53 82 262 168 24 32 64 128 256), losses := [] }

theorem u3460 : Upper (D 1) (R 1) [52,80,258,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 262 168 80 171 203 139 395), lower := (rows 53 82 262 168 80 32 64 128 256), losses := [] }

theorem u3461 : Upper (D 1) (R 1) [52,80,258,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3462 : Route 9 := (fun mask => (mask,id))

def c3462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3462 : Upper (D 1) (R 1) [52,80,258,160,128] 13 := by
  apply FastRouting.sound _ _ [52,80,258,160,128] 13 (by decide) (choices 1) [1,2,8,64] r3462 c3462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u851
  · exact u852
  · exact u853
  · exact u854

def b3463 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 82 262 200 17 170 234 170 426), lower := (rows 53 82 262 200 17 32 64 128 256), losses := [] }

theorem u3463 : Upper (D 1) (R 1) [52,80,258,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 200 18 169 233 169 425), lower := (rows 53 82 262 200 18 32 64 128 256), losses := [] }

theorem u3464 : Upper (D 1) (R 1) [52,80,258,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 82 262 200 24 163 227 163 419), lower := (rows 53 82 262 200 24 32 64 128 256), losses := [] }

theorem u3465 : Upper (D 1) (R 1) [52,80,258,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3465
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 262 200 48 171 203 139 395), lower := (rows 53 82 262 200 48 32 64 128 256), losses := [] }

theorem u3466 : Upper (D 1) (R 1) [52,80,258,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 262 200 144 43 107 171 299), lower := (rows 53 82 262 200 144 32 64 128 256), losses := [] }

theorem u3467 : Upper (D 1) (R 1) [52,80,258,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 73 18 162 226 162 418), lower := (rows 53 82 268 73 18 32 64 128 256), losses := [] }

theorem u3468 : Upper (D 1) (R 1) [52,80,264,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 73 48 162 194 130 386), lower := (rows 53 82 268 73 48 32 64 128 256), losses := [] }

theorem u3469 : Upper (D 1) (R 1) [52,80,264,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3470 : Route 9 := (fun mask => (mask,id))

def c3470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3470 : Upper (D 1) (R 1) [52,80,264,65,128] 13 := by
  apply FastRouting.sound _ _ [52,80,264,65,128] 13 (by decide) (choices 1) [2,128] r3470 c3470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u855
  · exact u856

def b3471 : PairBound 9 := { available := 226, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 137 18 226 226 226 482), lower := (rows 53 82 268 137 18 32 64 128 256), losses := [] }

theorem u3471 : Upper (D 1) (R 1) [52,80,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 137 48 226 194 194 450), lower := (rows 53 82 268 137 48 32 64 128 256), losses := [] }

theorem u3472 : Upper (D 1) (R 1) [52,80,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 268 137 80 162 226 162 418), lower := (rows 53 82 268 137 80 32 64 128 256), losses := [] }

theorem u3473 : Upper (D 1) (R 1) [52,80,264,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 268 137 144 98 98 226 354), lower := (rows 53 82 268 137 144 32 64 128 256), losses := [] }

theorem u3474 : Upper (D 1) (R 1) [52,80,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3475 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 82 268 138 17 226 226 226 482), lower := (rows 53 82 268 138 17 32 64 128 256), losses := [] }

theorem u3475 : Upper (D 1) (R 1) [52,80,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 225, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 138 18 225 225 225 481), lower := (rows 53 82 268 138 18 32 64 128 256), losses := [] }

theorem u3476 : Upper (D 1) (R 1) [52,80,264,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 138 48 227 195 195 451), lower := (rows 53 82 268 138 48 32 64 128 256), losses := [] }

theorem u3477 : Upper (D 1) (R 1) [52,80,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 268 138 80 163 227 163 419), lower := (rows 53 82 268 138 80 32 64 128 256), losses := [] }

theorem u3478 : Upper (D 1) (R 1) [52,80,264,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3478
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 268 138 144 99 99 227 355), lower := (rows 53 82 268 138 144 32 64 128 256), losses := [] }

theorem u3479 : Upper (D 1) (R 1) [52,80,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3479
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P01
