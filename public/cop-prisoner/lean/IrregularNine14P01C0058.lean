import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0014

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3480 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 268 200 17 162 226 162 418), lower := (rows 53 82 268 200 17 32 64 128 256), losses := [] }

theorem u3480 : Upper (D 1) (R 1) [52,80,264,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 200 18 163 227 163 419), lower := (rows 53 82 268 200 18 32 64 128 256), losses := [] }

theorem u3481 : Upper (D 1) (R 1) [52,80,264,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3482 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 200 48 163 195 131 387), lower := (rows 53 82 268 200 48 32 64 128 256), losses := [] }

theorem u3482 : Upper (D 1) (R 1) [52,80,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3483 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 268 200 144 35 99 163 291), lower := (rows 53 82 268 200 144 32 64 128 256), losses := [] }

theorem u3483 : Upper (D 1) (R 1) [52,80,264,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 324 42 17 170 202 138 394), lower := (rows 53 82 324 42 17 32 64 128 256), losses := [] }

theorem u3484 : Upper (D 1) (R 1) [52,80,320,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 42 18 169 201 137 393), lower := (rows 53 82 324 42 18 32 64 128 256), losses := [] }

theorem u3485 : Upper (D 1) (R 1) [52,80,320,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 324 42 24 163 195 131 387), lower := (rows 53 82 324 42 24 32 64 128 256), losses := [] }

theorem u3486 : Upper (D 1) (R 1) [52,80,320,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3487 : Route 9 := (fun mask => (mask,id))

def c3487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3487 : Upper (D 1) (R 1) [52,80,320,34,128] 13 := by
  apply FastRouting.sound _ _ [52,80,320,34,128] 13 (by decide) (choices 1) [1,2,8,128] r3487 c3487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u857
  · exact u858
  · exact u859
  · exact u860

def b3488 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 137 18 170 234 170 426), lower := (rows 53 82 324 137 18 32 64 128 256), losses := [] }

theorem u3488 : Upper (D 1) (R 1) [52,80,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 324 137 24 162 226 162 418), lower := (rows 53 82 324 137 24 32 64 128 256), losses := [] }

theorem u3489 : Upper (D 1) (R 1) [52,80,320,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 137 48 170 202 138 394), lower := (rows 53 82 324 137 48 32 64 128 256), losses := [] }

theorem u3490 : Upper (D 1) (R 1) [52,80,320,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3491 : Route 9 := (fun mask => (mask,id))

def c3491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3491 : Upper (D 1) (R 1) [52,80,320,129,128] 13 := by
  apply FastRouting.sound _ _ [52,80,320,129,128] 13 (by decide) (choices 1) [2,8] r3491 c3491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u861
  · exact u862

def b3492 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 82 324 138 17 170 234 170 426), lower := (rows 53 82 324 138 17 32 64 128 256), losses := [] }

theorem u3492 : Upper (D 1) (R 1) [52,80,320,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 138 18 169 233 169 425), lower := (rows 53 82 324 138 18 32 64 128 256), losses := [] }

theorem u3493 : Upper (D 1) (R 1) [52,80,320,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 82 324 138 24 163 227 163 419), lower := (rows 53 82 324 138 24 32 64 128 256), losses := [] }

theorem u3494 : Upper (D 1) (R 1) [52,80,320,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 138 48 171 203 139 395), lower := (rows 53 82 324 138 48 32 64 128 256), losses := [] }

theorem u3495 : Upper (D 1) (R 1) [52,80,320,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3496 : Route 9 := (fun mask => (mask,id))

def c3496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3496 : Upper (D 1) (R 1) [52,80,320,130,128] 13 := by
  apply FastRouting.sound _ _ [52,80,320,130,128] 13 (by decide) (choices 1) [1,2,8] r3496 c3496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u863
  · exact u864
  · exact u865

def b3497 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 324 168 17 170 202 138 394), lower := (rows 53 82 324 168 17 32 64 128 256), losses := [] }

theorem u3497 : Upper (D 1) (R 1) [52,80,320,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3498 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 324 168 18 171 203 139 395), lower := (rows 53 82 324 168 18 32 64 128 256), losses := [] }

theorem u3498 : Upper (D 1) (R 1) [52,80,320,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3499 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 324 168 24 163 195 131 387), lower := (rows 53 82 324 168 24 32 64 128 256), losses := [] }

theorem u3499 : Upper (D 1) (R 1) [52,80,320,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3500 : Route 9 := (fun mask => (mask,id))

def c3500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3500 : Upper (D 1) (R 1) [52,80,320,160,128] 13 := by
  apply FastRouting.sound _ _ [52,80,320,160,128] 13 (by decide) (choices 1) [1,2,8] r3500 c3500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u866
  · exact u867
  · exact u868

def b3501 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 53 82 388 42 17 234 202 202 458), lower := (rows 53 82 388 42 17 32 64 128 256), losses := [] }

theorem u3501 : Upper (D 1) (R 1) [52,80,384,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3502 : PairBound 9 := { available := 201, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 42 18 233 201 201 457), lower := (rows 53 82 388 42 18 32 64 128 256), losses := [] }

theorem u3502 : Upper (D 1) (R 1) [52,80,384,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3503 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 82 388 42 24 227 195 195 451), lower := (rows 53 82 388 42 24 32 64 128 256), losses := [] }

theorem u3503 : Upper (D 1) (R 1) [52,80,384,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3504 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 388 42 80 171 203 139 395), lower := (rows 53 82 388 42 80 32 64 128 256), losses := [] }

theorem u3504 : Upper (D 1) (R 1) [52,80,384,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3505 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 388 42 144 107 75 203 331), lower := (rows 53 82 388 42 144 32 64 128 256), losses := [] }

theorem u3505 : Upper (D 1) (R 1) [52,80,384,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 73 18 170 234 170 426), lower := (rows 53 82 388 73 18 32 64 128 256), losses := [] }

theorem u3506 : Upper (D 1) (R 1) [52,80,384,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3507 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 388 73 24 162 226 162 418), lower := (rows 53 82 388 73 24 32 64 128 256), losses := [] }

theorem u3507 : Upper (D 1) (R 1) [52,80,384,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3508 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 73 48 170 202 138 394), lower := (rows 53 82 388 73 48 32 64 128 256), losses := [] }

theorem u3508 : Upper (D 1) (R 1) [52,80,384,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 388 73 144 42 106 170 298), lower := (rows 53 82 388 73 144 32 64 128 256), losses := [] }

theorem u3509 : Upper (D 1) (R 1) [52,80,384,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 388 104 17 170 202 138 394), lower := (rows 53 82 388 104 17 32 64 128 256), losses := [] }

theorem u3510 : Upper (D 1) (R 1) [52,80,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3511 : PairBound 9 := { available := 139, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 104 18 171 203 139 395), lower := (rows 53 82 388 104 18 32 64 128 256), losses := [] }

theorem u3511 : Upper (D 1) (R 1) [52,80,384,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3512 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 388 104 24 163 195 131 387), lower := (rows 53 82 388 104 24 32 64 128 256), losses := [] }

theorem u3512 : Upper (D 1) (R 1) [52,80,384,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 388 104 144 43 75 139 267), lower := (rows 53 82 388 104 144 32 64 128 256), losses := [] }

theorem u3513 : Upper (D 1) (R 1) [52,80,384,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3514 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 53 82 388 138 17 106 106 234 362), lower := (rows 53 82 388 138 17 32 64 128 256), losses := [] }

theorem u3514 : Upper (D 1) (R 1) [52,80,384,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3515 : PairBound 9 := { available := 105, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 138 18 105 105 233 361), lower := (rows 53 82 388 138 18 32 64 128 256), losses := [] }

theorem u3515 : Upper (D 1) (R 1) [52,80,384,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3515
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 53 82 388 138 24 99 99 227 355), lower := (rows 53 82 388 138 24 32 64 128 256), losses := [] }

theorem u3516 : Upper (D 1) (R 1) [52,80,384,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 138 48 107 75 203 331), lower := (rows 53 82 388 138 48 32 64 128 256), losses := [] }

theorem u3517 : Upper (D 1) (R 1) [52,80,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 388 138 80 43 107 171 299), lower := (rows 53 82 388 138 80 32 64 128 256), losses := [] }

theorem u3518 : Upper (D 1) (R 1) [52,80,384,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 53 82 388 168 17 106 74 202 330), lower := (rows 53 82 388 168 17 32 64 128 256), losses := [] }

theorem u3519 : Upper (D 1) (R 1) [52,80,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3519
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 75, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 168 18 107 75 203 331), lower := (rows 53 82 388 168 18 32 64 128 256), losses := [] }

theorem u3520 : Upper (D 1) (R 1) [52,80,384,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 53 82 388 168 24 99 67 195 323), lower := (rows 53 82 388 168 24 32 64 128 256), losses := [] }

theorem u3521 : Upper (D 1) (R 1) [52,80,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 388 168 80 43 75 139 267), lower := (rows 53 82 388 168 80 32 64 128 256), losses := [] }

theorem u3522 : Upper (D 1) (R 1) [52,80,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 82 388 200 17 42 106 170 298), lower := (rows 53 82 388 200 17 32 64 128 256), losses := [] }

theorem u3523 : Upper (D 1) (R 1) [52,80,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3524 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 200 18 43 107 171 299), lower := (rows 53 82 388 200 18 32 64 128 256), losses := [] }

theorem u3524 : Upper (D 1) (R 1) [52,80,384,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3525 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 82 388 200 24 35 99 163 291), lower := (rows 53 82 388 200 24 32 64 128 256), losses := [] }

theorem u3525 : Upper (D 1) (R 1) [52,80,384,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3526 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 388 200 48 43 75 139 267), lower := (rows 53 82 388 200 48 32 64 128 256), losses := [] }

theorem u3526 : Upper (D 1) (R 1) [52,80,384,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 194 7 266 24 240 240 240 496), lower := (rows 53 194 7 266 24 32 64 128 256), losses := [] }

theorem u3527 : Upper (D 1) (R 1) [52,192,3,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3528 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 7 266 48 248 216 216 472), lower := (rows 53 194 7 266 48 32 64 128 256), losses := [] }

theorem u3528 : Upper (D 1) (R 1) [52,192,3,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3529 : PairBound 9 := { available := 184, camps := [], pairs := [(3,6)], upper := (rows 53 194 7 266 80 184 248 184 440), lower := (rows 53 194 7 266 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 33 0 129 257), good := (rows 445 130 431 266 16 32 0 128 256) }] }

theorem u3529 : Upper (D 1) (R 1) [52,192,3,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 7 328 18 184 248 184 440), lower := (rows 53 194 7 328 18 32 64 128 256), losses := [] }

theorem u3530 : Upper (D 1) (R 1) [52,192,3,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3531 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 194 7 328 24 178 242 178 434), lower := (rows 53 194 7 328 24 32 64 128 256), losses := [] }

theorem u3531 : Upper (D 1) (R 1) [52,192,3,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3532 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 7 328 48 186 218 154 410), lower := (rows 53 194 7 328 48 32 64 128 256), losses := [] }

theorem u3532 : Upper (D 1) (R 1) [52,192,3,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3532
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3533_2 : Upper (D 1) (R 1) [52,192,3,320,128,2] 13 :=
  permutation_upper _ _ _ [52,192,3,320,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u869

theorem m3533_8 : Upper (D 1) (R 1) [52,192,3,320,128,8] 13 :=
  permutation_upper _ _ _ [52,192,3,320,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u870

theorem m3533_16 : Upper (D 1) (R 1) [52,192,3,320,128,16] 13 :=
  permutation_upper _ _ _ [52,192,3,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u871

def r3533 : Route 9 := (fun mask => (mask,id))

def c3533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3533 : Upper (D 1) (R 1) [52,192,3,320,128] 13 := by
  apply FastRouting.sound _ _ [52,192,3,320,128] 13 (by decide) (choices 1) [2,8,16] r3533 c3533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3533_2
  · exact m3533_8
  · exact m3533_16

def r3534 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3534 : Upper (D 1) (R 1) [52,192,9,258,2] 13 := by
  apply FastRouting.sound _ _ [52,192,9,258,2] 13 (by decide) (choices 1) [16,64] r3534 c3534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u872
  · exact u873

def b3535 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 13 266 48 242 210 210 466), lower := (rows 53 194 13 266 48 32 64 128 256), losses := [] }

theorem u3535 : Upper (D 1) (R 1) [52,192,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3535
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3536_2 : Upper (D 1) (R 1) [52,192,9,258,64,2] 13 :=
  permutation_upper _ _ _ [52,192,9,258,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u873

theorem m3536_16 : Upper (D 1) (R 1) [52,192,9,258,64,16] 13 :=
  permutation_upper _ _ _ [52,192,9,258,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u874

def r3536 : Route 9 := (fun mask => (mask,id))

def c3536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3536 : Upper (D 1) (R 1) [52,192,9,258,64] 13 := by
  apply FastRouting.sound _ _ [52,192,9,258,64] 13 (by decide) (choices 1) [2,16,128] r3536 c3536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3536_2
  · exact m3536_16
  · exact u875

def r3537 : Route 9 := (fun mask => (mask,id))

def c3537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3537 : Upper (D 1) (R 1) [52,192,9,320,2] 13 := by
  apply FastRouting.sound _ _ [52,192,9,320,2] 13 (by decide) (choices 1) [2,16,128] r3537 c3537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u876
  · exact u877
  · exact u878

def b3538 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 13 328 48 178 210 146 402), lower := (rows 53 194 13 328 48 32 64 128 256), losses := [] }

theorem u3538 : Upper (D 1) (R 1) [52,192,9,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3538
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3539_2 : Upper (D 1) (R 1) [52,192,9,320,128,2] 13 :=
  permutation_upper _ _ _ [52,192,9,320,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u878

theorem m3539_16 : Upper (D 1) (R 1) [52,192,9,320,128,16] 13 :=
  permutation_upper _ _ _ [52,192,9,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u879

def r3539 : Route 9 := (fun mask => (mask,id))

def c3539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3539 : Upper (D 1) (R 1) [52,192,9,320,128] 13 := by
  apply FastRouting.sound _ _ [52,192,9,320,128] 13 (by decide) (choices 1) [2,16] r3539 c3539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3539_2
  · exact m3539_16

#print axioms u3539
end Delivery.IrregularNine14.P01
