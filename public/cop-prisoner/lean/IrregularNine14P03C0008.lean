import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0000
import IrregularNine14P03C0001

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b480 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 69 56 336 40 193 129 385), lower := (rows 7 35 69 56 336 40 64 128 256), losses := [] }

theorem u480 : Upper (D 3) (R 3) [6,33,65,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r481 : Route 9 := (fun mask => (mask,id))

def c481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u481 : Upper (D 3) (R 3) [6,33,65,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,320,128] 13 (by decide) (choices 1) [1,8,128] r481 c481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u58
  · exact u59
  · exact u60

def b482 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 56 400 33 200 200 456), lower := (rows 7 35 69 56 400 33 64 128 256), losses := [] }

theorem u482 : Upper (D 3) (R 3) [6,33,65,48,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b482
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 69 56 400 40 193 193 449), lower := (rows 7 35 69 56 400 40 64 128 256), losses := [] }

theorem u483 : Upper (D 3) (R 3) [6,33,65,48,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 56 400 96 201 137 393), lower := (rows 7 35 69 56 400 96 64 128 256), losses := [] }

theorem u484 : Upper (D 3) (R 3) [6,33,65,48,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b484
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 56 400 160 73 201 329), lower := (rows 7 35 69 56 400 160 64 128 256), losses := [] }

theorem u485 : Upper (D 3) (R 3) [6,33,65,48,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b485
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 152 280 33 224 224 480), lower := (rows 7 35 69 152 280 33 64 128 256), losses := [] }

theorem u486 : Upper (D 3) (R 3) [6,33,65,144,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b486
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 152 280 96 225 161 417), lower := (rows 7 35 69 152 280 96 64 128 256), losses := [] }

theorem u487 : Upper (D 3) (R 3) [6,33,65,144,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 152 280 160 97 225 353), lower := (rows 7 35 69 152 280 160 64 128 256), losses := [] }

theorem u488 : Upper (D 3) (R 3) [6,33,65,144,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 152 304 33 200 200 456), lower := (rows 7 35 69 152 304 33 64 128 256), losses := [] }

theorem u489 : Upper (D 3) (R 3) [6,33,65,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 69 152 304 40 193 193 449), lower := (rows 7 35 69 152 304 40 64 128 256), losses := [] }

theorem u490 : Upper (D 3) (R 3) [6,33,65,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 152 304 96 201 137 393), lower := (rows 7 35 69 152 304 96 64 128 256), losses := [] }

theorem u491 : Upper (D 3) (R 3) [6,33,65,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r492 : Route 9 := (fun mask => (mask,id))

def c492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u492 : Upper (D 3) (R 3) [6,33,65,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288,128] 13 (by decide) (choices 1) [1,8] r492 c492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u61
  · exact u62

def b493 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 168 208 33 344 408 280), lower := (rows 7 35 69 168 208 33 64 128 256), losses := [] }

theorem u493 : Upper (D 3) (R 3) [6,33,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b493
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 7 35 69 168 208 40 337 401 273), lower := (rows 7 35 69 168 208 40 64 128 256), losses := [] }

theorem u494 : Upper (D 3) (R 3) [6,33,65,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 7 35 69 168 208 48 329 393 265), lower := (rows 7 35 69 168 208 48 64 128 256), losses := [] }

theorem u495 : Upper (D 3) (R 3) [6,33,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 7 35 69 168 208 288 89 153 281), lower := (rows 7 35 69 168 208 288 64 128 256), losses := [] }

theorem u496 : Upper (D 3) (R 3) [6,33,65,160,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b496
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 168 280 33 208 208 464), lower := (rows 7 35 69 168 280 33 64 128 256), losses := [] }

theorem u497 : Upper (D 3) (R 3) [6,33,65,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b497
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 69 168 280 48 193 193 449), lower := (rows 7 35 69 168 280 48 64 128 256), losses := [] }

theorem u498 : Upper (D 3) (R 3) [6,33,65,160,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b498
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 168 280 96 209 145 401), lower := (rows 7 35 69 168 280 96 64 128 256), losses := [] }

theorem u499 : Upper (D 3) (R 3) [6,33,65,160,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b499
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 168 280 160 81 209 337), lower := (rows 7 35 69 168 280 160 64 128 256), losses := [] }

theorem u500 : Upper (D 3) (R 3) [6,33,65,160,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 168 336 33 216 152 408), lower := (rows 7 35 69 168 336 33 64 128 256), losses := [] }

theorem u501 : Upper (D 3) (R 3) [6,33,65,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b501
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 69 168 336 40 209 145 401), lower := (rows 7 35 69 168 336 40 64 128 256), losses := [] }

theorem u502 : Upper (D 3) (R 3) [6,33,65,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b502
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 69 168 336 48 201 137 393), lower := (rows 7 35 69 168 336 48 64 128 256), losses := [] }

theorem u503 : Upper (D 3) (R 3) [6,33,65,160,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b503
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 168 336 160 89 153 281), lower := (rows 7 35 69 168 336 160 64 128 256), losses := [] }

theorem u504 : Upper (D 3) (R 3) [6,33,65,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 168 400 33 88 216 344), lower := (rows 7 35 69 168 400 33 64 128 256), losses := [] }

theorem u505 : Upper (D 3) (R 3) [6,33,65,160,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b505
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 35 69 168 400 40 81 209 337), lower := (rows 7 35 69 168 400 40 64 128 256), losses := [] }

theorem u506 : Upper (D 3) (R 3) [6,33,65,160,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 7 35 69 168 400 48 73 201 329), lower := (rows 7 35 69 168 400 48 64 128 256), losses := [] }

theorem u507 : Upper (D 3) (R 3) [6,33,65,160,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 168 400 96 89 153 281), lower := (rows 7 35 69 168 400 96 64 128 256), losses := [] }

theorem u508 : Upper (D 3) (R 3) [6,33,65,160,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 25 400 33 224 224 480), lower := (rows 7 35 76 25 400 33 64 128 256), losses := [] }

theorem u509 : Upper (D 3) (R 3) [6,33,72,17,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 25 400 96 225 161 417), lower := (rows 7 35 76 25 400 96 64 128 256), losses := [] }

theorem u510 : Upper (D 3) (R 3) [6,33,72,17,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 97, camps := [], pairs := [(0,6)], upper := (rows 7 35 76 25 400 160 97 225 353), lower := (rows 7 35 76 25 400 160 64 128 256), losses := [{ target := 6, region := (rows 5 10 4 8 16 176 0 128 256), good := (rows 7 35 15 59 432 160 0 160 256) }] }

theorem u511 : Upper (D 3) (R 3) [6,33,72,17,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 137 112 33 464 400 400), lower := (rows 7 35 76 137 112 33 64 128 256), losses := [] }

theorem u512 : Upper (D 3) (R 3) [6,33,72,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 7 35 76 137 112 48 449 385 385), lower := (rows 7 35 76 137 112 48 64 128 256), losses := [] }

theorem u513 : Upper (D 3) (R 3) [6,33,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 137 112 160 337 401 273), lower := (rows 7 35 76 137 112 160 64 128 256), losses := [] }

theorem u514 : Upper (D 3) (R 3) [6,33,72,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 76 137 112 288 209 145 401), lower := (rows 7 35 76 137 112 288 64 128 256), losses := [] }

theorem u515 : Upper (D 3) (R 3) [6,33,72,129,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 137 176 33 336 464 336), lower := (rows 7 35 76 137 176 33 64 128 256), losses := [] }

theorem u516 : Upper (D 3) (R 3) [6,33,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 7 35 76 137 176 48 321 449 321), lower := (rows 7 35 76 137 176 48 64 128 256), losses := [] }

theorem u517 : Upper (D 3) (R 3) [6,33,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b517
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 137 176 96 337 401 273), lower := (rows 7 35 76 137 176 96 64 128 256), losses := [] }

theorem u518 : Upper (D 3) (R 3) [6,33,72,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 35 76 137 176 288 81 209 337), lower := (rows 7 35 76 137 176 288 64 128 256), losses := [] }

theorem u519 : Upper (D 3) (R 3) [6,33,72,129,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b519
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 137 208 33 368 432 304), lower := (rows 7 35 76 137 208 33 64 128 256), losses := [] }

theorem u520 : Upper (D 3) (R 3) [6,33,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b520
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 35 76 137 208 48 353 417 289), lower := (rows 7 35 76 137 208 48 64 128 256), losses := [] }

theorem u521 : Upper (D 3) (R 3) [6,33,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 35 76 137 208 288 113 177 305), lower := (rows 7 35 76 137 208 288 64 128 256), losses := [] }

theorem u522 : Upper (D 3) (R 3) [6,33,72,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 7 35 76 137 273 48 224 224 480), lower := (rows 7 35 76 137 273 48 64 128 256), losses := [] }

theorem u523 : Upper (D 3) (R 3) [6,33,72,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 137 273 96 240 176 432), lower := (rows 7 35 76 137 273 96 64 128 256), losses := [] }

theorem u524 : Upper (D 3) (R 3) [6,33,72,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b524
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 137 273 160 112 240 368), lower := (rows 7 35 76 137 273 160 64 128 256), losses := [] }

theorem u525 : Upper (D 3) (R 3) [6,33,72,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 137 304 33 208 208 464), lower := (rows 7 35 76 137 304 33 64 128 256), losses := [] }

theorem u526 : Upper (D 3) (R 3) [6,33,72,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b526
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 76 137 304 48 193 193 449), lower := (rows 7 35 76 137 304 48 64 128 256), losses := [] }

theorem u527 : Upper (D 3) (R 3) [6,33,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b527
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 137 304 96 209 145 401), lower := (rows 7 35 76 137 304 96 64 128 256), losses := [] }

theorem u528 : Upper (D 3) (R 3) [6,33,72,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b528
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 137 304 160 81 209 337), lower := (rows 7 35 76 137 304 160 64 128 256), losses := [] }

theorem u529 : Upper (D 3) (R 3) [6,33,72,129,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 137 336 33 240 176 432), lower := (rows 7 35 76 137 336 33 64 128 256), losses := [] }

theorem u530 : Upper (D 3) (R 3) [6,33,72,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 76 137 336 48 225 161 417), lower := (rows 7 35 76 137 336 48 64 128 256), losses := [] }

theorem u531 : Upper (D 3) (R 3) [6,33,72,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 137 336 160 113 177 305), lower := (rows 7 35 76 137 336 160 64 128 256), losses := [] }

theorem u532 : Upper (D 3) (R 3) [6,33,72,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 137 400 33 112 240 368), lower := (rows 7 35 76 137 400 33 64 128 256), losses := [] }

theorem u533 : Upper (D 3) (R 3) [6,33,72,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 35 76 137 400 48 97 225 353), lower := (rows 7 35 76 137 400 48 64 128 256), losses := [] }

theorem u534 : Upper (D 3) (R 3) [6,33,72,129,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 137 400 96 113 177 305), lower := (rows 7 35 76 137 400 96 64 128 256), losses := [] }

theorem u535 : Upper (D 3) (R 3) [6,33,72,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 273 33 224 224 480), lower := (rows 7 35 76 152 273 33 64 128 256), losses := [] }

theorem u536 : Upper (D 3) (R 3) [6,33,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 152 273 96 225 161 417), lower := (rows 7 35 76 152 273 96 64 128 256), losses := [] }

theorem u537 : Upper (D 3) (R 3) [6,33,72,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 152 273 160 97 225 353), lower := (rows 7 35 76 152 273 160 64 128 256), losses := [] }

theorem u538 : Upper (D 3) (R 3) [6,33,72,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 304 33 193 193 449), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u539 : Upper (D 3) (R 3) [6,33,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b539
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P03
