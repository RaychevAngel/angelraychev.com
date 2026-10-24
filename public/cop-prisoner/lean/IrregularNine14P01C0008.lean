import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b480 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 29 98 7 392 48 48 194 194 450), lower := (rows 29 98 7 392 48 48 64 128 256), losses := [] }

theorem u480 : Upper (D 1) (R 1) [28,96,3,384,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 7 392 48 96 210 146 402), lower := (rows 29 98 7 392 48 96 64 128 256), losses := [] }

theorem u481 : Upper (D 1) (R 1) [28,96,3,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 7 392 48 160 82 210 338), lower := (rows 29 98 7 392 48 160 64 128 256), losses := [] }

theorem u482 : Upper (D 1) (R 1) [28,96,3,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 29 98 133 266 48 34 208 208 464), lower := (rows 29 98 133 266 48 34 64 128 256), losses := [] }

theorem u483 : Upper (D 1) (R 1) [28,96,129,258,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 29 98 133 266 48 48 194 194 450), lower := (rows 29 98 133 266 48 48 64 128 256), losses := [] }

theorem u484 : Upper (D 1) (R 1) [28,96,129,258,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 133 266 48 96 210 146 402), lower := (rows 29 98 133 266 48 96 64 128 256), losses := [] }

theorem u485 : Upper (D 1) (R 1) [28,96,129,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 266 48 160 82 210 338), lower := (rows 29 98 133 266 48 160 64 128 256), losses := [] }

theorem u486 : Upper (D 1) (R 1) [28,96,129,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 133 296 80 34 210 146 402), lower := (rows 29 98 133 296 80 34 64 128 256), losses := [] }

theorem u487 : Upper (D 1) (R 1) [28,96,129,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 133 296 80 48 194 130 386), lower := (rows 29 98 133 296 80 48 64 128 256), losses := [] }

theorem u488 : Upper (D 1) (R 1) [28,96,129,288,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 133 296 80 160 82 146 274), lower := (rows 29 98 133 296 80 160 64 128 256), losses := [] }

theorem u489 : Upper (D 1) (R 1) [28,96,129,288,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 134 265 48 34 208 208 464), lower := (rows 29 98 134 265 48 34 64 128 256), losses := [] }

theorem u490 : Upper (D 1) (R 1) [28,96,130,257,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b490
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 132, targets := 16 }], pairs := [(2,4)], upper := (rows 29 98 134 265 48 48 194 194 450), lower := (rows 29 98 134 265 48 48 64 128 256), losses := [] }

theorem u491 : Upper (D 1) (R 1) [28,96,130,257,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 134 265 48 96 210 146 402), lower := (rows 29 98 134 265 48 96 64 128 256), losses := [] }

theorem u492 : Upper (D 1) (R 1) [28,96,130,257,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 265 48 160 82 210 338), lower := (rows 29 98 134 265 48 160 64 128 256), losses := [] }

theorem u493 : Upper (D 1) (R 1) [28,96,130,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 29 98 134 266 48 33 208 208 464), lower := (rows 29 98 134 266 48 33 64 128 256), losses := [] }

theorem u494 : Upper (D 1) (R 1) [28,96,130,258,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 266 48 48 193 193 449), lower := (rows 29 98 134 266 48 48 64 128 256), losses := [] }

theorem u495 : Upper (D 1) (R 1) [28,96,130,258,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 134 266 48 96 209 145 401), lower := (rows 29 98 134 266 48 96 64 128 256), losses := [] }

theorem u496 : Upper (D 1) (R 1) [28,96,130,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 81, camps := [], pairs := [(0,7)], upper := (rows 29 98 134 266 48 160 81 209 337), lower := (rows 29 98 134 266 48 160 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 12 50 32 69 0 261), good := (rows 349 114 351 282 48 48 64 0 256) }] }

theorem u497 : Upper (D 1) (R 1) [28,96,130,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 29 98 134 296 80 33 210 146 402), lower := (rows 29 98 134 296 80 33 64 128 256), losses := [] }

theorem u498 : Upper (D 1) (R 1) [28,96,130,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 134 296 80 34 209 145 401), lower := (rows 29 98 134 296 80 34 64 128 256), losses := [] }

theorem u499 : Upper (D 1) (R 1) [28,96,130,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 134 296 80 48 195 131 387), lower := (rows 29 98 134 296 80 48 64 128 256), losses := [] }

theorem u500 : Upper (D 1) (R 1) [28,96,130,288,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r501 : Route 9 := (fun mask => (mask,id))

def c501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u501 : Upper (D 1) (R 1) [28,96,130,288,64,128] 13 := by
  apply FastRouting.sound _ _ [28,96,130,288,64,128] 13 (by decide) (choices 1) [1,2,16] r501 c501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23
  · exact u24
  · exact u25

def b502 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 164 265 80 34 210 146 402), lower := (rows 29 98 164 265 80 34 64 128 256), losses := [] }

theorem u502 : Upper (D 1) (R 1) [28,96,160,257,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 164 265 80 48 194 130 386), lower := (rows 29 98 164 265 80 48 64 128 256), losses := [] }

theorem u503 : Upper (D 1) (R 1) [28,96,160,257,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 164 265 80 160 82 146 274), lower := (rows 29 98 164 265 80 160 64 128 256), losses := [] }

theorem u504 : Upper (D 1) (R 1) [28,96,160,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 29 98 164 266 80 33 210 146 402), lower := (rows 29 98 164 266 80 33 64 128 256), losses := [] }

theorem u505 : Upper (D 1) (R 1) [28,96,160,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 164 266 80 34 209 145 401), lower := (rows 29 98 164 266 80 34 64 128 256), losses := [] }

theorem u506 : Upper (D 1) (R 1) [28,96,160,258,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 266 80 48 195 131 387), lower := (rows 29 98 164 266 80 48 64 128 256), losses := [] }

theorem u507 : Upper (D 1) (R 1) [28,96,160,258,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 164 266 80 160 83 147 275), lower := (rows 29 98 164 266 80 160 64 128 256), losses := [] }

theorem u508 : Upper (D 1) (R 1) [28,96,160,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 29 98 164 328 18 33 210 146 402), lower := (rows 29 98 164 328 18 33 64 128 256), losses := [] }

theorem u509 : Upper (D 1) (R 1) [28,96,160,320,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 164 328 18 34 209 145 401), lower := (rows 29 98 164 328 18 34 64 128 256), losses := [] }

theorem u510 : Upper (D 1) (R 1) [28,96,160,320,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 29 98 164 328 18 48 195 131 387), lower := (rows 29 98 164 328 18 48 64 128 256), losses := [] }

theorem u511 : Upper (D 1) (R 1) [28,96,160,320,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 164 328 18 160 83 147 275), lower := (rows 29 98 164 328 18 160 64 128 256), losses := [] }

theorem u512 : Upper (D 1) (R 1) [28,96,160,320,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 29 259 38 74 144 48 224 224 480), lower := (rows 29 259 38 74 144 48 64 128 256), losses := [] }

theorem u513 : Upper (D 1) (R 1) [28,257,34,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 29 259 38 74 144 96 240 176 432), lower := (rows 29 259 38 74 144 96 64 128 256), losses := [] }

theorem u514 : Upper (D 1) (R 1) [28,257,34,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b514
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m515_16 : Upper (D 1) (R 1) [28,257,34,66,128,128,16] 13 :=
  permutation_upper _ _ _ [28,257,34,66,128,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26

theorem m515_32 : Upper (D 1) (R 1) [28,257,34,66,128,128,32] 13 :=
  permutation_upper _ _ _ [28,257,34,66,128,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27

def r515 : Route 9 := (fun mask => (mask,id))

def c515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u515 : Upper (D 1) (R 1) [28,257,34,66,128,128] 13 := by
  apply FastRouting.sound _ _ [28,257,34,66,128,128] 13 (by decide) (choices 1) [16,32] r515 c515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m515_16
  · exact m515_32

def b516 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 29 274 38 74 144 33 224 224 480), lower := (rows 29 274 38 74 144 33 64 128 256), losses := [] }

theorem u516 : Upper (D 1) (R 1) [28,272,34,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 29 274 38 74 144 96 225 161 417), lower := (rows 29 274 38 74 144 96 64 128 256), losses := [] }

theorem u517 : Upper (D 1) (R 1) [28,272,34,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 97, camps := [], pairs := [(2,4)], upper := (rows 29 274 38 74 144 160 97 225 353), lower := (rows 29 274 38 74 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 8 0 177 65 129 257), good := (rows 493 294 38 78 160 160 64 160 256) }] }

theorem u518 : Upper (D 1) (R 1) [28,272,34,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 74 144 48 224 224 480), lower := (rows 29 290 7 74 144 48 64 128 256), losses := [] }

theorem u519 : Upper (D 1) (R 1) [28,288,3,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b519
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 402, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 7 74 144 96 240 176 432), lower := (rows 29 290 7 74 144 96 64 128 256), losses := [] }

theorem u520 : Upper (D 1) (R 1) [28,288,3,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r521 : Route 9 := (fun mask => (mask,id))

def c521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u521 : Upper (D 1) (R 1) [28,288,3,66,128,128] 13 := by
  apply FastRouting.sound _ _ [28,288,3,66,128,128] 13 (by decide) (choices 1) [16,32] r521 c521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28
  · exact u29

def b522 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 104 144 34 208 208 464), lower := (rows 29 290 7 104 144 34 64 128 256), losses := [] }

theorem u522 : Upper (D 1) (R 1) [28,288,3,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 29 290 7 104 144 48 194 194 450), lower := (rows 29 290 7 104 144 48 64 128 256), losses := [] }

theorem u523 : Upper (D 1) (R 1) [28,288,3,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 29 290 7 104 144 96 210 146 402), lower := (rows 29 290 7 104 144 96 64 128 256), losses := [] }

theorem u524 : Upper (D 1) (R 1) [28,288,3,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r525 : Route 9 := (fun mask => (mask,id))

def c525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u525 : Upper (D 1) (R 1) [28,288,3,96,128,128] 13 := by
  apply FastRouting.sound _ _ [28,288,3,96,128,128] 13 (by decide) (choices 1) [2,16] r525 c525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30
  · exact u31

def b526 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 29 290 7 200 48 34 208 208 464), lower := (rows 29 290 7 200 48 34 64 128 256), losses := [] }

theorem u526 : Upper (D 1) (R 1) [28,288,3,192,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 7 200 48 48 194 194 450), lower := (rows 29 290 7 200 48 48 64 128 256), losses := [] }

theorem u527 : Upper (D 1) (R 1) [28,288,3,192,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 7 200 48 96 210 146 402), lower := (rows 29 290 7 200 48 96 64 128 256), losses := [] }

theorem u528 : Upper (D 1) (R 1) [28,288,3,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 29 290 69 138 48 34 208 208 464), lower := (rows 29 290 69 138 48 34 64 128 256), losses := [] }

theorem u529 : Upper (D 1) (R 1) [28,288,65,130,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 29 290 69 138 48 48 194 194 450), lower := (rows 29 290 69 138 48 48 64 128 256), losses := [] }

theorem u530 : Upper (D 1) (R 1) [28,288,65,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 69 138 48 96 210 146 402), lower := (rows 29 290 69 138 48 96 64 128 256), losses := [] }

theorem u531 : Upper (D 1) (R 1) [28,288,65,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 29 290 69 138 48 160 82 210 338), lower := (rows 29 290 69 138 48 160 64 128 256), losses := [] }

theorem u532 : Upper (D 1) (R 1) [28,288,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 29 290 70 138 48 33 208 208 464), lower := (rows 29 290 70 138 48 33 64 128 256), losses := [] }

theorem u533 : Upper (D 1) (R 1) [28,288,66,130,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 29 290 70 138 48 48 193 193 449), lower := (rows 29 290 70 138 48 48 64 128 256), losses := [] }

theorem u534 : Upper (D 1) (R 1) [28,288,66,130,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 145, camps := [], pairs := [(0,6)], upper := (rows 29 290 70 138 48 96 209 145 401), lower := (rows 29 290 70 138 48 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 50 32 0 133 261), good := (rows 413 306 415 154 48 48 0 128 256) }] }

theorem u535 : Upper (D 1) (R 1) [28,288,66,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b535
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 280 144 34 224 224 480), lower := (rows 51 7 76 280 144 34 64 128 256), losses := [] }

theorem u536 : Upper (D 1) (R 1) [50,5,72,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 280 144 96 226 162 418), lower := (rows 51 7 76 280 144 96 64 128 256), losses := [] }

theorem u537 : Upper (D 1) (R 1) [50,5,72,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b537
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 76 280 144 160 98 226 354), lower := (rows 51 7 76 280 144 160 64 128 256), losses := [] }

theorem u538 : Upper (D 1) (R 1) [50,5,72,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 392 18 160 112 240 368), lower := (rows 51 7 76 392 18 160 64 128 256), losses := [] }

theorem u539 : Upper (D 1) (R 1) [50,5,72,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b539
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P01
