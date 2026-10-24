import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b480 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 290, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 138 28 288 65 176 304), lower := (rows 7 42 69 138 28 288 65 128 256), losses := [] }

theorem u480 : Upper (D 5) (R 5) [6,40,65,130,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 69 138 28 288 80 161 289), lower := (rows 7 42 69 138 28 288 80 128 256), losses := [] }

theorem u481 : Upper (D 5) (R 5) [6,40,65,130,12,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 138 28 288 96 145 273), lower := (rows 7 42 69 138 28 288 96 128 256), losses := [] }

theorem u482 : Upper (D 5) (R 5) [6,40,65,130,12,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 138 49 288 68 152 280), lower := (rows 7 42 69 138 49 288 68 128 256), losses := [] }

theorem u483 : Upper (D 5) (R 5) [6,40,65,130,33,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 138 49 288 72 148 276), lower := (rows 7 42 69 138 49 288 72 128 256), losses := [] }

theorem u484 : Upper (D 5) (R 5) [6,40,65,130,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 7 42 69 138 49 288 80 140 268), lower := (rows 7 42 69 138 49 288 80 128 256), losses := [] }

theorem u485 : Upper (D 5) (R 5) [6,40,65,130,33,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 138, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 138 52 288 65 152 280), lower := (rows 7 42 69 138 52 288 65 128 256), losses := [] }

theorem u486 : Upper (D 5) (R 5) [6,40,65,130,36,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 138 52 288 72 145 273), lower := (rows 7 42 69 138 52 288 72 128 256), losses := [] }

theorem u487 : Upper (D 5) (R 5) [6,40,65,130,36,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 42 69 138 52 288 80 137 265), lower := (rows 7 42 69 138 52 288 80 128 256), losses := [] }

theorem u488 : Upper (D 5) (R 5) [6,40,65,130,36,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 138 273 48 68 168 296), lower := (rows 7 42 69 138 273 48 68 128 256), losses := [] }

theorem u489 : Upper (D 5) (R 5) [6,40,65,130,257,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 138 273 48 72 164 292), lower := (rows 7 42 69 138 273 48 72 128 256), losses := [] }

theorem u490 : Upper (D 5) (R 5) [6,40,65,130,257,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 138 273 48 96 140 268), lower := (rows 7 42 69 138 273 48 96 128 256), losses := [] }

theorem u491 : Upper (D 5) (R 5) [6,40,65,130,257,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 138 276 48 65 168 296), lower := (rows 7 42 69 138 276 48 65 128 256), losses := [] }

theorem u492 : Upper (D 5) (R 5) [6,40,65,130,260,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 138 276 48 72 161 289), lower := (rows 7 42 69 138 276 48 72 128 256), losses := [] }

theorem u493 : Upper (D 5) (R 5) [6,40,65,130,260,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 138 276 48 96 137 265), lower := (rows 7 42 69 138 276 48 96 128 256), losses := [] }

theorem u494 : Upper (D 5) (R 5) [6,40,65,130,260,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 280 36 65 176 304), lower := (rows 7 42 69 138 280 36 65 128 256), losses := [] }

theorem u495 : Upper (D 5) (R 5) [6,40,65,130,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r496 : Route 9 := (fun mask => (mask,id))

def c496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u496 : Upper (D 5) (R 5) [6,40,65,130,264,4,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,130,264,4,16] 13 (by decide) (choices 1) [1,32] r496 c496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u34
  · exact u35

def b497 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 69 138 280 36 96 145 273), lower := (rows 7 42 69 138 280 36 96 128 256), losses := [] }

theorem u497 : Upper (D 5) (R 5) [6,40,65,130,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 304 33 68 152 280), lower := (rows 7 42 69 138 304 33 68 128 256), losses := [] }

theorem u498 : Upper (D 5) (R 5) [6,40,65,130,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 69 138 304 33 72 148 276), lower := (rows 7 42 69 138 304 33 72 128 256), losses := [] }

theorem u499 : Upper (D 5) (R 5) [6,40,65,130,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 69 138 304 33 80 140 268), lower := (rows 7 42 69 138 304 33 80 128 256), losses := [] }

theorem u500 : Upper (D 5) (R 5) [6,40,65,130,288,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 138 304 36 65 152 280), lower := (rows 7 42 69 138 304 36 65 128 256), losses := [] }

theorem u501 : Upper (D 5) (R 5) [6,40,65,130,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 69 138 304 36 72 145 273), lower := (rows 7 42 69 138 304 36 72 128 256), losses := [] }

theorem u502 : Upper (D 5) (R 5) [6,40,65,130,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 4 }], pairs := [(3,2)], upper := (rows 7 42 69 138 304 36 80 137 265), lower := (rows 7 42 69 138 304 36 80 128 256), losses := [] }

theorem u503 : Upper (D 5) (R 5) [6,40,65,130,288,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 5, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 140 49 288 66 152 280), lower := (rows 7 42 69 140 49 288 66 128 256), losses := [] }

theorem u504 : Upper (D 5) (R 5) [6,40,65,132,33,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 42 69 140 49 288 72 146 274), lower := (rows 7 42 69 140 49 288 72 128 256), losses := [] }

theorem u505 : Upper (D 5) (R 5) [6,40,65,132,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 7 42 69 140 49 288 80 138 266), lower := (rows 7 42 69 140 49 288 80 128 256), losses := [] }

theorem u506 : Upper (D 5) (R 5) [6,40,65,132,33,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 140 274 48 65 168 296), lower := (rows 7 42 69 140 274 48 65 128 256), losses := [] }

theorem u507 : Upper (D 5) (R 5) [6,40,65,132,258,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 42 69 140 274 48 72 161 289), lower := (rows 7 42 69 140 274 48 72 128 256), losses := [] }

theorem u508 : Upper (D 5) (R 5) [6,40,65,132,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 140 274 48 96 137 265), lower := (rows 7 42 69 140 274 48 96 128 256), losses := [] }

theorem u509 : Upper (D 5) (R 5) [6,40,65,132,258,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 152 274 33 68 168 296), lower := (rows 7 42 69 152 274 33 68 128 256), losses := [] }

theorem u510 : Upper (D 5) (R 5) [6,40,65,144,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 152 274 33 72 164 292), lower := (rows 7 42 69 152 274 33 72 128 256), losses := [] }

theorem u511 : Upper (D 5) (R 5) [6,40,65,144,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 42 69 152 274 33 96 140 268), lower := (rows 7 42 69 152 274 33 96 128 256), losses := [] }

theorem u512 : Upper (D 5) (R 5) [6,40,65,144,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 152 274 36 65 168 296), lower := (rows 7 42 69 152 274 36 65 128 256), losses := [] }

theorem u513 : Upper (D 5) (R 5) [6,40,65,144,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 69 152 274 36 72 161 289), lower := (rows 7 42 69 152 274 36 72 128 256), losses := [] }

theorem u514 : Upper (D 5) (R 5) [6,40,65,144,258,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 69 152 274 36 96 137 265), lower := (rows 7 42 69 152 274 36 96 128 256), losses := [] }

theorem u515 : Upper (D 5) (R 5) [6,40,65,144,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 152 274 33 65 164 292), lower := (rows 7 42 76 152 274 33 65 128 256), losses := [] }

theorem u516 : Upper (D 5) (R 5) [6,40,72,144,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 76 152 274 33 68 161 289), lower := (rows 7 42 76 152 274 33 68 128 256), losses := [] }

theorem u517 : Upper (D 5) (R 5) [6,40,72,144,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 76 152 274 33 96 133 261), lower := (rows 7 42 76 152 274 33 96 128 256), losses := [] }

theorem u518 : Upper (D 5) (R 5) [6,40,72,144,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 42 76 152 276 33 65 162 290), lower := (rows 7 42 76 152 276 33 65 128 256), losses := [] }

theorem u519 : Upper (D 5) (R 5) [6,40,72,144,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 76 152 276 33 66 161 289), lower := (rows 7 42 76 152 276 33 66 128 256), losses := [] }

theorem u520 : Upper (D 5) (R 5) [6,40,72,144,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 76 152 276 33 96 131 259), lower := (rows 7 42 76 152 276 33 96 128 256), losses := [] }

theorem u521 : Upper (D 5) (R 5) [6,40,72,144,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 137 280 36 65 162 290), lower := (rows 7 42 84 137 280 36 65 128 256), losses := [] }

theorem u522 : Upper (D 5) (R 5) [6,40,80,129,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 42 84 137 280 36 66 161 289), lower := (rows 7 42 84 137 280 36 66 128 256), losses := [] }

theorem u523 : Upper (D 5) (R 5) [6,40,80,129,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 137 280 36 96 131 259), lower := (rows 7 42 84 137 280 36 96 128 256), losses := [] }

theorem u524 : Upper (D 5) (R 5) [6,40,80,129,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 84 138 273 33 68 168 296), lower := (rows 7 42 84 138 273 33 68 128 256), losses := [] }

theorem u525 : Upper (D 5) (R 5) [6,40,80,130,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 138 273 33 72 164 292), lower := (rows 7 42 84 138 273 33 72 128 256), losses := [] }

theorem u526 : Upper (D 5) (R 5) [6,40,80,130,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 84 138 273 33 96 140 268), lower := (rows 7 42 84 138 273 33 96 128 256), losses := [] }

theorem u527 : Upper (D 5) (R 5) [6,40,80,130,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 138, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 138 273 36 65 168 296), lower := (rows 7 42 84 138 273 36 65 128 256), losses := [] }

theorem u528 : Upper (D 5) (R 5) [6,40,80,130,257,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 138 273 36 72 161 289), lower := (rows 7 42 84 138 273 36 72 128 256), losses := [] }

theorem u529 : Upper (D 5) (R 5) [6,40,80,130,257,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 138 273 36 96 137 265), lower := (rows 7 42 84 138 273 36 96 128 256), losses := [] }

theorem u530 : Upper (D 5) (R 5) [6,40,80,130,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r531 : Route 9 := (fun mask => (mask,id))

def c531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u531 : Upper (D 5) (R 5) [6,40,80,130,264,4,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,264,4,1] 13 (by decide) (choices 1) [1,32] r531 c531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36
  · exact u37

def b532 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 138 280 36 96 129 257), lower := (rows 7 42 84 138 280 36 96 128 256), losses := [] }

theorem u532 : Upper (D 5) (R 5) [6,40,80,130,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 1 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 42 84 138 304 33 65 140 268), lower := (rows 7 42 84 138 304 33 65 128 256), losses := [] }

theorem u533 : Upper (D 5) (R 5) [6,40,80,130,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 42 84 138 304 33 68 137 265), lower := (rows 7 42 84 138 304 33 68 128 256), losses := [] }

theorem u534 : Upper (D 5) (R 5) [6,40,80,130,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 84 138 304 33 72 133 261), lower := (rows 7 42 84 138 304 33 72 128 256), losses := [] }

theorem u535 : Upper (D 5) (R 5) [6,40,80,130,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 274 33 65 168 296), lower := (rows 7 42 84 140 274 33 65 128 256), losses := [] }

theorem u536 : Upper (D 5) (R 5) [6,40,80,132,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 42 84 140 274 33 72 161 289), lower := (rows 7 42 84 140 274 33 72 128 256), losses := [] }

theorem u537 : Upper (D 5) (R 5) [6,40,80,132,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 84 140 274 33 96 137 265), lower := (rows 7 42 84 140 274 33 96 128 256), losses := [] }

theorem u538 : Upper (D 5) (R 5) [6,40,80,132,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 84 140 280 33 65 162 290), lower := (rows 7 42 84 140 280 33 65 128 256), losses := [] }

theorem u539 : Upper (D 5) (R 5) [6,40,80,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b539
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P05
