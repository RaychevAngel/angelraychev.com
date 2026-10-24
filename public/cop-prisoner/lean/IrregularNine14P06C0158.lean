import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0016
import IrregularNine14P06C0017

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9480 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 140 273 34 112 240 368), lower := (rows 7 35 76 140 273 34 64 128 256), losses := [] }

theorem u9480 : Upper (D 6) (R 6) [6,33,72,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9480
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9481 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 273 48 98 226 354), lower := (rows 7 35 76 140 273 48 64 128 256), losses := [] }

theorem u9481 : Upper (D 6) (R 6) [6,33,72,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9482 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 140 273 96 114 178 306), lower := (rows 7 35 76 140 273 96 64 128 256), losses := [] }

theorem u9482 : Upper (D 6) (R 6) [6,33,72,132,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9482
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9483 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 140 274 33 112 240 368), lower := (rows 7 35 76 140 274 33 64 128 256), losses := [] }

theorem u9483 : Upper (D 6) (R 6) [6,33,72,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9483
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9484 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 274 48 97 225 353), lower := (rows 7 35 76 140 274 48 64 128 256), losses := [] }

theorem u9484 : Upper (D 6) (R 6) [6,33,72,132,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9484
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9485 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 140 274 96 113 177 305), lower := (rows 7 35 76 140 274 96 64 128 256), losses := [] }

theorem u9485 : Upper (D 6) (R 6) [6,33,72,132,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9485
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9486 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 140 304 33 82 210 338), lower := (rows 7 35 76 140 304 33 64 128 256), losses := [] }

theorem u9486 : Upper (D 6) (R 6) [6,33,72,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9486
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9487 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 140 304 34 81 209 337), lower := (rows 7 35 76 140 304 34 64 128 256), losses := [] }

theorem u9487 : Upper (D 6) (R 6) [6,33,72,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9487
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9488 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 140 304 48 67 195 323), lower := (rows 7 35 76 140 304 48 64 128 256), losses := [] }

theorem u9488 : Upper (D 6) (R 6) [6,33,72,132,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9488
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9489 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 140 304 96 83 147 275), lower := (rows 7 35 76 140 304 96 64 128 256), losses := [] }

theorem u9489 : Upper (D 6) (R 6) [6,33,72,132,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9490 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 140 336 33 114 178 306), lower := (rows 7 35 76 140 336 33 64 128 256), losses := [] }

theorem u9490 : Upper (D 6) (R 6) [6,33,72,132,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9490
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9491 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 140 336 34 113 177 305), lower := (rows 7 35 76 140 336 34 64 128 256), losses := [] }

theorem u9491 : Upper (D 6) (R 6) [6,33,72,132,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9491
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9492 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 336 48 99 163 291), lower := (rows 7 35 76 140 336 48 64 128 256), losses := [] }

theorem u9492 : Upper (D 6) (R 6) [6,33,72,132,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9492
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9493 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 82 33 356 420 292), lower := (rows 7 35 76 152 82 33 64 128 256), losses := [] }

theorem u9493 : Upper (D 6) (R 6) [6,33,72,144,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9493
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9494 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 152 82 36 353 417 289), lower := (rows 7 35 76 152 82 36 64 128 256), losses := [] }

theorem u9494 : Upper (D 6) (R 6) [6,33,72,144,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9494
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9495 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 152 82 288 101 165 293), lower := (rows 7 35 76 152 82 288 64 128 256), losses := [] }

theorem u9495 : Upper (D 6) (R 6) [6,33,72,144,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9495
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9496 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 112 33 326 390 262), lower := (rows 7 35 76 152 112 33 64 128 256), losses := [] }

theorem u9496 : Upper (D 6) (R 6) [6,33,72,144,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9497 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 112 34 325 389 261), lower := (rows 7 35 76 152 112 34 64 128 256), losses := [] }

theorem u9497 : Upper (D 6) (R 6) [6,33,72,144,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9497
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9498 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 76 152 112 36 323 387 259), lower := (rows 7 35 76 152 112 36 64 128 256), losses := [] }

theorem u9498 : Upper (D 6) (R 6) [6,33,72,144,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9498
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9499 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 152 112 288 71 135 263), lower := (rows 7 35 76 152 112 288 64 128 256), losses := [] }

theorem u9499 : Upper (D 6) (R 6) [6,33,72,144,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9499
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9500 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 273 34 100 228 356), lower := (rows 7 35 76 152 273 34 64 128 256), losses := [] }

theorem u9500 : Upper (D 6) (R 6) [6,33,72,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9500
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9501 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 152 273 36 98 226 354), lower := (rows 7 35 76 152 273 36 64 128 256), losses := [] }

theorem u9501 : Upper (D 6) (R 6) [6,33,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9501
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9502 : PairBound 9 := { available := 38, camps := [], pairs := [(1,2),(2,0),(3,0)], upper := (rows 7 35 76 152 273 96 102 166 294), lower := (rows 7 35 76 152 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 65 129 257), good := (rows 486 482 108 188 508 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 152 275 96 96 128 256) }] }

theorem u9502 : Upper (D 6) (R 6) [6,33,72,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9502
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9503 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 274 33 100 228 356), lower := (rows 7 35 76 152 274 33 64 128 256), losses := [] }

theorem u9503 : Upper (D 6) (R 6) [6,33,72,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9503
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9504 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 152 274 36 97 225 353), lower := (rows 7 35 76 152 274 36 64 128 256), losses := [] }

theorem u9504 : Upper (D 6) (R 6) [6,33,72,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9504
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9505 : Route 9 := (fun mask => (mask,id))

def c9505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9505 : Upper (D 6) (R 6) [6,33,72,144,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258,64] 13 (by decide) (choices 1) [1,4,32] r9505 c9505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1018
  · exact u1019
  · exact u1020

def b9506 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 276 33 98 226 354), lower := (rows 7 35 76 152 276 33 64 128 256), losses := [] }

theorem u9506 : Upper (D 6) (R 6) [6,33,72,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9506
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9507 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 276 34 97 225 353), lower := (rows 7 35 76 152 276 34 64 128 256), losses := [] }

theorem u9507 : Upper (D 6) (R 6) [6,33,72,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9507
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9508 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 76 152 276 96 99 163 291), lower := (rows 7 35 76 152 276 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 11 17 32 0 130 258), good := (rows 415 443 12 152 276 32 0 128 256) }] }

theorem u9508 : Upper (D 6) (R 6) [6,33,72,144,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9508
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9509 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 304 33 70 198 326), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u9509 : Upper (D 6) (R 6) [6,33,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9509
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9510 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 304 34 69 197 325), lower := (rows 7 35 76 152 304 34 64 128 256), losses := [] }

theorem u9510 : Upper (D 6) (R 6) [6,33,72,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9510
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9511 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 152 304 36 67 195 323), lower := (rows 7 35 76 152 304 36 64 128 256), losses := [] }

theorem u9511 : Upper (D 6) (R 6) [6,33,72,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9511
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9512 : PairBound 9 := { available := 7, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 76 152 304 96 71 135 263), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 152 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 11 18 32 0 129 257), good := (rows 415 443 12 152 304 32 0 128 256) }] }

theorem u9512 : Upper (D 6) (R 6) [6,33,72,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9512
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9513 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 336 33 102 166 294), lower := (rows 7 35 76 152 336 33 64 128 256), losses := [] }

theorem u9513 : Upper (D 6) (R 6) [6,33,72,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9513
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9514 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 336 34 101 165 293), lower := (rows 7 35 76 152 336 34 64 128 256), losses := [] }

theorem u9514 : Upper (D 6) (R 6) [6,33,72,144,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9514
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9515 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 152 336 36 99 163 291), lower := (rows 7 35 76 152 336 36 64 128 256), losses := [] }

theorem u9515 : Upper (D 6) (R 6) [6,33,72,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9515
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9516 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 168 81 34 340 404 276), lower := (rows 7 35 76 168 81 34 64 128 256), losses := [] }

theorem u9516 : Upper (D 6) (R 6) [6,33,72,160,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9516
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9517 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 168 81 36 338 402 274), lower := (rows 7 35 76 168 81 36 64 128 256), losses := [] }

theorem u9517 : Upper (D 6) (R 6) [6,33,72,160,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9517
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9518 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 168 81 48 326 390 262), lower := (rows 7 35 76 168 81 48 64 128 256), losses := [] }

theorem u9518 : Upper (D 6) (R 6) [6,33,72,160,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9518
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9519 : Route 9 := (fun mask => (mask,id))

def c9519 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9519 : Upper (D 6) (R 6) [6,33,72,160,65,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,65,256] 13 (by decide) (choices 1) [2,4,16] r9519 c9519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1021
  · exact u1022
  · exact u1023

def b9520 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 168 82 33 340 404 276), lower := (rows 7 35 76 168 82 33 64 128 256), losses := [] }

theorem u9520 : Upper (D 6) (R 6) [6,33,72,160,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9521 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 168 82 36 337 401 273), lower := (rows 7 35 76 168 82 36 64 128 256), losses := [] }

theorem u9521 : Upper (D 6) (R 6) [6,33,72,160,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9521
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9522 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 82 48 325 389 261), lower := (rows 7 35 76 168 82 48 64 128 256), losses := [] }

theorem u9522 : Upper (D 6) (R 6) [6,33,72,160,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9522
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9523 : Route 9 := (fun mask => (mask,id))

def c9523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9523 : Upper (D 6) (R 6) [6,33,72,160,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,66,256] 13 (by decide) (choices 1) [1,4,16] r9523 c9523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1024
  · exact u1025
  · exact u1026

def b9524 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 168 273 34 84 212 340), lower := (rows 7 35 76 168 273 34 64 128 256), losses := [] }

theorem u9524 : Upper (D 6) (R 6) [6,33,72,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9524
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9525 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 168 273 36 82 210 338), lower := (rows 7 35 76 168 273 36 64 128 256), losses := [] }

theorem u9525 : Upper (D 6) (R 6) [6,33,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9525
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9526 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 168 273 48 70 198 326), lower := (rows 7 35 76 168 273 48 64 128 256), losses := [] }

theorem u9526 : Upper (D 6) (R 6) [6,33,72,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9526
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9527 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 168 273 96 86 150 278), lower := (rows 7 35 76 168 273 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 168 275 96 96 128 256) }] }

theorem u9527 : Upper (D 6) (R 6) [6,33,72,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9527
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9528 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 168 274 33 84 212 340), lower := (rows 7 35 76 168 274 33 64 128 256), losses := [] }

theorem u9528 : Upper (D 6) (R 6) [6,33,72,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9528
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9529 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 168 274 36 81 209 337), lower := (rows 7 35 76 168 274 36 64 128 256), losses := [] }

theorem u9529 : Upper (D 6) (R 6) [6,33,72,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9529
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9530 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 168 274 48 69 197 325), lower := (rows 7 35 76 168 274 48 64 128 256), losses := [] }

theorem u9530 : Upper (D 6) (R 6) [6,33,72,160,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9531 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 168 274 96 85 149 277), lower := (rows 7 35 76 168 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 168 274 96 96 128 256) }] }

theorem u9531 : Upper (D 6) (R 6) [6,33,72,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9531
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9532 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 168 276 33 82 210 338), lower := (rows 7 35 76 168 276 33 64 128 256), losses := [] }

theorem u9532 : Upper (D 6) (R 6) [6,33,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9532
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9533 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 168 276 34 81 209 337), lower := (rows 7 35 76 168 276 34 64 128 256), losses := [] }

theorem u9533 : Upper (D 6) (R 6) [6,33,72,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9533
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9534 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 168 276 48 67 195 323), lower := (rows 7 35 76 168 276 48 64 128 256), losses := [] }

theorem u9534 : Upper (D 6) (R 6) [6,33,72,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9534
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9535 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 168 276 96 83 147 275), lower := (rows 7 35 76 168 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 168 304 96 96 128 256) }] }

theorem u9535 : Upper (D 6) (R 6) [6,33,72,160,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9535
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9536 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 168 336 33 86 150 278), lower := (rows 7 35 76 168 336 33 64 128 256), losses := [] }

theorem u9536 : Upper (D 6) (R 6) [6,33,72,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9536
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9537 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 168 336 34 85 149 277), lower := (rows 7 35 76 168 336 34 64 128 256), losses := [] }

theorem u9537 : Upper (D 6) (R 6) [6,33,72,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9537
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9538 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 168 336 36 83 147 275), lower := (rows 7 35 76 168 336 36 64 128 256), losses := [] }

theorem u9538 : Upper (D 6) (R 6) [6,33,72,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9538
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9539 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(3,6),(4,5)], upper := (rows 7 35 76 168 336 48 71 135 263), lower := (rows 7 35 76 168 336 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 10 16 48 0 129 257), good := (rows 399 427 12 168 304 48 0 128 256) }] }

theorem u9539 : Upper (D 6) (R 6) [6,33,72,160,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9539
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9539
end Delivery.IrregularNine14.P06
