import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0034

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5520 : PairBound 9 := { available := 396, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 41 19 428 460 396 396), lower := (rows 7 26 100 41 19 32 64 128 256), losses := [] }

theorem u5520 : Upper (D 5) (R 5) [6,24,96,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5521 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 41 21 426 458 394 394), lower := (rows 7 26 100 41 21 32 64 128 256), losses := [] }

theorem u5521 : Upper (D 5) (R 5) [6,24,96,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5522 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 41 22 425 457 393 393), lower := (rows 7 26 100 41 22 32 64 128 256), losses := [] }

theorem u5522 : Upper (D 5) (R 5) [6,24,96,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5523 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 41 25 422 454 390 390), lower := (rows 7 26 100 41 25 32 64 128 256), losses := [] }

theorem u5523 : Upper (D 5) (R 5) [6,24,96,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 41 26 421 453 389 389), lower := (rows 7 26 100 41 26 32 64 128 256), losses := [] }

theorem u5524 : Upper (D 5) (R 5) [6,24,96,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 485, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 41 28 419 451 387 387), lower := (rows 7 26 100 41 28 32 64 128 256), losses := [] }

theorem u5525 : Upper (D 5) (R 5) [6,24,96,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5526 : Route 9 := (fun mask => (mask,id))

def c5526 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5526 : Upper (D 5) (R 5) [6,24,96,33,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,129] 13 (by decide) (choices 1) [2,4,8,256] r5526 c5526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2050
  · exact u2051
  · exact u2052
  · exact u2053

def b5527 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 41 146 301 333 397 269), lower := (rows 7 26 100 41 146 32 64 128 256), losses := [] }

theorem u5527 : Upper (D 5) (R 5) [6,24,96,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5528 : Route 9 := (fun mask => (mask,id))

def c5528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5528 : Upper (D 5) (R 5) [6,24,96,33,132] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,132] 13 (by decide) (choices 1) [1,2,8,256] r5528 c5528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2054
  · exact u2055
  · exact u2056
  · exact u2057

def b5529 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 41 152 295 327 391 263), lower := (rows 7 26 100 41 152 32 64 128 256), losses := [] }

theorem u5529 : Upper (D 5) (R 5) [6,24,96,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5530 : Route 9 := (fun mask => (mask,id))

def c5530 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5530 : Upper (D 5) (R 5) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [1,2,4,8] r5530 c5530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2058
  · exact u2059
  · exact u2060
  · exact u2061

def b5531 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 42 21 425 457 393 393), lower := (rows 7 26 100 42 21 32 64 128 256), losses := [] }

theorem u5531 : Upper (D 5) (R 5) [6,24,96,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5532 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 42 25 421 453 389 389), lower := (rows 7 26 100 42 25 32 64 128 256), losses := [] }

theorem u5532 : Upper (D 5) (R 5) [6,24,96,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5533 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 26, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 42 28 417 449 385 385), lower := (rows 7 26 100 42 28 32 64 128 256), losses := [] }

theorem u5533 : Upper (D 5) (R 5) [6,24,96,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5534 : Route 9 := (fun mask => (mask,id))

def c5534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5534 : Upper (D 5) (R 5) [6,24,96,34,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,129] 13 (by decide) (choices 1) [1,4,8,256] r5534 c5534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2062
  · exact u2063
  · exact u2064
  · exact u2065

def r5535 : Route 9 := (fun mask => (mask,id))

def c5535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5535 : Upper (D 5) (R 5) [6,24,96,34,132] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,132] 13 (by decide) (choices 1) [1,8,256] r5535 c5535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2066
  · exact u2067
  · exact u2068

def b5536 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 42 152 293 325 389 261), lower := (rows 7 26 100 42 152 32 64 128 256), losses := [] }

theorem u5536 : Upper (D 5) (R 5) [6,24,96,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5537 : Route 9 := (fun mask => (mask,id))

def c5537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5537 : Upper (D 5) (R 5) [6,24,96,34,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34,384] 13 (by decide) (choices 1) [1,4,8] r5537 c5537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2069
  · exact u2070
  · exact u2071

def b5538 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 137 19 300 364 428 300), lower := (rows 7 26 100 137 19 32 64 128 256), losses := [] }

theorem u5538 : Upper (D 5) (R 5) [6,24,96,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 137 21 298 362 426 298), lower := (rows 7 26 100 137 21 32 64 128 256), losses := [] }

theorem u5539 : Upper (D 5) (R 5) [6,24,96,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 137 22 297 361 425 297), lower := (rows 7 26 100 137 22 32 64 128 256), losses := [] }

theorem u5540 : Upper (D 5) (R 5) [6,24,96,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 100 137 25 294 358 422 294), lower := (rows 7 26 100 137 25 32 64 128 256), losses := [] }

theorem u5541 : Upper (D 5) (R 5) [6,24,96,129,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 137 26 293 357 421 293), lower := (rows 7 26 100 137 26 32 64 128 256), losses := [] }

theorem u5542 : Upper (D 5) (R 5) [6,24,96,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 357, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 137 28 291 355 419 291), lower := (rows 7 26 100 137 28 32 64 128 256), losses := [] }

theorem u5543 : Upper (D 5) (R 5) [6,24,96,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 392, targets := 32 },{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0),(3,5)], upper := (rows 7 26 100 137 49 302 334 398 270), lower := (rows 7 26 100 137 49 32 64 128 256), losses := [] }

theorem u5544 : Upper (D 5) (R 5) [6,24,96,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 137 50 301 333 397 269), lower := (rows 7 26 100 137 50 32 64 128 256), losses := [] }

theorem u5545 : Upper (D 5) (R 5) [6,24,96,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 100 137 52 299 331 395 267), lower := (rows 7 26 100 137 52 32 64 128 256), losses := [] }

theorem u5546 : Upper (D 5) (R 5) [6,24,96,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 137 56 295 327 391 263), lower := (rows 7 26 100 137 56 32 64 128 256), losses := [] }

theorem u5547 : Upper (D 5) (R 5) [6,24,96,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5548 : Route 9 := (fun mask => (mask,id))

def c5548 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5548 : Upper (D 5) (R 5) [6,24,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257] 13 (by decide) (choices 1) [2,4,8] r5548 c5548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2072
  · exact u2073
  · exact u2074

def b5549 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 137 274 45 109 173 301), lower := (rows 7 26 100 137 274 32 64 128 256), losses := [] }

theorem u5549 : Upper (D 5) (R 5) [6,24,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5550 : Route 9 := (fun mask => (mask,id))

def c5550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5550 : Upper (D 5) (R 5) [6,24,96,129,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260] 13 (by decide) (choices 1) [1,2,8] r5550 c5550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2075
  · exact u2076
  · exact u2077

def b5551 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 137 280 39 103 167 295), lower := (rows 7 26 100 137 280 32 64 128 256), losses := [] }

theorem u5551 : Upper (D 5) (R 5) [6,24,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5552 : Route 9 := (fun mask => (mask,id))

def c5552 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5552 : Upper (D 5) (R 5) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [1,2,4,8] r5552 c5552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2078
  · exact u2079
  · exact u2080
  · exact u2081

def b5553 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 138 21 297 361 425 297), lower := (rows 7 26 100 138 21 32 64 128 256), losses := [] }

theorem u5553 : Upper (D 5) (R 5) [6,24,96,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 138 25 293 357 421 293), lower := (rows 7 26 100 138 25 32 64 128 256), losses := [] }

theorem u5554 : Upper (D 5) (R 5) [6,24,96,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 356, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 100 138 28 289 353 417 289), lower := (rows 7 26 100 138 28 32 64 128 256), losses := [] }

theorem u5555 : Upper (D 5) (R 5) [6,24,96,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 26 100 138 49 301 333 397 269), lower := (rows 7 26 100 138 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 65 129 257), good := (rows 463 26 68 138 475 0 64 128 256) }] }

theorem u5556 : Upper (D 5) (R 5) [6,24,96,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5556
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 100 138 52 297 329 393 265), lower := (rows 7 26 100 138 52 32 64 128 256), losses := [] }

theorem u5557 : Upper (D 5) (R 5) [6,24,96,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 138 56 293 325 389 261), lower := (rows 7 26 100 138 56 32 64 128 256), losses := [] }

theorem u5558 : Upper (D 5) (R 5) [6,24,96,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5559 : Route 9 := (fun mask => (mask,id))

def c5559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5559 : Upper (D 5) (R 5) [6,24,96,130,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,257] 13 (by decide) (choices 1) [1,4,8] r5559 c5559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2082
  · exact u2083
  · exact u2084

def r5560 : Route 9 := (fun mask => (mask,id))

def c5560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5560 : Upper (D 5) (R 5) [6,24,96,130,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,260] 13 (by decide) (choices 1) [1,8] r5560 c5560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2085
  · exact u2086

def b5561 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 138 280 37 101 165 293), lower := (rows 7 26 100 138 280 32 64 128 256), losses := [] }

theorem u5561 : Upper (D 5) (R 5) [6,24,96,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5562 : Route 9 := (fun mask => (mask,id))

def c5562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5562 : Upper (D 5) (R 5) [6,24,96,130,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,288] 13 (by decide) (choices 1) [1,4,8] r5562 c5562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2087
  · exact u2088
  · exact u2089

def b5563 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 140 19 297 361 425 297), lower := (rows 7 26 100 140 19 32 64 128 256), losses := [] }

theorem u5563 : Upper (D 5) (R 5) [6,24,96,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 140 25 291 355 419 291), lower := (rows 7 26 100 140 25 32 64 128 256), losses := [] }

theorem u5564 : Upper (D 5) (R 5) [6,24,96,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5565 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 140 26 289 353 417 289), lower := (rows 7 26 100 140 26 32 64 128 256), losses := [] }

theorem u5565 : Upper (D 5) (R 5) [6,24,96,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 26 100 140 49 299 331 395 267), lower := (rows 7 26 100 140 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 9 16 0 81 145 273), good := (rows 463 474 68 140 475 0 64 128 256) }] }

theorem u5566 : Upper (D 5) (R 5) [6,24,96,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 140 50 297 329 393 265), lower := (rows 7 26 100 140 50 32 64 128 256), losses := [] }

theorem u5567 : Upper (D 5) (R 5) [6,24,96,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 140 56 291 323 387 259), lower := (rows 7 26 100 140 56 32 64 128 256), losses := [] }

theorem u5568 : Upper (D 5) (R 5) [6,24,96,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5569 : Route 9 := (fun mask => (mask,id))

def c5569 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5569 : Upper (D 5) (R 5) [6,24,96,132,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,257] 13 (by decide) (choices 1) [1,2,8] r5569 c5569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2090
  · exact u2091
  · exact u2092

def b5570 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 140 274 41 105 169 297), lower := (rows 7 26 100 140 274 32 64 128 256), losses := [] }

theorem u5570 : Upper (D 5) (R 5) [6,24,96,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 140 280 35 99 163 291), lower := (rows 7 26 100 140 280 32 64 128 256), losses := [] }

theorem u5571 : Upper (D 5) (R 5) [6,24,96,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5572 : Route 9 := (fun mask => (mask,id))

def c5572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5572 : Upper (D 5) (R 5) [6,24,96,132,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,288] 13 (by decide) (choices 1) [1,2,8] r5572 c5572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2093
  · exact u2094
  · exact u2095

def b5573 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 168 19 301 333 397 269), lower := (rows 7 26 100 168 19 32 64 128 256), losses := [] }

theorem u5573 : Upper (D 5) (R 5) [6,24,96,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 168 21 299 331 395 267), lower := (rows 7 26 100 168 21 32 64 128 256), losses := [] }

theorem u5574 : Upper (D 5) (R 5) [6,24,96,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 168 22 297 329 393 265), lower := (rows 7 26 100 168 22 32 64 128 256), losses := [] }

theorem u5575 : Upper (D 5) (R 5) [6,24,96,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 168 25 295 327 391 263), lower := (rows 7 26 100 168 25 32 64 128 256), losses := [] }

theorem u5576 : Upper (D 5) (R 5) [6,24,96,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 168 26 293 325 389 261), lower := (rows 7 26 100 168 26 32 64 128 256), losses := [] }

theorem u5577 : Upper (D 5) (R 5) [6,24,96,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5578 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 357, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 168 28 291 323 387 259), lower := (rows 7 26 100 168 28 32 64 128 256), losses := [] }

theorem u5578 : Upper (D 5) (R 5) [6,24,96,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5579 : Route 9 := (fun mask => (mask,id))

def c5579 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5579 : Upper (D 5) (R 5) [6,24,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,257] 13 (by decide) (choices 1) [1,2,4,8] r5579 c5579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2096
  · exact u2097
  · exact u2098
  · exact u2099

#print axioms u5579
end Delivery.IrregularNine14.P05
