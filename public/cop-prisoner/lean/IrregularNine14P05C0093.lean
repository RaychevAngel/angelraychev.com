import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0035

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5580 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 168 274 45 77 141 269), lower := (rows 7 26 100 168 274 32 64 128 256), losses := [] }

theorem u5580 : Upper (D 5) (R 5) [6,24,96,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5581 : Route 9 := (fun mask => (mask,id))

def c5581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5581 : Upper (D 5) (R 5) [6,24,96,160,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,260] 13 (by decide) (choices 1) [1,2,8] r5581 c5581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2100
  · exact u2101
  · exact u2102

def b5582 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 168 280 39 71 135 263), lower := (rows 7 26 100 168 280 32 64 128 256), losses := [] }

theorem u5582 : Upper (D 5) (R 5) [6,24,96,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 100 392 19 45 109 173 301), lower := (rows 7 26 100 392 19 32 64 128 256), losses := [] }

theorem u5583 : Upper (D 5) (R 5) [6,24,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 100 392 21 43 107 171 299), lower := (rows 7 26 100 392 21 32 64 128 256), losses := [] }

theorem u5584 : Upper (D 5) (R 5) [6,24,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 392 22 41 105 169 297), lower := (rows 7 26 100 392 22 32 64 128 256), losses := [] }

theorem u5585 : Upper (D 5) (R 5) [6,24,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 392 25 39 103 167 295), lower := (rows 7 26 100 392 25 32 64 128 256), losses := [] }

theorem u5586 : Upper (D 5) (R 5) [6,24,96,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5587 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 392 26 37 101 165 293), lower := (rows 7 26 100 392 26 32 64 128 256), losses := [] }

theorem u5587 : Upper (D 5) (R 5) [6,24,96,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5588 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 392 28 35 99 163 291), lower := (rows 7 26 100 392 28 32 64 128 256), losses := [] }

theorem u5588 : Upper (D 5) (R 5) [6,24,96,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5589 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 392, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 7 26 100 392 49 47 79 143 271), lower := (rows 7 26 100 392 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 65 129 257), good := (rows 463 26 68 392 475 0 64 128 256) }] }

theorem u5589 : Upper (D 5) (R 5) [6,24,96,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 100 392 50 45 77 141 269), lower := (rows 7 26 100 392 50 32 64 128 256), losses := [] }

theorem u5590 : Upper (D 5) (R 5) [6,24,96,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5591 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 100 392 52 43 75 139 267), lower := (rows 7 26 100 392 52 32 64 128 256), losses := [] }

theorem u5591 : Upper (D 5) (R 5) [6,24,96,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5592 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 100 392 56 39 71 135 263), lower := (rows 7 26 100 392 56 32 64 128 256), losses := [] }

theorem u5592 : Upper (D 5) (R 5) [6,24,96,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5593 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 196 41 19 300 364 428 300), lower := (rows 7 26 196 41 19 32 64 128 256), losses := [] }

theorem u5593 : Upper (D 5) (R 5) [6,24,192,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 41 21 298 362 426 298), lower := (rows 7 26 196 41 21 32 64 128 256), losses := [] }

theorem u5594 : Upper (D 5) (R 5) [6,24,192,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 41 22 297 361 425 297), lower := (rows 7 26 196 41 22 32 64 128 256), losses := [] }

theorem u5595 : Upper (D 5) (R 5) [6,24,192,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5596 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 196 41 25 294 358 422 294), lower := (rows 7 26 196 41 25 32 64 128 256), losses := [] }

theorem u5596 : Upper (D 5) (R 5) [6,24,192,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5597 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 41 26 293 357 421 293), lower := (rows 7 26 196 41 26 32 64 128 256), losses := [] }

theorem u5597 : Upper (D 5) (R 5) [6,24,192,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 485, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 196 41 28 291 355 419 291), lower := (rows 7 26 196 41 28 32 64 128 256), losses := [] }

theorem u5598 : Upper (D 5) (R 5) [6,24,192,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 41 49 302 334 398 270), lower := (rows 7 26 196 41 49 32 64 128 256), losses := [] }

theorem u5599 : Upper (D 5) (R 5) [6,24,192,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 41 50 301 333 397 269), lower := (rows 7 26 196 41 50 32 64 128 256), losses := [] }

theorem u5600 : Upper (D 5) (R 5) [6,24,192,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5601 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 41 52 299 331 395 267), lower := (rows 7 26 196 41 52 32 64 128 256), losses := [] }

theorem u5601 : Upper (D 5) (R 5) [6,24,192,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5602 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 41 56 295 327 391 263), lower := (rows 7 26 196 41 56 32 64 128 256), losses := [] }

theorem u5602 : Upper (D 5) (R 5) [6,24,192,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5603 : Route 9 := (fun mask => (mask,id))

def c5603 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5603 : Upper (D 5) (R 5) [6,24,192,33,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,257] 13 (by decide) (choices 1) [2,4,8] r5603 c5603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2103
  · exact u2104
  · exact u2105

def b5604 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 41 274 45 109 173 301), lower := (rows 7 26 196 41 274 32 64 128 256), losses := [] }

theorem u5604 : Upper (D 5) (R 5) [6,24,192,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5605 : Route 9 := (fun mask => (mask,id))

def c5605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5605 : Upper (D 5) (R 5) [6,24,192,33,260] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,260] 13 (by decide) (choices 1) [1,2,8] r5605 c5605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2106
  · exact u2107
  · exact u2108

def b5606 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 41 280 39 103 167 295), lower := (rows 7 26 196 41 280 32 64 128 256), losses := [] }

theorem u5606 : Upper (D 5) (R 5) [6,24,192,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 41 304 47 79 143 271), lower := (rows 7 26 196 41 304 32 64 128 256), losses := [] }

theorem u5607 : Upper (D 5) (R 5) [6,24,192,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 42 21 297 361 425 297), lower := (rows 7 26 196 42 21 32 64 128 256), losses := [] }

theorem u5608 : Upper (D 5) (R 5) [6,24,192,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 25 293 357 421 293), lower := (rows 7 26 196 42 25 32 64 128 256), losses := [] }

theorem u5609 : Upper (D 5) (R 5) [6,24,192,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 484, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 196 42 28 289 353 417 289), lower := (rows 7 26 196 42 28 32 64 128 256), losses := [] }

theorem u5610 : Upper (D 5) (R 5) [6,24,192,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5611 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 49 301 333 397 269), lower := (rows 7 26 196 42 49 32 64 128 256), losses := [] }

theorem u5611 : Upper (D 5) (R 5) [6,24,192,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 52 297 329 393 265), lower := (rows 7 26 196 42 52 32 64 128 256), losses := [] }

theorem u5612 : Upper (D 5) (R 5) [6,24,192,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 26, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 56 293 325 389 261), lower := (rows 7 26 196 42 56 32 64 128 256), losses := [] }

theorem u5613 : Upper (D 5) (R 5) [6,24,192,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5614 : Route 9 := (fun mask => (mask,id))

def c5614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5614 : Upper (D 5) (R 5) [6,24,192,34,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,34,257] 13 (by decide) (choices 1) [1,4,8] r5614 c5614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2109
  · exact u2110
  · exact u2111

def r5615 : Route 9 := (fun mask => (mask,id))

def c5615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5615 : Upper (D 5) (R 5) [6,24,192,34,260] 13 := by
  apply FastRouting.sound _ _ [6,24,192,34,260] 13 (by decide) (choices 1) [1,8] r5615 c5615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2112
  · exact u2113

def b5616 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 280 37 101 165 293), lower := (rows 7 26 196 42 280 32 64 128 256), losses := [] }

theorem u5616 : Upper (D 5) (R 5) [6,24,192,34,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 42 304 45 77 141 269), lower := (rows 7 26 196 42 304 32 64 128 256), losses := [] }

theorem u5617 : Upper (D 5) (R 5) [6,24,192,34,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 196 44 19 297 361 425 297), lower := (rows 7 26 196 44 19 32 64 128 256), losses := [] }

theorem u5618 : Upper (D 5) (R 5) [6,24,192,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 196 44 25 291 355 419 291), lower := (rows 7 26 196 44 25 32 64 128 256), losses := [] }

theorem u5619 : Upper (D 5) (R 5) [6,24,192,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 44 26 289 353 417 289), lower := (rows 7 26 196 44 26 32 64 128 256), losses := [] }

theorem u5620 : Upper (D 5) (R 5) [6,24,192,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 44 49 299 331 395 267), lower := (rows 7 26 196 44 49 32 64 128 256), losses := [] }

theorem u5621 : Upper (D 5) (R 5) [6,24,192,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 44 50 297 329 393 265), lower := (rows 7 26 196 44 50 32 64 128 256), losses := [] }

theorem u5622 : Upper (D 5) (R 5) [6,24,192,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 44 56 291 323 387 259), lower := (rows 7 26 196 44 56 32 64 128 256), losses := [] }

theorem u5623 : Upper (D 5) (R 5) [6,24,192,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5624 : Route 9 := (fun mask => (mask,id))

def c5624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5624 : Upper (D 5) (R 5) [6,24,192,36,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,36,257] 13 (by decide) (choices 1) [1,2,8] r5624 c5624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2114
  · exact u2115
  · exact u2116

def b5625 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 44 274 41 105 169 297), lower := (rows 7 26 196 44 274 32 64 128 256), losses := [] }

theorem u5625 : Upper (D 5) (R 5) [6,24,192,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 44 280 35 99 163 291), lower := (rows 7 26 196 44 280 32 64 128 256), losses := [] }

theorem u5626 : Upper (D 5) (R 5) [6,24,192,36,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 44 304 43 75 139 267), lower := (rows 7 26 196 44 304 32 64 128 256), losses := [] }

theorem u5627 : Upper (D 5) (R 5) [6,24,192,36,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 196 265 19 44 108 172 300), lower := (rows 7 26 196 265 19 32 64 128 256), losses := [] }

theorem u5628 : Upper (D 5) (R 5) [6,24,192,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 265 21 42 106 170 298), lower := (rows 7 26 196 265 21 32 64 128 256), losses := [] }

theorem u5629 : Upper (D 5) (R 5) [6,24,192,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 265 22 41 105 169 297), lower := (rows 7 26 196 265 22 32 64 128 256), losses := [] }

theorem u5630 : Upper (D 5) (R 5) [6,24,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 196 265 25 38 102 166 294), lower := (rows 7 26 196 265 25 32 64 128 256), losses := [] }

theorem u5631 : Upper (D 5) (R 5) [6,24,192,257,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 265 26 37 101 165 293), lower := (rows 7 26 196 265 26 32 64 128 256), losses := [] }

theorem u5632 : Upper (D 5) (R 5) [6,24,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 229, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 196 265 28 35 99 163 291), lower := (rows 7 26 196 265 28 32 64 128 256), losses := [] }

theorem u5633 : Upper (D 5) (R 5) [6,24,192,257,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5634 : Route 9 := (fun mask => (mask,id))

def c5634 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5634 : Upper (D 5) (R 5) [6,24,192,257,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,257,33] 13 (by decide) (choices 1) [2,4,8] r5634 c5634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2117
  · exact u2118
  · exact u2119

def b5635 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 265 50 45 109 173 301), lower := (rows 7 26 196 265 50 32 64 128 256), losses := [] }

theorem u5635 : Upper (D 5) (R 5) [6,24,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5636 : Route 9 := (fun mask => (mask,id))

def c5636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5636 : Upper (D 5) (R 5) [6,24,192,257,36] 13 := by
  apply FastRouting.sound _ _ [6,24,192,257,36] 13 (by decide) (choices 1) [1,2,8] r5636 c5636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2120
  · exact u2121
  · exact u2122

def b5637 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 265 56 39 103 167 295), lower := (rows 7 26 196 265 56 32 64 128 256), losses := [] }

theorem u5637 : Upper (D 5) (R 5) [6,24,192,257,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5638 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 266 21 41 105 169 297), lower := (rows 7 26 196 266 21 32 64 128 256), losses := [] }

theorem u5638 : Upper (D 5) (R 5) [6,24,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5639 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 266 25 37 101 165 293), lower := (rows 7 26 196 266 25 32 64 128 256), losses := [] }

theorem u5639 : Upper (D 5) (R 5) [6,24,192,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5639
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P05
