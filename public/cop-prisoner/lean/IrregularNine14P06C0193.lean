import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0032

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11580 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 452, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 11 19 388 44 112 33 70 198 326), lower := (rows 11 19 388 44 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 39 56 48 32 67 131 259), good := (rows 462 478 388 60 124 508 64 128 256) }] }

theorem u11580 : Upper (D 6) (R 6) [10,17,384,36,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11580
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11581 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 19 388 44 112 34 69 197 325), lower := (rows 11 19 388 44 112 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 39 56 48 32 67 131 259), good := (rows 461 477 388 60 124 508 64 128 256) }] }

theorem u11581 : Upper (D 6) (R 6) [10,17,384,36,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11581
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11582 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 388 44 112 36 67 195 323), lower := (rows 11 19 388 44 112 36 64 128 256), losses := [] }

theorem u11582 : Upper (D 6) (R 6) [10,17,384,36,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11582
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11583 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 388 44 112 96 71 135 263), lower := (rows 11 19 388 44 112 96 64 128 256), losses := [] }

theorem u11583 : Upper (D 6) (R 6) [10,17,384,36,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11583
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11584 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 22 37 73 400 34 100 228 356), lower := (rows 11 22 37 73 400 34 64 128 256), losses := [] }

theorem u11584 : Upper (D 6) (R 6) [10,20,33,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11584
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11585 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 22 37 73 400 36 98 226 354), lower := (rows 11 22 37 73 400 36 64 128 256), losses := [] }

theorem u11585 : Upper (D 6) (R 6) [10,20,33,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11585
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11586 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 73 400 96 102 166 294), lower := (rows 11 22 37 73 400 96 64 128 256), losses := [] }

theorem u11586 : Upper (D 6) (R 6) [10,20,33,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11586
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11587 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 22 37 76 145 34 352 480 352), lower := (rows 11 22 37 76 145 34 64 128 256), losses := [] }

theorem u11587 : Upper (D 6) (R 6) [10,20,33,68,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11587
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11588 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 22 37 76 145 96 354 418 290), lower := (rows 11 22 37 76 145 96 64 128 256), losses := [] }

theorem u11588 : Upper (D 6) (R 6) [10,20,33,68,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11588
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11589 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 496, targets := 4 },{ cop := 1, region := 360, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 22 37 76 145 288 98 226 354), lower := (rows 11 22 37 76 145 288 64 128 256), losses := [] }

theorem u11589 : Upper (D 6) (R 6) [10,20,33,68,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11589
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11590 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 76 208 33 354 418 290), lower := (rows 11 22 37 76 208 33 64 128 256), losses := [] }

theorem u11590 : Upper (D 6) (R 6) [10,20,33,68,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11590
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11591 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 0, region := 496, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 37 76 208 34 353 417 289), lower := (rows 11 22 37 76 208 34 64 128 256), losses := [] }

theorem u11591 : Upper (D 6) (R 6) [10,20,33,68,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11591
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11592 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 496, targets := 4 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6),(4,2)], upper := (rows 11 22 37 76 208 288 99 163 291), lower := (rows 11 22 37 76 208 288 64 128 256), losses := [] }

theorem u11592 : Upper (D 6) (R 6) [10,20,33,68,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11592
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11593 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 76 400 33 98 226 354), lower := (rows 11 22 37 76 400 33 64 128 256), losses := [] }

theorem u11593 : Upper (D 6) (R 6) [10,20,33,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11593
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11594 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 0, region := 496, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 37 76 400 34 97 225 353), lower := (rows 11 22 37 76 400 34 64 128 256), losses := [] }

theorem u11594 : Upper (D 6) (R 6) [10,20,33,68,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11594
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11595 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(1,6),(4,2),(4,6)], upper := (rows 11 22 37 76 400 96 99 163 291), lower := (rows 11 22 37 76 400 96 64 128 256), losses := [] }

theorem u11595 : Upper (D 6) (R 6) [10,20,33,68,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11595
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11596 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 104 400 33 70 198 326), lower := (rows 11 22 37 104 400 33 64 128 256), losses := [] }

theorem u11596 : Upper (D 6) (R 6) [10,20,33,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11596
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11597 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 22 37 104 400 34 69 197 325), lower := (rows 11 22 37 104 400 34 64 128 256), losses := [] }

theorem u11597 : Upper (D 6) (R 6) [10,20,33,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11597
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11598 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 22 37 104 400 36 67 195 323), lower := (rows 11 22 37 104 400 36 64 128 256), losses := [] }

theorem u11598 : Upper (D 6) (R 6) [10,20,33,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11598
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11599 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 104 400 96 71 135 263), lower := (rows 11 22 37 104 400 96 64 128 256), losses := [] }

theorem u11599 : Upper (D 6) (R 6) [10,20,33,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11599
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11600 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 2, region := 200, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 22 37 137 336 34 100 228 356), lower := (rows 11 22 37 137 336 34 64 128 256), losses := [] }

theorem u11600 : Upper (D 6) (R 6) [10,20,33,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11601 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 22 37 137 336 36 98 226 354), lower := (rows 11 22 37 137 336 36 64 128 256), losses := [] }

theorem u11601 : Upper (D 6) (R 6) [10,20,33,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11602 : Route 9 := (fun mask => (mask,id))

def c11602 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11602 : Upper (D 6) (R 6) [10,20,33,129,320,64] 13 := by
  apply FastRouting.sound _ _ [10,20,33,129,320,64] 13 (by decide) (choices 1) [2,4,32] r11602 c11602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1934
  · exact u1935
  · exact u1936

def b11603 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 22 37 140 81 34 352 480 352), lower := (rows 11 22 37 140 81 34 64 128 256), losses := [] }

theorem u11603 : Upper (D 6) (R 6) [10,20,33,132,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11603
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11604 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 488, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 22 37 140 81 96 354 418 290), lower := (rows 11 22 37 140 81 96 64 128 256), losses := [] }

theorem u11604 : Upper (D 6) (R 6) [10,20,33,132,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11604
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11605 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 488, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 22 37 140 81 288 98 226 354), lower := (rows 11 22 37 140 81 288 64 128 256), losses := [] }

theorem u11605 : Upper (D 6) (R 6) [10,20,33,132,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11605
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11606 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 22 37 140 273 34 96 224 352), lower := (rows 11 22 37 140 273 34 64 128 256), losses := [] }

theorem u11606 : Upper (D 6) (R 6) [10,20,33,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11606
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11607 : Route 9 := (fun mask => (mask,id))

def c11607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11607 : Upper (D 6) (R 6) [10,20,33,132,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132,257,64] 13 (by decide) (choices 1) [2,32] r11607 c11607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1937
  · exact u1938

def b11608 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 140 336 33 98 226 354), lower := (rows 11 22 37 140 336 33 64 128 256), losses := [] }

theorem u11608 : Upper (D 6) (R 6) [10,20,33,132,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11609 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 37 140 336 34 97 225 353), lower := (rows 11 22 37 140 336 34 64 128 256), losses := [] }

theorem u11609 : Upper (D 6) (R 6) [10,20,33,132,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11610 : Route 9 := (fun mask => (mask,id))

def c11610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11610 : Upper (D 6) (R 6) [10,20,33,132,320,64] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132,320,64] 13 (by decide) (choices 1) [1,2,32] r11610 c11610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1939
  · exact u1940
  · exact u1941

def b11611 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 168 336 33 70 198 326), lower := (rows 11 22 37 168 336 33 64 128 256), losses := [] }

theorem u11611 : Upper (D 6) (R 6) [10,20,33,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11611
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11612 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 22 37 168 336 34 69 197 325), lower := (rows 11 22 37 168 336 34 64 128 256), losses := [] }

theorem u11612 : Upper (D 6) (R 6) [10,20,33,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11613 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 22 37 168 336 36 67 195 323), lower := (rows 11 22 37 168 336 36 64 128 256), losses := [] }

theorem u11613 : Upper (D 6) (R 6) [10,20,33,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11613
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11614 : Route 9 := (fun mask => (mask,id))

def c11614 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11614 : Upper (D 6) (R 6) [10,20,33,160,320,64] 13 := by
  apply FastRouting.sound _ _ [10,20,33,160,320,64] 13 (by decide) (choices 1) [1,2,4] r11614 c11614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1942
  · exact u1943
  · exact u1944

def b11615 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 22 37 200 273 34 100 228 356), lower := (rows 11 22 37 200 273 34 64 128 256), losses := [] }

theorem u11615 : Upper (D 6) (R 6) [10,20,33,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11615
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11616 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 1, region := 232, targets := 1 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 22 37 200 273 36 98 226 354), lower := (rows 11 22 37 200 273 36 64 128 256), losses := [] }

theorem u11616 : Upper (D 6) (R 6) [10,20,33,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11616
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11617 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 274, targets := 64 },{ cop := 1, region := 232, targets := 1 }], pairs := [(1,6),(3,0),(4,6)], upper := (rows 11 22 37 200 273 96 102 166 294), lower := (rows 11 22 37 200 273 96 64 128 256), losses := [] }

theorem u11617 : Upper (D 6) (R 6) [10,20,33,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11618 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 200 274 33 100 228 356), lower := (rows 11 22 37 200 274 33 64 128 256), losses := [] }

theorem u11618 : Upper (D 6) (R 6) [10,20,33,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11618
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11619 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 22 37 200 274 36 97 225 353), lower := (rows 11 22 37 200 274 36 64 128 256), losses := [] }

theorem u11619 : Upper (D 6) (R 6) [10,20,33,192,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11619
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11620 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 274, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 22 37 200 274 96 101 165 293), lower := (rows 11 22 37 200 274 96 64 128 256), losses := [] }

theorem u11620 : Upper (D 6) (R 6) [10,20,33,192,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11620
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11621 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 200 304 33 70 198 326), lower := (rows 11 22 37 200 304 33 64 128 256), losses := [] }

theorem u11621 : Upper (D 6) (R 6) [10,20,33,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11621
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11622 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 2, region := 200, targets := 2 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 22 37 200 304 34 69 197 325), lower := (rows 11 22 37 200 304 34 64 128 256), losses := [] }

theorem u11622 : Upper (D 6) (R 6) [10,20,33,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11623 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 37 200 304 36 67 195 323), lower := (rows 11 22 37 200 304 36 64 128 256), losses := [] }

theorem u11623 : Upper (D 6) (R 6) [10,20,33,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11623
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11624 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 2, region := 274, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 37 200 304 96 71 135 263), lower := (rows 11 22 37 200 304 96 64 128 256), losses := [] }

theorem u11624 : Upper (D 6) (R 6) [10,20,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11624
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11625 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 200 336 33 102 166 294), lower := (rows 11 22 37 200 336 33 64 128 256), losses := [] }

theorem u11625 : Upper (D 6) (R 6) [10,20,33,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11626 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 22 37 200 336 34 101 165 293), lower := (rows 11 22 37 200 336 34 64 128 256), losses := [] }

theorem u11626 : Upper (D 6) (R 6) [10,20,33,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11626
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11627 : Route 9 := (fun mask => (mask,id))

def c11627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11627 : Upper (D 6) (R 6) [10,20,33,192,320,4] 13 := by
  apply FastRouting.sound _ _ [10,20,33,192,320,4] 13 (by decide) (choices 1) [1,2,32] r11627 c11627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1945
  · exact u1946
  · exact u1947

def b11628 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 472, targets := 2 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 22 37 392 81 34 100 228 356), lower := (rows 11 22 37 392 81 34 64 128 256), losses := [] }

theorem u11628 : Upper (D 6) (R 6) [10,20,33,384,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11628
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11629 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 1, region := 488, targets := 1 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 22 37 392 81 36 98 226 354), lower := (rows 11 22 37 392 81 36 64 128 256), losses := [] }

theorem u11629 : Upper (D 6) (R 6) [10,20,33,384,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11629
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11630 : Route 9 := (fun mask => (mask,id))

def c11630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11630 : Upper (D 6) (R 6) [10,20,33,384,65,64] 13 := by
  apply FastRouting.sound _ _ [10,20,33,384,65,64] 13 (by decide) (choices 1) [2,4,32] r11630 c11630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1948
  · exact u1949
  · exact u1950

def b11631 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 392 82 33 100 228 356), lower := (rows 11 22 37 392 82 33 64 128 256), losses := [] }

theorem u11631 : Upper (D 6) (R 6) [10,20,33,384,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11631
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11632 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 22 37 392 82 36 97 225 353), lower := (rows 11 22 37 392 82 36 64 128 256), losses := [] }

theorem u11632 : Upper (D 6) (R 6) [10,20,33,384,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11633 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 392, targets := 64 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 11 22 37 392 82 96 101 165 293), lower := (rows 11 22 37 392 82 96 64 128 256), losses := [] }

theorem u11633 : Upper (D 6) (R 6) [10,20,33,384,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11633
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11634 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 22 37 392 112 33 70 198 326), lower := (rows 11 22 37 392 112 33 64 128 256), losses := [] }

theorem u11634 : Upper (D 6) (R 6) [10,20,33,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11634
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11635 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 456, targets := 2 }], pairs := [(0,5),(3,1),(3,5)], upper := (rows 11 22 37 392 112 34 69 197 325), lower := (rows 11 22 37 392 112 34 64 128 256), losses := [] }

theorem u11635 : Upper (D 6) (R 6) [10,20,33,384,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11635
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11636 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 37 392 112 36 67 195 323), lower := (rows 11 22 37 392 112 36 64 128 256), losses := [] }

theorem u11636 : Upper (D 6) (R 6) [10,20,33,384,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11636
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11637 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 392 112 96 71 135 263), lower := (rows 11 22 37 392 112 96 64 128 256), losses := [] }

theorem u11637 : Upper (D 6) (R 6) [10,20,33,384,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11637
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11638 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 73 208 33 356 420 292), lower := (rows 11 22 38 73 208 33 64 128 256), losses := [] }

theorem u11638 : Upper (D 6) (R 6) [10,20,34,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11638
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11639 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 208 36 353 417 289), lower := (rows 11 22 38 73 208 36 64 128 256), losses := [] }

theorem u11639 : Upper (D 6) (R 6) [10,20,34,65,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11639
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11639
end Delivery.IrregularNine14.P06
