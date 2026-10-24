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

def b600 : PairBound 9 := { available := 34, camps := [], pairs := [(1,0),(2,0)], upper := (rows 7 50 76 140 280 33 65 162 290), lower := (rows 7 50 76 140 280 33 65 128 256), losses := [{ target := 0, region := (rows 0 34 68 9 49 32 64 162 290), good := (rows 414 434 76 140 280 442 92 128 256) }] }

theorem u600 : Upper (D 5) (R 5) [6,48,72,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 140 280 33 66 161 289), lower := (rows 7 50 76 140 280 33 66 128 256), losses := [] }

theorem u601 : Upper (D 5) (R 5) [6,48,72,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 50 76 140 280 33 96 131 259), lower := (rows 7 50 76 140 280 33 96 128 256), losses := [] }

theorem u602 : Upper (D 5) (R 5) [6,48,72,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 6, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 50 76 168 280 33 65 134 262), lower := (rows 7 50 76 168 280 33 65 128 256), losses := [{ target := 0, region := (rows 0 42 4 40 52 32 64 133 261), good := (rows 406 58 478 186 282 442 448 128 256) }] }

theorem u603 : Upper (D 5) (R 5) [6,48,72,160,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 168 280 33 66 133 261), lower := (rows 7 50 76 168 280 33 66 128 256), losses := [] }

theorem u604 : Upper (D 5) (R 5) [6,48,72,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 50 76 168 280 33 68 131 259), lower := (rows 7 50 76 168 280 33 68 128 256), losses := [] }

theorem u605 : Upper (D 5) (R 5) [6,48,72,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r606 : Route 9 := (fun mask => (mask,id))

def c606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u606 : Upper (D 5) (R 5) [6,48,72,160,264,4,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,264,4,1] 13 (by decide) (choices 1) [1,2] r606 c606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u38
  · exact u39

def b607 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 76 168 280 36 66 129 257), lower := (rows 7 50 76 168 280 36 66 128 256), losses := [] }

theorem u607 : Upper (D 5) (R 5) [6,48,72,160,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 274, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 44 280 33 65 138 266), lower := (rows 7 50 196 44 280 33 65 128 256), losses := [] }

theorem u608 : Upper (D 5) (R 5) [6,48,192,36,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 196 44 280 33 66 137 265), lower := (rows 7 50 196 44 280 33 66 128 256), losses := [] }

theorem u609 : Upper (D 5) (R 5) [6,48,192,36,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 40, targets := 2 }], pairs := [(0,5),(3,1)], upper := (rows 7 50 196 44 280 33 72 131 259), lower := (rows 7 50 196 44 280 33 72 128 256), losses := [{ target := 5, region := (rows 3 2 6 8 16 0 88 131 259), good := (rows 391 471 196 76 344 385 72 128 256) }] }

theorem u610 : Upper (D 5) (R 5) [6,48,192,36,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 25 304 36 66 168 296), lower := (rows 7 67 140 25 304 36 66 128 256), losses := [] }

theorem u611 : Upper (D 5) (R 5) [6,65,136,17,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 140 25 304 36 72 162 290), lower := (rows 7 67 140 25 304 36 72 128 256), losses := [] }

theorem u612 : Upper (D 5) (R 5) [6,65,136,17,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 25 304 36 96 138 266), lower := (rows 7 67 140 25 304 36 96 128 256), losses := [] }

theorem u613 : Upper (D 5) (R 5) [6,65,136,17,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 26 52 288 65 168 296), lower := (rows 7 67 140 26 52 288 65 128 256), losses := [] }

theorem u614 : Upper (D 5) (R 5) [6,65,136,18,36,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 26 52 288 72 161 289), lower := (rows 7 67 140 26 52 288 72 128 256), losses := [] }

theorem u615 : Upper (D 5) (R 5) [6,65,136,18,36,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 26 52 288 96 137 265), lower := (rows 7 67 140 26 52 288 96 128 256), losses := [] }

theorem u616 : Upper (D 5) (R 5) [6,65,136,18,36,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 26 304 36 65 168 296), lower := (rows 7 67 140 26 304 36 65 128 256), losses := [] }

theorem u617 : Upper (D 5) (R 5) [6,65,136,18,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 26 304 36 72 161 289), lower := (rows 7 67 140 26 304 36 72 128 256), losses := [] }

theorem u618 : Upper (D 5) (R 5) [6,65,136,18,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 140 26 304 36 96 137 265), lower := (rows 7 67 140 26 304 36 96 128 256), losses := [] }

theorem u619 : Upper (D 5) (R 5) [6,65,136,18,288,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 140 26 304 40 65 164 292), lower := (rows 7 67 140 26 304 40 65 128 256), losses := [] }

theorem u620 : Upper (D 5) (R 5) [6,65,136,18,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 140 26 304 40 68 161 289), lower := (rows 7 67 140 26 304 40 68 128 256), losses := [] }

theorem u621 : Upper (D 5) (R 5) [6,65,136,18,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 67 140 26 304 40 96 133 261), lower := (rows 7 67 140 26 304 40 96 128 256), losses := [] }

theorem u622 : Upper (D 5) (R 5) [6,65,136,18,288,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 28 49 288 66 168 296), lower := (rows 7 67 140 28 49 288 66 128 256), losses := [] }

theorem u623 : Upper (D 5) (R 5) [6,65,136,20,33,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 28 49 288 72 162 290), lower := (rows 7 67 140 28 49 288 72 128 256), losses := [] }

theorem u624 : Upper (D 5) (R 5) [6,65,136,20,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 140 28 49 288 96 138 266), lower := (rows 7 67 140 28 49 288 96 128 256), losses := [] }

theorem u625 : Upper (D 5) (R 5) [6,65,136,20,33,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 28 50 288 65 168 296), lower := (rows 7 67 140 28 50 288 65 128 256), losses := [] }

theorem u626 : Upper (D 5) (R 5) [6,65,136,20,34,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 4 }], pairs := [(4,2)], upper := (rows 7 67 140 28 50 288 72 161 289), lower := (rows 7 67 140 28 50 288 72 128 256), losses := [] }

theorem u627 : Upper (D 5) (R 5) [6,65,136,20,34,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 28 50 288 96 137 265), lower := (rows 7 67 140 28 50 288 96 128 256), losses := [] }

theorem u628 : Upper (D 5) (R 5) [6,65,136,20,34,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 28 304 33 66 168 296), lower := (rows 7 67 140 28 304 33 66 128 256), losses := [] }

theorem u629 : Upper (D 5) (R 5) [6,65,136,20,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 67 140 28 304 33 72 162 290), lower := (rows 7 67 140 28 304 33 72 128 256), losses := [] }

theorem u630 : Upper (D 5) (R 5) [6,65,136,20,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 28 304 33 96 138 266), lower := (rows 7 67 140 28 304 33 96 128 256), losses := [] }

theorem u631 : Upper (D 5) (R 5) [6,65,136,20,288,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 28 304 34 65 168 296), lower := (rows 7 67 140 28 304 34 65 128 256), losses := [] }

theorem u632 : Upper (D 5) (R 5) [6,65,136,20,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 67 140 28 304 34 72 161 289), lower := (rows 7 67 140 28 304 34 72 128 256), losses := [] }

theorem u633 : Upper (D 5) (R 5) [6,65,136,20,288,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 140 28 304 34 96 137 265), lower := (rows 7 67 140 28 304 34 96 128 256), losses := [] }

theorem u634 : Upper (D 5) (R 5) [6,65,136,20,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 41 52 288 66 152 280), lower := (rows 7 67 140 41 52 288 66 128 256), losses := [] }

theorem u635 : Upper (D 5) (R 5) [6,65,136,33,36,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 41 52 288 72 146 274), lower := (rows 7 67 140 41 52 288 72 128 256), losses := [] }

theorem u636 : Upper (D 5) (R 5) [6,65,136,33,36,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 7 67 140 41 52 288 80 138 266), lower := (rows 7 67 140 41 52 288 80 128 256), losses := [] }

theorem u637 : Upper (D 5) (R 5) [6,65,136,33,36,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 42 49 288 68 152 280), lower := (rows 7 67 140 42 49 288 68 128 256), losses := [] }

theorem u638 : Upper (D 5) (R 5) [6,65,136,34,33,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 42 49 288 72 148 276), lower := (rows 7 67 140 42 49 288 72 128 256), losses := [] }

theorem u639 : Upper (D 5) (R 5) [6,65,136,34,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 7 67 140 42 49 288 80 140 268), lower := (rows 7 67 140 42 49 288 80 128 256), losses := [] }

theorem u640 : Upper (D 5) (R 5) [6,65,136,34,33,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 42 52 288 65 152 280), lower := (rows 7 67 140 42 52 288 65 128 256), losses := [] }

theorem u641 : Upper (D 5) (R 5) [6,65,136,34,36,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 42 52 288 72 145 273), lower := (rows 7 67 140 42 52 288 72 128 256), losses := [] }

theorem u642 : Upper (D 5) (R 5) [6,65,136,34,36,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 67 140 42 52 288 80 137 265), lower := (rows 7 67 140 42 52 288 80 128 256), losses := [] }

theorem u643 : Upper (D 5) (R 5) [6,65,136,34,36,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 42 276 48 65 168 296), lower := (rows 7 67 140 42 276 48 65 128 256), losses := [] }

theorem u644 : Upper (D 5) (R 5) [6,65,136,34,260,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 2 }], pairs := [(4,1)], upper := (rows 7 67 140 42 276 48 72 161 289), lower := (rows 7 67 140 42 276 48 72 128 256), losses := [] }

theorem u645 : Upper (D 5) (R 5) [6,65,136,34,260,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 42 276 48 96 137 265), lower := (rows 7 67 140 42 276 48 96 128 256), losses := [] }

theorem u646 : Upper (D 5) (R 5) [6,65,136,34,260,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 280 36 65 176 304), lower := (rows 7 67 140 42 280 36 65 128 256), losses := [] }

theorem u647 : Upper (D 5) (R 5) [6,65,136,34,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 42 280 36 80 161 289), lower := (rows 7 67 140 42 280 36 80 128 256), losses := [] }

theorem u648 : Upper (D 5) (R 5) [6,65,136,34,264,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 67 140 42 280 36 96 145 273), lower := (rows 7 67 140 42 280 36 96 128 256), losses := [] }

theorem u649 : Upper (D 5) (R 5) [6,65,136,34,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 42 280 48 65 164 292), lower := (rows 7 67 140 42 280 48 65 128 256), losses := [] }

theorem u650 : Upper (D 5) (R 5) [6,65,136,34,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 42 280 48 68 161 289), lower := (rows 7 67 140 42 280 48 68 128 256), losses := [] }

theorem u651 : Upper (D 5) (R 5) [6,65,136,34,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 42 280 48 96 133 261), lower := (rows 7 67 140 42 280 48 96 128 256), losses := [] }

theorem u652 : Upper (D 5) (R 5) [6,65,136,34,264,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 304 36 65 152 280), lower := (rows 7 67 140 42 304 36 65 128 256), losses := [] }

theorem u653 : Upper (D 5) (R 5) [6,65,136,34,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 42 304 36 72 145 273), lower := (rows 7 67 140 42 304 36 72 128 256), losses := [] }

theorem u654 : Upper (D 5) (R 5) [6,65,136,34,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 42 304 36 80 137 265), lower := (rows 7 67 140 42 304 36 80 128 256), losses := [] }

theorem u655 : Upper (D 5) (R 5) [6,65,136,34,288,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 44 26 288 65 176 304), lower := (rows 7 67 140 44 26 288 65 128 256), losses := [] }

theorem u656 : Upper (D 5) (R 5) [6,65,136,36,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 140 44 26 288 80 161 289), lower := (rows 7 67 140 44 26 288 80 128 256), losses := [] }

theorem u657 : Upper (D 5) (R 5) [6,65,136,36,10,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 26 288 96 145 273), lower := (rows 7 67 140 44 26 288 96 128 256), losses := [] }

theorem u658 : Upper (D 5) (R 5) [6,65,136,36,10,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 140 44 49 288 66 152 280), lower := (rows 7 67 140 44 49 288 66 128 256), losses := [] }

theorem u659 : Upper (D 5) (R 5) [6,65,136,36,33,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b659
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P05
