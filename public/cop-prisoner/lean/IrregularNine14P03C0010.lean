import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0001

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 56 208 96 201 137 393), lower := (rows 7 35 261 56 208 96 64 128 256), losses := [] }

theorem u600 : Upper (D 3) (R 3) [6,33,257,48,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 88 152 33 224 224 480), lower := (rows 7 35 261 88 152 33 64 128 256), losses := [] }

theorem u601 : Upper (D 3) (R 3) [6,33,257,80,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 88 152 96 225 161 417), lower := (rows 7 35 261 88 152 96 64 128 256), losses := [] }

theorem u602 : Upper (D 3) (R 3) [6,33,257,80,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 88 176 33 200 200 456), lower := (rows 7 35 261 88 176 33 64 128 256), losses := [] }

theorem u603 : Upper (D 3) (R 3) [6,33,257,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 261 88 176 40 193 193 449), lower := (rows 7 35 261 88 176 40 64 128 256), losses := [] }

theorem u604 : Upper (D 3) (R 3) [6,33,257,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r605 : Route 9 := (fun mask => (mask,id))

def c605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u605 : Upper (D 3) (R 3) [6,33,257,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,160,64] 13 (by decide) (choices 1) [1,8,128] r605 c605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u69
  · exact u70
  · exact u71

def b606 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 261 88 176 160 73 201 329), lower := (rows 7 35 261 88 176 160 64 128 256), losses := [] }

theorem u606 : Upper (D 3) (R 3) [6,33,257,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 152, camps := [{ cop := 8, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 104 208 33 216 152 408), lower := (rows 7 35 261 104 208 33 64 128 256), losses := [] }

theorem u607 : Upper (D 3) (R 3) [6,33,257,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 261 104 208 40 209 145 401), lower := (rows 7 35 261 104 208 40 64 128 256), losses := [] }

theorem u608 : Upper (D 3) (R 3) [6,33,257,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 261 104 208 48 201 137 393), lower := (rows 7 35 261 104 208 48 64 128 256), losses := [] }

theorem u609 : Upper (D 3) (R 3) [6,33,257,96,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 261 104 208 160 89 153 281), lower := (rows 7 35 261 104 208 160 64 128 256), losses := [] }

theorem u610 : Upper (D 3) (R 3) [6,33,257,96,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 25 208 33 224 224 480), lower := (rows 7 35 268 25 208 33 64 128 256), losses := [] }

theorem u611 : Upper (D 3) (R 3) [6,33,264,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 161, camps := [], pairs := [(0,7)], upper := (rows 7 35 268 25 208 96 225 161 417), lower := (rows 7 35 268 25 208 96 64 128 256), losses := [{ target := 7, region := (rows 5 10 4 8 16 112 64 0 256), good := (rows 7 35 271 59 112 96 96 0 256) }] }

theorem u612 : Upper (D 3) (R 3) [6,33,264,17,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 73 112 33 208 144 400), lower := (rows 7 35 268 73 112 33 64 128 256), losses := [] }

theorem u613 : Upper (D 3) (R 3) [6,33,264,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 268 73 112 48 193 129 385), lower := (rows 7 35 268 73 112 48 64 128 256), losses := [] }

theorem u614 : Upper (D 3) (R 3) [6,33,264,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r615 : Route 9 := (fun mask => (mask,id))

def c615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u615 : Upper (D 3) (R 3) [6,33,264,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,96,128] 13 (by decide) (choices 1) [1,16,128] r615 c615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u72
  · exact u73
  · exact u74

def b616 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 7 35 268 73 145 48 224 224 480), lower := (rows 7 35 268 73 145 48 64 128 256), losses := [] }

theorem u616 : Upper (D 3) (R 3) [6,33,264,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 73 145 96 240 176 432), lower := (rows 7 35 268 73 145 96 64 128 256), losses := [] }

theorem u617 : Upper (D 3) (R 3) [6,33,264,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 268 73 145 160 112 240 368), lower := (rows 7 35 268 73 145 160 64 128 256), losses := [] }

theorem u618 : Upper (D 3) (R 3) [6,33,264,65,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 73 176 33 208 208 464), lower := (rows 7 35 268 73 176 33 64 128 256), losses := [] }

theorem u619 : Upper (D 3) (R 3) [6,33,264,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b619
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 268 73 176 48 193 193 449), lower := (rows 7 35 268 73 176 48 64 128 256), losses := [] }

theorem u620 : Upper (D 3) (R 3) [6,33,264,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b620
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 73 176 96 209 145 401), lower := (rows 7 35 268 73 176 96 64 128 256), losses := [] }

theorem u621 : Upper (D 3) (R 3) [6,33,264,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b621
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 268 73 176 160 81 209 337), lower := (rows 7 35 268 73 176 160 64 128 256), losses := [] }

theorem u622 : Upper (D 3) (R 3) [6,33,264,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 73 208 33 240 176 432), lower := (rows 7 35 268 73 208 33 64 128 256), losses := [] }

theorem u623 : Upper (D 3) (R 3) [6,33,264,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 268 73 208 48 225 161 417), lower := (rows 7 35 268 73 208 48 64 128 256), losses := [] }

theorem u624 : Upper (D 3) (R 3) [6,33,264,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r625 : Route 9 := (fun mask => (mask,id))

def c625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u625 : Upper (D 3) (R 3) [6,33,264,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,192,128] 13 (by decide) (choices 1) [1,16,32] r625 c625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u75
  · exact u76
  · exact u77

def b626 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 145 33 224 224 480), lower := (rows 7 35 268 88 145 33 64 128 256), losses := [] }

theorem u626 : Upper (D 3) (R 3) [6,33,264,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 88 145 96 225 161 417), lower := (rows 7 35 268 88 145 96 64 128 256), losses := [] }

theorem u627 : Upper (D 3) (R 3) [6,33,264,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 268 88 145 160 97 225 353), lower := (rows 7 35 268 88 145 160 64 128 256), losses := [] }

theorem u628 : Upper (D 3) (R 3) [6,33,264,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 176 33 193 193 449), lower := (rows 7 35 268 88 176 33 64 128 256), losses := [] }

theorem u629 : Upper (D 3) (R 3) [6,33,264,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 88 176 96 193 129 385), lower := (rows 7 35 268 88 176 96 64 128 256), losses := [] }

theorem u630 : Upper (D 3) (R 3) [6,33,264,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 268 88 176 160 65 193 321), lower := (rows 7 35 268 88 176 160 64 128 256), losses := [] }

theorem u631 : Upper (D 3) (R 3) [6,33,264,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 200 112 33 209 145 401), lower := (rows 7 35 268 200 112 33 64 128 256), losses := [] }

theorem u632 : Upper (D 3) (R 3) [6,33,264,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 268 200 112 48 193 129 385), lower := (rows 7 35 268 200 112 48 64 128 256), losses := [] }

theorem u633 : Upper (D 3) (R 3) [6,33,264,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b633
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 268 200 112 160 81 145 273), lower := (rows 7 35 268 200 112 160 64 128 256), losses := [] }

theorem u634 : Upper (D 3) (R 3) [6,33,264,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 25 152 33 224 224 480), lower := (rows 7 35 324 25 152 33 64 128 256), losses := [] }

theorem u635 : Upper (D 3) (R 3) [6,33,320,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 25 152 96 225 161 417), lower := (rows 7 35 324 25 152 96 64 128 256), losses := [] }

theorem u636 : Upper (D 3) (R 3) [6,33,320,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 25 152 160 97 225 353), lower := (rows 7 35 324 25 152 160 64 128 256), losses := [] }

theorem u637 : Upper (D 3) (R 3) [6,33,320,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 56 145 33 200 200 456), lower := (rows 7 35 324 56 145 33 64 128 256), losses := [] }

theorem u638 : Upper (D 3) (R 3) [6,33,320,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 324 56 145 40 193 193 449), lower := (rows 7 35 324 56 145 40 64 128 256), losses := [] }

theorem u639 : Upper (D 3) (R 3) [6,33,320,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b639
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 56 145 96 201 137 393), lower := (rows 7 35 324 56 145 96 64 128 256), losses := [] }

theorem u640 : Upper (D 3) (R 3) [6,33,320,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b640
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 56 145 160 73 201 329), lower := (rows 7 35 324 56 145 160 64 128 256), losses := [] }

theorem u641 : Upper (D 3) (R 3) [6,33,320,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 56 208 33 201 137 393), lower := (rows 7 35 324 56 208 33 64 128 256), losses := [] }

theorem u642 : Upper (D 3) (R 3) [6,33,320,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b642
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 324 56 208 40 193 129 385), lower := (rows 7 35 324 56 208 40 64 128 256), losses := [] }

theorem u643 : Upper (D 3) (R 3) [6,33,320,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 56 208 160 73 137 265), lower := (rows 7 35 324 56 208 160 64 128 256), losses := [] }

theorem u644 : Upper (D 3) (R 3) [6,33,320,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 88 145 33 232 168 424), lower := (rows 7 35 324 88 145 33 64 128 256), losses := [] }

theorem u645 : Upper (D 3) (R 3) [6,33,320,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 324 88 145 40 225 161 417), lower := (rows 7 35 324 88 145 40 64 128 256), losses := [] }

theorem u646 : Upper (D 3) (R 3) [6,33,320,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b646
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 88 145 160 105 169 297), lower := (rows 7 35 324 88 145 160 64 128 256), losses := [] }

theorem u647 : Upper (D 3) (R 3) [6,33,320,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b647
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 88 176 33 201 137 393), lower := (rows 7 35 324 88 176 33 64 128 256), losses := [] }

theorem u648 : Upper (D 3) (R 3) [6,33,320,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b648
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 324 88 176 40 193 129 385), lower := (rows 7 35 324 88 176 40 64 128 256), losses := [] }

theorem u649 : Upper (D 3) (R 3) [6,33,320,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 88 176 160 73 137 265), lower := (rows 7 35 324 88 176 160 64 128 256), losses := [] }

theorem u650 : Upper (D 3) (R 3) [6,33,320,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b650
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 104 145 33 216 152 408), lower := (rows 7 35 324 104 145 33 64 128 256), losses := [] }

theorem u651 : Upper (D 3) (R 3) [6,33,320,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 324 104 145 40 209 145 401), lower := (rows 7 35 324 104 145 40 64 128 256), losses := [] }

theorem u652 : Upper (D 3) (R 3) [6,33,320,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b652
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 324 104 145 48 201 137 393), lower := (rows 7 35 324 104 145 48 64 128 256), losses := [] }

theorem u653 : Upper (D 3) (R 3) [6,33,320,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 104 145 160 89 153 281), lower := (rows 7 35 324 104 145 160 64 128 256), losses := [] }

theorem u654 : Upper (D 3) (R 3) [6,33,320,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 104 152 33 209 145 401), lower := (rows 7 35 324 104 152 33 64 128 256), losses := [] }

theorem u655 : Upper (D 3) (R 3) [6,33,320,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 324 104 152 48 193 129 385), lower := (rows 7 35 324 104 152 48 64 128 256), losses := [] }

theorem u656 : Upper (D 3) (R 3) [6,33,320,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r657 : Route 9 := (fun mask => (mask,id))

def c657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u657 : Upper (D 3) (R 3) [6,33,320,96,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136,128] 13 (by decide) (choices 1) [1,16] r657 c657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def b658 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 137 176 33 88 216 344), lower := (rows 7 35 324 137 176 33 64 128 256), losses := [] }

theorem u658 : Upper (D 3) (R 3) [6,33,320,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 35 324 137 176 40 81 209 337), lower := (rows 7 35 324 137 176 40 64 128 256), losses := [] }

theorem u659 : Upper (D 3) (R 3) [6,33,320,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b659
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P03
