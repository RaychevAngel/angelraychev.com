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

def b600 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 13 266 48 160 208 208 464), lower := (rows 51 70 13 266 48 160 64 128 256), losses := [] }

theorem u600 : Upper (D 1) (R 1) [50,68,9,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 13 266 80 160 240 176 432), lower := (rows 51 70 13 266 80 160 64 128 256), losses := [] }

theorem u601 : Upper (D 1) (R 1) [50,68,9,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 70 13 266 144 160 112 240 368), lower := (rows 51 70 13 266 144 160 64 128 256), losses := [] }

theorem u602 : Upper (D 1) (R 1) [50,68,9,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 261 88 144 34 232 168 424), lower := (rows 51 70 261 88 144 34 64 128 256), losses := [] }

theorem u603 : Upper (D 1) (R 1) [50,68,257,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 70 261 88 144 40 226 162 418), lower := (rows 51 70 261 88 144 40 64 128 256), losses := [] }

theorem u604 : Upper (D 1) (R 1) [50,68,257,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 70 261 88 144 160 106 170 298), lower := (rows 51 70 261 88 144 160 64 128 256), losses := [] }

theorem u605 : Upper (D 1) (R 1) [50,68,257,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 70 261 138 24 160 112 240 368), lower := (rows 51 70 261 138 24 160 64 128 256), losses := [] }

theorem u606 : Upper (D 1) (R 1) [50,68,257,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b606
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 138 48 160 88 216 344), lower := (rows 51 70 261 138 48 160 64 128 256), losses := [] }

theorem u607 : Upper (D 1) (R 1) [50,68,257,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 138 80 160 120 184 312), lower := (rows 51 70 261 138 80 160 64 128 256), losses := [] }

theorem u608 : Upper (D 1) (R 1) [50,68,257,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 261 200 18 160 120 184 312), lower := (rows 51 70 261 200 18 160 64 128 256), losses := [] }

theorem u609 : Upper (D 1) (R 1) [50,68,257,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 70 261 200 24 160 114 178 306), lower := (rows 51 70 261 200 24 160 64 128 256), losses := [] }

theorem u610 : Upper (D 1) (R 1) [50,68,257,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 200 48 160 90 154 282), lower := (rows 51 70 261 200 48 160 64 128 256), losses := [] }

theorem u611 : Upper (D 1) (R 1) [50,68,257,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 70 268 138 17 160 112 240 368), lower := (rows 51 70 268 138 17 160 64 128 256), losses := [] }

theorem u612 : Upper (D 1) (R 1) [50,68,264,130,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 138 48 160 81 209 337), lower := (rows 51 70 268 138 48 160 64 128 256), losses := [] }

theorem u613 : Upper (D 1) (R 1) [50,68,264,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 138 80 160 113 177 305), lower := (rows 51 70 268 138 80 160 64 128 256), losses := [] }

theorem u614 : Upper (D 1) (R 1) [50,68,264,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 28 104 144 34 196 196 452), lower := (rows 51 259 28 104 144 34 64 128 256), losses := [] }

theorem u615 : Upper (D 1) (R 1) [50,257,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 51 259 28 104 144 36 194 194 450), lower := (rows 51 259 28 104 144 36 64 128 256), losses := [] }

theorem u616 : Upper (D 1) (R 1) [50,257,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 28 104 144 96 198 134 390), lower := (rows 51 259 28 104 144 96 64 128 256), losses := [] }

theorem u617 : Upper (D 1) (R 1) [50,257,24,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 259 28 104 144 160 70 198 326), lower := (rows 51 259 28 104 144 160 64 128 256), losses := [] }

theorem u618 : Upper (D 1) (R 1) [50,257,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 76 152 80 34 228 164 420), lower := (rows 51 259 76 152 80 34 64 128 256), losses := [] }

theorem u619 : Upper (D 1) (R 1) [50,257,72,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 259 76 152 80 36 226 162 418), lower := (rows 51 259 76 152 80 36 64 128 256), losses := [] }

theorem u620 : Upper (D 1) (R 1) [50,257,72,144,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r621 : Route 9 := (fun mask => (mask,id))

def c621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u621 : Upper (D 1) (R 1) [50,257,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144,64,128] 13 (by decide) (choices 1) [2,4,32] r621 c621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u38
  · exact u39
  · exact u40

def b622 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 104 18 160 204 140 396), lower := (rows 51 259 84 104 18 160 64 128 256), losses := [] }

theorem u622 : Upper (D 1) (R 1) [50,257,80,96,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 51 259 84 104 20 160 202 138 394), lower := (rows 51 259 84 104 20 160 64 128 256), losses := [] }

theorem u623 : Upper (D 1) (R 1) [50,257,80,96,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 259 84 104 24 160 198 134 390), lower := (rows 51 259 84 104 24 160 64 128 256), losses := [] }

theorem u624 : Upper (D 1) (R 1) [50,257,80,96,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 259 84 104 144 160 78 142 270), lower := (rows 51 259 84 104 144 160 64 128 256), losses := [] }

theorem u625 : Upper (D 1) (R 1) [50,257,80,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 84 168 18 96 204 140 396), lower := (rows 51 259 84 168 18 96 64 128 256), losses := [] }

theorem u626 : Upper (D 1) (R 1) [50,257,80,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 51 259 84 168 20 96 202 138 394), lower := (rows 51 259 84 168 20 96 64 128 256), losses := [] }

theorem u627 : Upper (D 1) (R 1) [50,257,80,160,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b627
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 259 84 168 24 96 198 134 390), lower := (rows 51 259 84 168 24 96 64 128 256), losses := [] }

theorem u628 : Upper (D 1) (R 1) [50,257,80,160,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b628
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r629 : Route 9 := (fun mask => (mask,id))

def c629 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u629 : Upper (D 1) (R 1) [50,257,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160,128,64] 13 (by decide) (choices 1) [2,4,8] r629 c629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u41
  · exact u42
  · exact u43

def b630 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 13 74 48 160 208 208 464), lower := (rows 51 262 13 74 48 160 64 128 256), losses := [] }

theorem u630 : Upper (D 1) (R 1) [50,260,9,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 176, camps := [], pairs := [(1,6)], upper := (rows 51 262 13 74 80 160 240 176 432), lower := (rows 51 262 13 74 80 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 181 0 145 273), good := (rows 435 294 431 10 432 160 0 160 256) }] }

theorem u631 : Upper (D 1) (R 1) [50,260,9,66,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 262 13 74 144 160 112 240 368), lower := (rows 51 262 13 74 144 160 64 128 256), losses := [] }

theorem u632 : Upper (D 1) (R 1) [50,260,9,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 69 88 144 34 232 168 424), lower := (rows 51 262 69 88 144 34 64 128 256), losses := [] }

theorem u633 : Upper (D 1) (R 1) [50,260,65,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 262 69 88 144 40 226 162 418), lower := (rows 51 262 69 88 144 40 64 128 256), losses := [] }

theorem u634 : Upper (D 1) (R 1) [50,260,65,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 262 69 88 144 160 106 170 298), lower := (rows 51 262 69 88 144 160 64 128 256), losses := [] }

theorem u635 : Upper (D 1) (R 1) [50,260,65,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b635
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 262 69 138 24 160 112 240 368), lower := (rows 51 262 69 138 24 160 64 128 256), losses := [] }

theorem u636 : Upper (D 1) (R 1) [50,260,65,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 138 48 160 88 216 344), lower := (rows 51 262 69 138 48 160 64 128 256), losses := [] }

theorem u637 : Upper (D 1) (R 1) [50,260,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b637
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 138 80 160 120 184 312), lower := (rows 51 262 69 138 80 160 64 128 256), losses := [] }

theorem u638 : Upper (D 1) (R 1) [50,260,65,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 69 200 18 160 120 184 312), lower := (rows 51 262 69 200 18 160 64 128 256), losses := [] }

theorem u639 : Upper (D 1) (R 1) [50,260,65,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b639
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 262 69 200 24 160 114 178 306), lower := (rows 51 262 69 200 24 160 64 128 256), losses := [] }

theorem u640 : Upper (D 1) (R 1) [50,260,65,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 200 48 160 90 154 282), lower := (rows 51 262 69 200 48 160 64 128 256), losses := [] }

theorem u641 : Upper (D 1) (R 1) [50,260,65,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 262 76 138 17 160 112 240 368), lower := (rows 51 262 76 138 17 160 64 128 256), losses := [] }

theorem u642 : Upper (D 1) (R 1) [50,260,72,130,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 76 138 48 160 81 209 337), lower := (rows 51 262 76 138 48 160 64 128 256), losses := [] }

theorem u643 : Upper (D 1) (R 1) [50,260,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 138 80 160 113 177 305), lower := (rows 51 262 76 138 80 160 64 128 256), losses := [] }

theorem u644 : Upper (D 1) (R 1) [50,260,72,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 322 13 138 20 160 112 240 368), lower := (rows 51 322 13 138 20 160 64 128 256), losses := [] }

theorem u645 : Upper (D 1) (R 1) [50,320,9,130,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 138 48 160 84 212 340), lower := (rows 51 322 13 138 48 160 64 128 256), losses := [] }

theorem u646 : Upper (D 1) (R 1) [50,320,9,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 13 138 80 160 116 180 308), lower := (rows 51 322 13 138 80 160 64 128 256), losses := [] }

theorem u647 : Upper (D 1) (R 1) [50,320,9,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 13 200 18 160 116 180 308), lower := (rows 51 322 13 200 18 160 64 128 256), losses := [] }

theorem u648 : Upper (D 1) (R 1) [50,320,9,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 322 13 200 20 160 114 178 306), lower := (rows 51 322 13 200 20 160 64 128 256), losses := [] }

theorem u649 : Upper (D 1) (R 1) [50,320,9,192,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 200 48 160 86 150 278), lower := (rows 51 322 13 200 48 160 64 128 256), losses := [] }

theorem u650 : Upper (D 1) (R 1) [50,320,9,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 322 14 137 20 160 112 240 368), lower := (rows 51 322 14 137 20 160 64 128 256), losses := [] }

theorem u651 : Upper (D 1) (R 1) [50,320,10,129,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 14 137 48 160 84 212 340), lower := (rows 51 322 14 137 48 160 64 128 256), losses := [] }

theorem u652 : Upper (D 1) (R 1) [50,320,10,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 14 137 80 160 116 180 308), lower := (rows 51 322 14 137 80 160 64 128 256), losses := [] }

theorem u653 : Upper (D 1) (R 1) [50,320,10,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 322 28 104 144 33 198 134 390), lower := (rows 51 322 28 104 144 33 64 128 256), losses := [] }

theorem u654 : Upper (D 1) (R 1) [50,320,24,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 104 144 34 197 133 389), lower := (rows 51 322 28 104 144 34 64 128 256), losses := [] }

theorem u655 : Upper (D 1) (R 1) [50,320,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 51 322 28 104 144 36 195 131 387), lower := (rows 51 322 28 104 144 36 64 128 256), losses := [] }

theorem u656 : Upper (D 1) (R 1) [50,320,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 322 28 104 144 160 71 135 263), lower := (rows 51 322 28 104 144 160 64 128 256), losses := [] }

theorem u657 : Upper (D 1) (R 1) [50,320,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 51 322 69 138 20 160 120 184 312), lower := (rows 51 322 69 138 20 160 64 128 256), losses := [] }

theorem u658 : Upper (D 1) (R 1) [50,320,65,130,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 51 322 69 138 24 160 116 180 308), lower := (rows 51 322 69 138 24 160 64 128 256), losses := [] }

theorem u659 : Upper (D 1) (R 1) [50,320,65,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b659
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P01
