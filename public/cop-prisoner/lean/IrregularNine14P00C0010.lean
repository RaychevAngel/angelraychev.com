import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0001

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 392 17 33 74 202 330), lower := (rows 113 22 164 392 17 33 64 128 256), losses := [] }

theorem u600 : Upper (D 0) (R 0) [112,20,160,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b600
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 164 392 17 34 73 201 329), lower := (rows 113 22 164 392 17 34 64 128 256), losses := [] }

theorem u601 : Upper (D 0) (R 0) [112,20,160,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b601
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 164 392 17 40 67 195 323), lower := (rows 113 22 164 392 17 40 64 128 256), losses := [] }

theorem u602 : Upper (D 0) (R 0) [112,20,160,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b602
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 392 17 96 75 139 267), lower := (rows 113 22 164 392 17 96 64 128 256), losses := [] }

theorem u603 : Upper (D 0) (R 0) [112,20,160,384,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b603
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 113 22 261 137 144 34 104 232 360), lower := (rows 113 22 261 137 144 34 64 128 256), losses := [] }

theorem u604 : Upper (D 0) (R 0) [112,20,257,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b604
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 22 261 137 144 40 98 226 354), lower := (rows 113 22 261 137 144 40 64 128 256), losses := [] }

theorem u605 : Upper (D 0) (R 0) [112,20,257,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b605
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 261 137 144 96 106 170 298), lower := (rows 113 22 261 137 144 96 64 128 256), losses := [] }

theorem u606 : Upper (D 0) (R 0) [112,20,257,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b606
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 104, camps := [], pairs := [(3,4)], upper := (rows 113 22 261 138 144 33 104 232 360), lower := (rows 113 22 261 138 144 33 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 66 130 258), good := (rows 97 494 293 458 128 33 64 128 256) }] }

theorem u607 : Upper (D 0) (R 0) [112,20,257,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b607
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 113 22 261 138 144 40 97 225 353), lower := (rows 113 22 261 138 144 40 64 128 256), losses := [] }

theorem u608 : Upper (D 0) (R 0) [112,20,257,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b608
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 261 138 144 96 105 169 297), lower := (rows 113 22 261 138 144 96 64 128 256), losses := [] }

theorem u609 : Upper (D 0) (R 0) [112,20,257,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b609
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 74, camps := [], pairs := [(3,4)], upper := (rows 113 22 261 168 144 33 74 202 330), lower := (rows 113 22 261 168 144 33 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 10 0 37 66 130 258), good := (rows 97 494 293 168 128 33 64 128 256) }] }

theorem u610 : Upper (D 0) (R 0) [112,20,257,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b610
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 261 168 144 34 73 201 329), lower := (rows 113 22 261 168 144 34 64 128 256), losses := [] }

theorem u611 : Upper (D 0) (R 0) [112,20,257,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b611
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 261 168 144 40 67 195 323), lower := (rows 113 22 261 168 144 40 64 128 256), losses := [] }

theorem u612 : Upper (D 0) (R 0) [112,20,257,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b612
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 261 168 144 96 75 139 267), lower := (rows 113 22 261 168 144 96 64 128 256), losses := [] }

theorem u613 : Upper (D 0) (R 0) [112,20,257,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b613
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 268 168 17 33 194 194 450), lower := (rows 113 22 268 168 17 33 64 128 256), losses := [] }

theorem u614 : Upper (D 0) (R 0) [112,20,264,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b614
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 268 168 17 34 193 193 449), lower := (rows 113 22 268 168 17 34 64 128 256), losses := [] }

theorem u615 : Upper (D 0) (R 0) [112,20,264,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b615
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 268 168 17 96 195 131 387), lower := (rows 113 22 268 168 17 96 64 128 256), losses := [] }

theorem u616 : Upper (D 0) (R 0) [112,20,264,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b616
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 268 168 17 160 67 195 323), lower := (rows 113 22 268 168 17 160 64 128 256), losses := [] }

theorem u617 : Upper (D 0) (R 0) [112,20,264,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b617
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 113 22 292 137 17 34 200 200 456), lower := (rows 113 22 292 137 17 34 64 128 256), losses := [] }

theorem u618 : Upper (D 0) (R 0) [112,20,288,129,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b618
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 292 137 17 40 194 194 450), lower := (rows 113 22 292 137 17 40 64 128 256), losses := [] }

theorem u619 : Upper (D 0) (R 0) [112,20,288,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b619
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 137 17 96 202 138 394), lower := (rows 113 22 292 137 17 96 64 128 256), losses := [] }

theorem u620 : Upper (D 0) (R 0) [112,20,288,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b620
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r621 : Route 9 := (fun mask => (mask,id))

def c621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u621 : Upper (D 0) (R 0) [112,20,288,129,1,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,1,128] 13 (by decide) (choices 1) [2,8] r621 c621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u92
  · exact u93

def r622 : Route 9 := (fun mask => (mask,id))

def c622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u622 : Upper (D 0) (R 0) [112,20,288,129,128,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,128,1] 13 (by decide) (choices 1) [2,8] r622 c622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u94
  · exact u95

def b623 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 292 137 144 34 73 201 329), lower := (rows 113 22 292 137 144 34 64 128 256), losses := [] }

theorem u623 : Upper (D 0) (R 0) [112,20,288,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b623
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 292 137 144 40 67 195 323), lower := (rows 113 22 292 137 144 40 64 128 256), losses := [] }

theorem u624 : Upper (D 0) (R 0) [112,20,288,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b624
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 137 144 96 75 139 267), lower := (rows 113 22 292 137 144 96 64 128 256), losses := [] }

theorem u625 : Upper (D 0) (R 0) [112,20,288,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b625
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 138 17 33 200 200 456), lower := (rows 113 22 292 138 17 33 64 128 256), losses := [] }

theorem u626 : Upper (D 0) (R 0) [112,20,288,130,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b626
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 292 138 17 40 193 193 449), lower := (rows 113 22 292 138 17 40 64 128 256), losses := [] }

theorem u627 : Upper (D 0) (R 0) [112,20,288,130,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b627
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 138 17 96 201 137 393), lower := (rows 113 22 292 138 17 96 64 128 256), losses := [] }

theorem u628 : Upper (D 0) (R 0) [112,20,288,130,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b628
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r629 : Route 9 := (fun mask => (mask,id))

def c629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u629 : Upper (D 0) (R 0) [112,20,288,130,1,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,1,128] 13 (by decide) (choices 1) [1,8] r629 c629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u96
  · exact u97

def r630 : Route 9 := (fun mask => (mask,id))

def c630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u630 : Upper (D 0) (R 0) [112,20,288,130,128,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,128,1] 13 (by decide) (choices 1) [1,8] r630 c630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u98
  · exact u99

def b631 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 22 292 138 144 40 65 193 321), lower := (rows 113 22 292 138 144 40 64 128 256), losses := [] }

theorem u631 : Upper (D 0) (R 0) [112,20,288,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b631
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 138 144 96 73 137 265), lower := (rows 113 22 292 138 144 96 64 128 256), losses := [] }

theorem u632 : Upper (D 0) (R 0) [112,20,288,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b632
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 292 200 17 33 202 138 394), lower := (rows 113 22 292 200 17 33 64 128 256), losses := [] }

theorem u633 : Upper (D 0) (R 0) [112,20,288,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b633
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 22 292 200 17 34 201 137 393), lower := (rows 113 22 292 200 17 34 64 128 256), losses := [] }

theorem u634 : Upper (D 0) (R 0) [112,20,288,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b634
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 292 200 17 40 195 131 387), lower := (rows 113 22 292 200 17 40 64 128 256), losses := [] }

theorem u635 : Upper (D 0) (R 0) [112,20,288,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b635
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r636 : Route 9 := (fun mask => (mask,id))

def c636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u636 : Upper (D 0) (R 0) [112,20,288,192,1,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,1,128] 13 (by decide) (choices 1) [1,2,8] r636 c636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u100
  · exact u101
  · exact u102

def r637 : Route 9 := (fun mask => (mask,id))

def c637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u637 : Upper (D 0) (R 0) [112,20,288,192,128,1] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,128,1] 13 (by decide) (choices 1) [1,2,8] r637 c637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u103
  · exact u104
  · exact u105

def b638 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 113 22 292 200 144 34 73 137 265), lower := (rows 113 22 292 200 144 34 64 128 256), losses := [] }

theorem u638 : Upper (D 0) (R 0) [112,20,288,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b638
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 22 292 200 144 40 67 131 259), lower := (rows 113 22 292 200 144 40 64 128 256), losses := [] }

theorem u639 : Upper (D 0) (R 0) [112,20,288,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b639
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 113 22 388 137 17 34 104 232 360), lower := (rows 113 22 388 137 17 34 64 128 256), losses := [] }

theorem u640 : Upper (D 0) (R 0) [112,20,384,129,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b640
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 22 388 137 17 40 98 226 354), lower := (rows 113 22 388 137 17 40 64 128 256), losses := [] }

theorem u641 : Upper (D 0) (R 0) [112,20,384,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b641
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 388 137 17 96 106 170 298), lower := (rows 113 22 388 137 17 96 64 128 256), losses := [] }

theorem u642 : Upper (D 0) (R 0) [112,20,384,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b642
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 388 168 17 33 74 202 330), lower := (rows 113 22 388 168 17 33 64 128 256), losses := [] }

theorem u643 : Upper (D 0) (R 0) [112,20,384,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b643
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 22 388 168 17 34 73 201 329), lower := (rows 113 22 388 168 17 34 64 128 256), losses := [] }

theorem u644 : Upper (D 0) (R 0) [112,20,384,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b644
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 388 168 17 40 67 195 323), lower := (rows 113 22 388 168 17 40 64 128 256), losses := [] }

theorem u645 : Upper (D 0) (R 0) [112,20,384,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b645
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 388 168 17 96 75 139 267), lower := (rows 113 22 388 168 17 96 64 128 256), losses := [] }

theorem u646 : Upper (D 0) (R 0) [112,20,384,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b646
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 113 131 140 280 17 34 100 228 356), lower := (rows 113 131 140 280 17 34 64 128 256), losses := [] }

theorem u647 : Upper (D 0) (R 0) [112,129,136,272,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b647
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 140 280 17 36 98 226 354), lower := (rows 113 131 140 280 17 36 64 128 256), losses := [] }

theorem u648 : Upper (D 0) (R 0) [112,129,136,272,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b648
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 140 280 17 96 102 166 294), lower := (rows 113 131 140 280 17 96 64 128 256), losses := [] }

theorem u649 : Upper (D 0) (R 0) [112,129,136,272,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b649
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 134 276 168 17 33 74 202 330), lower := (rows 113 134 276 168 17 33 64 128 256), losses := [] }

theorem u650 : Upper (D 0) (R 0) [112,132,272,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b650
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 134 276 168 17 34 73 201 329), lower := (rows 113 134 276 168 17 34 64 128 256), losses := [] }

theorem u651 : Upper (D 0) (R 0) [112,132,272,160,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b651
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 134 276 168 17 40 67 195 323), lower := (rows 113 134 276 168 17 40 64 128 256), losses := [] }

theorem u652 : Upper (D 0) (R 0) [112,132,272,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b652
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 168 17 96 75 139 267), lower := (rows 113 134 276 168 17 96 64 128 256), losses := [] }

theorem u653 : Upper (D 0) (R 0) [112,132,272,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b653
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 113 146 164 265 17 34 76 204 332), lower := (rows 113 146 164 265 17 34 64 128 256), losses := [] }

theorem u654 : Upper (D 0) (R 0) [112,144,160,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b654
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 146 164 265 17 36 74 202 330), lower := (rows 113 146 164 265 17 36 64 128 256), losses := [] }

theorem u655 : Upper (D 0) (R 0) [112,144,160,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b655
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 146 164 265 17 40 70 198 326), lower := (rows 113 146 164 265 17 40 64 128 256), losses := [] }

theorem u656 : Upper (D 0) (R 0) [112,144,160,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b656
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 265 17 96 78 142 270), lower := (rows 113 146 164 265 17 96 64 128 256), losses := [] }

theorem u657 : Upper (D 0) (R 0) [112,144,160,257,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b657
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 146 164 266 17 33 76 204 332), lower := (rows 113 146 164 266 17 33 64 128 256), losses := [] }

theorem u658 : Upper (D 0) (R 0) [112,144,160,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b658
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 146 164 266 17 36 73 201 329), lower := (rows 113 146 164 266 17 36 64 128 256), losses := [] }

theorem u659 : Upper (D 0) (R 0) [112,144,160,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b659
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P00
