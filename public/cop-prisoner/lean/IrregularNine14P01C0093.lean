import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0033
import IrregularNine14P01C0034

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5580 : PairBound 9 := { available := 225, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 140 18 225 225 225 481), lower := (rows 305 82 14 140 18 32 64 128 256), losses := [] }

theorem u5580 : Upper (D 1) (R 1) [304,80,10,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5581 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 140 48 227 195 195 451), lower := (rows 305 82 14 140 48 32 64 128 256), losses := [] }

theorem u5581 : Upper (D 1) (R 1) [304,80,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5582 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 140 80 163 227 163 419), lower := (rows 305 82 14 140 80 32 64 128 256), losses := [] }

theorem u5582 : Upper (D 1) (R 1) [304,80,10,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 305 82 14 140 144 99 99 227 355), lower := (rows 305 82 14 140 144 32 64 128 256), losses := [] }

theorem u5583 : Upper (D 1) (R 1) [304,80,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 305 82 14 168 17 230 198 198 454), lower := (rows 305 82 14 168 17 32 64 128 256), losses := [] }

theorem u5584 : Upper (D 1) (R 1) [304,80,10,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 197, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 168 18 229 197 197 453), lower := (rows 305 82 14 168 18 32 64 128 256), losses := [] }

theorem u5585 : Upper (D 1) (R 1) [304,80,10,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 82 14 168 20 227 195 195 451), lower := (rows 305 82 14 168 20 32 64 128 256), losses := [] }

theorem u5586 : Upper (D 1) (R 1) [304,80,10,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5587 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 168 80 167 199 135 391), lower := (rows 305 82 14 168 80 32 64 128 256), losses := [] }

theorem u5587 : Upper (D 1) (R 1) [304,80,10,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5587
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5588 : Route 9 := (fun mask => (mask,id))

def c5588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5588 : Upper (D 1) (R 1) [304,80,10,160,128] 13 := by
  apply FastRouting.sound _ _ [304,80,10,160,128] 13 (by decide) (choices 1) [1,2,4,64] r5588 c5588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2009
  · exact u2010
  · exact u2011
  · exact u2012

def b5589 : PairBound 9 := { available := 140, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 73 18 172 204 140 396), lower := (rows 305 82 38 73 18 32 64 128 256), losses := [] }

theorem u5589 : Upper (D 1) (R 1) [304,80,34,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 38 73 20 170 202 138 394), lower := (rows 305 82 38 73 20 32 64 128 256), losses := [] }

theorem u5590 : Upper (D 1) (R 1) [304,80,34,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5591 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 38 73 24 166 198 134 390), lower := (rows 305 82 38 73 24 32 64 128 256), losses := [] }

theorem u5591 : Upper (D 1) (R 1) [304,80,34,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5592 : Route 9 := (fun mask => (mask,id))

def c5592 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5592 : Upper (D 1) (R 1) [304,80,34,65,128] 13 := by
  apply FastRouting.sound _ _ [304,80,34,65,128] 13 (by decide) (choices 1) [2,4,8,128] r5592 c5592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2013
  · exact u2014
  · exact u2015
  · exact u2016

def b5593 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 38 76 17 170 202 138 394), lower := (rows 305 82 38 76 17 32 64 128 256), losses := [] }

theorem u5593 : Upper (D 1) (R 1) [304,80,34,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 76 18 169 201 137 393), lower := (rows 305 82 38 76 18 32 64 128 256), losses := [] }

theorem u5594 : Upper (D 1) (R 1) [304,80,34,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 82 38 76 24 163 195 131 387), lower := (rows 305 82 38 76 24 32 64 128 256), losses := [] }

theorem u5595 : Upper (D 1) (R 1) [304,80,34,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5596 : Route 9 := (fun mask => (mask,id))

def c5596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5596 : Upper (D 1) (R 1) [304,80,34,68,128] 13 := by
  apply FastRouting.sound _ _ [304,80,34,68,128] 13 (by decide) (choices 1) [1,2,8,128] r5596 c5596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2017
  · exact u2018
  · exact u2019
  · exact u2020

def b5597 : PairBound 9 := { available := 204, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 137 18 236 204 204 460), lower := (rows 305 82 38 137 18 32 64 128 256), losses := [] }

theorem u5597 : Upper (D 1) (R 1) [304,80,34,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 82 38 137 20 234 202 202 458), lower := (rows 305 82 38 137 20 32 64 128 256), losses := [] }

theorem u5598 : Upper (D 1) (R 1) [304,80,34,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 305 82 38 137 24 230 198 198 454), lower := (rows 305 82 38 137 24 32 64 128 256), losses := [] }

theorem u5599 : Upper (D 1) (R 1) [304,80,34,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5599
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 38 137 80 174 206 142 398), lower := (rows 305 82 38 137 80 32 64 128 256), losses := [] }

theorem u5600 : Upper (D 1) (R 1) [304,80,34,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5601 : Route 9 := (fun mask => (mask,id))

def c5601 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5601 : Upper (D 1) (R 1) [304,80,34,129,128] 13 := by
  apply FastRouting.sound _ _ [304,80,34,129,128] 13 (by decide) (choices 1) [2,4,8,64] r5601 c5601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2021
  · exact u2022
  · exact u2023
  · exact u2024

def b5602 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 305 82 38 138 17 236 204 204 460), lower := (rows 305 82 38 138 17 32 64 128 256), losses := [] }

theorem u5602 : Upper (D 1) (R 1) [304,80,34,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5603 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 305 82 38 138 20 233 201 201 457), lower := (rows 305 82 38 138 20 32 64 128 256), losses := [] }

theorem u5603 : Upper (D 1) (R 1) [304,80,34,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5604 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 305 82 38 138 24 229 197 197 453), lower := (rows 305 82 38 138 24 32 64 128 256), losses := [] }

theorem u5604 : Upper (D 1) (R 1) [304,80,34,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5605 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 38 138 80 173 205 141 397), lower := (rows 305 82 38 138 80 32 64 128 256), losses := [] }

theorem u5605 : Upper (D 1) (R 1) [304,80,34,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5606 : Route 9 := (fun mask => (mask,id))

def c5606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5606 : Upper (D 1) (R 1) [304,80,34,130,128] 13 := by
  apply FastRouting.sound _ _ [304,80,34,130,128] 13 (by decide) (choices 1) [1,4,8,64] r5606 c5606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2025
  · exact u2026
  · exact u2027
  · exact u2028

def b5607 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 82 38 140 17 234 202 202 458), lower := (rows 305 82 38 140 17 32 64 128 256), losses := [] }

theorem u5607 : Upper (D 1) (R 1) [304,80,34,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 201, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 140 18 233 201 201 457), lower := (rows 305 82 38 140 18 32 64 128 256), losses := [] }

theorem u5608 : Upper (D 1) (R 1) [304,80,34,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 82 38 140 24 227 195 195 451), lower := (rows 305 82 38 140 24 32 64 128 256), losses := [] }

theorem u5609 : Upper (D 1) (R 1) [304,80,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 38 140 80 171 203 139 395), lower := (rows 305 82 38 140 80 32 64 128 256), losses := [] }

theorem u5610 : Upper (D 1) (R 1) [304,80,34,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5611 : Route 9 := (fun mask => (mask,id))

def c5611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5611 : Upper (D 1) (R 1) [304,80,34,132,128] 13 := by
  apply FastRouting.sound _ _ [304,80,34,132,128] 13 (by decide) (choices 1) [1,2,8,64] r5611 c5611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2029
  · exact u2030
  · exact u2031
  · exact u2032

def b5612 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 305 82 38 200 17 174 206 142 398), lower := (rows 305 82 38 200 17 32 64 128 256), losses := [] }

theorem u5612 : Upper (D 1) (R 1) [304,80,34,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 141, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 200 18 173 205 141 397), lower := (rows 305 82 38 200 18 32 64 128 256), losses := [] }

theorem u5613 : Upper (D 1) (R 1) [304,80,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 305 82 38 200 20 171 203 139 395), lower := (rows 305 82 38 200 20 32 64 128 256), losses := [] }

theorem u5614 : Upper (D 1) (R 1) [304,80,34,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5615 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 305 82 38 200 24 167 199 135 391), lower := (rows 305 82 38 200 24 32 64 128 256), losses := [] }

theorem u5615 : Upper (D 1) (R 1) [304,80,34,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5616 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 38 200 144 47 79 143 271), lower := (rows 305 82 38 200 144 32 64 128 256), losses := [] }

theorem u5616 : Upper (D 1) (R 1) [304,80,34,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 305 82 44 138 17 230 198 198 454), lower := (rows 305 82 44 138 17 32 64 128 256), losses := [] }

theorem u5617 : Upper (D 1) (R 1) [304,80,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 197, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 138 18 229 197 197 453), lower := (rows 305 82 44 138 18 32 64 128 256), losses := [] }

theorem u5618 : Upper (D 1) (R 1) [304,80,40,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 82 44 138 20 227 195 195 451), lower := (rows 305 82 44 138 20 32 64 128 256), losses := [] }

theorem u5619 : Upper (D 1) (R 1) [304,80,40,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 135, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 44 138 80 167 199 135 391), lower := (rows 305 82 44 138 80 32 64 128 256), losses := [] }

theorem u5620 : Upper (D 1) (R 1) [304,80,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5621 : Route 9 := (fun mask => (mask,id))

def c5621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5621 : Upper (D 1) (R 1) [304,80,40,130,128] 13 := by
  apply FastRouting.sound _ _ [304,80,40,130,128] 13 (by decide) (choices 1) [1,2,4,64] r5621 c5621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2033
  · exact u2034
  · exact u2035
  · exact u2036

def b5622 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 44 200 17 166 198 134 390), lower := (rows 305 82 44 200 17 32 64 128 256), losses := [] }

theorem u5622 : Upper (D 1) (R 1) [304,80,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 135, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 200 18 167 199 135 391), lower := (rows 305 82 44 200 18 32 64 128 256), losses := [] }

theorem u5623 : Upper (D 1) (R 1) [304,80,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5624 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 82 44 200 20 163 195 131 387), lower := (rows 305 82 44 200 20 32 64 128 256), losses := [] }

theorem u5624 : Upper (D 1) (R 1) [304,80,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 44 200 144 39 71 135 263), lower := (rows 305 82 44 200 144 32 64 128 256), losses := [] }

theorem u5625 : Upper (D 1) (R 1) [304,80,40,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 138 18 172 236 172 428), lower := (rows 305 82 69 138 18 32 64 128 256), losses := [] }

theorem u5626 : Upper (D 1) (R 1) [304,80,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 305 82 69 138 20 170 234 170 426), lower := (rows 305 82 69 138 20 32 64 128 256), losses := [] }

theorem u5627 : Upper (D 1) (R 1) [304,80,65,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5627
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 82 69 138 24 166 230 166 422), lower := (rows 305 82 69 138 24 32 64 128 256), losses := [] }

theorem u5628 : Upper (D 1) (R 1) [304,80,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5628
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 138 48 174 206 142 398), lower := (rows 305 82 69 138 48 32 64 128 256), losses := [] }

theorem u5629 : Upper (D 1) (R 1) [304,80,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5630 : Route 9 := (fun mask => (mask,id))

def c5630 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5630 : Upper (D 1) (R 1) [304,80,65,130,128] 13 := by
  apply FastRouting.sound _ _ [304,80,65,130,128] 13 (by decide) (choices 1) [2,4,8] r5630 c5630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2037
  · exact u2038
  · exact u2039

def b5631 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 140 18 170 234 170 426), lower := (rows 305 82 69 140 18 32 64 128 256), losses := [] }

theorem u5631 : Upper (D 1) (R 1) [304,80,65,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 82 69 140 24 162 226 162 418), lower := (rows 305 82 69 140 24 32 64 128 256), losses := [] }

theorem u5632 : Upper (D 1) (R 1) [304,80,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 140 48 170 202 138 394), lower := (rows 305 82 69 140 48 32 64 128 256), losses := [] }

theorem u5633 : Upper (D 1) (R 1) [304,80,65,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5634 : Route 9 := (fun mask => (mask,id))

def c5634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5634 : Upper (D 1) (R 1) [304,80,65,132,128] 13 := by
  apply FastRouting.sound _ _ [304,80,65,132,128] 13 (by decide) (choices 1) [2,8] r5634 c5634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2040
  · exact u2041

def b5635 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 168 18 174 206 142 398), lower := (rows 305 82 69 168 18 32 64 128 256), losses := [] }

theorem u5635 : Upper (D 1) (R 1) [304,80,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5635
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5636 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 69 168 20 170 202 138 394), lower := (rows 305 82 69 168 20 32 64 128 256), losses := [] }

theorem u5636 : Upper (D 1) (R 1) [304,80,65,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5637 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 69 168 24 166 198 134 390), lower := (rows 305 82 69 168 24 32 64 128 256), losses := [] }

theorem u5637 : Upper (D 1) (R 1) [304,80,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5637
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5638 : Route 9 := (fun mask => (mask,id))

def c5638 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5638 : Upper (D 1) (R 1) [304,80,65,160,128] 13 := by
  apply FastRouting.sound _ _ [304,80,65,160,128] 13 (by decide) (choices 1) [2,4,8] r5638 c5638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2042
  · exact u2043
  · exact u2044

def b5639 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 76 137 18 166 230 166 422), lower := (rows 305 82 76 137 18 32 64 128 256), losses := [] }

theorem u5639 : Upper (D 1) (R 1) [304,80,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5639
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P01
