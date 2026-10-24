import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0035

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5580 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 42 208 57 89 153 281), lower := (rows 289 7 196 42 208 32 64 128 256), losses := [] }

theorem u5580 : Upper (D 3) (R 3) [288,5,192,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5581 : Route 9 := (fun mask => (mask,id))

def c5581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5581 : Upper (D 3) (R 3) [288,5,192,48,65] 13 := by
  apply FastRouting.sound _ _ [288,5,192,48,65] 13 (by decide) (choices 1) [1,2,8,128] r5581 c5581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2125
  · exact u2126
  · exact u2127
  · exact u2128

def b5582 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 56 82 169 201 137 393), lower := (rows 289 7 196 56 82 32 64 128 256), losses := [] }

theorem u5582 : Upper (D 3) (R 3) [288,5,192,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 56 88 163 195 131 387), lower := (rows 289 7 196 56 88 32 64 128 256), losses := [] }

theorem u5583 : Upper (D 3) (R 3) [288,5,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5583
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 56 208 43 75 139 267), lower := (rows 289 7 196 56 208 32 64 128 256), losses := [] }

theorem u5584 : Upper (D 3) (R 3) [288,5,192,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5584
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5585_16 : Upper (D 3) (R 3) [288,5,192,65,129,16] 13 :=
  permutation_upper _ _ _ [288,5,192,65,129,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2130

def r5585 : Route 9 := (fun mask => (mask,id))

def c5585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5585 : Upper (D 3) (R 3) [288,5,192,65,129] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65,129] 13 (by decide) (choices 1) [2,8,16] r5585 c5585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2129
  · exact u2130
  · exact m5585_16

def b5586 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 196 73 146 57 121 185 313), lower := (rows 289 7 196 73 146 32 64 128 256), losses := [] }

theorem u5586 : Upper (D 3) (R 3) [288,5,192,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5587 : Route 9 := (fun mask => (mask,id))

def c5587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5587 : Upper (D 3) (R 3) [288,5,192,65,136] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65,136] 13 (by decide) (choices 1) [1,2,16] r5587 c5587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2131
  · exact u2132
  · exact u2133

def r5588 : Route 9 := (fun mask => (mask,id))

def c5588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5588 : Upper (D 3) (R 3) [288,5,192,65,160] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65,160] 13 (by decide) (choices 1) [1,2,8,16] r5588 c5588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2134
  · exact u2135
  · exact u2136
  · exact u2137

def b5589 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 74 152 49 113 177 305), lower := (rows 289 7 196 74 152 32 64 128 256), losses := [] }

theorem u5589 : Upper (D 3) (R 3) [288,5,192,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 74 176 57 89 153 281), lower := (rows 289 7 196 74 176 32 64 128 256), losses := [] }

theorem u5590 : Upper (D 3) (R 3) [288,5,192,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5591 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 196 88 152 35 99 163 291), lower := (rows 289 7 196 88 152 32 64 128 256), losses := [] }

theorem u5591 : Upper (D 3) (R 3) [288,5,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5592 : Route 9 := (fun mask => (mask,id))

def c5592 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5592 : Upper (D 3) (R 3) [288,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,192,80,160] 13 (by decide) (choices 1) [1,2,8] r5592 c5592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2138
  · exact u2139
  · exact u2140

def b5593 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 22 41 81 225 193 193 449), lower := (rows 289 14 22 41 81 32 64 128 256), losses := [] }

theorem u5593 : Upper (D 3) (R 3) [288,12,18,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5593
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 22 41 208 225 193 193 449), lower := (rows 289 14 22 41 208 32 64 128 256), losses := [] }

theorem u5594 : Upper (D 3) (R 3) [288,12,18,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 22 73 81 161 225 161 417), lower := (rows 289 14 22 73 81 32 64 128 256), losses := [] }

theorem u5595 : Upper (D 3) (R 3) [288,12,18,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5596 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 22 73 112 161 193 129 385), lower := (rows 289 14 22 73 112 32 64 128 256), losses := [] }

theorem u5596 : Upper (D 3) (R 3) [288,12,18,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5596
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5597_128 : Upper (D 3) (R 3) [288,12,18,65,129,128] 13 :=
  permutation_upper _ _ _ [288,12,18,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2142

def r5597 : Route 9 := (fun mask => (mask,id))

def c5597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5597 : Upper (D 3) (R 3) [288,12,18,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,18,65,129] 13 (by decide) (choices 1) [1,64,128] r5597 c5597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2141
  · exact u2142
  · exact m5597_128

def b5598 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 22 73 176 225 193 193 449), lower := (rows 289 14 22 73 176 32 64 128 256), losses := [] }

theorem u5598 : Upper (D 3) (R 3) [288,12,18,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 208 161 225 161 417), lower := (rows 289 14 22 73 208 32 64 128 256), losses := [] }

theorem u5599 : Upper (D 3) (R 3) [288,12,18,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5599
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 22 104 208 161 193 129 385), lower := (rows 289 14 22 104 208 32 64 128 256), losses := [] }

theorem u5600 : Upper (D 3) (R 3) [288,12,18,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5601 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 22 200 208 33 97 161 289), lower := (rows 289 14 22 200 208 32 64 128 256), losses := [] }

theorem u5601 : Upper (D 3) (R 3) [288,12,18,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5602 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 73 145 242 210 210 466), lower := (rows 289 14 37 73 145 32 64 128 256), losses := [] }

theorem u5602 : Upper (D 3) (R 3) [288,12,33,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5603 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 73 146 241 209 209 465), lower := (rows 289 14 37 73 146 32 64 128 256), losses := [] }

theorem u5603 : Upper (D 3) (R 3) [288,12,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5604 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 73 208 179 211 147 403), lower := (rows 289 14 37 73 208 32 64 128 256), losses := [] }

theorem u5604 : Upper (D 3) (R 3) [288,12,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5605 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 74 145 241 209 209 465), lower := (rows 289 14 37 74 145 32 64 128 256), losses := [] }

theorem u5605 : Upper (D 3) (R 3) [288,12,33,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5606 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 88 145 227 195 195 451), lower := (rows 289 14 37 88 145 32 64 128 256), losses := [] }

theorem u5606 : Upper (D 3) (R 3) [288,12,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 88 146 225 193 193 449), lower := (rows 289 14 37 88 146 32 64 128 256), losses := [] }

theorem u5607 : Upper (D 3) (R 3) [288,12,33,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 200 81 179 211 147 403), lower := (rows 289 14 37 200 81 32 64 128 256), losses := [] }

theorem u5608 : Upper (D 3) (R 3) [288,12,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 73 145 241 209 209 465), lower := (rows 289 14 38 73 145 32 64 128 256), losses := [] }

theorem u5609 : Upper (D 3) (R 3) [288,12,34,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 73 208 177 209 145 401), lower := (rows 289 14 38 73 208 32 64 128 256), losses := [] }

theorem u5610 : Upper (D 3) (R 3) [288,12,34,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5611 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 88 145 225 193 193 449), lower := (rows 289 14 38 88 145 32 64 128 256), losses := [] }

theorem u5611 : Upper (D 3) (R 3) [288,12,34,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 200 81 177 209 145 401), lower := (rows 289 14 38 200 81 32 64 128 256), losses := [] }

theorem u5612 : Upper (D 3) (R 3) [288,12,34,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 52 73 81 163 195 131 387), lower := (rows 289 14 52 73 81 32 64 128 256), losses := [] }

theorem u5613 : Upper (D 3) (R 3) [288,12,48,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 82 161 193 129 385), lower := (rows 289 14 52 73 82 32 64 128 256), losses := [] }

theorem u5614 : Upper (D 3) (R 3) [288,12,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5615 : Route 9 := (fun mask => (mask,id))

def c5615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5615 : Upper (D 3) (R 3) [288,12,48,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65,129] 13 (by decide) (choices 1) [1,2,64,128] r5615 c5615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2143
  · exact u2144
  · exact u2145
  · exact u2146

def b5616 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 52 73 146 225 193 193 449), lower := (rows 289 14 52 73 146 32 64 128 256), losses := [] }

theorem u5616 : Upper (D 3) (R 3) [288,12,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 208 163 195 131 387), lower := (rows 289 14 52 73 208 32 64 128 256), losses := [] }

theorem u5617 : Upper (D 3) (R 3) [288,12,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 74 81 161 193 129 385), lower := (rows 289 14 52 74 81 32 64 128 256), losses := [] }

theorem u5618 : Upper (D 3) (R 3) [288,12,48,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 52 74 145 225 193 193 449), lower := (rows 289 14 52 74 145 32 64 128 256), losses := [] }

theorem u5619 : Upper (D 3) (R 3) [288,12,48,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5619
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 74 208 161 193 129 385), lower := (rows 289 14 52 74 208 32 64 128 256), losses := [] }

theorem u5620 : Upper (D 3) (R 3) [288,12,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5620
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 200 81 163 195 131 387), lower := (rows 289 14 52 200 81 32 64 128 256), losses := [] }

theorem u5621 : Upper (D 3) (R 3) [288,12,48,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5621
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 200 82 161 193 129 385), lower := (rows 289 14 52 200 82 32 64 128 256), losses := [] }

theorem u5622 : Upper (D 3) (R 3) [288,12,48,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 52 200 208 35 67 131 259), lower := (rows 289 14 52 200 208 32 64 128 256), losses := [] }

theorem u5623 : Upper (D 3) (R 3) [288,12,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5624 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 50 177 209 145 401), lower := (rows 289 14 69 73 50 32 64 128 256), losses := [] }

theorem u5624 : Upper (D 3) (R 3) [288,12,65,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 145 178 242 178 434), lower := (rows 289 14 69 73 145 32 64 128 256), losses := [] }

theorem u5625 : Upper (D 3) (R 3) [288,12,65,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 146 177 241 177 433), lower := (rows 289 14 69 73 146 32 64 128 256), losses := [] }

theorem u5626 : Upper (D 3) (R 3) [288,12,65,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 176 179 211 147 403), lower := (rows 289 14 69 73 176 32 64 128 256), losses := [] }

theorem u5627 : Upper (D 3) (R 3) [288,12,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 69 74 145 177 241 177 433), lower := (rows 289 14 69 74 145 32 64 128 256), losses := [] }

theorem u5628 : Upper (D 3) (R 3) [288,12,65,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 69 74 176 177 209 145 401), lower := (rows 289 14 69 74 176 32 64 128 256), losses := [] }

theorem u5629 : Upper (D 3) (R 3) [288,12,65,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 50 161 193 129 385), lower := (rows 289 14 69 88 50 32 64 128 256), losses := [] }

theorem u5630 : Upper (D 3) (R 3) [288,12,65,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 145 163 227 163 419), lower := (rows 289 14 69 88 145 32 64 128 256), losses := [] }

theorem u5631 : Upper (D 3) (R 3) [288,12,65,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 146 161 225 161 417), lower := (rows 289 14 69 88 146 32 64 128 256), losses := [] }

theorem u5632 : Upper (D 3) (R 3) [288,12,65,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 176 163 195 131 387), lower := (rows 289 14 69 88 176 32 64 128 256), losses := [] }

theorem u5633 : Upper (D 3) (R 3) [288,12,65,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5633
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5634 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 145 179 211 147 403), lower := (rows 289 14 69 104 145 32 64 128 256), losses := [] }

theorem u5634 : Upper (D 3) (R 3) [288,12,65,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5635 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 146 177 209 145 401), lower := (rows 289 14 69 104 146 32 64 128 256), losses := [] }

theorem u5635 : Upper (D 3) (R 3) [288,12,65,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5636 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 137 49 242 210 210 466), lower := (rows 289 14 69 137 49 32 64 128 256), losses := [] }

theorem u5636 : Upper (D 3) (R 3) [288,12,65,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5636
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5637_128 : Upper (D 3) (R 3) [288,12,65,129,34,128] 13 :=
  permutation_upper _ _ _ [288,12,65,129,34,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2149

def r5637 : Route 9 := (fun mask => (mask,id))

def c5637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5637 : Upper (D 3) (R 3) [288,12,65,129,34] 13 := by
  apply FastRouting.sound _ _ [288,12,65,129,34] 13 (by decide) (choices 1) [1,16,64,128] r5637 c5637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2147
  · exact u2148
  · exact u2149
  · exact m5637_128

def b5638 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 137 81 178 242 178 434), lower := (rows 289 14 69 137 81 32 64 128 256), losses := [] }

theorem u5638 : Upper (D 3) (R 3) [288,12,65,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5639 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 82 177 241 177 433), lower := (rows 289 14 69 137 82 32 64 128 256), losses := [] }

theorem u5639 : Upper (D 3) (R 3) [288,12,65,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5639
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P03
