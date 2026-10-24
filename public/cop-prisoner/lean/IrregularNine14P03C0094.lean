import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0035
import IrregularNine14P03C0036

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5640 : Route 9 := (fun mask => (mask,id))

def c5640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5640 : Upper (D 3) (R 3) [288,12,65,129,96] 13 := by
  apply FastRouting.sound _ _ [288,12,65,129,96] 13 (by decide) (choices 1) [1,2,16,128] r5640 c5640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2150
  · exact u2151
  · exact u2152
  · exact u2153

def r5641 : Route 9 := (fun mask => (mask,id))

def c5641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5641 : Upper (D 3) (R 3) [288,12,65,129,192] 13 := by
  apply FastRouting.sound _ _ [288,12,65,129,192] 13 (by decide) (choices 1) [1,2,16] r5641 c5641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2154
  · exact u2155
  · exact u2156

def b5642 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 138 49 241 209 209 465), lower := (rows 289 14 69 138 49 32 64 128 256), losses := [] }

theorem u5642 : Upper (D 3) (R 3) [288,12,65,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5642
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5643 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 138 81 177 241 177 433), lower := (rows 289 14 69 138 81 32 64 128 256), losses := [] }

theorem u5643 : Upper (D 3) (R 3) [288,12,65,130,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5644 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 138 112 177 209 145 401), lower := (rows 289 14 69 138 112 32 64 128 256), losses := [] }

theorem u5644 : Upper (D 3) (R 3) [288,12,65,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 145 113 113 241 369), lower := (rows 289 14 69 138 145 32 64 128 256), losses := [] }

theorem u5645 : Upper (D 3) (R 3) [288,12,65,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 176 113 81 209 337), lower := (rows 289 14 69 138 176 32 64 128 256), losses := [] }

theorem u5646 : Upper (D 3) (R 3) [288,12,65,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5646
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5647 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 208 49 113 177 305), lower := (rows 289 14 69 138 208 32 64 128 256), losses := [] }

theorem u5647 : Upper (D 3) (R 3) [288,12,65,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5647
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5648 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 152 49 227 195 195 451), lower := (rows 289 14 69 152 49 32 64 128 256), losses := [] }

theorem u5648 : Upper (D 3) (R 3) [288,12,65,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5648
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 289 14 69 152 50 225 193 193 449), lower := (rows 289 14 69 152 50 32 64 128 256), losses := [] }

theorem u5649 : Upper (D 3) (R 3) [288,12,65,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 152 81 163 227 163 419), lower := (rows 289 14 69 152 81 32 64 128 256), losses := [] }

theorem u5650 : Upper (D 3) (R 3) [288,12,65,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5650
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 82 161 225 161 417), lower := (rows 289 14 69 152 82 32 64 128 256), losses := [] }

theorem u5651 : Upper (D 3) (R 3) [288,12,65,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 112 163 195 131 387), lower := (rows 289 14 69 152 112 32 64 128 256), losses := [] }

theorem u5652 : Upper (D 3) (R 3) [288,12,65,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5652
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 145 99 99 227 355), lower := (rows 289 14 69 152 145 32 64 128 256), losses := [] }

theorem u5653 : Upper (D 3) (R 3) [288,12,65,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 146 97 97 225 353), lower := (rows 289 14 69 152 146 32 64 128 256), losses := [] }

theorem u5654 : Upper (D 3) (R 3) [288,12,65,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5655 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 176 99 67 195 323), lower := (rows 289 14 69 152 176 32 64 128 256), losses := [] }

theorem u5655 : Upper (D 3) (R 3) [288,12,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 208 35 99 163 291), lower := (rows 289 14 69 152 208 32 64 128 256), losses := [] }

theorem u5656 : Upper (D 3) (R 3) [288,12,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 168 81 179 211 147 403), lower := (rows 289 14 69 168 81 32 64 128 256), losses := [] }

theorem u5657 : Upper (D 3) (R 3) [288,12,65,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5657
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 82 177 209 145 401), lower := (rows 289 14 69 168 82 32 64 128 256), losses := [] }

theorem u5658 : Upper (D 3) (R 3) [288,12,65,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5659 : Route 9 := (fun mask => (mask,id))

def c5659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5659 : Upper (D 3) (R 3) [288,12,65,160,129] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,129] 13 (by decide) (choices 1) [1,2,16,64] r5659 c5659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2157
  · exact u2158
  · exact u2159
  · exact u2160

def b5660 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 146 113 81 209 337), lower := (rows 289 14 69 168 146 32 64 128 256), losses := [] }

theorem u5660 : Upper (D 3) (R 3) [288,12,65,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5661 : Route 9 := (fun mask => (mask,id))

def c5661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5661 : Upper (D 3) (R 3) [288,12,65,160,192] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,192] 13 (by decide) (choices 1) [1,2,16] r5661 c5661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2161
  · exact u2162
  · exact u2163

def b5662 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 50 177 209 145 401), lower := (rows 289 14 69 200 50 32 64 128 256), losses := [] }

theorem u5662 : Upper (D 3) (R 3) [288,12,65,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5662
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 145 51 115 179 307), lower := (rows 289 14 69 200 145 32 64 128 256), losses := [] }

theorem u5663 : Upper (D 3) (R 3) [288,12,65,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5664 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 146 49 113 177 305), lower := (rows 289 14 69 200 146 32 64 128 256), losses := [] }

theorem u5664 : Upper (D 3) (R 3) [288,12,65,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5664
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 176 51 83 147 275), lower := (rows 289 14 69 200 176 32 64 128 256), losses := [] }

theorem u5665 : Upper (D 3) (R 3) [288,12,65,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 88 145 161 225 161 417), lower := (rows 289 14 70 88 145 32 64 128 256), losses := [] }

theorem u5666 : Upper (D 3) (R 3) [288,12,66,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5666
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5667 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 88 176 161 193 129 385), lower := (rows 289 14 70 88 176 32 64 128 256), losses := [] }

theorem u5667 : Upper (D 3) (R 3) [288,12,66,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5667
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5668 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 104 145 177 209 145 401), lower := (rows 289 14 70 104 145 32 64 128 256), losses := [] }

theorem u5668 : Upper (D 3) (R 3) [288,12,66,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5668
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5669 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 70 152 49 225 193 193 449), lower := (rows 289 14 70 152 49 32 64 128 256), losses := [] }

theorem u5669 : Upper (D 3) (R 3) [288,12,66,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5669
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5670 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 152 81 161 225 161 417), lower := (rows 289 14 70 152 81 32 64 128 256), losses := [] }

theorem u5670 : Upper (D 3) (R 3) [288,12,66,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 152 112 161 193 129 385), lower := (rows 289 14 70 152 112 32 64 128 256), losses := [] }

theorem u5671 : Upper (D 3) (R 3) [288,12,66,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5671
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 70 152 145 97 97 225 353), lower := (rows 289 14 70 152 145 32 64 128 256), losses := [] }

theorem u5672 : Upper (D 3) (R 3) [288,12,66,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 70 152 176 97 65 193 321), lower := (rows 289 14 70 152 176 32 64 128 256), losses := [] }

theorem u5673 : Upper (D 3) (R 3) [288,12,66,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5674 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 152 208 33 97 161 289), lower := (rows 289 14 70 152 208 32 64 128 256), losses := [] }

theorem u5674 : Upper (D 3) (R 3) [288,12,66,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 168 81 177 209 145 401), lower := (rows 289 14 70 168 81 32 64 128 256), losses := [] }

theorem u5675 : Upper (D 3) (R 3) [288,12,66,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 70 168 145 113 81 209 337), lower := (rows 289 14 70 168 145 32 64 128 256), losses := [] }

theorem u5676 : Upper (D 3) (R 3) [288,12,66,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5676
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 70 168 208 49 81 145 273), lower := (rows 289 14 70 168 208 32 64 128 256), losses := [] }

theorem u5677 : Upper (D 3) (R 3) [288,12,66,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5678 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 200 145 49 113 177 305), lower := (rows 289 14 70 200 145 32 64 128 256), losses := [] }

theorem u5678 : Upper (D 3) (R 3) [288,12,66,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5678
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 200 176 49 81 145 273), lower := (rows 289 14 70 200 176 32 64 128 256), losses := [] }

theorem u5679 : Upper (D 3) (R 3) [288,12,66,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5679
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 145 163 195 131 387), lower := (rows 289 14 84 104 145 32 64 128 256), losses := [] }

theorem u5680 : Upper (D 3) (R 3) [288,12,80,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5681 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 146 161 193 129 385), lower := (rows 289 14 84 104 146 32 64 128 256), losses := [] }

theorem u5681 : Upper (D 3) (R 3) [288,12,80,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5681
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5682 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 81 163 195 131 387), lower := (rows 289 14 84 168 81 32 64 128 256), losses := [] }

theorem u5682 : Upper (D 3) (R 3) [288,12,80,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 82 161 193 129 385), lower := (rows 289 14 84 168 82 32 64 128 256), losses := [] }

theorem u5683 : Upper (D 3) (R 3) [288,12,80,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5683
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 84 168 145 99 67 195 323), lower := (rows 289 14 84 168 145 32 64 128 256), losses := [] }

theorem u5684 : Upper (D 3) (R 3) [288,12,80,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5684
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 84 168 146 97 65 193 321), lower := (rows 289 14 84 168 146 32 64 128 256), losses := [] }

theorem u5685 : Upper (D 3) (R 3) [288,12,80,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 168 208 35 67 131 259), lower := (rows 289 14 84 168 208 32 64 128 256), losses := [] }

theorem u5686 : Upper (D 3) (R 3) [288,12,80,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5687 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 50 161 193 129 385), lower := (rows 289 14 84 200 50 32 64 128 256), losses := [] }

theorem u5687 : Upper (D 3) (R 3) [288,12,80,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5687
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5688 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 145 35 99 163 291), lower := (rows 289 14 84 200 145 32 64 128 256), losses := [] }

theorem u5688 : Upper (D 3) (R 3) [288,12,80,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5688
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5689 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 84 200 146 33 97 161 289), lower := (rows 289 14 84 200 146 32 64 128 256), losses := [] }

theorem u5689 : Upper (D 3) (R 3) [288,12,80,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5690 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 176 35 67 131 259), lower := (rows 289 14 84 200 176 32 64 128 256), losses := [] }

theorem u5690 : Upper (D 3) (R 3) [288,12,80,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5690
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 145 51 83 147 275), lower := (rows 289 14 100 200 145 32 64 128 256), losses := [] }

theorem u5691 : Upper (D 3) (R 3) [288,12,96,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 146 49 81 145 273), lower := (rows 289 14 100 200 146 32 64 128 256), losses := [] }

theorem u5692 : Upper (D 3) (R 3) [288,12,96,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5692
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5693 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 196 200 50 49 81 145 273), lower := (rows 289 14 196 200 50 32 64 128 256), losses := [] }

theorem u5693 : Upper (D 3) (R 3) [288,12,192,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 74 145 188 220 156 412), lower := (rows 289 35 69 74 145 32 64 128 256), losses := [] }

theorem u5694 : Upper (D 3) (R 3) [288,33,65,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 74 148 185 217 153 409), lower := (rows 289 35 69 74 148 32 64 128 256), losses := [] }

theorem u5695 : Upper (D 3) (R 3) [288,33,65,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 74 152 181 213 149 405), lower := (rows 289 35 69 74 152 32 64 128 256), losses := [] }

theorem u5696 : Upper (D 3) (R 3) [288,33,65,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5696
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 142, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 88 145 174 206 142 398), lower := (rows 289 35 69 88 145 32 64 128 256), losses := [] }

theorem u5697 : Upper (D 3) (R 3) [288,33,65,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5697
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 88 146 173 205 141 397), lower := (rows 289 35 69 88 146 32 64 128 256), losses := [] }

theorem u5698 : Upper (D 3) (R 3) [288,33,65,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5698
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5699 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5)], upper := (rows 289 35 69 137 208 62 94 158 286), lower := (rows 289 35 69 137 208 32 64 128 256), losses := [] }

theorem u5699 : Upper (D 3) (R 3) [288,33,65,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5699
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5699
end Delivery.IrregularNine14.P03
