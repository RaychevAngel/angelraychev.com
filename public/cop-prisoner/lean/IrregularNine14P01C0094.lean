import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0034

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5640 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 82 76 137 20 162 226 162 418), lower := (rows 305 82 76 137 20 32 64 128 256), losses := [] }

theorem u5640 : Upper (D 1) (R 1) [304,80,72,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5641 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 76 137 48 166 198 134 390), lower := (rows 305 82 76 137 48 32 64 128 256), losses := [] }

theorem u5641 : Upper (D 1) (R 1) [304,80,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5642 : PairBound 9 := { available := 38, camps := [], pairs := [(1,5)], upper := (rows 305 82 76 137 144 38 102 166 294), lower := (rows 305 82 76 137 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 152 0 64 128 256), good := (rows 273 82 94 153 144 0 64 144 256) }] }

theorem u5642 : Upper (D 1) (R 1) [304,80,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5643 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 305 82 76 138 17 166 230 166 422), lower := (rows 305 82 76 138 17 32 64 128 256), losses := [] }

theorem u5643 : Upper (D 1) (R 1) [304,80,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5644 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 76 138 18 165 229 165 421), lower := (rows 305 82 76 138 18 32 64 128 256), losses := [] }

theorem u5644 : Upper (D 1) (R 1) [304,80,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 82 76 138 20 163 227 163 419), lower := (rows 305 82 76 138 20 32 64 128 256), losses := [] }

theorem u5645 : Upper (D 1) (R 1) [304,80,72,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 76 138 48 167 199 135 391), lower := (rows 305 82 76 138 48 32 64 128 256), losses := [] }

theorem u5646 : Upper (D 1) (R 1) [304,80,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5647 : PairBound 9 := { available := 39, camps := [], pairs := [(1,5)], upper := (rows 305 82 76 138 144 39 103 167 295), lower := (rows 305 82 76 138 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 152 0 64 128 256), good := (rows 273 82 94 154 144 0 64 144 256) }] }

theorem u5647 : Upper (D 1) (R 1) [304,80,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5648 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 76 168 17 166 198 134 390), lower := (rows 305 82 76 168 17 32 64 128 256), losses := [] }

theorem u5648 : Upper (D 1) (R 1) [304,80,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 135, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 76 168 18 167 199 135 391), lower := (rows 305 82 76 168 18 32 64 128 256), losses := [] }

theorem u5649 : Upper (D 1) (R 1) [304,80,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 82 76 168 20 163 195 131 387), lower := (rows 305 82 76 168 20 32 64 128 256), losses := [] }

theorem u5650 : Upper (D 1) (R 1) [304,80,72,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 7, camps := [], pairs := [(1,5)], upper := (rows 305 82 76 168 144 39 71 135 263), lower := (rows 305 82 76 168 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 152 0 64 128 256), good := (rows 273 82 94 152 144 0 64 144 256) }] }

theorem u5651 : Upper (D 1) (R 1) [304,80,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 100 137 18 174 206 142 398), lower := (rows 305 82 100 137 18 32 64 128 256), losses := [] }

theorem u5652 : Upper (D 1) (R 1) [304,80,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 100 137 20 170 202 138 394), lower := (rows 305 82 100 137 20 32 64 128 256), losses := [] }

theorem u5653 : Upper (D 1) (R 1) [304,80,96,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 305 82 100 137 24 166 198 134 390), lower := (rows 305 82 100 137 24 32 64 128 256), losses := [] }

theorem u5654 : Upper (D 1) (R 1) [304,80,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5655 : Route 9 := (fun mask => (mask,id))

def c5655 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5655 : Upper (D 1) (R 1) [304,80,96,129,128] 13 := by
  apply FastRouting.sound _ _ [304,80,96,129,128] 13 (by decide) (choices 1) [2,4,8] r5655 c5655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2045
  · exact u2046
  · exact u2047

def b5656 : PairBound 9 := { available := 142, camps := [], pairs := [], upper := (rows 305 82 100 138 17 174 206 142 398), lower := (rows 305 82 100 138 17 32 64 128 256), losses := [] }

theorem u5656 : Upper (D 1) (R 1) [304,80,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 100 138 18 173 205 141 397), lower := (rows 305 82 100 138 18 32 64 128 256), losses := [] }

theorem u5657 : Upper (D 1) (R 1) [304,80,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 305 82 100 138 20 171 203 139 395), lower := (rows 305 82 100 138 20 32 64 128 256), losses := [] }

theorem u5658 : Upper (D 1) (R 1) [304,80,96,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 135, camps := [], pairs := [], upper := (rows 305 82 100 138 24 167 199 135 391), lower := (rows 305 82 100 138 24 32 64 128 256), losses := [] }

theorem u5659 : Upper (D 1) (R 1) [304,80,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5659
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5660 : Route 9 := (fun mask => (mask,id))

def c5660 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5660 : Upper (D 1) (R 1) [304,80,96,130,128] 13 := by
  apply FastRouting.sound _ _ [304,80,96,130,128] 13 (by decide) (choices 1) [1,2,4,8] r5660 c5660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2048
  · exact u2049
  · exact u2050
  · exact u2051

def b5661 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 82 100 140 17 170 202 138 394), lower := (rows 305 82 100 140 17 32 64 128 256), losses := [] }

theorem u5661 : Upper (D 1) (R 1) [304,80,96,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 100 140 18 171 203 139 395), lower := (rows 305 82 100 140 18 32 64 128 256), losses := [] }

theorem u5662 : Upper (D 1) (R 1) [304,80,96,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 82 100 140 24 163 195 131 387), lower := (rows 305 82 100 140 24 32 64 128 256), losses := [] }

theorem u5663 : Upper (D 1) (R 1) [304,80,96,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5664 : Route 9 := (fun mask => (mask,id))

def c5664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5664 : Upper (D 1) (R 1) [304,80,96,132,128] 13 := by
  apply FastRouting.sound _ _ [304,80,96,132,128] 13 (by decide) (choices 1) [1,2,8] r5664 c5664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2052
  · exact u2053
  · exact u2054

def b5665 : PairBound 9 := { available := 108, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 133 138 18 108 108 236 364), lower := (rows 305 82 133 138 18 32 64 128 256), losses := [] }

theorem u5665 : Upper (D 1) (R 1) [304,80,129,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 305 82 133 138 20 106 106 234 362), lower := (rows 305 82 133 138 20 32 64 128 256), losses := [] }

theorem u5666 : Upper (D 1) (R 1) [304,80,129,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5667 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 305 82 133 138 24 102 102 230 358), lower := (rows 305 82 133 138 24 32 64 128 256), losses := [] }

theorem u5667 : Upper (D 1) (R 1) [304,80,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5668 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 133 138 48 110 78 206 334), lower := (rows 305 82 133 138 48 32 64 128 256), losses := [] }

theorem u5668 : Upper (D 1) (R 1) [304,80,129,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5669 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 133 138 80 46 110 174 302), lower := (rows 305 82 133 138 80 32 64 128 256), losses := [] }

theorem u5669 : Upper (D 1) (R 1) [304,80,129,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5670 : PairBound 9 := { available := 78, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 133 168 18 110 78 206 334), lower := (rows 305 82 133 168 18 32 64 128 256), losses := [] }

theorem u5670 : Upper (D 1) (R 1) [304,80,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 82 133 168 20 106 74 202 330), lower := (rows 305 82 133 168 20 32 64 128 256), losses := [] }

theorem u5671 : Upper (D 1) (R 1) [304,80,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 305 82 133 168 24 102 70 198 326), lower := (rows 305 82 133 168 24 32 64 128 256), losses := [] }

theorem u5672 : Upper (D 1) (R 1) [304,80,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 133 168 80 46 78 142 270), lower := (rows 305 82 133 168 80 32 64 128 256), losses := [] }

theorem u5673 : Upper (D 1) (R 1) [304,80,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5674 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 133 200 18 46 110 174 302), lower := (rows 305 82 133 200 18 32 64 128 256), losses := [] }

theorem u5674 : Upper (D 1) (R 1) [304,80,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 82 133 200 20 42 106 170 298), lower := (rows 305 82 133 200 20 32 64 128 256), losses := [] }

theorem u5675 : Upper (D 1) (R 1) [304,80,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 305 82 133 200 24 38 102 166 294), lower := (rows 305 82 133 200 24 32 64 128 256), losses := [] }

theorem u5676 : Upper (D 1) (R 1) [304,80,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 133 200 48 46 78 142 270), lower := (rows 305 82 133 200 48 32 64 128 256), losses := [] }

theorem u5677 : Upper (D 1) (R 1) [304,80,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5678 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 305 82 134 168 17 110 78 206 334), lower := (rows 305 82 134 168 17 32 64 128 256), losses := [] }

theorem u5678 : Upper (D 1) (R 1) [304,80,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 77, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 134 168 18 109 77 205 333), lower := (rows 305 82 134 168 18 32 64 128 256), losses := [] }

theorem u5679 : Upper (D 1) (R 1) [304,80,130,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 305 82 134 168 20 107 75 203 331), lower := (rows 305 82 134 168 20 32 64 128 256), losses := [] }

theorem u5680 : Upper (D 1) (R 1) [304,80,130,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5681 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 305 82 134 168 24 103 71 199 327), lower := (rows 305 82 134 168 24 32 64 128 256), losses := [] }

theorem u5681 : Upper (D 1) (R 1) [304,80,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5682 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 134 168 80 47 79 143 271), lower := (rows 305 82 134 168 80 32 64 128 256), losses := [] }

theorem u5682 : Upper (D 1) (R 1) [304,80,130,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 46, camps := [], pairs := [], upper := (rows 305 82 134 200 17 46 110 174 302), lower := (rows 305 82 134 200 17 32 64 128 256), losses := [] }

theorem u5683 : Upper (D 1) (R 1) [304,80,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 134 200 18 45 109 173 301), lower := (rows 305 82 134 200 18 32 64 128 256), losses := [] }

theorem u5684 : Upper (D 1) (R 1) [304,80,130,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 305 82 134 200 20 43 107 171 299), lower := (rows 305 82 134 200 20 32 64 128 256), losses := [] }

theorem u5685 : Upper (D 1) (R 1) [304,80,130,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 39, camps := [], pairs := [], upper := (rows 305 82 134 200 24 39 103 167 295), lower := (rows 305 82 134 200 24 32 64 128 256), losses := [] }

theorem u5686 : Upper (D 1) (R 1) [304,80,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5687 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 134 200 48 47 79 143 271), lower := (rows 305 82 134 200 48 32 64 128 256), losses := [] }

theorem u5687 : Upper (D 1) (R 1) [304,80,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5688 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 305 82 164 200 17 46 78 142 270), lower := (rows 305 82 164 200 17 32 64 128 256), losses := [] }

theorem u5688 : Upper (D 1) (R 1) [304,80,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5689 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 164 200 18 47 79 143 271), lower := (rows 305 82 164 200 18 32 64 128 256), losses := [] }

theorem u5689 : Upper (D 1) (R 1) [304,80,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5690 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 82 164 200 20 43 75 139 267), lower := (rows 305 82 164 200 20 32 64 128 256), losses := [] }

theorem u5690 : Upper (D 1) (R 1) [304,80,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 82 164 200 24 39 71 135 263), lower := (rows 305 82 164 200 24 32 64 128 256), losses := [] }

theorem u5691 : Upper (D 1) (R 1) [304,80,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 305 194 7 26 20 232 232 232 488), lower := (rows 305 194 7 26 20 32 64 128 256), losses := [] }

theorem u5692 : Upper (D 1) (R 1) [304,192,3,18,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5693 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 305 194 7 26 24 228 228 228 484), lower := (rows 305 194 7 26 24 32 64 128 256), losses := [] }

theorem u5693 : Upper (D 1) (R 1) [304,192,3,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 7 26 48 236 204 204 460), lower := (rows 305 194 7 26 48 32 64 128 256), losses := [] }

theorem u5694 : Upper (D 1) (R 1) [304,192,3,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 194 7 26 80 172 236 172 428), lower := (rows 305 194 7 26 80 32 64 128 256), losses := [] }

theorem u5695 : Upper (D 1) (R 1) [304,192,3,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 184, camps := [], pairs := [(0,6)], upper := (rows 305 194 7 76 18 184 248 184 440), lower := (rows 305 194 7 76 18 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 22 40 0 136 264), good := (rows 305 146 23 445 18 32 0 128 256) }] }

theorem u5696 : Upper (D 1) (R 1) [304,192,3,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 194 7 76 24 178 242 178 434), lower := (rows 305 194 7 76 24 32 64 128 256), losses := [] }

theorem u5697 : Upper (D 1) (R 1) [304,192,3,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 7 76 48 186 218 154 410), lower := (rows 305 194 7 76 48 32 64 128 256), losses := [] }

theorem u5698 : Upper (D 1) (R 1) [304,192,3,68,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5698
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5699_2 : Upper (D 1) (R 1) [304,192,3,68,128,2] 13 :=
  permutation_upper _ _ _ [304,192,3,68,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2055

theorem m5699_8 : Upper (D 1) (R 1) [304,192,3,68,128,8] 13 :=
  permutation_upper _ _ _ [304,192,3,68,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2056

theorem m5699_16 : Upper (D 1) (R 1) [304,192,3,68,128,16] 13 :=
  permutation_upper _ _ _ [304,192,3,68,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2057

def r5699 : Route 9 := (fun mask => (mask,id))

def c5699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5699 : Upper (D 1) (R 1) [304,192,3,68,128] 13 := by
  apply FastRouting.sound _ _ [304,192,3,68,128] 13 (by decide) (choices 1) [2,8,16] r5699 c5699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5699_2
  · exact m5699_8
  · exact m5699_16

#print axioms u5699
end Delivery.IrregularNine14.P01
