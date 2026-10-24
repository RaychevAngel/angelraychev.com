import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0035
import IrregularNine14P05C0036

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5640 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 228, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 26 196 266 28 33 97 161 289), lower := (rows 7 26 196 266 28 32 64 128 256), losses := [] }

theorem u5640 : Upper (D 5) (R 5) [6,24,192,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5641 : Route 9 := (fun mask => (mask,id))

def c5641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5641 : Upper (D 5) (R 5) [6,24,192,258,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,258,33] 13 (by decide) (choices 1) [1,4,8] r5641 c5641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2123
  · exact u2124
  · exact u2125

def r5642 : Route 9 := (fun mask => (mask,id))

def c5642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5642 : Upper (D 5) (R 5) [6,24,192,258,36] 13 := by
  apply FastRouting.sound _ _ [6,24,192,258,36] 13 (by decide) (choices 1) [1,8] r5642 c5642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2126
  · exact u2127

def b5643 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 266 56 37 101 165 293), lower := (rows 7 26 196 266 56 32 64 128 256), losses := [] }

theorem u5643 : Upper (D 5) (R 5) [6,24,192,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5644 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 196 268 19 41 105 169 297), lower := (rows 7 26 196 268 19 32 64 128 256), losses := [] }

theorem u5644 : Upper (D 5) (R 5) [6,24,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 196 268 25 35 99 163 291), lower := (rows 7 26 196 268 25 32 64 128 256), losses := [] }

theorem u5645 : Upper (D 5) (R 5) [6,24,192,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 268 26 33 97 161 289), lower := (rows 7 26 196 268 26 32 64 128 256), losses := [] }

theorem u5646 : Upper (D 5) (R 5) [6,24,192,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5647 : Route 9 := (fun mask => (mask,id))

def c5647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5647 : Upper (D 5) (R 5) [6,24,192,260,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,260,33] 13 (by decide) (choices 1) [1,2,8] r5647 c5647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2128
  · exact u2129
  · exact u2130

def b5648 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 268 50 41 105 169 297), lower := (rows 7 26 196 268 50 32 64 128 256), losses := [] }

theorem u5648 : Upper (D 5) (R 5) [6,24,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 268 56 35 99 163 291), lower := (rows 7 26 196 268 56 32 64 128 256), losses := [] }

theorem u5649 : Upper (D 5) (R 5) [6,24,192,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 196 296 19 45 109 173 301), lower := (rows 7 26 196 296 19 32 64 128 256), losses := [] }

theorem u5650 : Upper (D 5) (R 5) [6,24,192,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 296 21 43 107 171 299), lower := (rows 7 26 196 296 21 32 64 128 256), losses := [] }

theorem u5651 : Upper (D 5) (R 5) [6,24,192,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 196 296 22 41 105 169 297), lower := (rows 7 26 196 296 22 32 64 128 256), losses := [] }

theorem u5652 : Upper (D 5) (R 5) [6,24,192,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 296 25 39 103 167 295), lower := (rows 7 26 196 296 25 32 64 128 256), losses := [] }

theorem u5653 : Upper (D 5) (R 5) [6,24,192,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 296 26 37 101 165 293), lower := (rows 7 26 196 296 26 32 64 128 256), losses := [] }

theorem u5654 : Upper (D 5) (R 5) [6,24,192,288,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5655 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 229, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 196 296 28 35 99 163 291), lower := (rows 7 26 196 296 28 32 64 128 256), losses := [] }

theorem u5655 : Upper (D 5) (R 5) [6,24,192,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 296 49 47 79 143 271), lower := (rows 7 26 196 296 49 32 64 128 256), losses := [] }

theorem u5656 : Upper (D 5) (R 5) [6,24,192,288,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 296 50 45 77 141 269), lower := (rows 7 26 196 296 50 32 64 128 256), losses := [] }

theorem u5657 : Upper (D 5) (R 5) [6,24,192,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 196 296 52 43 75 139 267), lower := (rows 7 26 196 296 52 32 64 128 256), losses := [] }

theorem u5658 : Upper (D 5) (R 5) [6,24,192,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 196 296 56 39 71 135 263), lower := (rows 7 26 196 296 56 32 64 128 256), losses := [] }

theorem u5659 : Upper (D 5) (R 5) [6,24,192,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5659
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5660 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 76 25 22 424 488 424 424), lower := (rows 7 35 76 25 22 32 64 128 256), losses := [] }

theorem u5660 : Upper (D 5) (R 5) [6,33,72,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5661 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 76 25 26 420 484 420 420), lower := (rows 7 35 76 25 26 32 64 128 256), losses := [] }

theorem u5661 : Upper (D 5) (R 5) [6,33,72,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 76 25 28 418 482 418 418), lower := (rows 7 35 76 25 28 32 64 128 256), losses := [] }

theorem u5662 : Upper (D 5) (R 5) [6,33,72,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 25 50 428 460 396 396), lower := (rows 7 35 76 25 50 32 64 128 256), losses := [] }

theorem u5663 : Upper (D 5) (R 5) [6,33,72,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5664 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 25 52 426 458 394 394), lower := (rows 7 35 76 25 52 32 64 128 256), losses := [] }

theorem u5664 : Upper (D 5) (R 5) [6,33,72,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 76 25 56 422 454 390 390), lower := (rows 7 35 76 25 56 32 64 128 256), losses := [] }

theorem u5665 : Upper (D 5) (R 5) [6,33,72,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 25 146 300 364 428 300), lower := (rows 7 35 76 25 146 32 64 128 256), losses := [] }

theorem u5666 : Upper (D 5) (R 5) [6,33,72,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5667 : Route 9 := (fun mask => (mask,id))

def c5667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5667 : Upper (D 5) (R 5) [6,33,72,17,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,132] 13 (by decide) (choices 1) [2,8,256] r5667 c5667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2131
  · exact u2132
  · exact u2133

def b5668 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 25 152 294 358 422 294), lower := (rows 7 35 76 25 152 32 64 128 256), losses := [] }

theorem u5668 : Upper (D 5) (R 5) [6,33,72,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5669 : Route 9 := (fun mask => (mask,id))

def c5669 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5669 : Upper (D 5) (R 5) [6,33,72,17,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,160] 13 (by decide) (choices 1) [2,4,8,256] r5669 c5669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2134
  · exact u2135
  · exact u2136
  · exact u2137

def r5670 : Route 9 := (fun mask => (mask,id))

def c5670 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5670 : Upper (D 5) (R 5) [6,33,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,384] 13 (by decide) (choices 1) [2,4,8] r5670 c5670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2138
  · exact u2139
  · exact u2140

def b5671 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 26 21 424 488 424 424), lower := (rows 7 35 76 26 21 32 64 128 256), losses := [] }

theorem u5671 : Upper (D 5) (R 5) [6,33,72,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 76 26 25 420 484 420 420), lower := (rows 7 35 76 26 25 32 64 128 256), losses := [] }

theorem u5672 : Upper (D 5) (R 5) [6,33,72,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 26 28 417 481 417 417), lower := (rows 7 35 76 26 28 32 64 128 256), losses := [] }

theorem u5673 : Upper (D 5) (R 5) [6,33,72,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5674 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 24, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 76 26 49 428 460 396 396), lower := (rows 7 35 76 26 49 32 64 128 256), losses := [] }

theorem u5674 : Upper (D 5) (R 5) [6,33,72,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 26 52 425 457 393 393), lower := (rows 7 35 76 26 52 32 64 128 256), losses := [] }

theorem u5675 : Upper (D 5) (R 5) [6,33,72,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 35 76 26 56 421 453 389 389), lower := (rows 7 35 76 26 56 32 64 128 256), losses := [] }

theorem u5676 : Upper (D 5) (R 5) [6,33,72,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 26 145 300 364 428 300), lower := (rows 7 35 76 26 145 32 64 128 256), losses := [] }

theorem u5677 : Upper (D 5) (R 5) [6,33,72,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5678 : Route 9 := (fun mask => (mask,id))

def c5678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5678 : Upper (D 5) (R 5) [6,33,72,18,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,132] 13 (by decide) (choices 1) [1,8,256] r5678 c5678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2141
  · exact u2142
  · exact u2143

def b5679 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 26 152 293 357 421 293), lower := (rows 7 35 76 26 152 32 64 128 256), losses := [] }

theorem u5679 : Upper (D 5) (R 5) [6,33,72,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5679
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 26 176 301 333 397 269), lower := (rows 7 35 76 26 176 32 64 128 256), losses := [] }

theorem u5680 : Upper (D 5) (R 5) [6,33,72,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5681 : Route 9 := (fun mask => (mask,id))

def c5681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5681 : Upper (D 5) (R 5) [6,33,72,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,384] 13 (by decide) (choices 1) [1,4,8] r5681 c5681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2144
  · exact u2145
  · exact u2146

def b5682 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 28 19 424 488 424 424), lower := (rows 7 35 76 28 19 32 64 128 256), losses := [] }

theorem u5682 : Upper (D 5) (R 5) [6,33,72,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 76 28 25 418 482 418 418), lower := (rows 7 35 76 28 25 32 64 128 256), losses := [] }

theorem u5683 : Upper (D 5) (R 5) [6,33,72,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 76 28 26 417 481 417 417), lower := (rows 7 35 76 28 26 32 64 128 256), losses := [] }

theorem u5684 : Upper (D 5) (R 5) [6,33,72,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 28 49 426 458 394 394), lower := (rows 7 35 76 28 49 32 64 128 256), losses := [] }

theorem u5685 : Upper (D 5) (R 5) [6,33,72,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 76 28 50 425 457 393 393), lower := (rows 7 35 76 28 50 32 64 128 256), losses := [] }

theorem u5686 : Upper (D 5) (R 5) [6,33,72,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5687 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 418, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 35 76 28 56 419 451 387 387), lower := (rows 7 35 76 28 56 32 64 128 256), losses := [] }

theorem u5687 : Upper (D 5) (R 5) [6,33,72,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5688 : Route 9 := (fun mask => (mask,id))

def c5688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5688 : Upper (D 5) (R 5) [6,33,72,20,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,129] 13 (by decide) (choices 1) [2,8,256] r5688 c5688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2147
  · exact u2148
  · exact u2149

def r5689 : Route 9 := (fun mask => (mask,id))

def c5689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5689 : Upper (D 5) (R 5) [6,33,72,20,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,130] 13 (by decide) (choices 1) [1,8,256] r5689 c5689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2150
  · exact u2151
  · exact u2152

def b5690 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 290, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 35 76 28 152 291 355 419 291), lower := (rows 7 35 76 28 152 32 64 128 256), losses := [] }

theorem u5690 : Upper (D 5) (R 5) [6,33,72,20,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5691 : Route 9 := (fun mask => (mask,id))

def c5691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5691 : Upper (D 5) (R 5) [6,33,72,20,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,160] 13 (by decide) (choices 1) [1,2,8,256] r5691 c5691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2153
  · exact u2154
  · exact u2155
  · exact u2156

def r5692 : Route 9 := (fun mask => (mask,id))

def c5692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5692 : Upper (D 5) (R 5) [6,33,72,20,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,384] 13 (by decide) (choices 1) [1,2,8] r5692 c5692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2157
  · exact u2158
  · exact u2159

def b5693 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 56 19 428 460 396 396), lower := (rows 7 35 76 56 19 32 64 128 256), losses := [] }

theorem u5693 : Upper (D 5) (R 5) [6,33,72,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 56 21 426 458 394 394), lower := (rows 7 35 76 56 21 32 64 128 256), losses := [] }

theorem u5694 : Upper (D 5) (R 5) [6,33,72,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 56 22 425 457 393 393), lower := (rows 7 35 76 56 22 32 64 128 256), losses := [] }

theorem u5695 : Upper (D 5) (R 5) [6,33,72,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 76 56 25 422 454 390 390), lower := (rows 7 35 76 56 25 32 64 128 256), losses := [] }

theorem u5696 : Upper (D 5) (R 5) [6,33,72,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 35 76 56 26 421 453 389 389), lower := (rows 7 35 76 56 26 32 64 128 256), losses := [] }

theorem u5697 : Upper (D 5) (R 5) [6,33,72,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 56 28 419 451 387 387), lower := (rows 7 35 76 56 28 32 64 128 256), losses := [] }

theorem u5698 : Upper (D 5) (R 5) [6,33,72,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5699 : Route 9 := (fun mask => (mask,id))

def c5699 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5699 : Upper (D 5) (R 5) [6,33,72,48,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,129] 13 (by decide) (choices 1) [2,4,8,256] r5699 c5699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2160
  · exact u2161
  · exact u2162
  · exact u2163

#print axioms u5699
end Delivery.IrregularNine14.P05
