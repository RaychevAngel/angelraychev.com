import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0018
import IrregularNine14P05C0019

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3660 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 137 276 34 105 169 297), lower := (rows 19 38 76 137 276 34 64 128 256), losses := [] }

theorem u3660 : Upper (D 5) (R 5) [18,36,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3661 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 38 76 137 276 40 99 163 291), lower := (rows 19 38 76 137 276 40 64 128 256), losses := [] }

theorem u3661 : Upper (D 5) (R 5) [18,36,72,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3662 : Route 9 := (fun mask => (mask,id))

def c3662 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3662 : Upper (D 5) (R 5) [18,36,72,129,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129,264,1] 13 (by decide) (choices 1) [2,4,32] r3662 c3662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131

def b3663 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 137 280 34 101 165 293), lower := (rows 19 38 76 137 280 34 64 128 256), losses := [] }

theorem u3663 : Upper (D 5) (R 5) [18,36,72,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3664 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 137 280 36 99 163 291), lower := (rows 19 38 76 137 280 36 64 128 256), losses := [] }

theorem u3664 : Upper (D 5) (R 5) [18,36,72,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3665 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 138 273 33 108 172 300), lower := (rows 19 38 76 138 273 33 64 128 256), losses := [] }

theorem u3665 : Upper (D 5) (R 5) [18,36,72,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 138 273 36 105 169 297), lower := (rows 19 38 76 138 273 36 64 128 256), losses := [] }

theorem u3666 : Upper (D 5) (R 5) [18,36,72,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 38 76 138 273 40 101 165 293), lower := (rows 19 38 76 138 273 40 64 128 256), losses := [] }

theorem u3667 : Upper (D 5) (R 5) [18,36,72,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3667
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3668 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 76 138 276 33 105 169 297), lower := (rows 19 38 76 138 276 33 64 128 256), losses := [] }

theorem u3668 : Upper (D 5) (R 5) [18,36,72,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3668
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3669 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 38 76 138 276 40 97 161 289), lower := (rows 19 38 76 138 276 40 64 128 256), losses := [] }

theorem u3669 : Upper (D 5) (R 5) [18,36,72,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3670 : Route 9 := (fun mask => (mask,id))

def c3670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3670 : Upper (D 5) (R 5) [18,36,72,130,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130,264,1] 13 (by decide) (choices 1) [1,4,32] r3670 c3670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1132
  · exact u1133
  · exact u1134

def b3671 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 138 280 36 97 161 289), lower := (rows 19 38 76 138 280 36 64 128 256), losses := [] }

theorem u3671 : Upper (D 5) (R 5) [18,36,72,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3671
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3672 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 140 25 33 354 418 290), lower := (rows 19 38 76 140 25 33 64 128 256), losses := [] }

theorem u3672 : Upper (D 5) (R 5) [18,36,72,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3673 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 140 25 34 353 417 289), lower := (rows 19 38 76 140 25 34 64 128 256), losses := [] }

theorem u3673 : Upper (D 5) (R 5) [18,36,72,132,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3674 : Route 9 := (fun mask => (mask,id))

def c3674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3674 : Upper (D 5) (R 5) [18,36,72,132,9,256] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132,9,256] 13 (by decide) (choices 1) [1,2,32] r3674 c3674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1135
  · exact u1136
  · exact u1137

def b3675 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 140 273 33 106 170 298), lower := (rows 19 38 76 140 273 33 64 128 256), losses := [] }

theorem u3675 : Upper (D 5) (R 5) [18,36,72,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3676 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 140 273 34 105 169 297), lower := (rows 19 38 76 140 273 34 64 128 256), losses := [] }

theorem u3676 : Upper (D 5) (R 5) [18,36,72,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3676
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 273, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 76 140 273 40 99 163 291), lower := (rows 19 38 76 140 273 40 64 128 256), losses := [] }

theorem u3677 : Upper (D 5) (R 5) [18,36,72,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3678 : Route 9 := (fun mask => (mask,id))

def c3678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3678 : Upper (D 5) (R 5) [18,36,72,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132,264,1] 13 (by decide) (choices 1) [1,2,32] r3678 c3678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1138
  · exact u1139
  · exact u1140

def b3679 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 140 280 34 97 161 289), lower := (rows 19 38 76 140 280 34 64 128 256), losses := [] }

theorem u3679 : Upper (D 5) (R 5) [18,36,72,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3679
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 168 25 33 326 390 262), lower := (rows 19 38 76 168 25 33 64 128 256), losses := [] }

theorem u3680 : Upper (D 5) (R 5) [18,36,72,160,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 168 25 34 325 389 261), lower := (rows 19 38 76 168 25 34 64 128 256), losses := [] }

theorem u3681 : Upper (D 5) (R 5) [18,36,72,160,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3682 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 168 25 36 323 387 259), lower := (rows 19 38 76 168 25 36 64 128 256), losses := [] }

theorem u3682 : Upper (D 5) (R 5) [18,36,72,160,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3682
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3683 : PairBound 9 := { available := 7, camps := [], pairs := [(2,5)], upper := (rows 19 38 76 168 25 288 71 135 263), lower := (rows 19 38 76 168 25 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 65 129 257), good := (rows 471 6 76 136 477 256 64 128 256) }] }

theorem u3683 : Upper (D 5) (R 5) [18,36,72,160,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 168 273 33 78 142 270), lower := (rows 19 38 76 168 273 33 64 128 256), losses := [] }

theorem u3684 : Upper (D 5) (R 5) [18,36,72,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 168 273 34 77 141 269), lower := (rows 19 38 76 168 273 34 64 128 256), losses := [] }

theorem u3685 : Upper (D 5) (R 5) [18,36,72,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3685
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 168 273 36 75 139 267), lower := (rows 19 38 76 168 273 36 64 128 256), losses := [] }

theorem u3686 : Upper (D 5) (R 5) [18,36,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 273, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 168 273 40 71 135 263), lower := (rows 19 38 76 168 273 40 64 128 256), losses := [] }

theorem u3687 : Upper (D 5) (R 5) [18,36,72,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 76 168 276 33 75 139 267), lower := (rows 19 38 76 168 276 33 64 128 256), losses := [] }

theorem u3688 : Upper (D 5) (R 5) [18,36,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3688
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3689 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 168 276 34 73 137 265), lower := (rows 19 38 76 168 276 34 64 128 256), losses := [] }

theorem u3689 : Upper (D 5) (R 5) [18,36,72,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3689
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 273, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 168 276 40 67 131 259), lower := (rows 19 38 76 168 276 40 64 128 256), losses := [] }

theorem u3690 : Upper (D 5) (R 5) [18,36,72,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3691 : Route 9 := (fun mask => (mask,id))

def c3691 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3691 : Upper (D 5) (R 5) [18,36,72,160,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160,264,1] 13 (by decide) (choices 1) [1,2,4] r3691 c3691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1141
  · exact u1142
  · exact u1143

def b3692 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 168 280 34 69 133 261), lower := (rows 19 38 76 168 280 34 64 128 256), losses := [] }

theorem u3692 : Upper (D 5) (R 5) [18,36,72,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 168 280 36 67 131 259), lower := (rows 19 38 76 168 280 36 64 128 256), losses := [] }

theorem u3693 : Upper (D 5) (R 5) [18,36,72,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3693
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 392 25 33 102 166 294), lower := (rows 19 38 76 392 25 33 64 128 256), losses := [] }

theorem u3694 : Upper (D 5) (R 5) [18,36,72,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 76 392 25 34 101 165 293), lower := (rows 19 38 76 392 25 34 64 128 256), losses := [] }

theorem u3695 : Upper (D 5) (R 5) [18,36,72,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 392 25 36 99 163 291), lower := (rows 19 38 76 392 25 36 64 128 256), losses := [] }

theorem u3696 : Upper (D 5) (R 5) [18,36,72,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 41 28 33 330 394 266), lower := (rows 19 38 196 41 28 33 64 128 256), losses := [] }

theorem u3697 : Upper (D 5) (R 5) [18,36,192,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 452, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 196 41 28 34 329 393 265), lower := (rows 19 38 196 41 28 34 64 128 256), losses := [] }

theorem u3698 : Upper (D 5) (R 5) [18,36,192,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 452, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 196 41 28 40 323 387 259), lower := (rows 19 38 196 41 28 40 64 128 256), losses := [] }

theorem u3699 : Upper (D 5) (R 5) [18,36,192,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3699
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 38 196 41 28 288 75 139 267), lower := (rows 19 38 196 41 28 288 64 128 256), losses := [] }

theorem u3700 : Upper (D 5) (R 5) [18,36,192,33,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 41 276 33 74 138 266), lower := (rows 19 38 196 41 276 33 64 128 256), losses := [] }

theorem u3701 : Upper (D 5) (R 5) [18,36,192,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3701
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 196 41 276 34 73 137 265), lower := (rows 19 38 196 41 276 34 64 128 256), losses := [] }

theorem u3702 : Upper (D 5) (R 5) [18,36,192,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 196 41 276 40 75 139 267), lower := (rows 19 38 196 41 276 40 64 128 256), losses := [] }

theorem u3703 : Upper (D 5) (R 5) [18,36,192,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 41 280 33 78 142 270), lower := (rows 19 38 196 41 280 33 64 128 256), losses := [] }

theorem u3704 : Upper (D 5) (R 5) [18,36,192,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 196 41 280 34 77 141 269), lower := (rows 19 38 196 41 280 34 64 128 256), losses := [] }

theorem u3705 : Upper (D 5) (R 5) [18,36,192,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3706 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 196 41 280 36 75 139 267), lower := (rows 19 38 196 41 280 36 64 128 256), losses := [] }

theorem u3706 : Upper (D 5) (R 5) [18,36,192,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 196 41 280 40 71 135 263), lower := (rows 19 38 196 41 280 40 64 128 256), losses := [] }

theorem u3707 : Upper (D 5) (R 5) [18,36,192,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3708 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 196 265 28 33 106 170 298), lower := (rows 19 38 196 265 28 33 64 128 256), losses := [] }

theorem u3708 : Upper (D 5) (R 5) [18,36,192,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 196 265 28 34 105 169 297), lower := (rows 19 38 196 265 28 34 64 128 256), losses := [] }

theorem u3709 : Upper (D 5) (R 5) [18,36,192,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 196 265 28 40 99 163 291), lower := (rows 19 38 196 265 28 40 64 128 256), losses := [] }

theorem u3710 : Upper (D 5) (R 5) [18,36,192,257,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3710
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 196 266 28 33 105 169 297), lower := (rows 19 38 196 266 28 33 64 128 256), losses := [] }

theorem u3711 : Upper (D 5) (R 5) [18,36,192,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3711
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 196 266 28 40 97 161 289), lower := (rows 19 38 196 266 28 40 64 128 256), losses := [] }

theorem u3712 : Upper (D 5) (R 5) [18,36,192,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 268 25 33 106 170 298), lower := (rows 19 38 196 268 25 33 64 128 256), losses := [] }

theorem u3713 : Upper (D 5) (R 5) [18,36,192,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3714 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 196 268 25 34 105 169 297), lower := (rows 19 38 196 268 25 34 64 128 256), losses := [] }

theorem u3714 : Upper (D 5) (R 5) [18,36,192,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3715 : Route 9 := (fun mask => (mask,id))

def c3715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3715 : Upper (D 5) (R 5) [18,36,192,260,9,8] 13 := by
  apply FastRouting.sound _ _ [18,36,192,260,9,8] 13 (by decide) (choices 1) [1,2,32] r3715 c3715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1144
  · exact u1145
  · exact u1146

def b3716 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 296 25 33 78 142 270), lower := (rows 19 38 196 296 25 33 64 128 256), losses := [] }

theorem u3716 : Upper (D 5) (R 5) [18,36,192,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3717 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 196 296 25 34 77 141 269), lower := (rows 19 38 196 296 25 34 64 128 256), losses := [] }

theorem u3717 : Upper (D 5) (R 5) [18,36,192,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3718 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 196 296 25 36 75 139 267), lower := (rows 19 38 196 296 25 36 64 128 256), losses := [] }

theorem u3718 : Upper (D 5) (R 5) [18,36,192,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3719 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 196 296 25 40 71 135 263), lower := (rows 19 38 196 296 25 40 64 128 256), losses := [] }

theorem u3719 : Upper (D 5) (R 5) [18,36,192,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3719
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3719
end Delivery.IrregularNine14.P05
