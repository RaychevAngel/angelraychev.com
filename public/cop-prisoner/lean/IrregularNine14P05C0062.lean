import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0019

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 196 296 28 33 75 139 267), lower := (rows 19 38 196 296 28 33 64 128 256), losses := [] }

theorem u3720 : Upper (D 5) (R 5) [18,36,192,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 196 296 28 34 73 137 265), lower := (rows 19 38 196 296 28 34 64 128 256), losses := [] }

theorem u3721 : Upper (D 5) (R 5) [18,36,192,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3721
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 196 296 28 40 67 131 259), lower := (rows 19 38 196 296 28 40 64 128 256), losses := [] }

theorem u3722 : Upper (D 5) (R 5) [18,36,192,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 42 148 36 328 392 264), lower := (rows 19 67 37 42 148 36 64 128 256), losses := [] }

theorem u3723 : Upper (D 5) (R 5) [18,65,33,34,132,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 67 37 42 148 40 332 396 268), lower := (rows 19 67 37 42 148 40 64 128 256), losses := [] }

theorem u3724 : Upper (D 5) (R 5) [18,65,33,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 12, camps := [], pairs := [(3,0)], upper := (rows 19 67 37 42 148 288 76 140 268), lower := (rows 19 67 37 42 148 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 308 68 132 260), good := (rows 58 74 508 42 500 288 64 128 288) }] }

theorem u3725 : Upper (D 5) (R 5) [18,65,33,34,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3726 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 42 152 36 332 396 268), lower := (rows 19 67 37 42 152 36 64 128 256), losses := [] }

theorem u3726 : Upper (D 5) (R 5) [18,65,33,34,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 67 37 42 152 40 324 388 260), lower := (rows 19 67 37 42 152 40 64 128 256), losses := [] }

theorem u3727 : Upper (D 5) (R 5) [18,65,33,34,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3728 : Route 9 := (fun mask => (mask,id))

def c3728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3728 : Upper (D 5) (R 5) [18,65,33,34,136,256] 13 := by
  apply FastRouting.sound _ _ [18,65,33,34,136,256] 13 (by decide) (choices 1) [4,8] r3728 c3728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1147
  · exact u1148

def b3729 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 42 400 36 76 140 268), lower := (rows 19 67 37 42 400 36 64 128 256), losses := [] }

theorem u3729 : Upper (D 5) (R 5) [18,65,33,34,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3730 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 67 37 42 400 40 76 140 268), lower := (rows 19 67 37 42 400 40 64 128 256), losses := [] }

theorem u3730 : Upper (D 5) (R 5) [18,65,33,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3731 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 138 276 36 104 168 296), lower := (rows 19 67 37 138 276 36 64 128 256), losses := [] }

theorem u3731 : Upper (D 5) (R 5) [18,65,33,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3732 : Route 9 := (fun mask => (mask,id))

def c3732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3732 : Upper (D 5) (R 5) [18,65,33,130,260,8] 13 := by
  apply FastRouting.sound _ _ [18,65,33,130,260,8] 13 (by decide) (choices 1) [4,8,32] r3732 c3732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1149
  · exact u1150
  · exact u1151

def b3733 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 138 280 36 108 172 300), lower := (rows 19 67 37 138 280 36 64 128 256), losses := [] }

theorem u3733 : Upper (D 5) (R 5) [18,65,33,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 67 37 138 280 40 100 164 292), lower := (rows 19 67 37 138 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 69 133 261), good := (rows 501 453 485 168 312 40 64 128 256) }] }

theorem u3734 : Upper (D 5) (R 5) [18,65,33,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 140 276 34 104 168 296), lower := (rows 19 67 37 140 276 34 64 128 256), losses := [] }

theorem u3735 : Upper (D 5) (R 5) [18,65,33,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3736 : Route 9 := (fun mask => (mask,id))

def c3736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3736 : Upper (D 5) (R 5) [18,65,33,132,260,8] 13 := by
  apply FastRouting.sound _ _ [18,65,33,132,260,8] 13 (by decide) (choices 1) [2,8,32] r3736 c3736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1152
  · exact u1153
  · exact u1154

def b3737 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 140 280 34 108 172 300), lower := (rows 19 67 37 140 280 34 64 128 256), losses := [] }

theorem u3737 : Upper (D 5) (R 5) [18,65,33,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 140 280 36 106 170 298), lower := (rows 19 67 37 140 280 36 64 128 256), losses := [] }

theorem u3738 : Upper (D 5) (R 5) [18,65,33,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3739 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 67 37 140 280 40 102 166 294), lower := (rows 19 67 37 140 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 64 128 256), good := (rows 53 69 37 172 312 40 64 128 256) }] }

theorem u3739 : Upper (D 5) (R 5) [18,65,33,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3740 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 168 276 34 76 140 268), lower := (rows 19 67 37 168 276 34 64 128 256), losses := [] }

theorem u3740 : Upper (D 5) (R 5) [18,65,33,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3741 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 168 276 36 74 138 266), lower := (rows 19 67 37 168 276 36 64 128 256), losses := [] }

theorem u3741 : Upper (D 5) (R 5) [18,65,33,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3742 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 168 276 40 78 142 270), lower := (rows 19 67 37 168 276 40 64 128 256), losses := [] }

theorem u3742 : Upper (D 5) (R 5) [18,65,33,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 168 280 34 76 140 268), lower := (rows 19 67 37 168 280 34 64 128 256), losses := [] }

theorem u3743 : Upper (D 5) (R 5) [18,65,33,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3744 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 168 280 36 78 142 270), lower := (rows 19 67 37 168 280 36 64 128 256), losses := [] }

theorem u3744 : Upper (D 5) (R 5) [18,65,33,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3745 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 168 280 40 70 134 262), lower := (rows 19 67 37 168 280 40 64 128 256), losses := [] }

theorem u3745 : Upper (D 5) (R 5) [18,65,33,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3746 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 37 392 28 34 108 172 300), lower := (rows 19 67 37 392 28 34 64 128 256), losses := [] }

theorem u3746 : Upper (D 5) (R 5) [18,65,33,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3747 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 67 37 392 28 36 106 170 298), lower := (rows 19 67 37 392 28 36 64 128 256), losses := [] }

theorem u3747 : Upper (D 5) (R 5) [18,65,33,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3748 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 67 37 392 28 40 102 166 294), lower := (rows 19 67 37 392 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 64 128 256), good := (rows 53 69 37 424 60 40 64 128 256) }] }

theorem u3748 : Upper (D 5) (R 5) [18,65,33,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3749 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 137 56 36 332 396 268), lower := (rows 19 67 38 137 56 36 64 128 256), losses := [] }

theorem u3749 : Upper (D 5) (R 5) [18,65,34,129,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3750 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 137 56 40 324 388 260), lower := (rows 19 67 38 137 56 40 64 128 256), losses := [] }

theorem u3750 : Upper (D 5) (R 5) [18,65,34,129,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3751 : PairBound 9 := { available := 12, camps := [], pairs := [(2,0)], upper := (rows 19 67 38 137 56 288 76 140 268), lower := (rows 19 67 38 137 56 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 312 72 136 264), good := (rows 54 70 38 508 504 288 64 128 288) }] }

theorem u3751 : Upper (D 5) (R 5) [18,65,34,129,40,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 137 276 36 104 168 296), lower := (rows 19 67 38 137 276 36 64 128 256), losses := [] }

theorem u3752 : Upper (D 5) (R 5) [18,65,34,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3753 : Route 9 := (fun mask => (mask,id))

def c3753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3753 : Upper (D 5) (R 5) [18,65,34,129,260,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,260,8] 13 (by decide) (choices 1) [4,8,32] r3753 c3753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1155
  · exact u1156
  · exact u1157

def b3754 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 137 280 36 108 172 300), lower := (rows 19 67 38 137 280 36 64 128 256), losses := [] }

theorem u3754 : Upper (D 5) (R 5) [18,65,34,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(4,0)], upper := (rows 19 67 38 137 280 40 100 164 292), lower := (rows 19 67 38 137 280 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 56 56 77 141 269), good := (rows 502 454 502 508 504 504 64 128 256) }] }

theorem u3755 : Upper (D 5) (R 5) [18,65,34,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 137 304 36 76 140 268), lower := (rows 19 67 38 137 304 36 64 128 256), losses := [] }

theorem u3756 : Upper (D 5) (R 5) [18,65,34,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3757 : Route 9 := (fun mask => (mask,id))

def c3757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3757 : Upper (D 5) (R 5) [18,65,34,129,288,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129,288,8] 13 (by decide) (choices 1) [4,8] r3757 c3757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1158
  · exact u1159

def b3758 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 56 33 332 396 268), lower := (rows 19 67 38 140 56 33 64 128 256), losses := [] }

theorem u3758 : Upper (D 5) (R 5) [18,65,34,132,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3759 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 323, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 67 38 140 56 36 329 393 265), lower := (rows 19 67 38 140 56 36 64 128 256), losses := [] }

theorem u3759 : Upper (D 5) (R 5) [18,65,34,132,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3759
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 140 56 40 325 389 261), lower := (rows 19 67 38 140 56 40 64 128 256), losses := [] }

theorem u3760 : Upper (D 5) (R 5) [18,65,34,132,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3761 : Route 9 := (fun mask => (mask,id))

def c3761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3761 : Upper (D 5) (R 5) [18,65,34,132,40,256] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,40,256] 13 (by decide) (choices 1) [1,4,8] r3761 c3761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162

def b3762 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 276 33 104 168 296), lower := (rows 19 67 38 140 276 33 64 128 256), losses := [] }

theorem u3762 : Upper (D 5) (R 5) [18,65,34,132,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3763 : Route 9 := (fun mask => (mask,id))

def c3763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3763 : Upper (D 5) (R 5) [18,65,34,132,260,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,260,8] 13 (by decide) (choices 1) [1,8,32] r3763 c3763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165

def b3764 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 280 33 108 172 300), lower := (rows 19 67 38 140 280 33 64 128 256), losses := [] }

theorem u3764 : Upper (D 5) (R 5) [18,65,34,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 140 280 36 105 169 297), lower := (rows 19 67 38 140 280 36 64 128 256), losses := [] }

theorem u3765 : Upper (D 5) (R 5) [18,65,34,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3766 : Route 9 := (fun mask => (mask,id))

def c3766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3766 : Upper (D 5) (R 5) [18,65,34,132,264,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,264,8] 13 (by decide) (choices 1) [1,4,32] r3766 c3766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1166
  · exact u1167
  · exact u1168

def b3767 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 304 33 76 140 268), lower := (rows 19 67 38 140 304 33 64 128 256), losses := [] }

theorem u3767 : Upper (D 5) (R 5) [18,65,34,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3768 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 140 304 36 73 137 265), lower := (rows 19 67 38 140 304 36 64 128 256), losses := [] }

theorem u3768 : Upper (D 5) (R 5) [18,65,34,132,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3769 : Route 9 := (fun mask => (mask,id))

def c3769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3769 : Upper (D 5) (R 5) [18,65,34,132,288,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132,288,8] 13 (by decide) (choices 1) [1,4,8] r3769 c3769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1169
  · exact u1170
  · exact u1171

def b3770 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 168 276 33 76 140 268), lower := (rows 19 67 38 168 276 33 64 128 256), losses := [] }

theorem u3770 : Upper (D 5) (R 5) [18,65,34,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3771 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 168 276 36 73 137 265), lower := (rows 19 67 38 168 276 36 64 128 256), losses := [] }

theorem u3771 : Upper (D 5) (R 5) [18,65,34,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3771
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3772 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 168 276 40 77 141 269), lower := (rows 19 67 38 168 276 40 64 128 256), losses := [] }

theorem u3772 : Upper (D 5) (R 5) [18,65,34,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3773 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 168 280 33 76 140 268), lower := (rows 19 67 38 168 280 33 64 128 256), losses := [] }

theorem u3773 : Upper (D 5) (R 5) [18,65,34,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3774 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 168 280 36 77 141 269), lower := (rows 19 67 38 168 280 36 64 128 256), losses := [] }

theorem u3774 : Upper (D 5) (R 5) [18,65,34,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3775 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 168 280 40 69 133 261), lower := (rows 19 67 38 168 280 40 64 128 256), losses := [] }

theorem u3775 : Upper (D 5) (R 5) [18,65,34,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3776 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 392 28 33 108 172 300), lower := (rows 19 67 38 392 28 33 64 128 256), losses := [] }

theorem u3776 : Upper (D 5) (R 5) [18,65,34,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3777 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 392 28 36 105 169 297), lower := (rows 19 67 38 392 28 36 64 128 256), losses := [] }

theorem u3777 : Upper (D 5) (R 5) [18,65,34,384,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3778 : Route 9 := (fun mask => (mask,id))

def c3778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3778 : Upper (D 5) (R 5) [18,65,34,384,12,8] 13 := by
  apply FastRouting.sound _ _ [18,65,34,384,12,8] 13 (by decide) (choices 1) [1,4,32] r3778 c3778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1172
  · exact u1173
  · exact u1174

def b3779 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 392 56 33 76 140 268), lower := (rows 19 67 38 392 56 33 64 128 256), losses := [] }

theorem u3779 : Upper (D 5) (R 5) [18,65,34,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3779
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P05
