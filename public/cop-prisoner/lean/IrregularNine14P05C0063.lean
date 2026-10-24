import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0019
import IrregularNine14P05C0020

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3780 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 9 }], pairs := [(2,0),(2,3)], upper := (rows 19 67 38 392 56 36 77 141 269), lower := (rows 19 67 38 392 56 36 64 128 256), losses := [] }

theorem u3780 : Upper (D 5) (R 5) [18,65,34,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3781 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 392 56 40 69 133 261), lower := (rows 19 67 38 392 56 40 64 128 256), losses := [] }

theorem u3781 : Upper (D 5) (R 5) [18,65,34,384,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 276 34 108 172 300), lower := (rows 19 67 44 137 276 34 64 128 256), losses := [] }

theorem u3782 : Upper (D 5) (R 5) [18,65,40,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 137 276 36 106 170 298), lower := (rows 19 67 44 137 276 36 64 128 256), losses := [] }

theorem u3783 : Upper (D 5) (R 5) [18,65,40,129,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 137 276 40 102 166 294), lower := (rows 19 67 44 137 276 40 64 128 256), losses := [] }

theorem u3784 : Upper (D 5) (R 5) [18,65,40,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 280 34 100 164 292), lower := (rows 19 67 44 137 280 34 64 128 256), losses := [] }

theorem u3785 : Upper (D 5) (R 5) [18,65,40,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3786 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 137 280 36 102 166 294), lower := (rows 19 67 44 137 280 36 64 128 256), losses := [] }

theorem u3786 : Upper (D 5) (R 5) [18,65,40,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3787 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 137 304 34 76 140 268), lower := (rows 19 67 44 137 304 34 64 128 256), losses := [] }

theorem u3787 : Upper (D 5) (R 5) [18,65,40,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 137 304 36 78 142 270), lower := (rows 19 67 44 137 304 36 64 128 256), losses := [] }

theorem u3788 : Upper (D 5) (R 5) [18,65,40,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 137 304 40 70 134 262), lower := (rows 19 67 44 137 304 40 64 128 256), losses := [] }

theorem u3789 : Upper (D 5) (R 5) [18,65,40,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3790 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 276 33 108 172 300), lower := (rows 19 67 44 138 276 33 64 128 256), losses := [] }

theorem u3790 : Upper (D 5) (R 5) [18,65,40,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3790
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 138 276 36 105 169 297), lower := (rows 19 67 44 138 276 36 64 128 256), losses := [] }

theorem u3791 : Upper (D 5) (R 5) [18,65,40,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 138 276 40 101 165 293), lower := (rows 19 67 44 138 276 40 64 128 256), losses := [] }

theorem u3792 : Upper (D 5) (R 5) [18,65,40,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3792
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 280 33 100 164 292), lower := (rows 19 67 44 138 280 33 64 128 256), losses := [] }

theorem u3793 : Upper (D 5) (R 5) [18,65,40,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3794 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 138 280 36 101 165 293), lower := (rows 19 67 44 138 280 36 64 128 256), losses := [] }

theorem u3794 : Upper (D 5) (R 5) [18,65,40,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3794
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3795 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 44 138 304 33 76 140 268), lower := (rows 19 67 44 138 304 33 64 128 256), losses := [] }

theorem u3795 : Upper (D 5) (R 5) [18,65,40,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3795
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3796 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 138 304 36 77 141 269), lower := (rows 19 67 44 138 304 36 64 128 256), losses := [] }

theorem u3796 : Upper (D 5) (R 5) [18,65,40,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3797 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 339, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 138 304 40 69 133 261), lower := (rows 19 67 44 138 304 40 64 128 256), losses := [] }

theorem u3797 : Upper (D 5) (R 5) [18,65,40,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3798 : Route 9 := (fun mask => (mask,id))

def c3798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3798 : Upper (D 5) (R 5) [18,65,40,132,260,1] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,260,1] 13 (by decide) (choices 1) [2,8,32] r3798 c3798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1175
  · exact u1176
  · exact u1177

def r3799 : Route 9 := (fun mask => (mask,id))

def c3799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3799 : Upper (D 5) (R 5) [18,65,40,132,260,2] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,260,2] 13 (by decide) (choices 1) [1,8,32] r3799 c3799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1178
  · exact u1179
  · exact u1180

def b3800 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 276 40 99 163 291), lower := (rows 19 67 44 140 276 40 64 128 256), losses := [] }

theorem u3800 : Upper (D 5) (R 5) [18,65,40,132,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3801 : Route 9 := (fun mask => (mask,id))

def c3801 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3801 : Upper (D 5) (R 5) [18,65,40,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,264,1] 13 (by decide) (choices 1) [2,4,32] r3801 c3801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1181
  · exact u1182
  · exact u1183

def r3802 : Route 9 := (fun mask => (mask,id))

def c3802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3802 : Upper (D 5) (R 5) [18,65,40,132,264,2] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,264,2] 13 (by decide) (choices 1) [1,4,32] r3802 c3802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1184
  · exact u1185
  · exact u1186

def b3803 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 280 36 99 163 291), lower := (rows 19 67 44 140 280 36 64 128 256), losses := [] }

theorem u3803 : Upper (D 5) (R 5) [18,65,40,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 14, camps := [], pairs := [(2,0),(3,0)], upper := (rows 19 67 44 140 304 33 78 142 270), lower := (rows 19 67 44 140 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 41 48 32 65 129 257), good := (rows 478 458 60 140 316 508 64 128 256) }] }

theorem u3804 : Upper (D 5) (R 5) [18,65,40,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3805 : Route 9 := (fun mask => (mask,id))

def c3805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3805 : Upper (D 5) (R 5) [18,65,40,132,288,2] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,288,2] 13 (by decide) (choices 1) [1,4,8] r3805 c3805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1187
  · exact u1188
  · exact u1189

def b3806 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 304 36 75 139 267), lower := (rows 19 67 44 140 304 36 64 128 256), losses := [] }

theorem u3806 : Upper (D 5) (R 5) [18,65,40,132,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 304 40 71 135 263), lower := (rows 19 67 44 140 304 40 64 128 256), losses := [] }

theorem u3807 : Upper (D 5) (R 5) [18,65,40,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 266 52 36 104 168 296), lower := (rows 19 67 133 266 52 36 64 128 256), losses := [] }

theorem u3808 : Upper (D 5) (R 5) [18,65,129,258,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3809 : Route 9 := (fun mask => (mask,id))

def c3809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3809 : Upper (D 5) (R 5) [18,65,129,258,36,8] 13 := by
  apply FastRouting.sound _ _ [18,65,129,258,36,8] 13 (by decide) (choices 1) [4,8,32] r3809 c3809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1190
  · exact u1191
  · exact u1192

def r3810 : Route 9 := (fun mask => (mask,id))

def c3810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3810 : Upper (D 5) (R 5) [18,65,129,258,40,4] 13 := by
  apply FastRouting.sound _ _ [18,65,129,258,40,4] 13 (by decide) (choices 1) [4,8,32] r3810 c3810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1193
  · exact u1194
  · exact u1195

def b3811 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 133 266 56 40 100 164 292), lower := (rows 19 67 133 266 56 40 64 128 256), losses := [] }

theorem u3811 : Upper (D 5) (R 5) [18,65,129,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3812 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 133 268 52 34 104 168 296), lower := (rows 19 67 133 268 52 34 64 128 256), losses := [] }

theorem u3812 : Upper (D 5) (R 5) [18,65,129,260,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 268 52 40 106 170 298), lower := (rows 19 67 133 268 52 40 64 128 256), losses := [] }

theorem u3813 : Upper (D 5) (R 5) [18,65,129,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3814 : PairBound 9 := { available := 44, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 133 268 56 34 108 172 300), lower := (rows 19 67 133 268 56 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 68 132 260), good := (rows 50 98 508 476 56 34 64 128 256) }] }

theorem u3814 : Upper (D 5) (R 5) [18,65,129,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 268 56 36 106 170 298), lower := (rows 19 67 133 268 56 36 64 128 256), losses := [] }

theorem u3815 : Upper (D 5) (R 5) [18,65,129,260,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 268 56 40 102 166 294), lower := (rows 19 67 133 268 56 40 64 128 256), losses := [] }

theorem u3816 : Upper (D 5) (R 5) [18,65,129,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3817 : PairBound 9 := { available := 44, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 133 296 28 34 108 172 300), lower := (rows 19 67 133 296 28 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 68 132 260), good := (rows 50 98 508 296 476 34 64 128 256) }] }

theorem u3817 : Upper (D 5) (R 5) [18,65,129,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 42, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 133 296 28 36 106 170 298), lower := (rows 19 67 133 296 28 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 13 52 52 65 129 257), good := (rows 506 458 508 312 60 60 64 128 256) }] }

theorem u3818 : Upper (D 5) (R 5) [18,65,129,288,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3819 : PairBound 9 := { available := 38, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 133 296 28 40 102 166 294), lower := (rows 19 67 133 296 28 40 64 128 256), losses := [] }

theorem u3819 : Upper (D 5) (R 5) [18,65,129,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3820 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 133 296 52 34 76 140 268), lower := (rows 19 67 133 296 52 34 64 128 256), losses := [] }

theorem u3820 : Upper (D 5) (R 5) [18,65,129,288,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 133 296 52 36 74 138 266), lower := (rows 19 67 133 296 52 36 64 128 256), losses := [] }

theorem u3821 : Upper (D 5) (R 5) [18,65,129,288,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 133 296 52 40 78 142 270), lower := (rows 19 67 133 296 52 40 64 128 256), losses := [] }

theorem u3822 : Upper (D 5) (R 5) [18,65,129,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 67 134 268 52 33 104 168 296), lower := (rows 19 67 134 268 52 33 64 128 256), losses := [] }

theorem u3823 : Upper (D 5) (R 5) [18,65,130,260,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 134 268 52 40 105 169 297), lower := (rows 19 67 134 268 52 40 64 128 256), losses := [] }

theorem u3824 : Upper (D 5) (R 5) [18,65,130,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3825 : PairBound 9 := { available := 44, camps := [], pairs := [(3,1),(4,1)], upper := (rows 19 67 134 268 56 33 108 172 300), lower := (rows 19 67 134 268 56 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 68 132 260), good := (rows 49 97 508 476 56 33 64 128 256) }] }

theorem u3825 : Upper (D 5) (R 5) [18,65,130,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3826 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 134 268 56 36 105 169 297), lower := (rows 19 67 134 268 56 36 64 128 256), losses := [] }

theorem u3826 : Upper (D 5) (R 5) [18,65,130,260,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3827 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 134 268 56 40 101 165 293), lower := (rows 19 67 134 268 56 40 64 128 256), losses := [] }

theorem u3827 : Upper (D 5) (R 5) [18,65,130,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3827
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3828 : PairBound 9 := { available := 44, camps := [], pairs := [(3,1),(4,1)], upper := (rows 19 67 134 296 28 33 108 172 300), lower := (rows 19 67 134 296 28 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 35 68 132 260), good := (rows 49 97 508 296 476 33 64 128 256) }] }

theorem u3828 : Upper (D 5) (R 5) [18,65,130,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3829 : Route 9 := (fun mask => (mask,id))

def c3829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3829 : Upper (D 5) (R 5) [18,65,130,288,12,4] 13 := by
  apply FastRouting.sound _ _ [18,65,130,288,12,4] 13 (by decide) (choices 1) [1,8,32] r3829 c3829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1196
  · exact u1197
  · exact u1198

def b3830 : PairBound 9 := { available := 37, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 134 296 28 40 101 165 293), lower := (rows 19 67 134 296 28 40 64 128 256), losses := [] }

theorem u3830 : Upper (D 5) (R 5) [18,65,130,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 67 134 296 52 33 76 140 268), lower := (rows 19 67 134 296 52 33 64 128 256), losses := [] }

theorem u3831 : Upper (D 5) (R 5) [18,65,130,288,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 67 134 296 52 36 73 137 265), lower := (rows 19 67 134 296 52 36 64 128 256), losses := [] }

theorem u3832 : Upper (D 5) (R 5) [18,65,130,288,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 134 296 52 40 77 141 269), lower := (rows 19 67 134 296 52 40 64 128 256), losses := [] }

theorem u3833 : Upper (D 5) (R 5) [18,65,130,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3834 : Route 9 := (fun mask => (mask,id))

def c3834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3834 : Upper (D 5) (R 5) [18,65,136,260,36,1] 13 := by
  apply FastRouting.sound _ _ [18,65,136,260,36,1] 13 (by decide) (choices 1) [2,8,32] r3834 c3834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1199
  · exact u1200
  · exact u1201

def r3835 : Route 9 := (fun mask => (mask,id))

def c3835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3835 : Upper (D 5) (R 5) [18,65,136,260,36,2] 13 := by
  apply FastRouting.sound _ _ [18,65,136,260,36,2] 13 (by decide) (choices 1) [1,8,32] r3835 c3835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1202
  · exact u1203
  · exact u1204

def b3836 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 140 268 52 40 99 163 291), lower := (rows 19 67 140 268 52 40 64 128 256), losses := [] }

theorem u3836 : Upper (D 5) (R 5) [18,65,136,260,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3837 : Route 9 := (fun mask => (mask,id))

def c3837 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3837 : Upper (D 5) (R 5) [18,65,136,288,36,1] 13 := by
  apply FastRouting.sound _ _ [18,65,136,288,36,1] 13 (by decide) (choices 1) [2,4,8] r3837 c3837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1205
  · exact u1206
  · exact u1207

def r3838 : Route 9 := (fun mask => (mask,id))

def c3838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3838 : Upper (D 5) (R 5) [18,65,136,288,36,2] 13 := by
  apply FastRouting.sound _ _ [18,65,136,288,36,2] 13 (by decide) (choices 1) [1,4,8] r3838 c3838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1208
  · exact u1209
  · exact u1210

def b3839 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 140 296 52 36 75 139 267), lower := (rows 19 67 140 296 52 36 64 128 256), losses := [] }

theorem u3839 : Upper (D 5) (R 5) [18,65,136,288,36,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3839
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3839
end Delivery.IrregularNine14.P05
