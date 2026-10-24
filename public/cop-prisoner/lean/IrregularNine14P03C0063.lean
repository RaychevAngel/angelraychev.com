import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0025
import IrregularNine14P03C0026

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3780 : Route 9 := (fun mask => (mask,id))

def c3780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3780 : Upper (D 3) (R 3) [34,257,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,160,192] 13 (by decide) (choices 1) [1,4,8,16] r3780 c3780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1515
  · exact u1516
  · exact u1517
  · exact u1518

def b3781 : PairBound 9 := { available := 145, camps := [{ cop := 6, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 76 176 177 209 145 401), lower := (rows 35 259 76 76 176 32 64 128 256), losses := [] }

theorem u3781 : Upper (D 3) (R 3) [34,257,72,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3781
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 88 148 161 225 161 417), lower := (rows 35 259 76 88 148 32 64 128 256), losses := [] }

theorem u3782 : Upper (D 3) (R 3) [34,257,72,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3782
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 88 176 165 197 133 389), lower := (rows 35 259 76 88 176 32 64 128 256), losses := [] }

theorem u3783 : Upper (D 3) (R 3) [34,257,72,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 104 148 177 209 145 401), lower := (rows 35 259 76 104 148 32 64 128 256), losses := [] }

theorem u3784 : Upper (D 3) (R 3) [34,257,72,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 140 112 177 209 145 401), lower := (rows 35 259 76 140 112 32 64 128 256), losses := [] }

theorem u3785 : Upper (D 3) (R 3) [34,257,72,132,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3786 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 140 208 49 113 177 305), lower := (rows 35 259 76 140 208 32 64 128 256), losses := [] }

theorem u3786 : Upper (D 3) (R 3) [34,257,72,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3787 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 152 112 165 197 133 389), lower := (rows 35 259 76 152 112 32 64 128 256), losses := [] }

theorem u3787 : Upper (D 3) (R 3) [34,257,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3787
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 76 152 208 37 101 165 293), lower := (rows 35 259 76 152 208 32 64 128 256), losses := [] }

theorem u3788 : Upper (D 3) (R 3) [34,257,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3789 : Route 9 := (fun mask => (mask,id))

def c3789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3789 : Upper (D 3) (R 3) [34,257,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,72,160,192] 13 (by decide) (choices 1) [1,4,16] r3789 c3789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1519
  · exact u1520
  · exact u1521

def b3790 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 200 176 53 85 149 277), lower := (rows 35 259 76 200 176 32 64 128 256), losses := [] }

theorem u3790 : Upper (D 3) (R 3) [34,257,72,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 13 88 49 225 193 193 449), lower := (rows 35 262 13 88 49 32 64 128 256), losses := [] }

theorem u3791 : Upper (D 3) (R 3) [34,260,9,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3791
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 13 88 81 161 225 161 417), lower := (rows 35 262 13 88 81 32 64 128 256), losses := [] }

theorem u3792 : Upper (D 3) (R 3) [34,260,9,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3792
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 88 112 161 193 129 385), lower := (rows 35 262 13 88 112 32 64 128 256), losses := [] }

theorem u3793 : Upper (D 3) (R 3) [34,260,9,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3793
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3794 : Route 9 := (fun mask => (mask,id))

def c3794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3794 : Upper (D 3) (R 3) [34,260,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,9,80,129] 13 (by decide) (choices 1) [1,64,128] r3794 c3794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1522
  · exact u1523
  · exact u1524

def b3795 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 13 88 176 225 193 193 449), lower := (rows 35 262 13 88 176 32 64 128 256), losses := [] }

theorem u3795 : Upper (D 3) (R 3) [34,260,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3795
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3796 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 13 88 208 161 225 161 417), lower := (rows 35 262 13 88 208 32 64 128 256), losses := [] }

theorem u3796 : Upper (D 3) (R 3) [34,260,9,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3797 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 13 200 49 241 209 209 465), lower := (rows 35 262 13 200 49 32 64 128 256), losses := [] }

theorem u3797 : Upper (D 3) (R 3) [34,260,9,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3797
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3798 : Route 9 := (fun mask => (mask,id))

def c3798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3798 : Upper (D 3) (R 3) [34,260,9,192,65] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,65] 13 (by decide) (choices 1) [1,16,128] r3798 c3798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1525
  · exact u1526
  · exact u1527

def r3799 : Route 9 := (fun mask => (mask,id))

def c3799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3799 : Upper (D 3) (R 3) [34,260,9,192,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,192,96] 13 (by decide) (choices 1) [1,16,128] r3799 c3799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1528
  · exact u1529
  · exact u1530

def b3800 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 13 200 208 49 113 177 305), lower := (rows 35 262 13 200 208 32 64 128 256), losses := [] }

theorem u3800 : Upper (D 3) (R 3) [34,260,9,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3800
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 28 41 81 225 193 193 449), lower := (rows 35 262 28 41 81 32 64 128 256), losses := [] }

theorem u3801 : Upper (D 3) (R 3) [34,260,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 28 41 208 225 193 193 449), lower := (rows 35 262 28 41 208 32 64 128 256), losses := [] }

theorem u3802 : Upper (D 3) (R 3) [34,260,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3803 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 28 73 81 161 225 161 417), lower := (rows 35 262 28 73 81 32 64 128 256), losses := [] }

theorem u3803 : Upper (D 3) (R 3) [34,260,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3803
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 112 161 193 129 385), lower := (rows 35 262 28 73 112 32 64 128 256), losses := [] }

theorem u3804 : Upper (D 3) (R 3) [34,260,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3804
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m3805_128 : Upper (D 3) (R 3) [34,260,24,65,129,128] 13 :=
  permutation_upper _ _ _ [34,260,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1532

def r3805 : Route 9 := (fun mask => (mask,id))

def c3805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3805 : Upper (D 3) (R 3) [34,260,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,129] 13 (by decide) (choices 1) [1,64,128] r3805 c3805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1531
  · exact u1532
  · exact m3805_128

def b3806 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 28 73 176 225 193 193 449), lower := (rows 35 262 28 73 176 32 64 128 256), losses := [] }

theorem u3806 : Upper (D 3) (R 3) [34,260,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3806
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 73 208 161 225 161 417), lower := (rows 35 262 28 73 208 32 64 128 256), losses := [] }

theorem u3807 : Upper (D 3) (R 3) [34,260,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 28 104 208 161 193 129 385), lower := (rows 35 262 28 104 208 32 64 128 256), losses := [] }

theorem u3808 : Upper (D 3) (R 3) [34,260,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 28 200 208 33 97 161 289), lower := (rows 35 262 28 200 208 32 64 128 256), losses := [] }

theorem u3809 : Upper (D 3) (R 3) [34,260,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3809
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 25 25 224 224 224 480), lower := (rows 35 262 69 25 25 32 64 128 256), losses := [] }

theorem u3810 : Upper (D 3) (R 3) [34,260,65,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3811 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 25 49 232 200 200 456), lower := (rows 35 262 69 25 49 32 64 128 256), losses := [] }

theorem u3811 : Upper (D 3) (R 3) [34,260,65,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3811
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3812 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 25 56 225 193 193 449), lower := (rows 35 262 69 25 56 32 64 128 256), losses := [] }

theorem u3812 : Upper (D 3) (R 3) [34,260,65,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 25 81 168 232 168 424), lower := (rows 35 262 69 25 81 32 64 128 256), losses := [] }

theorem u3813 : Upper (D 3) (R 3) [34,260,65,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3813
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3814 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 25 88 161 225 161 417), lower := (rows 35 262 69 25 88 32 64 128 256), losses := [] }

theorem u3814 : Upper (D 3) (R 3) [34,260,65,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3814
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 25 112 169 201 137 393), lower := (rows 35 262 69 25 112 32 64 128 256), losses := [] }

theorem u3815 : Upper (D 3) (R 3) [34,260,65,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3815
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 25 145 232 232 232 488), lower := (rows 35 262 69 25 145 32 64 128 256), losses := [] }

theorem u3816 : Upper (D 3) (R 3) [34,260,65,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3817 : Route 9 := (fun mask => (mask,id))

def c3817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3817 : Upper (D 3) (R 3) [34,260,65,17,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,136] 13 (by decide) (choices 1) [1,64,128] r3817 c3817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1533
  · exact u1534
  · exact u1535

def b3818 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 25 176 233 201 201 457), lower := (rows 35 262 69 25 176 32 64 128 256), losses := [] }

theorem u3818 : Upper (D 3) (R 3) [34,260,65,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3819 : Route 9 := (fun mask => (mask,id))

def c3819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3819 : Upper (D 3) (R 3) [34,260,65,17,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,17,192] 13 (by decide) (choices 1) [1,8,128] r3819 c3819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1536
  · exact u1537
  · exact u1538

def b3820 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 41 88 177 209 145 401), lower := (rows 35 262 69 41 88 32 64 128 256), losses := [] }

theorem u3820 : Upper (D 3) (R 3) [34,260,65,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 41 145 248 216 216 472), lower := (rows 35 262 69 41 145 32 64 128 256), losses := [] }

theorem u3821 : Upper (D 3) (R 3) [34,260,65,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 41 152 241 209 209 465), lower := (rows 35 262 69 41 152 32 64 128 256), losses := [] }

theorem u3822 : Upper (D 3) (R 3) [34,260,65,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3822
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 41 208 185 217 153 409), lower := (rows 35 262 69 41 208 32 64 128 256), losses := [] }

theorem u3823 : Upper (D 3) (R 3) [34,260,65,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 69 56 81 169 201 137 393), lower := (rows 35 262 69 56 81 32 64 128 256), losses := [] }

theorem u3824 : Upper (D 3) (R 3) [34,260,65,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3824
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3825 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 56 88 161 193 129 385), lower := (rows 35 262 69 56 88 32 64 128 256), losses := [] }

theorem u3825 : Upper (D 3) (R 3) [34,260,65,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3825
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3826 : Route 9 := (fun mask => (mask,id))

def c3826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3826 : Upper (D 3) (R 3) [34,260,65,48,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,129] 13 (by decide) (choices 1) [1,8,64,128] r3826 c3826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1539
  · exact u1540
  · exact u1541
  · exact u1542

def b3827 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 56 152 225 193 193 449), lower := (rows 35 262 69 56 152 32 64 128 256), losses := [] }

theorem u3827 : Upper (D 3) (R 3) [34,260,65,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3827
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3828 : Route 9 := (fun mask => (mask,id))

def c3828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3828 : Upper (D 3) (R 3) [34,260,65,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,192] 13 (by decide) (choices 1) [1,8,128] r3828 c3828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1543
  · exact u1544
  · exact u1545

def b3829 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 145 184 248 184 440), lower := (rows 35 262 69 73 145 32 64 128 256), losses := [] }

theorem u3829 : Upper (D 3) (R 3) [34,260,65,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3829
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3830 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 152 177 241 177 433), lower := (rows 35 262 69 73 152 32 64 128 256), losses := [] }

theorem u3830 : Upper (D 3) (R 3) [34,260,65,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3830
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 262 69 73 176 185 217 153 409), lower := (rows 35 262 69 73 176 32 64 128 256), losses := [] }

theorem u3831 : Upper (D 3) (R 3) [34,260,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3831
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3832 : Route 9 := (fun mask => (mask,id))

def c3832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3832 : Upper (D 3) (R 3) [34,260,65,80,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,129] 13 (by decide) (choices 1) [1,8,128] r3832 c3832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1546
  · exact u1547
  · exact u1548

def b3833 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 88 152 161 225 161 417), lower := (rows 35 262 69 88 152 32 64 128 256), losses := [] }

theorem u3833 : Upper (D 3) (R 3) [34,260,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3833
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3834 : Route 9 := (fun mask => (mask,id))

def c3834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3834 : Upper (D 3) (R 3) [34,260,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,160] 13 (by decide) (choices 1) [1,8,128] r3834 c3834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1549
  · exact u1550
  · exact u1551

def r3835 : Route 9 := (fun mask => (mask,id))

def c3835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3835 : Upper (D 3) (R 3) [34,260,65,96,129] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,129] 13 (by decide) (choices 1) [1,8,16,128] r3835 c3835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1552
  · exact u1553
  · exact u1554
  · exact u1555

def r3836 : Route 9 := (fun mask => (mask,id))

def c3836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3836 : Upper (D 3) (R 3) [34,260,65,96,136] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136] 13 (by decide) (choices 1) [1,16,128] r3836 c3836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1556
  · exact u1557
  · exact u1558

def b3837 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 262 69 137 145 120 120 248 376), lower := (rows 35 262 69 137 145 32 64 128 256), losses := [] }

theorem u3837 : Upper (D 3) (R 3) [34,260,65,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3837
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3838 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 262 69 137 152 113 113 241 369), lower := (rows 35 262 69 137 152 32 64 128 256), losses := [] }

theorem u3838 : Upper (D 3) (R 3) [34,260,65,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3838
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3839 : Route 9 := (fun mask => (mask,id))

def c3839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3839 : Upper (D 3) (R 3) [34,260,65,129,160] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,160] 13 (by decide) (choices 1) [1,8,16,64] r3839 c3839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1559
  · exact u1560
  · exact u1561
  · exact u1562

#print axioms u3839
end Delivery.IrregularNine14.P03
