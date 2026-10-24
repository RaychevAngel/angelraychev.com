import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0016
import IrregularNine14P01C0017

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3780 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 53 322 196 138 17 58 122 186 314), lower := (rows 53 322 196 138 17 32 64 128 256), losses := [] }

theorem u3780 : Upper (D 1) (R 1) [52,320,192,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3780
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3781_1 : Upper (D 1) (R 1) [52,320,192,130,2,1] 13 :=
  permutation_upper _ _ _ [52,320,192,130,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u992

def r3781 : Route 9 := (fun mask => (mask,id))

def c3781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3781 : Upper (D 1) (R 1) [52,320,192,130,2] 13 := by
  apply FastRouting.sound _ _ [52,320,192,130,2] 13 (by decide) (choices 1) [1,8,16] r3781 c3781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3781_1
  · exact u993
  · exact u994

def b3782 : PairBound 9 := { available := 51, camps := [], pairs := [], upper := (rows 53 322 196 138 24 51 115 179 307), lower := (rows 53 322 196 138 24 32 64 128 256), losses := [] }

theorem u3782 : Upper (D 1) (R 1) [52,320,192,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 196 138 48 59 91 155 283), lower := (rows 53 322 196 138 48 32 64 128 256), losses := [] }

theorem u3783 : Upper (D 1) (R 1) [52,320,192,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 322 196 152 17 42 106 170 298), lower := (rows 53 322 196 152 17 32 64 128 256), losses := [] }

theorem u3784 : Upper (D 1) (R 1) [52,320,192,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3785 : Route 9 := (fun mask => (mask,id))

def c3785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3785 : Upper (D 1) (R 1) [52,320,192,144,2] 13 := by
  apply FastRouting.sound _ _ [52,320,192,144,2] 13 (by decide) (choices 1) [1,2,8] r3785 c3785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u995
  · exact u996
  · exact u997

def b3786 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 322 196 152 24 35 99 163 291), lower := (rows 53 322 196 152 24 32 64 128 256), losses := [] }

theorem u3786 : Upper (D 1) (R 1) [52,320,192,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3787 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 196 152 48 43 75 139 267), lower := (rows 53 322 196 152 48 32 64 128 256), losses := [] }

theorem u3787 : Upper (D 1) (R 1) [52,320,192,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 14 152 18 480 480 480 480), lower := (rows 113 7 14 152 18 32 64 128 256), losses := [] }

theorem u3788 : Upper (D 1) (R 1) [112,5,10,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 152 48 482 450 450 450), lower := (rows 113 7 14 152 48 32 64 128 256), losses := [] }

theorem u3789 : Upper (D 1) (R 1) [112,5,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3790 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 14 152 144 354 354 482 354), lower := (rows 113 7 14 152 144 32 64 128 256), losses := [] }

theorem u3790 : Upper (D 1) (R 1) [112,5,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 7 14 152 272 226 226 226 482), lower := (rows 113 7 14 152 272 32 64 128 256), losses := [] }

theorem u3791 : Upper (D 1) (R 1) [112,5,10,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 14 280 18 224 224 224 480), lower := (rows 113 7 14 280 18 32 64 128 256), losses := [] }

theorem u3792 : Upper (D 1) (R 1) [112,5,10,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 280 48 226 194 194 450), lower := (rows 113 7 14 280 48 32 64 128 256), losses := [] }

theorem u3793 : Upper (D 1) (R 1) [112,5,10,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3794 : Route 9 := (fun mask => (mask,id))

def c3794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3794 : Upper (D 1) (R 1) [112,5,10,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,10,272,128] 13 (by decide) (choices 1) [2,64,128] r3794 c3794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u998
  · exact u999
  · exact u1000

def b3795 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 14 392 18 240 240 240 496), lower := (rows 113 7 14 392 18 32 64 128 256), losses := [] }

theorem u3795 : Upper (D 1) (R 1) [112,5,10,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3796 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 392 48 242 210 210 466), lower := (rows 113 7 14 392 48 32 64 128 256), losses := [] }

theorem u3796 : Upper (D 1) (R 1) [112,5,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3796
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3797_2 : Upper (D 1) (R 1) [112,5,10,384,128,2] 13 :=
  permutation_upper _ _ _ [112,5,10,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1001

theorem m3797_16 : Upper (D 1) (R 1) [112,5,10,384,128,16] 13 :=
  permutation_upper _ _ _ [112,5,10,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1002

theorem m3797_64 : Upper (D 1) (R 1) [112,5,10,384,128,64] 13 :=
  permutation_upper _ _ _ [112,5,10,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1003

def r3797 : Route 9 := (fun mask => (mask,id))

def c3797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3797 : Upper (D 1) (R 1) [112,5,10,384,128] 13 := by
  apply FastRouting.sound _ _ [112,5,10,384,128] 13 (by decide) (choices 1) [2,16,64] r3797 c3797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3797_2
  · exact m3797_16
  · exact m3797_64

def b3798 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 134 152 18 360 360 488 360), lower := (rows 113 7 134 152 18 32 64 128 256), losses := [] }

theorem u3798 : Upper (D 1) (R 1) [112,5,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3799 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 113 7 134 152 24 354 354 482 354), lower := (rows 113 7 134 152 24 32 64 128 256), losses := [] }

theorem u3799 : Upper (D 1) (R 1) [112,5,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3800 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 134 152 48 362 330 458 330), lower := (rows 113 7 134 152 48 32 64 128 256), losses := [] }

theorem u3800 : Upper (D 1) (R 1) [112,5,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 7 134 152 272 106 106 234 362), lower := (rows 113 7 134 152 272 32 64 128 256), losses := [] }

theorem u3801 : Upper (D 1) (R 1) [112,5,130,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 134 280 18 232 232 232 488), lower := (rows 113 7 134 280 18 32 64 128 256), losses := [] }

theorem u3802 : Upper (D 1) (R 1) [112,5,130,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3803 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 7 134 280 24 226 226 226 482), lower := (rows 113 7 134 280 24 32 64 128 256), losses := [] }

theorem u3803 : Upper (D 1) (R 1) [112,5,130,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 134 280 48 234 202 202 458), lower := (rows 113 7 134 280 48 32 64 128 256), losses := [] }

theorem u3804 : Upper (D 1) (R 1) [112,5,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3805 : Route 9 := (fun mask => (mask,id))

def c3805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3805 : Upper (D 1) (R 1) [112,5,130,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,130,272,128] 13 (by decide) (choices 1) [2,8,64] r3805 c3805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1004
  · exact u1005
  · exact u1006

def b3806 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 134 392 18 120 120 248 376), lower := (rows 113 7 134 392 18 32 64 128 256), losses := [] }

theorem u3806 : Upper (D 1) (R 1) [112,5,130,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 7 134 392 24 114 114 242 370), lower := (rows 113 7 134 392 24 32 64 128 256), losses := [] }

theorem u3807 : Upper (D 1) (R 1) [112,5,130,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 134 392 48 122 90 218 346), lower := (rows 113 7 134 392 48 32 64 128 256), losses := [] }

theorem u3808 : Upper (D 1) (R 1) [112,5,130,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 140 266 18 240 240 240 496), lower := (rows 113 7 140 266 18 32 64 128 256), losses := [] }

theorem u3809 : Upper (D 1) (R 1) [112,5,136,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 266 48 242 210 210 466), lower := (rows 113 7 140 266 48 32 64 128 256), losses := [] }

theorem u3810 : Upper (D 1) (R 1) [112,5,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3810
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3811_2 : Upper (D 1) (R 1) [112,5,136,258,128,2] 13 :=
  permutation_upper _ _ _ [112,5,136,258,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1007

theorem m3811_16 : Upper (D 1) (R 1) [112,5,136,258,128,16] 13 :=
  permutation_upper _ _ _ [112,5,136,258,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1008

theorem m3811_64 : Upper (D 1) (R 1) [112,5,136,258,128,64] 13 :=
  permutation_upper _ _ _ [112,5,136,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1009

def r3811 : Route 9 := (fun mask => (mask,id))

def c3811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3811 : Upper (D 1) (R 1) [112,5,136,258,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,258,128] 13 (by decide) (choices 1) [2,16,64] r3811 c3811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3811_2
  · exact m3811_16
  · exact m3811_64

def b3812 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 113 7 140 280 18 226 226 226 482), lower := (rows 113 7 140 280 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 50 82 146 274), good := (rows 481 487 140 492 482 32 64 128 256) }] }

theorem u3812 : Upper (D 1) (R 1) [112,5,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 280 48 226 194 194 450), lower := (rows 113 7 140 280 48 32 64 128 256), losses := [] }

theorem u3813 : Upper (D 1) (R 1) [112,5,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3814 : Route 9 := (fun mask => (mask,id))

def c3814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3814 : Upper (D 1) (R 1) [112,5,136,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,128] 13 (by decide) (choices 1) [2,64] r3814 c3814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1010
  · exact u1011

def b3815 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 262 152 18 232 232 232 488), lower := (rows 113 7 262 152 18 32 64 128 256), losses := [] }

theorem u3815 : Upper (D 1) (R 1) [112,5,258,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 7 262 152 24 226 226 226 482), lower := (rows 113 7 262 152 24 32 64 128 256), losses := [] }

theorem u3816 : Upper (D 1) (R 1) [112,5,258,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3817 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 262 152 48 234 202 202 458), lower := (rows 113 7 262 152 48 32 64 128 256), losses := [] }

theorem u3817 : Upper (D 1) (R 1) [112,5,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 262 152 144 106 106 234 362), lower := (rows 113 7 262 152 144 32 64 128 256), losses := [] }

theorem u3818 : Upper (D 1) (R 1) [112,5,258,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3819 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 7 268 138 18 240 240 240 496), lower := (rows 113 7 268 138 18 32 64 128 256), losses := [] }

theorem u3819 : Upper (D 1) (R 1) [112,5,264,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3819
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3820 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 138 48 242 210 210 466), lower := (rows 113 7 268 138 48 32 64 128 256), losses := [] }

theorem u3820 : Upper (D 1) (R 1) [112,5,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3820
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3821_2 : Upper (D 1) (R 1) [112,5,264,130,128,2] 13 :=
  permutation_upper _ _ _ [112,5,264,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1012

theorem m3821_16 : Upper (D 1) (R 1) [112,5,264,130,128,16] 13 :=
  permutation_upper _ _ _ [112,5,264,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1013

theorem m3821_64 : Upper (D 1) (R 1) [112,5,264,130,128,64] 13 :=
  permutation_upper _ _ _ [112,5,264,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1014

def r3821 : Route 9 := (fun mask => (mask,id))

def c3821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3821 : Upper (D 1) (R 1) [112,5,264,130,128] 13 := by
  apply FastRouting.sound _ _ [112,5,264,130,128] 13 (by decide) (choices 1) [2,16,64] r3821 c3821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3821_2
  · exact m3821_16
  · exact m3821_64

def b3822 : PairBound 9 := { available := 226, camps := [], pairs := [(2,4)], upper := (rows 113 7 268 152 18 226 226 226 482), lower := (rows 113 7 268 152 18 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 50 82 146 274), good := (rows 481 487 268 492 482 32 64 128 256) }] }

theorem u3822 : Upper (D 1) (R 1) [112,5,264,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 152 48 226 194 194 450), lower := (rows 113 7 268 152 48 32 64 128 256), losses := [] }

theorem u3823 : Upper (D 1) (R 1) [112,5,264,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 268 152 144 98 98 226 354), lower := (rows 113 7 268 152 144 32 64 128 256), losses := [] }

theorem u3824 : Upper (D 1) (R 1) [112,5,264,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3825 : Route 9 := (fun mask => (mask,id))

def c3825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3825 : Upper (D 1) (R 1) [112,5,384,144,2] 13 := by
  apply FastRouting.sound _ _ [112,5,384,144,2] 13 (by decide) (choices 1) [2,8,64] r3825 c3825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1015
  · exact u1016
  · exact u1017

def b3826 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 7 388 152 24 98 98 226 354), lower := (rows 113 7 388 152 24 32 64 128 256), losses := [] }

theorem u3826 : Upper (D 1) (R 1) [112,5,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3827 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 388 152 48 106 74 202 330), lower := (rows 113 7 388 152 48 32 64 128 256), losses := [] }

theorem u3827 : Upper (D 1) (R 1) [112,5,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3828 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 152 18 480 480 480 480), lower := (rows 113 14 7 152 18 32 64 128 256), losses := [] }

theorem u3828 : Upper (D 1) (R 1) [112,12,3,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3829 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 7 152 48 482 450 450 450), lower := (rows 113 14 7 152 48 32 64 128 256), losses := [] }

theorem u3829 : Upper (D 1) (R 1) [112,12,3,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3830 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 7 152 144 354 354 482 354), lower := (rows 113 14 7 152 144 32 64 128 256), losses := [] }

theorem u3830 : Upper (D 1) (R 1) [112,12,3,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3830
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 14 7 152 272 226 226 226 482), lower := (rows 113 14 7 152 272 32 64 128 256), losses := [] }

theorem u3831 : Upper (D 1) (R 1) [112,12,3,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 280 18 224 224 224 480), lower := (rows 113 14 7 280 18 32 64 128 256), losses := [] }

theorem u3832 : Upper (D 1) (R 1) [112,12,3,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 7 280 48 226 194 194 450), lower := (rows 113 14 7 280 48 32 64 128 256), losses := [] }

theorem u3833 : Upper (D 1) (R 1) [112,12,3,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3834 : Route 9 := (fun mask => (mask,id))

def c3834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3834 : Upper (D 1) (R 1) [112,12,3,272,128] 13 := by
  apply FastRouting.sound _ _ [112,12,3,272,128] 13 (by decide) (choices 1) [2,64,128] r3834 c3834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1018
  · exact u1019
  · exact u1020

def b3835 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 392 18 240 240 240 496), lower := (rows 113 14 7 392 18 32 64 128 256), losses := [] }

theorem u3835 : Upper (D 1) (R 1) [112,12,3,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3836 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 7 392 48 242 210 210 466), lower := (rows 113 14 7 392 48 32 64 128 256), losses := [] }

theorem u3836 : Upper (D 1) (R 1) [112,12,3,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3836
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3837_2 : Upper (D 1) (R 1) [112,12,3,384,128,2] 13 :=
  permutation_upper _ _ _ [112,12,3,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1021

theorem m3837_16 : Upper (D 1) (R 1) [112,12,3,384,128,16] 13 :=
  permutation_upper _ _ _ [112,12,3,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1022

theorem m3837_64 : Upper (D 1) (R 1) [112,12,3,384,128,64] 13 :=
  permutation_upper _ _ _ [112,12,3,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1023

def r3837 : Route 9 := (fun mask => (mask,id))

def c3837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3837 : Upper (D 1) (R 1) [112,12,3,384,128] 13 := by
  apply FastRouting.sound _ _ [112,12,3,384,128] 13 (by decide) (choices 1) [2,16,64] r3837 c3837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3837_2
  · exact m3837_16
  · exact m3837_64

def b3838 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 137 18 480 480 480 480), lower := (rows 113 14 22 137 18 32 64 128 256), losses := [] }

theorem u3838 : Upper (D 1) (R 1) [112,12,18,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3839 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 137 48 482 450 450 450), lower := (rows 113 14 22 137 48 32 64 128 256), losses := [] }

theorem u3839 : Upper (D 1) (R 1) [112,12,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3839
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3839
end Delivery.IrregularNine14.P01
