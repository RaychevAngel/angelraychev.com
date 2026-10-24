import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0015
import IrregularNine14P01C0016

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3660 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 14 200 80 163 227 163 419), lower := (rows 53 274 14 200 80 32 64 128 256), losses := [] }

theorem u3660 : Upper (D 1) (R 1) [52,272,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3661 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 53 274 70 42 17 232 200 200 456), lower := (rows 53 274 70 42 17 32 64 128 256), losses := [] }

theorem u3661 : Upper (D 1) (R 1) [52,272,66,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 53 274 70 42 24 225 193 193 449), lower := (rows 53 274 70 42 24 32 64 128 256), losses := [] }

theorem u3662 : Upper (D 1) (R 1) [52,272,66,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3663 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 42 80 169 201 137 393), lower := (rows 53 274 70 42 80 32 64 128 256), losses := [] }

theorem u3663 : Upper (D 1) (R 1) [52,272,66,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3664 : Route 9 := (fun mask => (mask,id))

def c3664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3664 : Upper (D 1) (R 1) [52,272,66,34,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,34,128] 13 (by decide) (choices 1) [1,8,64,128] r3664 c3664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u942
  · exact u943
  · exact u944
  · exact u945

def b3665 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 274 70 104 17 170 202 138 394), lower := (rows 53 274 70 104 17 32 64 128 256), losses := [] }

theorem u3665 : Upper (D 1) (R 1) [52,272,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 104 18 169 201 137 393), lower := (rows 53 274 70 104 18 32 64 128 256), losses := [] }

theorem u3666 : Upper (D 1) (R 1) [52,272,66,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 274 70 104 24 163 195 131 387), lower := (rows 53 274 70 104 24 32 64 128 256), losses := [] }

theorem u3667 : Upper (D 1) (R 1) [52,272,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3668 : Route 9 := (fun mask => (mask,id))

def c3668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3668 : Upper (D 1) (R 1) [52,272,66,96,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,96,128] 13 (by decide) (choices 1) [1,2,8,128] r3668 c3668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u946
  · exact u947
  · exact u948
  · exact u949

def b3669 : PairBound 9 := { available := 232, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 137 18 232 232 232 488), lower := (rows 53 274 70 137 18 32 64 128 256), losses := [] }

theorem u3669 : Upper (D 1) (R 1) [52,272,66,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3670 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 274 70 137 24 226 226 226 482), lower := (rows 53 274 70 137 24 32 64 128 256), losses := [] }

theorem u3670 : Upper (D 1) (R 1) [52,272,66,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3671 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 137 48 234 202 202 458), lower := (rows 53 274 70 137 48 32 64 128 256), losses := [] }

theorem u3671 : Upper (D 1) (R 1) [52,272,66,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3672 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 137 80 170 234 170 426), lower := (rows 53 274 70 137 80 32 64 128 256), losses := [] }

theorem u3672 : Upper (D 1) (R 1) [52,272,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3673 : Route 9 := (fun mask => (mask,id))

def c3673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3673 : Upper (D 1) (R 1) [52,272,66,129,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,129,128] 13 (by decide) (choices 1) [2,8,64] r3673 c3673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u950
  · exact u951
  · exact u952

def b3674 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 53 274 70 138 17 232 232 232 488), lower := (rows 53 274 70 138 17 32 64 128 256), losses := [] }

theorem u3674 : Upper (D 1) (R 1) [52,272,66,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3675 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 53 274 70 138 24 225 225 225 481), lower := (rows 53 274 70 138 24 32 64 128 256), losses := [] }

theorem u3675 : Upper (D 1) (R 1) [52,272,66,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3676 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 138 48 233 201 201 457), lower := (rows 53 274 70 138 48 32 64 128 256), losses := [] }

theorem u3676 : Upper (D 1) (R 1) [52,272,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 138 80 169 233 169 425), lower := (rows 53 274 70 138 80 32 64 128 256), losses := [] }

theorem u3677 : Upper (D 1) (R 1) [52,272,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3678 : Route 9 := (fun mask => (mask,id))

def c3678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3678 : Upper (D 1) (R 1) [52,272,66,130,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,130,128] 13 (by decide) (choices 1) [1,8,64] r3678 c3678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u953
  · exact u954
  · exact u955

def b3679 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 53 274 70 168 17 234 202 202 458), lower := (rows 53 274 70 168 17 32 64 128 256), losses := [] }

theorem u3679 : Upper (D 1) (R 1) [52,272,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3679
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 201, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 168 18 233 201 201 457), lower := (rows 53 274 70 168 18 32 64 128 256), losses := [] }

theorem u3680 : Upper (D 1) (R 1) [52,272,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 274 70 168 24 227 195 195 451), lower := (rows 53 274 70 168 24 32 64 128 256), losses := [] }

theorem u3681 : Upper (D 1) (R 1) [52,272,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3682 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 70 168 80 171 203 139 395), lower := (rows 53 274 70 168 80 32 64 128 256), losses := [] }

theorem u3682 : Upper (D 1) (R 1) [52,272,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3683 : Route 9 := (fun mask => (mask,id))

def c3683 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3683 : Upper (D 1) (R 1) [52,272,66,160,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,160,128] 13 (by decide) (choices 1) [1,2,8,64] r3683 c3683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u956
  · exact u957
  · exact u958
  · exact u959

def b3684 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 274 70 200 17 170 234 170 426), lower := (rows 53 274 70 200 17 32 64 128 256), losses := [] }

theorem u3684 : Upper (D 1) (R 1) [52,272,66,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 169, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 200 18 169 233 169 425), lower := (rows 53 274 70 200 18 32 64 128 256), losses := [] }

theorem u3685 : Upper (D 1) (R 1) [52,272,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 274 70 200 24 163 227 163 419), lower := (rows 53 274 70 200 24 32 64 128 256), losses := [] }

theorem u3686 : Upper (D 1) (R 1) [52,272,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 70 200 48 171 203 139 395), lower := (rows 53 274 70 200 48 32 64 128 256), losses := [] }

theorem u3687 : Upper (D 1) (R 1) [52,272,66,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3688 : Route 9 := (fun mask => (mask,id))

def c3688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3688 : Upper (D 1) (R 1) [52,272,66,192,128] 13 := by
  apply FastRouting.sound _ _ [52,272,66,192,128] 13 (by decide) (choices 1) [1,2,8] r3688 c3688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u960
  · exact u961
  · exact u962

def b3689 : PairBound 9 := { available := 226, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 137 18 226 226 226 482), lower := (rows 53 274 76 137 18 32 64 128 256), losses := [] }

theorem u3689 : Upper (D 1) (R 1) [52,272,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3689
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 137 48 226 194 194 450), lower := (rows 53 274 76 137 48 32 64 128 256), losses := [] }

theorem u3690 : Upper (D 1) (R 1) [52,272,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3691 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 76 137 80 162 226 162 418), lower := (rows 53 274 76 137 80 32 64 128 256), losses := [] }

theorem u3691 : Upper (D 1) (R 1) [52,272,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3692 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 76 137 144 98 98 226 354), lower := (rows 53 274 76 137 144 32 64 128 256), losses := [] }

theorem u3692 : Upper (D 1) (R 1) [52,272,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 274 76 138 17 226 226 226 482), lower := (rows 53 274 76 138 17 32 64 128 256), losses := [] }

theorem u3693 : Upper (D 1) (R 1) [52,272,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 138 18 225 225 225 481), lower := (rows 53 274 76 138 18 32 64 128 256), losses := [] }

theorem u3694 : Upper (D 1) (R 1) [52,272,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3694
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 76 138 48 227 195 195 451), lower := (rows 53 274 76 138 48 32 64 128 256), losses := [] }

theorem u3695 : Upper (D 1) (R 1) [52,272,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 76 138 80 163 227 163 419), lower := (rows 53 274 76 138 80 32 64 128 256), losses := [] }

theorem u3696 : Upper (D 1) (R 1) [52,272,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 76 138 144 99 99 227 355), lower := (rows 53 274 76 138 144 32 64 128 256), losses := [] }

theorem u3697 : Upper (D 1) (R 1) [52,272,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 53 274 196 42 17 234 202 202 458), lower := (rows 53 274 196 42 17 32 64 128 256), losses := [] }

theorem u3698 : Upper (D 1) (R 1) [52,272,192,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 201, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 196 42 18 233 201 201 457), lower := (rows 53 274 196 42 18 32 64 128 256), losses := [] }

theorem u3699 : Upper (D 1) (R 1) [52,272,192,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3699
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 274 196 42 24 227 195 195 451), lower := (rows 53 274 196 42 24 32 64 128 256), losses := [] }

theorem u3700 : Upper (D 1) (R 1) [52,272,192,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 274 196 42 80 171 203 139 395), lower := (rows 53 274 196 42 80 32 64 128 256), losses := [] }

theorem u3701 : Upper (D 1) (R 1) [52,272,192,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 274 196 74 17 170 234 170 426), lower := (rows 53 274 196 74 17 32 64 128 256), losses := [] }

theorem u3702 : Upper (D 1) (R 1) [52,272,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 169, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 196 74 18 169 233 169 425), lower := (rows 53 274 196 74 18 32 64 128 256), losses := [] }

theorem u3703 : Upper (D 1) (R 1) [52,272,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 274 196 74 24 163 227 163 419), lower := (rows 53 274 196 74 24 32 64 128 256), losses := [] }

theorem u3704 : Upper (D 1) (R 1) [52,272,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 196 74 48 171 203 139 395), lower := (rows 53 274 196 74 48 32 64 128 256), losses := [] }

theorem u3705 : Upper (D 1) (R 1) [52,272,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3706 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 196 74 144 43 107 171 299), lower := (rows 53 274 196 74 144 32 64 128 256), losses := [] }

theorem u3706 : Upper (D 1) (R 1) [52,272,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 274 196 104 17 170 202 138 394), lower := (rows 53 274 196 104 17 32 64 128 256), losses := [] }

theorem u3707 : Upper (D 1) (R 1) [52,272,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3708 : PairBound 9 := { available := 139, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 196 104 18 171 203 139 395), lower := (rows 53 274 196 104 18 32 64 128 256), losses := [] }

theorem u3708 : Upper (D 1) (R 1) [52,272,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 274 196 104 24 163 195 131 387), lower := (rows 53 274 196 104 24 32 64 128 256), losses := [] }

theorem u3709 : Upper (D 1) (R 1) [52,272,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 274 196 104 144 43 75 139 267), lower := (rows 53 274 196 104 144 32 64 128 256), losses := [] }

theorem u3710 : Upper (D 1) (R 1) [52,272,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 322 7 138 24 240 240 240 496), lower := (rows 53 322 7 138 24 32 64 128 256), losses := [] }

theorem u3711 : Upper (D 1) (R 1) [52,320,3,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 7 138 48 248 216 216 472), lower := (rows 53 322 7 138 48 32 64 128 256), losses := [] }

theorem u3712 : Upper (D 1) (R 1) [52,320,3,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 184, camps := [], pairs := [(3,6)], upper := (rows 53 322 7 138 80 184 248 184 440), lower := (rows 53 322 7 138 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 33 0 129 257), good := (rows 445 258 431 138 16 32 0 128 256) }] }

theorem u3713 : Upper (D 1) (R 1) [52,320,3,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3713
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3714_8 : Upper (D 1) (R 1) [52,320,3,130,128,8] 13 :=
  permutation_upper _ _ _ [52,320,3,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u963

theorem m3714_16 : Upper (D 1) (R 1) [52,320,3,130,128,16] 13 :=
  permutation_upper _ _ _ [52,320,3,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u964

theorem m3714_64 : Upper (D 1) (R 1) [52,320,3,130,128,64] 13 :=
  permutation_upper _ _ _ [52,320,3,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u965

def r3714 : Route 9 := (fun mask => (mask,id))

def c3714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3714 : Upper (D 1) (R 1) [52,320,3,130,128] 13 := by
  apply FastRouting.sound _ _ [52,320,3,130,128] 13 (by decide) (choices 1) [8,16,64] r3714 c3714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3714_8
  · exact m3714_16
  · exact m3714_64

def b3715 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 7 200 18 184 248 184 440), lower := (rows 53 322 7 200 18 32 64 128 256), losses := [] }

theorem u3715 : Upper (D 1) (R 1) [52,320,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3716 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 322 7 200 24 178 242 178 434), lower := (rows 53 322 7 200 24 32 64 128 256), losses := [] }

theorem u3716 : Upper (D 1) (R 1) [52,320,3,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3717 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 7 200 48 186 218 154 410), lower := (rows 53 322 7 200 48 32 64 128 256), losses := [] }

theorem u3717 : Upper (D 1) (R 1) [52,320,3,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3717
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3718_2 : Upper (D 1) (R 1) [52,320,3,192,128,2] 13 :=
  permutation_upper _ _ _ [52,320,3,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u966

theorem m3718_8 : Upper (D 1) (R 1) [52,320,3,192,128,8] 13 :=
  permutation_upper _ _ _ [52,320,3,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u967

theorem m3718_16 : Upper (D 1) (R 1) [52,320,3,192,128,16] 13 :=
  permutation_upper _ _ _ [52,320,3,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u968

def r3718 : Route 9 := (fun mask => (mask,id))

def c3718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3718 : Upper (D 1) (R 1) [52,320,3,192,128] 13 := by
  apply FastRouting.sound _ _ [52,320,3,192,128] 13 (by decide) (choices 1) [2,8,16] r3718 c3718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3718_2
  · exact m3718_8
  · exact m3718_16

def r3719 : Route 9 := (fun mask => (mask,id))

def c3719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3719 : Upper (D 1) (R 1) [52,320,9,130,2] 13 := by
  apply FastRouting.sound _ _ [52,320,9,130,2] 13 (by decide) (choices 1) [16,64,128] r3719 c3719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u969
  · exact u970
  · exact u971

#print axioms u3719
end Delivery.IrregularNine14.P01
