import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0024
import IrregularNine14P03C0025

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 13 200 208 53 117 181 309), lower := (rows 35 259 13 200 208 32 64 128 256), losses := [] }

theorem u3720 : Upper (D 3) (R 3) [34,257,9,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3720
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 41 81 228 196 196 452), lower := (rows 35 259 28 41 81 32 64 128 256), losses := [] }

theorem u3721 : Upper (D 3) (R 3) [34,257,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 41 84 225 193 193 449), lower := (rows 35 259 28 41 84 32 64 128 256), losses := [] }

theorem u3722 : Upper (D 3) (R 3) [34,257,24,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 41 208 229 197 197 453), lower := (rows 35 259 28 41 208 32 64 128 256), losses := [] }

theorem u3723 : Upper (D 3) (R 3) [34,257,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 44 81 225 193 193 449), lower := (rows 35 259 28 44 81 32 64 128 256), losses := [] }

theorem u3724 : Upper (D 3) (R 3) [34,257,24,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 44 208 225 193 193 449), lower := (rows 35 259 28 44 208 32 64 128 256), losses := [] }

theorem u3725 : Upper (D 3) (R 3) [34,257,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3725
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3726 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 28 73 81 164 228 164 420), lower := (rows 35 259 28 73 81 32 64 128 256), losses := [] }

theorem u3726 : Upper (D 3) (R 3) [34,257,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3726
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 73 84 161 225 161 417), lower := (rows 35 259 28 73 84 32 64 128 256), losses := [] }

theorem u3727 : Upper (D 3) (R 3) [34,257,24,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3728 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 112 165 197 133 389), lower := (rows 35 259 28 73 112 32 64 128 256), losses := [] }

theorem u3728 : Upper (D 3) (R 3) [34,257,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3728
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m3729_128 : Upper (D 3) (R 3) [34,257,24,65,129,128] 13 :=
  permutation_upper _ _ _ [34,257,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

def r3729 : Route 9 := (fun mask => (mask,id))

def c3729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3729 : Upper (D 3) (R 3) [34,257,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,129] 13 (by decide) (choices 1) [4,64,128] r3729 c3729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1458
  · exact u1459
  · exact m3729_128

def r3730 : Route 9 := (fun mask => (mask,id))

def c3730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3730 : Upper (D 3) (R 3) [34,257,24,65,132] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,132] 13 (by decide) (choices 1) [1,64,128] r3730 c3730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1460
  · exact u1461
  · exact u1462

def r3731 : Route 9 := (fun mask => (mask,id))

def c3731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3731 : Upper (D 3) (R 3) [34,257,24,65,160] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,160] 13 (by decide) (choices 1) [1,4,64,128] r3731 c3731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1463
  · exact u1464
  · exact u1465
  · exact u1466

def b3732 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 73 208 165 229 165 421), lower := (rows 35 259 28 73 208 32 64 128 256), losses := [] }

theorem u3732 : Upper (D 3) (R 3) [34,257,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3732
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3733 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 76 112 161 193 129 385), lower := (rows 35 259 28 76 112 32 64 128 256), losses := [] }

theorem u3733 : Upper (D 3) (R 3) [34,257,24,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3733
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 28 76 176 225 193 193 449), lower := (rows 35 259 28 76 176 32 64 128 256), losses := [] }

theorem u3734 : Upper (D 3) (R 3) [34,257,24,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3734
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 76 208 161 225 161 417), lower := (rows 35 259 28 76 208 32 64 128 256), losses := [] }

theorem u3735 : Upper (D 3) (R 3) [34,257,24,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3736 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 104 208 165 197 133 389), lower := (rows 35 259 28 104 208 32 64 128 256), losses := [] }

theorem u3736 : Upper (D 3) (R 3) [34,257,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 200 208 37 101 165 293), lower := (rows 35 259 28 200 208 32 64 128 256), losses := [] }

theorem u3737 : Upper (D 3) (R 3) [34,257,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 73 84 184 216 152 408), lower := (rows 35 259 37 73 84 32 64 128 256), losses := [] }

theorem u3738 : Upper (D 3) (R 3) [34,257,33,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3738
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3739 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 73 148 248 216 216 472), lower := (rows 35 259 37 73 148 32 64 128 256), losses := [] }

theorem u3739 : Upper (D 3) (R 3) [34,257,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3739
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3740 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 73 152 244 212 212 468), lower := (rows 35 259 37 73 152 32 64 128 256), losses := [] }

theorem u3740 : Upper (D 3) (R 3) [34,257,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3741 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 73 208 188 220 156 412), lower := (rows 35 259 37 73 208 32 64 128 256), losses := [] }

theorem u3741 : Upper (D 3) (R 3) [34,257,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3742 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 76 152 241 209 209 465), lower := (rows 35 259 37 76 152 32 64 128 256), losses := [] }

theorem u3742 : Upper (D 3) (R 3) [34,257,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 76 208 185 217 153 409), lower := (rows 35 259 37 76 208 32 64 128 256), losses := [] }

theorem u3743 : Upper (D 3) (R 3) [34,257,33,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3743
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3744 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 37 88 152 229 197 197 453), lower := (rows 35 259 37 88 152 32 64 128 256), losses := [] }

theorem u3744 : Upper (D 3) (R 3) [34,257,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3744
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3745 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 259 44 73 81 180 212 148 404), lower := (rows 35 259 44 73 81 32 64 128 256), losses := [] }

theorem u3745 : Upper (D 3) (R 3) [34,257,40,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3745
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3746 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 73 84 177 209 145 401), lower := (rows 35 259 44 73 84 32 64 128 256), losses := [] }

theorem u3746 : Upper (D 3) (R 3) [34,257,40,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3746
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3747 : Route 9 := (fun mask => (mask,id))

def c3747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3747 : Upper (D 3) (R 3) [34,257,40,65,129] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,129] 13 (by decide) (choices 1) [4,16,64,128] r3747 c3747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1467
  · exact u1468
  · exact u1469
  · exact u1470

def r3748 : Route 9 := (fun mask => (mask,id))

def c3748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3748 : Upper (D 3) (R 3) [34,257,40,65,132] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,132] 13 (by decide) (choices 1) [1,16,64,128] r3748 c3748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1471
  · exact u1472
  · exact u1473
  · exact u1474

def r3749 : Route 9 := (fun mask => (mask,id))

def c3749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3749 : Upper (D 3) (R 3) [34,257,40,65,192] 13 := by
  apply FastRouting.sound _ _ [34,257,40,65,192] 13 (by decide) (choices 1) [1,4,16,128] r3749 c3749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1475
  · exact u1476
  · exact u1477
  · exact u1478

def b3750 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 44 76 81 177 209 145 401), lower := (rows 35 259 44 76 81 32 64 128 256), losses := [] }

theorem u3750 : Upper (D 3) (R 3) [34,257,40,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3751 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 44 76 145 241 209 209 465), lower := (rows 35 259 44 76 145 32 64 128 256), losses := [] }

theorem u3751 : Upper (D 3) (R 3) [34,257,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 44 76 208 177 209 145 401), lower := (rows 35 259 44 76 208 32 64 128 256), losses := [] }

theorem u3752 : Upper (D 3) (R 3) [34,257,40,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3753 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 81 165 197 133 389), lower := (rows 35 259 44 88 81 32 64 128 256), losses := [] }

theorem u3753 : Upper (D 3) (R 3) [34,257,40,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3754 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 84 161 193 129 385), lower := (rows 35 259 44 88 84 32 64 128 256), losses := [] }

theorem u3754 : Upper (D 3) (R 3) [34,257,40,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3755 : Route 9 := (fun mask => (mask,id))

def c3755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3755 : Upper (D 3) (R 3) [34,257,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,257,40,80,129] 13 (by decide) (choices 1) [1,4,64,128] r3755 c3755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1479
  · exact u1480
  · exact u1481
  · exact u1482

def b3756 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 44 88 148 225 193 193 449), lower := (rows 35 259 44 88 148 32 64 128 256), losses := [] }

theorem u3756 : Upper (D 3) (R 3) [34,257,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3756
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 208 165 197 133 389), lower := (rows 35 259 44 88 208 32 64 128 256), losses := [] }

theorem u3757 : Upper (D 3) (R 3) [34,257,40,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3757
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3758 : Route 9 := (fun mask => (mask,id))

def c3758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3758 : Upper (D 3) (R 3) [34,257,40,192,65] 13 := by
  apply FastRouting.sound _ _ [34,257,40,192,65] 13 (by decide) (choices 1) [1,4,16,128] r3758 c3758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1483
  · exact u1484
  · exact u1485
  · exact u1486

def b3759 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 200 84 177 209 145 401), lower := (rows 35 259 44 200 84 32 64 128 256), losses := [] }

theorem u3759 : Upper (D 3) (R 3) [34,257,40,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3759
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 44 200 208 53 85 149 277), lower := (rows 35 259 44 200 208 32 64 128 256), losses := [] }

theorem u3760 : Upper (D 3) (R 3) [34,257,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 259 69 73 148 184 248 184 440), lower := (rows 35 259 69 73 148 32 64 128 256), losses := [] }

theorem u3761 : Upper (D 3) (R 3) [34,257,65,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 259 69 73 176 188 220 156 412), lower := (rows 35 259 69 73 176 32 64 128 256), losses := [] }

theorem u3762 : Upper (D 3) (R 3) [34,257,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 76 145 184 248 184 440), lower := (rows 35 259 69 76 145 32 64 128 256), losses := [] }

theorem u3763 : Upper (D 3) (R 3) [34,257,65,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3764 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 76 152 177 241 177 433), lower := (rows 35 259 69 76 152 32 64 128 256), losses := [] }

theorem u3764 : Upper (D 3) (R 3) [34,257,65,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3764
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 76 176 185 217 153 409), lower := (rows 35 259 69 76 176 32 64 128 256), losses := [] }

theorem u3765 : Upper (D 3) (R 3) [34,257,65,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3765
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3766 : Route 9 := (fun mask => (mask,id))

def c3766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3766 : Upper (D 3) (R 3) [34,257,65,80,129] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,129] 13 (by decide) (choices 1) [4,8,128] r3766 c3766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1487
  · exact u1488
  · exact u1489

def b3767 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 88 148 169 233 169 425), lower := (rows 35 259 69 88 148 32 64 128 256), losses := [] }

theorem u3767 : Upper (D 3) (R 3) [34,257,65,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3767
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3768 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 69 88 152 165 229 165 421), lower := (rows 35 259 69 88 152 32 64 128 256), losses := [] }

theorem u3768 : Upper (D 3) (R 3) [34,257,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3768
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3769 : Route 9 := (fun mask => (mask,id))

def c3769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3769 : Upper (D 3) (R 3) [34,257,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,160] 13 (by decide) (choices 1) [1,4,8,128] r3769 c3769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1490
  · exact u1491
  · exact u1492
  · exact u1493

def r3770 : Route 9 := (fun mask => (mask,id))

def c3770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3770 : Upper (D 3) (R 3) [34,257,65,96,129] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,129] 13 (by decide) (choices 1) [4,8,16,128] r3770 c3770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1494
  · exact u1495
  · exact u1496
  · exact u1497

def r3771 : Route 9 := (fun mask => (mask,id))

def c3771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3771 : Upper (D 3) (R 3) [34,257,65,96,132] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,132] 13 (by decide) (choices 1) [1,8,16,128] r3771 c3771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1498
  · exact u1499
  · exact u1500
  · exact u1501

def r3772 : Route 9 := (fun mask => (mask,id))

def c3772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3772 : Upper (D 3) (R 3) [34,257,65,96,136] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,136] 13 (by decide) (choices 1) [1,4,16,128] r3772 c3772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1502
  · exact u1503
  · exact u1504
  · exact u1505

theorem m3773_8 : Upper (D 3) (R 3) [34,257,65,129,192,8] 13 :=
  permutation_upper _ _ _ [34,257,65,129,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1506

def r3773 : Route 9 := (fun mask => (mask,id))

def c3773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3773 : Upper (D 3) (R 3) [34,257,65,129,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,129,192] 13 (by decide) (choices 1) [4,8,16] r3773 c3773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1506
  · exact m3773_8
  · exact u1507

def b3774 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 69 140 152 113 113 241 369), lower := (rows 35 259 69 140 152 32 64 128 256), losses := [] }

theorem u3774 : Upper (D 3) (R 3) [34,257,65,132,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3775 : Route 9 := (fun mask => (mask,id))

def c3775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3775 : Upper (D 3) (R 3) [34,257,65,132,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,160] 13 (by decide) (choices 1) [1,8,16,64] r3775 c3775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1508
  · exact u1509
  · exact u1510
  · exact u1511

def r3776 : Route 9 := (fun mask => (mask,id))

def c3776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3776 : Upper (D 3) (R 3) [34,257,65,132,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,192] 13 (by decide) (choices 1) [1,8,16] r3776 c3776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1512
  · exact u1513
  · exact u1514

def b3777 : PairBound 9 := { available := 101, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 152 152 101 101 229 357), lower := (rows 35 259 69 152 152 32 64 128 256), losses := [] }

theorem u3777 : Upper (D 3) (R 3) [34,257,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3778 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 69 152 176 109 77 205 333), lower := (rows 35 259 69 152 176 32 64 128 256), losses := [] }

theorem u3778 : Upper (D 3) (R 3) [34,257,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3778
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3779 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 69 152 208 45 109 173 301), lower := (rows 35 259 69 152 208 32 64 128 256), losses := [] }

theorem u3779 : Upper (D 3) (R 3) [34,257,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3779
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P03
