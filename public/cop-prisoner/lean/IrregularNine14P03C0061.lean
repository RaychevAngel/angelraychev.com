import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0023
import IrregularNine14P03C0024

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3660 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 276 57 89 153 281), lower := (rows 35 194 69 168 276 32 64 128 256), losses := [] }

theorem u3660 : Upper (D 3) (R 3) [34,192,65,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3661 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 168 280 53 85 149 277), lower := (rows 35 194 69 168 280 32 64 128 256), losses := [] }

theorem u3661 : Upper (D 3) (R 3) [34,192,65,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3661
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 76 140 273 49 113 177 305), lower := (rows 35 194 76 140 273 32 64 128 256), losses := [] }

theorem u3662 : Upper (D 3) (R 3) [34,192,72,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3662
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3663 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 76 140 304 49 81 145 273), lower := (rows 35 194 76 140 304 32 64 128 256), losses := [] }

theorem u3663 : Upper (D 3) (R 3) [34,192,72,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3664 : Route 9 := (fun mask => (mask,id))

def c3664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3664 : Upper (D 3) (R 3) [34,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257] 13 (by decide) (choices 1) [1,4] r3664 c3664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1419
  · exact u1420

def b3665 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 276 33 97 161 289), lower := (rows 35 194 76 152 276 32 64 128 256), losses := [] }

theorem u3665 : Upper (D 3) (R 3) [34,192,72,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3666 : Route 9 := (fun mask => (mask,id))

def c3666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3666 : Upper (D 3) (R 3) [34,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288] 13 (by decide) (choices 1) [1,4] r3666 c3666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1421
  · exact u1422

def r3667 : Route 9 := (fun mask => (mask,id))

def c3667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3667 : Upper (D 3) (R 3) [34,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257] 13 (by decide) (choices 1) [1,4,16] r3667 c3667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1423
  · exact u1424
  · exact u1425

def r3668 : Route 9 := (fun mask => (mask,id))

def c3668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3668 : Upper (D 3) (R 3) [34,192,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260] 13 (by decide) (choices 1) [1,16] r3668 c3668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1426
  · exact u1427

def r3669 : Route 9 := (fun mask => (mask,id))

def c3669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3669 : Upper (D 3) (R 3) [34,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160] 13 (by decide) (choices 1) [1,4,16] r3669 c3669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1428
  · exact u1429
  · exact u1430

def b3670 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 268 176 49 81 145 273), lower := (rows 35 194 76 268 176 32 64 128 256), losses := [] }

theorem u3670 : Upper (D 3) (R 3) [34,192,72,260,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3671 : Route 9 := (fun mask => (mask,id))

def c3671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3671 : Upper (D 3) (R 3) [34,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160] 13 (by decide) (choices 1) [1,4] r3671 c3671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1431
  · exact u1432

def b3672 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 13 112 240 208 208 464), lower := (rows 35 259 13 13 112 32 64 128 256), losses := [] }

theorem u3672 : Upper (D 3) (R 3) [34,257,9,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3673 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 13 208 240 240 240 496), lower := (rows 35 259 13 13 208 32 64 128 256), losses := [] }

theorem u3673 : Upper (D 3) (R 3) [34,257,9,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 25 52 224 192 192 448), lower := (rows 35 259 13 25 52 32 64 128 256), losses := [] }

theorem u3674 : Upper (D 3) (R 3) [34,257,9,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3675 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 25 84 224 224 224 480), lower := (rows 35 259 13 25 84 32 64 128 256), losses := [] }

theorem u3675 : Upper (D 3) (R 3) [34,257,9,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3676 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 25 112 228 196 196 452), lower := (rows 35 259 13 25 112 32 64 128 256), losses := [] }

theorem u3676 : Upper (D 3) (R 3) [34,257,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3676
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 25 208 228 228 228 484), lower := (rows 35 259 13 25 208 32 64 128 256), losses := [] }

theorem u3677 : Upper (D 3) (R 3) [34,257,9,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3678 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 28 49 224 192 192 448), lower := (rows 35 259 13 28 49 32 64 128 256), losses := [] }

theorem u3678 : Upper (D 3) (R 3) [34,257,9,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3678
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3679 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 28 81 224 224 224 480), lower := (rows 35 259 13 28 81 32 64 128 256), losses := [] }

theorem u3679 : Upper (D 3) (R 3) [34,257,9,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3679
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 28 112 225 193 193 449), lower := (rows 35 259 13 28 112 32 64 128 256), losses := [] }

theorem u3680 : Upper (D 3) (R 3) [34,257,9,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3681 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3681 : Upper (D 3) (R 3) [34,257,9,20,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,192] 13 (by decide) (choices 1) [1,64] r3681 c3681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1433
  · exact u1434

def b3682 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 41 84 240 208 208 464), lower := (rows 35 259 13 41 84 32 64 128 256), losses := [] }

theorem u3682 : Upper (D 3) (R 3) [34,257,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3683 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 41 208 244 212 212 468), lower := (rows 35 259 13 41 208 32 64 128 256), losses := [] }

theorem u3683 : Upper (D 3) (R 3) [34,257,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3683
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 44 81 240 208 208 464), lower := (rows 35 259 13 44 81 32 64 128 256), losses := [] }

theorem u3684 : Upper (D 3) (R 3) [34,257,9,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3684
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 13 44 208 241 209 209 465), lower := (rows 35 259 13 44 208 32 64 128 256), losses := [] }

theorem u3685 : Upper (D 3) (R 3) [34,257,9,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 56 81 228 196 196 452), lower := (rows 35 259 13 56 81 32 64 128 256), losses := [] }

theorem u3686 : Upper (D 3) (R 3) [34,257,9,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 56 84 225 193 193 449), lower := (rows 35 259 13 56 84 32 64 128 256), losses := [] }

theorem u3687 : Upper (D 3) (R 3) [34,257,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3687
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 56 208 229 197 197 453), lower := (rows 35 259 13 56 208 32 64 128 256), losses := [] }

theorem u3688 : Upper (D 3) (R 3) [34,257,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3688
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3689 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 52 240 208 208 464), lower := (rows 35 259 13 73 52 32 64 128 256), losses := [] }

theorem u3689 : Upper (D 3) (R 3) [34,257,9,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 84 176 240 176 432), lower := (rows 35 259 13 73 84 32 64 128 256), losses := [] }

theorem u3690 : Upper (D 3) (R 3) [34,257,9,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3690
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3691 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 112 180 212 148 404), lower := (rows 35 259 13 73 112 32 64 128 256), losses := [] }

theorem u3691 : Upper (D 3) (R 3) [34,257,9,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3692 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 148 240 240 240 496), lower := (rows 35 259 13 73 148 32 64 128 256), losses := [] }

theorem u3692 : Upper (D 3) (R 3) [34,257,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3692
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 176 244 212 212 468), lower := (rows 35 259 13 73 176 32 64 128 256), losses := [] }

theorem u3693 : Upper (D 3) (R 3) [34,257,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 73 208 180 244 180 436), lower := (rows 35 259 13 73 208 32 64 128 256), losses := [] }

theorem u3694 : Upper (D 3) (R 3) [34,257,9,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 76 49 240 208 208 464), lower := (rows 35 259 13 76 49 32 64 128 256), losses := [] }

theorem u3695 : Upper (D 3) (R 3) [34,257,9,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 76 81 176 240 176 432), lower := (rows 35 259 13 76 81 32 64 128 256), losses := [] }

theorem u3696 : Upper (D 3) (R 3) [34,257,9,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3696
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 76 112 177 209 145 401), lower := (rows 35 259 13 76 112 32 64 128 256), losses := [] }

theorem u3697 : Upper (D 3) (R 3) [34,257,9,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3697
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3698 : Route 9 := (fun mask => (mask,id))

def c3698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3698 : Upper (D 3) (R 3) [34,257,9,68,129] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,129] 13 (by decide) (choices 1) [16,64,128] r3698 c3698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1435
  · exact u1436
  · exact u1437

def r3699 : Route 9 := (fun mask => (mask,id))

def c3699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3699 : Upper (D 3) (R 3) [34,257,9,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,160] 13 (by decide) (choices 1) [1,16,64,128] r3699 c3699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1438
  · exact u1439
  · exact u1440
  · exact u1441

def b3700 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 76 208 177 241 177 433), lower := (rows 35 259 13 76 208 32 64 128 256), losses := [] }

theorem u3700 : Upper (D 3) (R 3) [34,257,9,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 88 49 228 196 196 452), lower := (rows 35 259 13 88 49 32 64 128 256), losses := [] }

theorem u3701 : Upper (D 3) (R 3) [34,257,9,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3701
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 88 52 225 193 193 449), lower := (rows 35 259 13 88 52 32 64 128 256), losses := [] }

theorem u3702 : Upper (D 3) (R 3) [34,257,9,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3702
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 259 13 88 81 164 228 164 420), lower := (rows 35 259 13 88 81 32 64 128 256), losses := [] }

theorem u3703 : Upper (D 3) (R 3) [34,257,9,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3703
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 88 84 161 225 161 417), lower := (rows 35 259 13 88 84 32 64 128 256), losses := [] }

theorem u3704 : Upper (D 3) (R 3) [34,257,9,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 88 112 165 197 133 389), lower := (rows 35 259 13 88 112 32 64 128 256), losses := [] }

theorem u3705 : Upper (D 3) (R 3) [34,257,9,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3705
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3706 : Route 9 := (fun mask => (mask,id))

def c3706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3706 : Upper (D 3) (R 3) [34,257,9,80,129] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,129] 13 (by decide) (choices 1) [4,64,128] r3706 c3706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1442
  · exact u1443
  · exact u1444

def r3707 : Route 9 := (fun mask => (mask,id))

def c3707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3707 : Upper (D 3) (R 3) [34,257,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,132] 13 (by decide) (choices 1) [1,64,128] r3707 c3707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1445
  · exact u1446
  · exact u1447

def b3708 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 88 176 229 197 197 453), lower := (rows 35 259 13 88 176 32 64 128 256), losses := [] }

theorem u3708 : Upper (D 3) (R 3) [34,257,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3708
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 88 208 165 229 165 421), lower := (rows 35 259 13 88 208 32 64 128 256), losses := [] }

theorem u3709 : Upper (D 3) (R 3) [34,257,9,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3709
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 104 81 180 212 148 404), lower := (rows 35 259 13 104 81 32 64 128 256), losses := [] }

theorem u3710 : Upper (D 3) (R 3) [34,257,9,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 104 84 177 209 145 401), lower := (rows 35 259 13 104 84 32 64 128 256), losses := [] }

theorem u3711 : Upper (D 3) (R 3) [34,257,9,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3711
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 104 145 244 212 212 468), lower := (rows 35 259 13 104 145 32 64 128 256), losses := [] }

theorem u3712 : Upper (D 3) (R 3) [34,257,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 104 148 241 209 209 465), lower := (rows 35 259 13 104 148 32 64 128 256), losses := [] }

theorem u3713 : Upper (D 3) (R 3) [34,257,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3713
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3714 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 104 208 181 213 149 405), lower := (rows 35 259 13 104 208 32 64 128 256), losses := [] }

theorem u3714 : Upper (D 3) (R 3) [34,257,9,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3714
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3715 : PairBound 9 := { available := 212, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 13 200 49 244 212 212 468), lower := (rows 35 259 13 200 49 32 64 128 256), losses := [] }

theorem u3715 : Upper (D 3) (R 3) [34,257,9,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3715
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3716 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3716 : Upper (D 3) (R 3) [34,257,9,192,36] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,36] 13 (by decide) (choices 1) [1,16,64] r3716 c3716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1448
  · exact u1449
  · exact u1450

def r3717 : Route 9 := (fun mask => (mask,id))

def c3717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3717 : Upper (D 3) (R 3) [34,257,9,192,65] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,65] 13 (by decide) (choices 1) [4,16,128] r3717 c3717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1451
  · exact u1452
  · exact u1453

def b3718 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 13 200 84 177 241 177 433), lower := (rows 35 259 13 200 84 32 64 128 256), losses := [] }

theorem u3718 : Upper (D 3) (R 3) [34,257,9,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3718
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3719 : Route 9 := (fun mask => (mask,id))

def c3719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3719 : Upper (D 3) (R 3) [34,257,9,192,96] 13 := by
  apply FastRouting.sound _ _ [34,257,9,192,96] 13 (by decide) (choices 1) [1,4,16,128] r3719 c3719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1454
  · exact u1455
  · exact u1456
  · exact u1457

#print axioms u3719
end Delivery.IrregularNine14.P03
