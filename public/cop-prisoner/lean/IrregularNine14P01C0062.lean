import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0016

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 13 138 48 242 210 210 466), lower := (rows 53 322 13 138 48 32 64 128 256), losses := [] }

theorem u3720 : Upper (D 1) (R 1) [52,320,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3720
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3721_2 : Upper (D 1) (R 1) [52,320,9,130,64,2] 13 :=
  permutation_upper _ _ _ [52,320,9,130,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u970

theorem m3721_16 : Upper (D 1) (R 1) [52,320,9,130,64,16] 13 :=
  permutation_upper _ _ _ [52,320,9,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u972

def r3721 : Route 9 := (fun mask => (mask,id))

def c3721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3721 : Upper (D 1) (R 1) [52,320,9,130,64] 13 := by
  apply FastRouting.sound _ _ [52,320,9,130,64] 13 (by decide) (choices 1) [2,16,128] r3721 c3721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3721_2
  · exact m3721_16
  · exact u973

def b3722 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 13 138 144 114 114 242 370), lower := (rows 53 322 13 138 144 32 64 128 256), losses := [] }

theorem u3722 : Upper (D 1) (R 1) [52,320,9,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3723 : Route 9 := (fun mask => (mask,id))

def c3723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3723 : Upper (D 1) (R 1) [52,320,9,192,2] 13 := by
  apply FastRouting.sound _ _ [52,320,9,192,2] 13 (by decide) (choices 1) [2,16,128] r3723 c3723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u974
  · exact u975
  · exact u976

def b3724 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 13 200 48 178 210 146 402), lower := (rows 53 322 13 200 48 32 64 128 256), losses := [] }

theorem u3724 : Upper (D 1) (R 1) [52,320,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 13 200 144 50 114 178 306), lower := (rows 53 322 13 200 144 32 64 128 256), losses := [] }

theorem u3725 : Upper (D 1) (R 1) [52,320,9,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3726 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 14 137 18 240 240 240 496), lower := (rows 53 322 14 137 18 32 64 128 256), losses := [] }

theorem u3726 : Upper (D 1) (R 1) [52,320,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 14 137 48 242 210 210 466), lower := (rows 53 322 14 137 48 32 64 128 256), losses := [] }

theorem u3727 : Upper (D 1) (R 1) [52,320,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3727
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3728_2 : Upper (D 1) (R 1) [52,320,10,129,64,2] 13 :=
  permutation_upper _ _ _ [52,320,10,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u977

theorem m3728_16 : Upper (D 1) (R 1) [52,320,10,129,64,16] 13 :=
  permutation_upper _ _ _ [52,320,10,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u978

def r3728 : Route 9 := (fun mask => (mask,id))

def c3728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3728 : Upper (D 1) (R 1) [52,320,10,129,64] 13 := by
  apply FastRouting.sound _ _ [52,320,10,129,64] 13 (by decide) (choices 1) [2,16,128] r3728 c3728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3728_2
  · exact m3728_16
  · exact u979

def b3729 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 14 137 144 114 114 242 370), lower := (rows 53 322 14 137 144 32 64 128 256), losses := [] }

theorem u3729 : Upper (D 1) (R 1) [52,320,10,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3730 : PairBound 9 := { available := 178, camps := [], pairs := [(3,6)], upper := (rows 53 322 76 137 18 178 242 178 434), lower := (rows 53 322 76 137 18 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 50 0 146 274), good := (rows 445 434 12 137 434 32 0 128 256) }] }

theorem u3730 : Upper (D 1) (R 1) [52,320,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3731 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 76 137 48 178 210 146 402), lower := (rows 53 322 76 137 48 32 64 128 256), losses := [] }

theorem u3731 : Upper (D 1) (R 1) [52,320,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3732 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 76 137 144 50 114 178 306), lower := (rows 53 322 76 137 144 32 64 128 256), losses := [] }

theorem u3732 : Upper (D 1) (R 1) [52,320,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3733 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 322 76 138 17 178 242 178 434), lower := (rows 53 322 76 138 17 32 64 128 256), losses := [] }

theorem u3733 : Upper (D 1) (R 1) [52,320,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 177, camps := [], pairs := [(0,6)], upper := (rows 53 322 76 138 18 177 241 177 433), lower := (rows 53 322 76 138 18 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 37 0 133 261), good := (rows 437 274 445 154 18 32 0 128 256) }] }

theorem u3734 : Upper (D 1) (R 1) [52,320,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 76 138 48 179 211 147 403), lower := (rows 53 322 76 138 48 32 64 128 256), losses := [] }

theorem u3735 : Upper (D 1) (R 1) [52,320,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3736 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 76 138 144 51 115 179 307), lower := (rows 53 322 76 138 144 32 64 128 256), losses := [] }

theorem u3736 : Upper (D 1) (R 1) [52,320,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 322 134 11 24 240 240 240 496), lower := (rows 53 322 134 11 24 32 64 128 256), losses := [] }

theorem u3737 : Upper (D 1) (R 1) [52,320,130,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 11 48 248 216 216 472), lower := (rows 53 322 134 11 48 32 64 128 256), losses := [] }

theorem u3738 : Upper (D 1) (R 1) [52,320,130,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3738
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3739_8 : Upper (D 1) (R 1) [52,320,130,3,64,8] 13 :=
  permutation_upper _ _ _ [52,320,130,3,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u980

theorem m3739_16 : Upper (D 1) (R 1) [52,320,130,3,64,16] 13 :=
  permutation_upper _ _ _ [52,320,130,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u981

def r3739 : Route 9 := (fun mask => (mask,id))

def c3739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3739 : Upper (D 1) (R 1) [52,320,130,3,64] 13 := by
  apply FastRouting.sound _ _ [52,320,130,3,64] 13 (by decide) (choices 1) [8,16,128] r3739 c3739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3739_8
  · exact m3739_16
  · exact u982

def b3740 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 11 144 120 120 248 376), lower := (rows 53 322 134 11 144 32 64 128 256), losses := [] }

theorem u3740 : Upper (D 1) (R 1) [52,320,130,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3741 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 53 322 134 26 17 232 232 232 488), lower := (rows 53 322 134 26 17 32 64 128 256), losses := [] }

theorem u3741 : Upper (D 1) (R 1) [52,320,130,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3742 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 53 322 134 26 24 225 225 225 481), lower := (rows 53 322 134 26 24 32 64 128 256), losses := [] }

theorem u3742 : Upper (D 1) (R 1) [52,320,130,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 26 48 233 201 201 457), lower := (rows 53 322 134 26 48 32 64 128 256), losses := [] }

theorem u3743 : Upper (D 1) (R 1) [52,320,130,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3744 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 322 134 26 80 169 233 169 425), lower := (rows 53 322 134 26 80 32 64 128 256), losses := [] }

theorem u3744 : Upper (D 1) (R 1) [52,320,130,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3745 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 26 144 105 105 233 361), lower := (rows 53 322 134 26 144 32 64 128 256), losses := [] }

theorem u3745 : Upper (D 1) (R 1) [52,320,130,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3746 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 134 73 18 184 248 184 440), lower := (rows 53 322 134 73 18 32 64 128 256), losses := [] }

theorem u3746 : Upper (D 1) (R 1) [52,320,130,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3747 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 322 134 73 24 178 242 178 434), lower := (rows 53 322 134 73 24 32 64 128 256), losses := [] }

theorem u3747 : Upper (D 1) (R 1) [52,320,130,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3748 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 73 48 186 218 154 410), lower := (rows 53 322 134 73 48 32 64 128 256), losses := [] }

theorem u3748 : Upper (D 1) (R 1) [52,320,130,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3749 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 73 144 58 122 186 314), lower := (rows 53 322 134 73 144 32 64 128 256), losses := [] }

theorem u3749 : Upper (D 1) (R 1) [52,320,130,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3750 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 322 134 88 17 170 234 170 426), lower := (rows 53 322 134 88 17 32 64 128 256), losses := [] }

theorem u3750 : Upper (D 1) (R 1) [52,320,130,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3751 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 322 134 88 18 169 233 169 425), lower := (rows 53 322 134 88 18 32 64 128 256), losses := [] }

theorem u3751 : Upper (D 1) (R 1) [52,320,130,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 322 134 88 24 163 227 163 419), lower := (rows 53 322 134 88 24 32 64 128 256), losses := [] }

theorem u3752 : Upper (D 1) (R 1) [52,320,130,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3753 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 88 48 171 203 139 395), lower := (rows 53 322 134 88 48 32 64 128 256), losses := [] }

theorem u3753 : Upper (D 1) (R 1) [52,320,130,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3754 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 134 88 144 43 107 171 299), lower := (rows 53 322 134 88 144 32 64 128 256), losses := [] }

theorem u3754 : Upper (D 1) (R 1) [52,320,130,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 53 322 134 152 17 106 106 234 362), lower := (rows 53 322 134 152 17 32 64 128 256), losses := [] }

theorem u3755 : Upper (D 1) (R 1) [52,320,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 322 134 152 18 105 105 233 361), lower := (rows 53 322 134 152 18 32 64 128 256), losses := [] }

theorem u3756 : Upper (D 1) (R 1) [52,320,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 53 322 134 152 24 99 99 227 355), lower := (rows 53 322 134 152 24 32 64 128 256), losses := [] }

theorem u3757 : Upper (D 1) (R 1) [52,320,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3758 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 152 48 107 75 203 331), lower := (rows 53 322 134 152 48 32 64 128 256), losses := [] }

theorem u3758 : Upper (D 1) (R 1) [52,320,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3759 : PairBound 9 := { available := 43, camps := [], pairs := [(3,1)], upper := (rows 53 322 134 152 80 43 107 171 299), lower := (rows 53 322 134 152 80 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 82 32 64 128 256), good := (rows 61 336 156 152 80 32 80 128 256) }] }

theorem u3759 : Upper (D 1) (R 1) [52,320,130,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3759
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 53 322 134 200 17 58 122 186 314), lower := (rows 53 322 134 200 17 32 64 128 256), losses := [] }

theorem u3760 : Upper (D 1) (R 1) [52,320,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 322 134 200 18 57 121 185 313), lower := (rows 53 322 134 200 18 32 64 128 256), losses := [] }

theorem u3761 : Upper (D 1) (R 1) [52,320,130,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 51, camps := [], pairs := [], upper := (rows 53 322 134 200 24 51 115 179 307), lower := (rows 53 322 134 200 24 32 64 128 256), losses := [] }

theorem u3762 : Upper (D 1) (R 1) [52,320,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 134 200 48 59 91 155 283), lower := (rows 53 322 134 200 48 32 64 128 256), losses := [] }

theorem u3763 : Upper (D 1) (R 1) [52,320,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3764 : PairBound 9 := { available := 240, camps := [], pairs := [(2,1)], upper := (rows 53 322 140 11 18 240 240 240 496), lower := (rows 53 322 140 11 18 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 81 145 273), good := (rows 501 320 140 493 496 32 64 128 256) }] }

theorem u3764 : Upper (D 1) (R 1) [52,320,136,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 140 11 48 242 210 210 466), lower := (rows 53 322 140 11 48 32 64 128 256), losses := [] }

theorem u3765 : Upper (D 1) (R 1) [52,320,136,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3765
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3766_2 : Upper (D 1) (R 1) [52,320,136,3,64,2] 13 :=
  permutation_upper _ _ _ [52,320,136,3,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u983

theorem m3766_16 : Upper (D 1) (R 1) [52,320,136,3,64,16] 13 :=
  permutation_upper _ _ _ [52,320,136,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u984

def r3766 : Route 9 := (fun mask => (mask,id))

def c3766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3766 : Upper (D 1) (R 1) [52,320,136,3,64] 13 := by
  apply FastRouting.sound _ _ [52,320,136,3,64] 13 (by decide) (choices 1) [2,16,128] r3766 c3766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3766_2
  · exact m3766_16
  · exact u985

def b3767 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 140 11 144 114 114 242 370), lower := (rows 53 322 140 11 144 32 64 128 256), losses := [] }

theorem u3767 : Upper (D 1) (R 1) [52,320,136,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3768 : Route 9 := (fun mask => (mask,id))

def c3768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3768 : Upper (D 1) (R 1) [52,320,136,65,2] 13 := by
  apply FastRouting.sound _ _ [52,320,136,65,2] 13 (by decide) (choices 1) [2,16,128] r3768 c3768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u986
  · exact u987
  · exact u988

def b3769 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 140 73 48 178 210 146 402), lower := (rows 53 322 140 73 48 32 64 128 256), losses := [] }

theorem u3769 : Upper (D 1) (R 1) [52,320,136,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3770 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 140 73 144 50 114 178 306), lower := (rows 53 322 140 73 144 32 64 128 256), losses := [] }

theorem u3770 : Upper (D 1) (R 1) [52,320,136,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3771 : Route 9 := (fun mask => (mask,id))

def c3771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3771 : Upper (D 1) (R 1) [52,320,192,3,2] 13 := by
  apply FastRouting.sound _ _ [52,320,192,3,2] 13 (by decide) (choices 1) [8,16,128] r3771 c3771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u989
  · exact u990
  · exact u991

def b3772 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 322 196 11 24 178 242 178 434), lower := (rows 53 322 196 11 24 32 64 128 256), losses := [] }

theorem u3772 : Upper (D 1) (R 1) [52,320,192,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3773 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 196 11 48 186 218 154 410), lower := (rows 53 322 196 11 48 32 64 128 256), losses := [] }

theorem u3773 : Upper (D 1) (R 1) [52,320,192,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3774 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 196 11 144 58 122 186 314), lower := (rows 53 322 196 11 144 32 64 128 256), losses := [] }

theorem u3774 : Upper (D 1) (R 1) [52,320,192,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3775 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 322 196 26 17 170 234 170 426), lower := (rows 53 322 196 26 17 32 64 128 256), losses := [] }

theorem u3775 : Upper (D 1) (R 1) [52,320,192,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3776 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 322 196 26 18 169 233 169 425), lower := (rows 53 322 196 26 18 32 64 128 256), losses := [] }

theorem u3776 : Upper (D 1) (R 1) [52,320,192,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3777 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 322 196 26 24 163 227 163 419), lower := (rows 53 322 196 26 24 32 64 128 256), losses := [] }

theorem u3777 : Upper (D 1) (R 1) [52,320,192,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3778 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 322 196 26 48 171 203 139 395), lower := (rows 53 322 196 26 48 32 64 128 256), losses := [] }

theorem u3778 : Upper (D 1) (R 1) [52,320,192,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3779 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 322 196 26 144 43 107 171 299), lower := (rows 53 322 196 26 144 32 64 128 256), losses := [] }

theorem u3779 : Upper (D 1) (R 1) [52,320,192,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3779
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P01
