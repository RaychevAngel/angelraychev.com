import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0010

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 70 261 200 24 178 242 178 434), lower := (rows 51 70 261 200 24 32 64 128 256), losses := [] }

theorem u2700 : Upper (D 1) (R 1) [50,68,257,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 200 48 186 218 154 410), lower := (rows 51 70 261 200 48 32 64 128 256), losses := [] }

theorem u2701 : Upper (D 1) (R 1) [50,68,257,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2701
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2702_2 : Upper (D 1) (R 1) [50,68,257,192,128,2] 13 :=
  permutation_upper _ _ _ [50,68,257,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u609

theorem m2702_8 : Upper (D 1) (R 1) [50,68,257,192,128,8] 13 :=
  permutation_upper _ _ _ [50,68,257,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u610

theorem m2702_16 : Upper (D 1) (R 1) [50,68,257,192,128,16] 13 :=
  permutation_upper _ _ _ [50,68,257,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u611

def r2702 : Route 9 := (fun mask => (mask,id))

def c2702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2702 : Upper (D 1) (R 1) [50,68,257,192,128] 13 := by
  apply FastRouting.sound _ _ [50,68,257,192,128] 13 (by decide) (choices 1) [2,8,16] r2702 c2702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2702_2
  · exact m2702_8
  · exact m2702_16

def b2703 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 268 137 18 240 240 240 496), lower := (rows 51 70 268 137 18 32 64 128 256), losses := [] }

theorem u2703 : Upper (D 1) (R 1) [50,68,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 137 48 242 210 210 466), lower := (rows 51 70 268 137 48 32 64 128 256), losses := [] }

theorem u2704 : Upper (D 1) (R 1) [50,68,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 137 80 178 242 178 434), lower := (rows 51 70 268 137 80 32 64 128 256), losses := [] }

theorem u2705 : Upper (D 1) (R 1) [50,68,264,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2706 : PairBound 9 := { available := 114, camps := [], pairs := [(1,7)], upper := (rows 51 70 268 137 144 114 114 242 370), lower := (rows 51 70 268 137 144 32 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 33 65 0 257), good := (rows 371 70 270 367 16 32 64 0 256) }] }

theorem u2706 : Upper (D 1) (R 1) [50,68,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 70 268 138 17 240 240 240 496), lower := (rows 51 70 268 138 17 32 64 128 256), losses := [] }

theorem u2707 : Upper (D 1) (R 1) [50,68,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 138 48 241 209 209 465), lower := (rows 51 70 268 138 48 32 64 128 256), losses := [] }

theorem u2708 : Upper (D 1) (R 1) [50,68,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 138 80 177 241 177 433), lower := (rows 51 70 268 138 80 32 64 128 256), losses := [] }

theorem u2709 : Upper (D 1) (R 1) [50,68,264,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2709
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2710_1 : Upper (D 1) (R 1) [50,68,264,130,128,1] 13 :=
  permutation_upper _ _ _ [50,68,264,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u612

theorem m2710_16 : Upper (D 1) (R 1) [50,68,264,130,128,16] 13 :=
  permutation_upper _ _ _ [50,68,264,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u613

theorem m2710_64 : Upper (D 1) (R 1) [50,68,264,130,128,64] 13 :=
  permutation_upper _ _ _ [50,68,264,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u614

def r2710 : Route 9 := (fun mask => (mask,id))

def c2710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2710 : Upper (D 1) (R 1) [50,68,264,130,128] 13 := by
  apply FastRouting.sound _ _ [50,68,264,130,128] 13 (by decide) (choices 1) [1,16,64] r2710 c2710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2710_1
  · exact m2710_16
  · exact m2710_64

def b2711 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 70 268 152 17 226 226 226 482), lower := (rows 51 70 268 152 17 32 64 128 256), losses := [] }

theorem u2711 : Upper (D 1) (R 1) [50,68,264,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2712 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 268 152 18 225 225 225 481), lower := (rows 51 70 268 152 18 32 64 128 256), losses := [] }

theorem u2712 : Upper (D 1) (R 1) [50,68,264,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2713 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 268 152 48 227 195 195 451), lower := (rows 51 70 268 152 48 32 64 128 256), losses := [] }

theorem u2713 : Upper (D 1) (R 1) [50,68,264,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 268 152 80 163 227 163 419), lower := (rows 51 70 268 152 80 32 64 128 256), losses := [] }

theorem u2714 : Upper (D 1) (R 1) [50,68,264,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2715 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 70 268 152 144 99 99 227 355), lower := (rows 51 70 268 152 144 32 64 128 256), losses := [] }

theorem u2715 : Upper (D 1) (R 1) [50,68,264,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 388 73 18 184 248 184 440), lower := (rows 51 70 388 73 18 32 64 128 256), losses := [] }

theorem u2716 : Upper (D 1) (R 1) [50,68,384,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 70 388 73 24 178 242 178 434), lower := (rows 51 70 388 73 24 32 64 128 256), losses := [] }

theorem u2717 : Upper (D 1) (R 1) [50,68,384,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 73 48 186 218 154 410), lower := (rows 51 70 388 73 48 32 64 128 256), losses := [] }

theorem u2718 : Upper (D 1) (R 1) [50,68,384,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 388 73 144 58 122 186 314), lower := (rows 51 70 388 73 144 32 64 128 256), losses := [] }

theorem u2719 : Upper (D 1) (R 1) [50,68,384,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2719
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 70 388 88 17 170 234 170 426), lower := (rows 51 70 388 88 17 32 64 128 256), losses := [] }

theorem u2720 : Upper (D 1) (R 1) [50,68,384,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 388 88 18 169 233 169 425), lower := (rows 51 70 388 88 18 32 64 128 256), losses := [] }

theorem u2721 : Upper (D 1) (R 1) [50,68,384,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 70 388 88 24 163 227 163 419), lower := (rows 51 70 388 88 24 32 64 128 256), losses := [] }

theorem u2722 : Upper (D 1) (R 1) [50,68,384,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 88 48 171 203 139 395), lower := (rows 51 70 388 88 48 32 64 128 256), losses := [] }

theorem u2723 : Upper (D 1) (R 1) [50,68,384,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 388 88 144 43 107 171 299), lower := (rows 51 70 388 88 144 32 64 128 256), losses := [] }

theorem u2724 : Upper (D 1) (R 1) [50,68,384,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 388 137 18 120 120 248 376), lower := (rows 51 70 388 137 18 32 64 128 256), losses := [] }

theorem u2725 : Upper (D 1) (R 1) [50,68,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2726 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 51 70 388 137 24 114 114 242 370), lower := (rows 51 70 388 137 24 32 64 128 256), losses := [] }

theorem u2726 : Upper (D 1) (R 1) [50,68,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 137 48 122 90 218 346), lower := (rows 51 70 388 137 48 32 64 128 256), losses := [] }

theorem u2727 : Upper (D 1) (R 1) [50,68,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 137 80 58 122 186 314), lower := (rows 51 70 388 137 80 32 64 128 256), losses := [] }

theorem u2728 : Upper (D 1) (R 1) [50,68,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 51 70 388 152 17 106 106 234 362), lower := (rows 51 70 388 152 17 32 64 128 256), losses := [] }

theorem u2729 : Upper (D 1) (R 1) [50,68,384,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 388 152 18 105 105 233 361), lower := (rows 51 70 388 152 18 32 64 128 256), losses := [] }

theorem u2730 : Upper (D 1) (R 1) [50,68,384,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 51 70 388 152 24 99 99 227 355), lower := (rows 51 70 388 152 24 32 64 128 256), losses := [] }

theorem u2731 : Upper (D 1) (R 1) [50,68,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 152 48 107 75 203 331), lower := (rows 51 70 388 152 48 32 64 128 256), losses := [] }

theorem u2732 : Upper (D 1) (R 1) [50,68,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 152 80 43 107 171 299), lower := (rows 51 70 388 152 80 32 64 128 256), losses := [] }

theorem u2733 : Upper (D 1) (R 1) [50,68,384,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 58, camps := [], pairs := [], upper := (rows 51 70 388 200 17 58 122 186 314), lower := (rows 51 70 388 200 17 32 64 128 256), losses := [] }

theorem u2734 : Upper (D 1) (R 1) [50,68,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 70 388 200 18 57 121 185 313), lower := (rows 51 70 388 200 18 32 64 128 256), losses := [] }

theorem u2735 : Upper (D 1) (R 1) [50,68,384,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 51, camps := [], pairs := [], upper := (rows 51 70 388 200 24 51 115 179 307), lower := (rows 51 70 388 200 24 32 64 128 256), losses := [] }

theorem u2736 : Upper (D 1) (R 1) [50,68,384,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 388 200 48 59 91 155 283), lower := (rows 51 70 388 200 48 32 64 128 256), losses := [] }

theorem u2737 : Upper (D 1) (R 1) [50,68,384,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 194 13 266 20 240 240 240 496), lower := (rows 51 194 13 266 20 32 64 128 256), losses := [] }

theorem u2738 : Upper (D 1) (R 1) [50,192,9,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 13 266 48 244 212 212 468), lower := (rows 51 194 13 266 48 32 64 128 256), losses := [] }

theorem u2739 : Upper (D 1) (R 1) [50,192,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2739
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 13 266 80 180 244 180 436), lower := (rows 51 194 13 266 80 32 64 128 256), losses := [] }

theorem u2740 : Upper (D 1) (R 1) [50,192,9,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 13 268 18 240 240 240 496), lower := (rows 51 194 13 268 18 32 64 128 256), losses := [] }

theorem u2741 : Upper (D 1) (R 1) [50,192,9,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 13 268 48 242 210 210 466), lower := (rows 51 194 13 268 48 32 64 128 256), losses := [] }

theorem u2742 : Upper (D 1) (R 1) [50,192,9,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 13 268 80 178 242 178 434), lower := (rows 51 194 13 268 80 32 64 128 256), losses := [] }

theorem u2743 : Upper (D 1) (R 1) [50,192,9,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 13 328 18 180 244 180 436), lower := (rows 51 194 13 328 18 32 64 128 256), losses := [] }

theorem u2744 : Upper (D 1) (R 1) [50,192,9,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 194 13 328 20 178 242 178 434), lower := (rows 51 194 13 328 20 32 64 128 256), losses := [] }

theorem u2745 : Upper (D 1) (R 1) [50,192,9,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 13 328 48 182 214 150 406), lower := (rows 51 194 13 328 48 32 64 128 256), losses := [] }

theorem u2746 : Upper (D 1) (R 1) [50,192,9,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 13 328 144 54 118 182 310), lower := (rows 51 194 13 328 144 32 64 128 256), losses := [] }

theorem u2747 : Upper (D 1) (R 1) [50,192,9,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 194 14 265 20 240 240 240 496), lower := (rows 51 194 14 265 20 32 64 128 256), losses := [] }

theorem u2748 : Upper (D 1) (R 1) [50,192,10,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 14 265 48 244 212 212 468), lower := (rows 51 194 14 265 48 32 64 128 256), losses := [] }

theorem u2749 : Upper (D 1) (R 1) [50,192,10,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 14 265 80 180 244 180 436), lower := (rows 51 194 14 265 80 32 64 128 256), losses := [] }

theorem u2750 : Upper (D 1) (R 1) [50,192,10,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 194 14 268 17 240 240 240 496), lower := (rows 51 194 14 268 17 32 64 128 256), losses := [] }

theorem u2751 : Upper (D 1) (R 1) [50,192,10,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 14 268 48 241 209 209 465), lower := (rows 51 194 14 268 48 32 64 128 256), losses := [] }

theorem u2752 : Upper (D 1) (R 1) [50,192,10,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 14 268 80 177 241 177 433), lower := (rows 51 194 14 268 80 32 64 128 256), losses := [] }

theorem u2753 : Upper (D 1) (R 1) [50,192,10,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 51 194 14 280 17 228 228 228 484), lower := (rows 51 194 14 280 17 32 64 128 256), losses := [] }

theorem u2754 : Upper (D 1) (R 1) [50,192,10,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 194 14 280 20 225 225 225 481), lower := (rows 51 194 14 280 20 32 64 128 256), losses := [] }

theorem u2755 : Upper (D 1) (R 1) [50,192,10,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2756 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 194 14 280 48 229 197 197 453), lower := (rows 51 194 14 280 48 32 64 128 256), losses := [] }

theorem u2756 : Upper (D 1) (R 1) [50,192,10,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2757 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 14 280 80 165 229 165 421), lower := (rows 51 194 14 280 80 32 64 128 256), losses := [] }

theorem u2757 : Upper (D 1) (R 1) [50,192,10,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2758 : PairBound 9 := { available := 390, camps := [], pairs := [], upper := (rows 51 194 28 104 17 422 454 390 390), lower := (rows 51 194 28 104 17 32 64 128 256), losses := [] }

theorem u2758 : Upper (D 1) (R 1) [50,192,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 28 104 18 421 453 389 389), lower := (rows 51 194 28 104 18 32 64 128 256), losses := [] }

theorem u2759 : Upper (D 1) (R 1) [50,192,24,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2759
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P01
