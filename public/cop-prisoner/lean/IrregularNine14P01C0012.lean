import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000
import IrregularNine14P01C0001

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 266 48 96 216 152 408), lower := (rows 53 67 134 266 48 96 64 128 256), losses := [] }

theorem u720 : Upper (D 1) (R 1) [52,65,130,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 266 80 160 120 184 312), lower := (rows 53 67 134 266 80 160 64 128 256), losses := [] }

theorem u721 : Upper (D 1) (R 1) [52,65,130,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 280 80 34 232 168 424), lower := (rows 53 67 134 280 80 34 64 128 256), losses := [] }

theorem u722 : Upper (D 1) (R 1) [52,65,130,272,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 67 134 280 80 40 226 162 418), lower := (rows 53 67 134 280 80 40 64 128 256), losses := [] }

theorem u723 : Upper (D 1) (R 1) [52,65,130,272,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 134 280 80 160 106 170 298), lower := (rows 53 67 134 280 80 160 64 128 256), losses := [] }

theorem u724 : Upper (D 1) (R 1) [52,65,130,272,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 392 18 96 120 184 312), lower := (rows 53 67 134 392 18 96 64 128 256), losses := [] }

theorem u725 : Upper (D 1) (R 1) [52,65,130,384,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 67 134 392 24 96 114 178 306), lower := (rows 53 67 134 392 24 96 64 128 256), losses := [] }

theorem u726 : Upper (D 1) (R 1) [52,65,130,384,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 134 392 48 96 90 154 282), lower := (rows 53 67 134 392 48 96 64 128 256), losses := [] }

theorem u727 : Upper (D 1) (R 1) [52,65,130,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 140 266 18 48 224 224 480), lower := (rows 53 67 140 266 18 48 64 128 256), losses := [] }

theorem u728 : Upper (D 1) (R 1) [52,65,136,258,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 176, camps := [], pairs := [(2,6)], upper := (rows 53 67 140 266 18 96 240 176 432), lower := (rows 53 67 140 266 18 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 10 26 32 0 129 257), good := (rows 437 415 156 286 30 32 0 128 256) }] }

theorem u729 : Upper (D 1) (R 1) [52,65,136,258,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 140 266 18 160 112 240 368), lower := (rows 53 67 140 266 18 160 64 128 256), losses := [] }

theorem u730 : Upper (D 1) (R 1) [52,65,136,258,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 140 266 48 96 210 146 402), lower := (rows 53 67 140 266 48 96 64 128 256), losses := [] }

theorem u731 : Upper (D 1) (R 1) [52,65,136,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 140 266 80 160 114 178 306), lower := (rows 53 67 140 266 80 160 64 128 256), losses := [] }

theorem u732 : Upper (D 1) (R 1) [52,65,136,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 140 328 18 34 240 176 432), lower := (rows 53 67 140 328 18 34 64 128 256), losses := [] }

theorem u733 : Upper (D 1) (R 1) [52,65,136,320,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 140 328 18 48 226 162 418), lower := (rows 53 67 140 328 18 48 64 128 256), losses := [] }

theorem u734 : Upper (D 1) (R 1) [52,65,136,320,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 140 328 18 160 114 178 306), lower := (rows 53 67 140 328 18 160 64 128 256), losses := [] }

theorem u735 : Upper (D 1) (R 1) [52,65,136,320,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 88 144 34 232 168 424), lower := (rows 53 67 262 88 144 34 64 128 256), losses := [] }

theorem u736 : Upper (D 1) (R 1) [52,65,258,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 67 262 88 144 40 226 162 418), lower := (rows 53 67 262 88 144 40 64 128 256), losses := [] }

theorem u737 : Upper (D 1) (R 1) [52,65,258,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 262 88 144 160 106 170 298), lower := (rows 53 67 262 88 144 160 64 128 256), losses := [] }

theorem u738 : Upper (D 1) (R 1) [52,65,258,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 67 262 138 24 96 240 176 432), lower := (rows 53 67 262 138 24 96 64 128 256), losses := [] }

theorem u739 : Upper (D 1) (R 1) [52,65,258,130,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b739
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 53 67 262 138 24 160 112 240 368), lower := (rows 53 67 262 138 24 160 64 128 256), losses := [] }

theorem u740 : Upper (D 1) (R 1) [52,65,258,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b740
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 138 48 96 216 152 408), lower := (rows 53 67 262 138 48 96 64 128 256), losses := [] }

theorem u741 : Upper (D 1) (R 1) [52,65,258,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 138 48 160 88 216 344), lower := (rows 53 67 262 138 48 160 64 128 256), losses := [] }

theorem u742 : Upper (D 1) (R 1) [52,65,258,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r743 : Route 9 := (fun mask => (mask,id))

def c743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u743 : Upper (D 1) (R 1) [52,65,258,130,64,128] 13 := by
  apply FastRouting.sound _ _ [52,65,258,130,64,128] 13 (by decide) (choices 1) [8,16,32] r743 c743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u53
  · exact u54
  · exact u55

def b744 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 152 80 34 232 168 424), lower := (rows 53 67 262 152 80 34 64 128 256), losses := [] }

theorem u744 : Upper (D 1) (R 1) [52,65,258,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 67 262 152 80 40 226 162 418), lower := (rows 53 67 262 152 80 40 64 128 256), losses := [] }

theorem u745 : Upper (D 1) (R 1) [52,65,258,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r746 : Route 9 := (fun mask => (mask,id))

def c746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u746 : Upper (D 1) (R 1) [52,65,258,144,64,128] 13 := by
  apply FastRouting.sound _ _ [52,65,258,144,64,128] 13 (by decide) (choices 1) [2,8,32] r746 c746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u56
  · exact u57
  · exact u58

def b747 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 200 18 160 120 184 312), lower := (rows 53 67 262 200 18 160 64 128 256), losses := [] }

theorem u747 : Upper (D 1) (R 1) [52,65,258,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 67 262 200 24 160 114 178 306), lower := (rows 53 67 262 200 24 160 64 128 256), losses := [] }

theorem u748 : Upper (D 1) (R 1) [52,65,258,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 262 200 48 160 90 154 282), lower := (rows 53 67 262 200 48 160 64 128 256), losses := [] }

theorem u749 : Upper (D 1) (R 1) [52,65,258,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 268 138 18 48 224 224 480), lower := (rows 53 67 268 138 18 48 64 128 256), losses := [] }

theorem u750 : Upper (D 1) (R 1) [52,65,264,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 176, camps := [], pairs := [(2,6)], upper := (rows 53 67 268 138 18 96 240 176 432), lower := (rows 53 67 268 138 18 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 10 26 32 0 129 257), good := (rows 437 415 284 158 30 32 0 128 256) }] }

theorem u751 : Upper (D 1) (R 1) [52,65,264,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 268 138 18 160 112 240 368), lower := (rows 53 67 268 138 18 160 64 128 256), losses := [] }

theorem u752 : Upper (D 1) (R 1) [52,65,264,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 268 138 48 96 210 146 402), lower := (rows 53 67 268 138 48 96 64 128 256), losses := [] }

theorem u753 : Upper (D 1) (R 1) [52,65,264,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 268 138 80 160 114 178 306), lower := (rows 53 67 268 138 80 160 64 128 256), losses := [] }

theorem u754 : Upper (D 1) (R 1) [52,65,264,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 268 200 18 34 240 176 432), lower := (rows 53 67 268 200 18 34 64 128 256), losses := [] }

theorem u755 : Upper (D 1) (R 1) [52,65,264,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 268 200 18 48 226 162 418), lower := (rows 53 67 268 200 18 48 64 128 256), losses := [] }

theorem u756 : Upper (D 1) (R 1) [52,65,264,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 67 268 200 18 160 114 178 306), lower := (rows 53 67 268 200 18 160 64 128 256), losses := [] }

theorem u757 : Upper (D 1) (R 1) [52,65,264,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 53 67 388 138 18 40 112 240 368), lower := (rows 53 67 388 138 18 40 64 128 256), losses := [] }

theorem u758 : Upper (D 1) (R 1) [52,65,384,130,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 388 138 18 48 104 232 360), lower := (rows 53 67 388 138 18 48 64 128 256), losses := [] }

theorem u759 : Upper (D 1) (R 1) [52,65,384,130,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b759
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r760 : Route 9 := (fun mask => (mask,id))

def c760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u760 : Upper (D 1) (R 1) [52,65,384,130,2,64] 13 := by
  apply FastRouting.sound _ _ [52,65,384,130,2,64] 13 (by decide) (choices 1) [8,16,32] r760 c760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u59
  · exact u60
  · exact u61

def b761 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 67 388 138 24 96 114 178 306), lower := (rows 53 67 388 138 24 96 64 128 256), losses := [] }

theorem u761 : Upper (D 1) (R 1) [52,65,384,130,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 67 388 138 48 96 90 154 282), lower := (rows 53 67 388 138 48 96 64 128 256), losses := [] }

theorem u762 : Upper (D 1) (R 1) [52,65,384,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b762
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 388 152 18 34 104 232 360), lower := (rows 53 67 388 152 18 34 64 128 256), losses := [] }

theorem u763 : Upper (D 1) (R 1) [52,65,384,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 67 388 152 18 40 98 226 354), lower := (rows 53 67 388 152 18 40 64 128 256), losses := [] }

theorem u764 : Upper (D 1) (R 1) [52,65,384,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r765 : Route 9 := (fun mask => (mask,id))

def c765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u765 : Upper (D 1) (R 1) [52,65,384,144,2,64] 13 := by
  apply FastRouting.sound _ _ [52,65,384,144,2,64] 13 (by decide) (choices 1) [2,8,32] r765 c765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u62
  · exact u63
  · exact u64

def r766 : Route 9 := (fun mask => (mask,id))

def c766 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u766 : Upper (D 1) (R 1) [52,65,384,144,64,2] 13 := by
  apply FastRouting.sound _ _ [52,65,384,144,64,2] 13 (by decide) (choices 1) [2,8,32] r766 c766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u65
  · exact u66
  · exact u67

def b767 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 67 388 152 80 40 98 162 290), lower := (rows 53 67 388 152 80 40 64 128 256), losses := [] }

theorem u767 : Upper (D 1) (R 1) [52,65,384,144,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 388 200 18 34 120 184 312), lower := (rows 53 67 388 200 18 34 64 128 256), losses := [] }

theorem u768 : Upper (D 1) (R 1) [52,65,384,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 67 388 200 18 40 114 178 306), lower := (rows 53 67 388 200 18 40 64 128 256), losses := [] }

theorem u769 : Upper (D 1) (R 1) [52,65,384,192,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 388 200 18 48 106 170 298), lower := (rows 53 67 388 200 18 48 64 128 256), losses := [] }

theorem u770 : Upper (D 1) (R 1) [52,65,384,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 53, targets := 128 }], pairs := [(0,7)], upper := (rows 53 74 7 392 18 96 240 176 432), lower := (rows 53 74 7 392 18 96 64 128 256), losses := [] }

theorem u771 : Upper (D 1) (R 1) [52,72,3,384,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 7 392 18 160 112 240 368), lower := (rows 53 74 7 392 18 160 64 128 256), losses := [] }

theorem u772 : Upper (D 1) (R 1) [52,72,3,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 7 392 48 96 210 146 402), lower := (rows 53 74 7 392 48 96 64 128 256), losses := [] }

theorem u773 : Upper (D 1) (R 1) [52,72,3,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 7 392 48 160 82 210 338), lower := (rows 53 74 7 392 48 160 64 128 256), losses := [] }

theorem u774 : Upper (D 1) (R 1) [52,72,3,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b774
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r775 : Route 9 := (fun mask => (mask,id))

def c775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u775 : Upper (D 1) (R 1) [52,72,3,384,64,128] 13 := by
  apply FastRouting.sound _ _ [52,72,3,384,64,128] 13 (by decide) (choices 1) [2,16,32] r775 c775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u68
  · exact u69
  · exact u70

def b776 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 133 266 18 96 240 176 432), lower := (rows 53 74 133 266 18 96 64 128 256), losses := [] }

theorem u776 : Upper (D 1) (R 1) [52,72,129,258,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b776
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 133 266 48 96 210 146 402), lower := (rows 53 74 133 266 48 96 64 128 256), losses := [] }

theorem u777 : Upper (D 1) (R 1) [52,72,129,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 133 266 80 160 114 178 306), lower := (rows 53 74 133 266 80 160 64 128 256), losses := [] }

theorem u778 : Upper (D 1) (R 1) [52,72,129,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 265 18 96 240 176 432), lower := (rows 53 74 134 265 18 96 64 128 256), losses := [] }

theorem u779 : Upper (D 1) (R 1) [52,72,130,257,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b779
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P01
