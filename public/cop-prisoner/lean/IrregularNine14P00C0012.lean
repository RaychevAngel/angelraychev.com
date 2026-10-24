import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0001
import IrregularNine14P00C0002

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 69, camps := [], pairs := [(2,0)], upper := (rows 275 35 28 104 144 160 69 197 325), lower := (rows 275 35 28 104 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 64 128 256), good := (rows 306 50 60 124 176 176 64 176 256) }] }

theorem u720 : Upper (D 0) (R 0) [274,33,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b720
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 44 88 144 33 196 196 452), lower := (rows 275 35 44 88 144 33 64 128 256), losses := [] }

theorem u721 : Upper (D 0) (R 0) [274,33,40,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b721
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 44 88 144 36 193 193 449), lower := (rows 275 35 44 88 144 36 64 128 256), losses := [] }

theorem u722 : Upper (D 0) (R 0) [274,33,40,80,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b722
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 44 88 144 96 197 133 389), lower := (rows 275 35 44 88 144 96 64 128 256), losses := [] }

theorem u723 : Upper (D 0) (R 0) [274,33,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b723
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 69, camps := [], pairs := [(2,0)], upper := (rows 275 35 44 88 144 160 69 197 325), lower := (rows 275 35 44 88 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 64 128 256), good := (rows 306 50 60 124 176 176 64 176 256) }] }

theorem u724 : Upper (D 0) (R 0) [274,33,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b724
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 44 200 80 33 212 148 404), lower := (rows 275 35 44 200 80 33 64 128 256), losses := [] }

theorem u725 : Upper (D 0) (R 0) [274,33,40,192,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b725
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 35 44 200 80 36 209 145 401), lower := (rows 275 35 44 200 80 36 64 128 256), losses := [] }

theorem u726 : Upper (D 0) (R 0) [274,33,40,192,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b726
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 44 200 80 48 197 133 389), lower := (rows 275 35 44 200 80 48 64 128 256), losses := [] }

theorem u727 : Upper (D 0) (R 0) [274,33,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b727
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 44 200 80 160 85 149 277), lower := (rows 275 35 44 200 80 160 64 128 256), losses := [] }

theorem u728 : Upper (D 0) (R 0) [274,33,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b728
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 76 80 33 200 136 392), lower := (rows 275 35 52 76 80 33 64 128 256), losses := [] }

theorem u729 : Upper (D 0) (R 0) [274,33,48,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b729
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 35 52 76 80 40 193 129 385), lower := (rows 275 35 52 76 80 40 64 128 256), losses := [] }

theorem u730 : Upper (D 0) (R 0) [274,33,48,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b730
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r731 : Route 9 := (fun mask => (mask,id))

def c731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u731 : Upper (D 0) (R 0) [274,33,48,68,64,128] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,64,128] 13 (by decide) (choices 1) [1,8,128] r731 c731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u106
  · exact u107
  · exact u108

def b732 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 76 144 33 200 200 456), lower := (rows 275 35 52 76 144 33 64 128 256), losses := [] }

theorem u732 : Upper (D 0) (R 0) [274,33,48,68,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b732
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 35 52 76 144 40 193 193 449), lower := (rows 275 35 52 76 144 40 64 128 256), losses := [] }

theorem u733 : Upper (D 0) (R 0) [274,33,48,68,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b733
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r734 : Route 9 := (fun mask => (mask,id))

def c734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u734 : Upper (D 0) (R 0) [274,33,48,68,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,128,64] 13 (by decide) (choices 1) [1,8,128] r734 c734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u109
  · exact u110
  · exact u111

def b735 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 52 76 144 160 73 201 329), lower := (rows 275 35 52 76 144 160 64 128 256), losses := [] }

theorem u735 : Upper (D 0) (R 0) [274,33,48,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b735
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 52 200 80 33 204 140 396), lower := (rows 275 35 52 200 80 33 64 128 256), losses := [] }

theorem u736 : Upper (D 0) (R 0) [274,33,48,192,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b736
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 275 35 52 200 80 36 201 137 393), lower := (rows 275 35 52 200 80 36 64 128 256), losses := [] }

theorem u737 : Upper (D 0) (R 0) [274,33,48,192,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b737
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 275 35 52 200 80 40 197 133 389), lower := (rows 275 35 52 200 80 40 64 128 256), losses := [] }

theorem u738 : Upper (D 0) (R 0) [274,33,48,192,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b738
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 275 35 52 200 80 160 77 141 269), lower := (rows 275 35 52 200 80 160 64 128 256), losses := [] }

theorem u739 : Upper (D 0) (R 0) [274,33,48,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b739
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 152 80 33 228 164 420), lower := (rows 275 35 76 152 80 33 64 128 256), losses := [] }

theorem u740 : Upper (D 0) (R 0) [274,33,72,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b740
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 275 35 76 152 80 36 225 161 417), lower := (rows 275 35 76 152 80 36 64 128 256), losses := [] }

theorem u741 : Upper (D 0) (R 0) [274,33,72,144,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b741
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r742 : Route 9 := (fun mask => (mask,id))

def c742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u742 : Upper (D 0) (R 0) [274,33,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144,64,128] 13 (by decide) (choices 1) [1,4,32] r742 c742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u112
  · exact u113
  · exact u114

def b743 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 80 33 212 148 404), lower := (rows 275 35 76 168 80 33 64 128 256), losses := [] }

theorem u743 : Upper (D 0) (R 0) [274,33,72,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b743
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 35 76 168 80 36 209 145 401), lower := (rows 275 35 76 168 80 36 64 128 256), losses := [] }

theorem u744 : Upper (D 0) (R 0) [274,33,72,160,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b744
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 76 168 80 48 197 133 389), lower := (rows 275 35 76 168 80 48 64 128 256), losses := [] }

theorem u745 : Upper (D 0) (R 0) [274,33,72,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b745
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 76 168 80 160 85 149 277), lower := (rows 275 35 76 168 80 160 64 128 256), losses := [] }

theorem u746 : Upper (D 0) (R 0) [274,33,72,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b746
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 144 33 84 212 340), lower := (rows 275 35 76 168 144 33 64 128 256), losses := [] }

theorem u747 : Upper (D 0) (R 0) [274,33,72,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b747
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 35 76 168 144 36 81 209 337), lower := (rows 275 35 76 168 144 36 64 128 256), losses := [] }

theorem u748 : Upper (D 0) (R 0) [274,33,72,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b748
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 76 168 144 48 69 197 325), lower := (rows 275 35 76 168 144 48 64 128 256), losses := [] }

theorem u749 : Upper (D 0) (R 0) [274,33,72,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b749
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r750 : Route 9 := (fun mask => (mask,id))

def c750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u750 : Upper (D 0) (R 0) [274,33,72,160,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,128,64] 13 (by decide) (choices 1) [1,4,16] r750 c750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u115
  · exact u116
  · exact u117

def b751 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 84 104 144 33 204 140 396), lower := (rows 275 35 84 104 144 33 64 128 256), losses := [] }

theorem u751 : Upper (D 0) (R 0) [274,33,80,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b751
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 275 35 84 104 144 36 201 137 393), lower := (rows 275 35 84 104 144 36 64 128 256), losses := [] }

theorem u752 : Upper (D 0) (R 0) [274,33,80,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b752
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 275 35 84 104 144 40 197 133 389), lower := (rows 275 35 84 104 144 40 64 128 256), losses := [] }

theorem u753 : Upper (D 0) (R 0) [274,33,80,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b753
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 13, camps := [], pairs := [(2,0)], upper := (rows 275 35 84 104 144 160 77 141 269), lower := (rows 275 35 84 104 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 12 176 176 64 128 256), good := (rows 306 50 124 124 176 176 64 176 256) }] }

theorem u754 : Upper (D 0) (R 0) [274,33,80,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b754
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 84 168 144 33 76 204 332), lower := (rows 275 35 84 168 144 33 64 128 256), losses := [] }

theorem u755 : Upper (D 0) (R 0) [274,33,80,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b755
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 275 35 84 168 144 36 73 201 329), lower := (rows 275 35 84 168 144 36 64 128 256), losses := [] }

theorem u756 : Upper (D 0) (R 0) [274,33,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b756
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 275 35 84 168 144 40 69 197 325), lower := (rows 275 35 84 168 144 40 64 128 256), losses := [] }

theorem u757 : Upper (D 0) (R 0) [274,33,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b757
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r758 : Route 9 := (fun mask => (mask,id))

def c758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u758 : Upper (D 0) (R 0) [274,33,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160,128,64] 13 (by decide) (choices 1) [1,4,8] r758 c758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u118
  · exact u119
  · exact u120

def b759 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 100 200 144 33 92 156 284), lower := (rows 275 35 100 200 144 33 64 128 256), losses := [] }

theorem u759 : Upper (D 0) (R 0) [274,33,96,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b759
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 275 35 100 200 144 36 89 153 281), lower := (rows 275 35 100 200 144 36 64 128 256), losses := [] }

theorem u760 : Upper (D 0) (R 0) [274,33,96,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b760
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 275 35 100 200 144 40 85 149 277), lower := (rows 275 35 100 200 144 40 64 128 256), losses := [] }

theorem u761 : Upper (D 0) (R 0) [274,33,96,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b761
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 275 35 100 200 144 48 77 141 269), lower := (rows 275 35 100 200 144 48 64 128 256), losses := [] }

theorem u762 : Upper (D 0) (R 0) [274,33,96,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b762
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 56 144 33 200 200 456), lower := (rows 275 38 69 56 144 33 64 128 256), losses := [] }

theorem u763 : Upper (D 0) (R 0) [274,36,65,48,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b763
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 38 69 56 144 40 193 193 449), lower := (rows 275 38 69 56 144 40 64 128 256), losses := [] }

theorem u764 : Upper (D 0) (R 0) [274,36,65,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b764
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 69 56 144 96 201 137 393), lower := (rows 275 38 69 56 144 96 64 128 256), losses := [] }

theorem u765 : Upper (D 0) (R 0) [274,36,65,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b765
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 69 56 144 160 73 201 329), lower := (rows 275 38 69 56 144 160 64 128 256), losses := [] }

theorem u766 : Upper (D 0) (R 0) [274,36,65,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b766
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 88 144 33 232 168 424), lower := (rows 275 38 69 88 144 33 64 128 256), losses := [] }

theorem u767 : Upper (D 0) (R 0) [274,36,65,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b767
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 275 38 69 88 144 40 225 161 417), lower := (rows 275 38 69 88 144 40 64 128 256), losses := [] }

theorem u768 : Upper (D 0) (R 0) [274,36,65,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b768
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r769 : Route 9 := (fun mask => (mask,id))

def c769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u769 : Upper (D 0) (R 0) [274,36,65,80,128,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80,128,128] 13 (by decide) (choices 1) [1,8,32] r769 c769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u121
  · exact u122
  · exact u123

def b770 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 104 144 33 216 152 408), lower := (rows 275 38 69 104 144 33 64 128 256), losses := [] }

theorem u770 : Upper (D 0) (R 0) [274,36,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b770
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 38 69 104 144 40 209 145 401), lower := (rows 275 38 69 104 144 40 64 128 256), losses := [] }

theorem u771 : Upper (D 0) (R 0) [274,36,65,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b771
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 137, camps := [], pairs := [(1,0)], upper := (rows 275 38 69 104 144 48 201 137 393), lower := (rows 275 38 69 104 144 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 144 177 64 128 256), good := (rows 306 46 110 104 176 48 64 176 256) }] }

theorem u772 : Upper (D 0) (R 0) [274,36,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b772
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r773 : Route 9 := (fun mask => (mask,id))

def c773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u773 : Upper (D 0) (R 0) [274,36,65,96,128,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96,128,128] 13 (by decide) (choices 1) [1,8,16] r773 c773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u124
  · exact u125
  · exact u126

def b774 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 275 38 69 137 144 40 112 240 368), lower := (rows 275 38 69 137 144 40 64 128 256), losses := [] }

theorem u774 : Upper (D 0) (R 0) [274,36,65,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b774
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 104, camps := [], pairs := [(1,0)], upper := (rows 275 38 69 137 144 48 104 232 360), lower := (rows 275 38 69 137 144 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 152 185 72 136 264), good := (rows 306 38 102 504 176 48 64 176 256) }] }

theorem u775 : Upper (D 0) (R 0) [274,36,65,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b775
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 69 137 144 96 120 184 312), lower := (rows 275 38 69 137 144 96 64 128 256), losses := [] }

theorem u776 : Upper (D 0) (R 0) [274,36,65,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b776
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 168 144 33 88 216 344), lower := (rows 275 38 69 168 144 33 64 128 256), losses := [] }

theorem u777 : Upper (D 0) (R 0) [274,36,65,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b777
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 38 69 168 144 40 81 209 337), lower := (rows 275 38 69 168 144 40 64 128 256), losses := [] }

theorem u778 : Upper (D 0) (R 0) [274,36,65,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b778
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 275 38 69 168 144 48 73 201 329), lower := (rows 275 38 69 168 144 48 64 128 256), losses := [] }

theorem u779 : Upper (D 0) (R 0) [274,36,65,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b779
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P00
