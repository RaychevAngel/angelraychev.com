import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b720 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 266 56 36 65 168 296), lower := (rows 7 67 148 266 56 36 65 128 256), losses := [] }

theorem u720 : Upper (D 5) (R 5) [6,65,144,258,40,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 148 266 56 36 72 161 289), lower := (rows 7 67 148 266 56 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 88 127 88 131 259), good := (rows 421 501 244 508 124 36 124 128 256) }] }

theorem u721 : Upper (D 5) (R 5) [6,65,144,258,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b721
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 148 266 56 36 96 137 265), lower := (rows 7 67 148 266 56 36 96 128 256), losses := [] }

theorem u722 : Upper (D 5) (R 5) [6,65,144,258,40,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 268 56 33 66 168 296), lower := (rows 7 67 148 268 56 33 66 128 256), losses := [] }

theorem u723 : Upper (D 5) (R 5) [6,65,144,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 268 56 33 72 162 290), lower := (rows 7 67 148 268 56 33 72 128 256), losses := [] }

theorem u724 : Upper (D 5) (R 5) [6,65,144,260,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 98, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 67 148 268 56 33 96 138 266), lower := (rows 7 67 148 268 56 33 96 128 256), losses := [] }

theorem u725 : Upper (D 5) (R 5) [6,65,144,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 148 268 56 34 65 168 296), lower := (rows 7 67 148 268 56 34 65 128 256), losses := [] }

theorem u726 : Upper (D 5) (R 5) [6,65,144,260,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 148 268 56 34 72 161 289), lower := (rows 7 67 148 268 56 34 72 128 256), losses := [] }

theorem u727 : Upper (D 5) (R 5) [6,65,144,260,40,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 148 268 56 34 96 137 265), lower := (rows 7 67 148 268 56 34 96 128 256), losses := [] }

theorem u728 : Upper (D 5) (R 5) [6,65,144,260,40,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 25 56 288 66 140 268), lower := (rows 7 67 164 25 56 288 66 128 256), losses := [] }

theorem u729 : Upper (D 5) (R 5) [6,65,160,17,40,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 25 56 288 68 138 266), lower := (rows 7 67 164 25 56 288 68 128 256), losses := [] }

theorem u730 : Upper (D 5) (R 5) [6,65,160,17,40,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 25 56 288 72 134 262), lower := (rows 7 67 164 25 56 288 72 128 256), losses := [] }

theorem u731 : Upper (D 5) (R 5) [6,65,160,17,40,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 25 276 40 66 168 296), lower := (rows 7 67 164 25 276 40 66 128 256), losses := [] }

theorem u732 : Upper (D 5) (R 5) [6,65,160,17,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b732
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 25 276 40 72 162 290), lower := (rows 7 67 164 25 276 40 72 128 256), losses := [] }

theorem u733 : Upper (D 5) (R 5) [6,65,160,17,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 25 276 40 96 138 266), lower := (rows 7 67 164 25 276 40 96 128 256), losses := [] }

theorem u734 : Upper (D 5) (R 5) [6,65,160,17,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 25 304 40 66 140 268), lower := (rows 7 67 164 25 304 40 66 128 256), losses := [] }

theorem u735 : Upper (D 5) (R 5) [6,65,160,17,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 25 304 40 68 138 266), lower := (rows 7 67 164 25 304 40 68 128 256), losses := [] }

theorem u736 : Upper (D 5) (R 5) [6,65,160,17,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 66, targets := 4 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,2),(1,5)], upper := (rows 7 67 164 25 304 40 72 134 262), lower := (rows 7 67 164 25 304 40 72 128 256), losses := [] }

theorem u737 : Upper (D 5) (R 5) [6,65,160,17,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 26 56 288 65 140 268), lower := (rows 7 67 164 26 56 288 65 128 256), losses := [] }

theorem u738 : Upper (D 5) (R 5) [6,65,160,18,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 26 56 288 68 137 265), lower := (rows 7 67 164 26 56 288 68 128 256), losses := [] }

theorem u739 : Upper (D 5) (R 5) [6,65,160,18,40,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 26 56 288 72 133 261), lower := (rows 7 67 164 26 56 288 72 128 256), losses := [] }

theorem u740 : Upper (D 5) (R 5) [6,65,160,18,40,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 26 276 40 65 168 296), lower := (rows 7 67 164 26 276 40 65 128 256), losses := [] }

theorem u741 : Upper (D 5) (R 5) [6,65,160,18,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 26 276 40 72 161 289), lower := (rows 7 67 164 26 276 40 72 128 256), losses := [] }

theorem u742 : Upper (D 5) (R 5) [6,65,160,18,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 26 276 40 96 137 265), lower := (rows 7 67 164 26 276 40 96 128 256), losses := [] }

theorem u743 : Upper (D 5) (R 5) [6,65,160,18,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 26 304 40 65 140 268), lower := (rows 7 67 164 26 304 40 65 128 256), losses := [] }

theorem u744 : Upper (D 5) (R 5) [6,65,160,18,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 26 304 40 68 137 265), lower := (rows 7 67 164 26 304 40 68 128 256), losses := [] }

theorem u745 : Upper (D 5) (R 5) [6,65,160,18,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 164 26 304 40 72 133 261), lower := (rows 7 67 164 26 304 40 72 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 26 104 104 131 259), good := (rows 405 501 228 508 368 124 124 128 256) }] }

theorem u746 : Upper (D 5) (R 5) [6,65,160,18,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 28 273 40 66 168 296), lower := (rows 7 67 164 28 273 40 66 128 256), losses := [] }

theorem u747 : Upper (D 5) (R 5) [6,65,160,20,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 28 273 40 72 162 290), lower := (rows 7 67 164 28 273 40 72 128 256), losses := [] }

theorem u748 : Upper (D 5) (R 5) [6,65,160,20,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 28 273 40 96 138 266), lower := (rows 7 67 164 28 273 40 96 128 256), losses := [] }

theorem u749 : Upper (D 5) (R 5) [6,65,160,20,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 28 274 40 65 168 296), lower := (rows 7 67 164 28 274 40 65 128 256), losses := [] }

theorem u750 : Upper (D 5) (R 5) [6,65,160,20,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 28 274 40 72 161 289), lower := (rows 7 67 164 28 274 40 72 128 256), losses := [] }

theorem u751 : Upper (D 5) (R 5) [6,65,160,20,258,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 28 274 40 96 137 265), lower := (rows 7 67 164 28 274 40 96 128 256), losses := [] }

theorem u752 : Upper (D 5) (R 5) [6,65,160,20,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 28 280 33 66 168 296), lower := (rows 7 67 164 28 280 33 66 128 256), losses := [] }

theorem u753 : Upper (D 5) (R 5) [6,65,160,20,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 28 280 33 72 162 290), lower := (rows 7 67 164 28 280 33 72 128 256), losses := [] }

theorem u754 : Upper (D 5) (R 5) [6,65,160,20,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 28 280 33 96 138 266), lower := (rows 7 67 164 28 280 33 96 128 256), losses := [] }

theorem u755 : Upper (D 5) (R 5) [6,65,160,20,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 28 280 34 65 168 296), lower := (rows 7 67 164 28 280 34 65 128 256), losses := [] }

theorem u756 : Upper (D 5) (R 5) [6,65,160,20,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 28 280 34 72 161 289), lower := (rows 7 67 164 28 280 34 72 128 256), losses := [] }

theorem u757 : Upper (D 5) (R 5) [6,65,160,20,264,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 164 28 280 34 96 137 265), lower := (rows 7 67 164 28 280 34 96 128 256), losses := [] }

theorem u758 : Upper (D 5) (R 5) [6,65,160,20,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 41 280 48 66 140 268), lower := (rows 7 67 164 41 280 48 66 128 256), losses := [] }

theorem u759 : Upper (D 5) (R 5) [6,65,160,33,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b759
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 41 280 48 68 138 266), lower := (rows 7 67 164 41 280 48 68 128 256), losses := [] }

theorem u760 : Upper (D 5) (R 5) [6,65,160,33,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 164 41 280 48 72 134 262), lower := (rows 7 67 164 41 280 48 72 128 256), losses := [] }

theorem u761 : Upper (D 5) (R 5) [6,65,160,33,264,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 42 276 48 65 136 264), lower := (rows 7 67 164 42 276 48 65 128 256), losses := [] }

theorem u762 : Upper (D 5) (R 5) [6,65,160,34,260,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r763 : Route 9 := (fun mask => (mask,id))

def c763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u763 : Upper (D 5) (R 5) [6,65,160,34,260,16,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,260,16,8] 13 (by decide) (choices 1) [1,8] r763 c763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u48
  · exact u49

def b764 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 42 280 48 65 140 268), lower := (rows 7 67 164 42 280 48 65 128 256), losses := [] }

theorem u764 : Upper (D 5) (R 5) [6,65,160,34,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 42 280 48 68 137 265), lower := (rows 7 67 164 42 280 48 68 128 256), losses := [] }

theorem u765 : Upper (D 5) (R 5) [6,65,160,34,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 42 280 48 72 133 261), lower := (rows 7 67 164 42 280 48 72 128 256), losses := [] }

theorem u766 : Upper (D 5) (R 5) [6,65,160,34,264,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 25 288 66 140 268), lower := (rows 7 67 164 56 25 288 66 128 256), losses := [] }

theorem u767 : Upper (D 5) (R 5) [6,65,160,48,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 25 288 68 138 266), lower := (rows 7 67 164 56 25 288 68 128 256), losses := [] }

theorem u768 : Upper (D 5) (R 5) [6,65,160,48,9,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 25 288 72 134 262), lower := (rows 7 67 164 56 25 288 72 128 256), losses := [] }

theorem u769 : Upper (D 5) (R 5) [6,65,160,48,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 26 288 65 140 268), lower := (rows 7 67 164 56 26 288 65 128 256), losses := [] }

theorem u770 : Upper (D 5) (R 5) [6,65,160,48,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 26 288 68 137 265), lower := (rows 7 67 164 56 26 288 68 128 256), losses := [] }

theorem u771 : Upper (D 5) (R 5) [6,65,160,48,10,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b771
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 423, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 56 26 288 72 133 261), lower := (rows 7 67 164 56 26 288 72 128 256), losses := [] }

theorem u772 : Upper (D 5) (R 5) [6,65,160,48,10,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 276 34 65 136 264), lower := (rows 7 67 164 56 276 34 65 128 256), losses := [] }

theorem u773 : Upper (D 5) (R 5) [6,65,160,48,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r774 : Route 9 := (fun mask => (mask,id))

def c774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u774 : Upper (D 5) (R 5) [6,65,160,48,260,2,8] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,260,2,8] 13 (by decide) (choices 1) [1,8] r774 c774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u50
  · exact u51

def b775 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 280 34 65 140 268), lower := (rows 7 67 164 56 280 34 65 128 256), losses := [] }

theorem u775 : Upper (D 5) (R 5) [6,65,160,48,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 56 280 34 68 137 265), lower := (rows 7 67 164 56 280 34 68 128 256), losses := [] }

theorem u776 : Upper (D 5) (R 5) [6,65,160,48,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 56 280 34 72 133 261), lower := (rows 7 67 164 56 280 34 72 128 256), losses := [] }

theorem u777 : Upper (D 5) (R 5) [6,65,160,48,264,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 265 28 40 66 176 304), lower := (rows 7 67 164 265 28 40 66 128 256), losses := [] }

theorem u778 : Upper (D 5) (R 5) [6,65,160,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 265 28 40 80 162 290), lower := (rows 7 67 164 265 28 40 80 128 256), losses := [] }

theorem u779 : Upper (D 5) (R 5) [6,65,160,257,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b779
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P05
