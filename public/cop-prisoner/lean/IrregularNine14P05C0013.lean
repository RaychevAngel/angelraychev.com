import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 265 28 40 96 146 274), lower := (rows 7 67 164 265 28 40 96 128 256), losses := [] }

theorem u780 : Upper (D 5) (R 5) [6,65,160,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 265 28 48 66 168 296), lower := (rows 7 67 164 265 28 48 66 128 256), losses := [] }

theorem u781 : Upper (D 5) (R 5) [6,65,160,257,12,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 164 265 28 48 72 162 290), lower := (rows 7 67 164 265 28 48 72 128 256), losses := [] }

theorem u782 : Upper (D 5) (R 5) [6,65,160,257,12,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 265 28 48 96 138 266), lower := (rows 7 67 164 265 28 48 96 128 256), losses := [] }

theorem u783 : Upper (D 5) (R 5) [6,65,160,257,12,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 265 50 40 68 152 280), lower := (rows 7 67 164 265 50 40 68 128 256), losses := [] }

theorem u784 : Upper (D 5) (R 5) [6,65,160,257,34,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 114, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 164 265 50 40 72 148 276), lower := (rows 7 67 164 265 50 40 72 128 256), losses := [] }

theorem u785 : Upper (D 5) (R 5) [6,65,160,257,34,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 265 50 40 80 140 268), lower := (rows 7 67 164 265 50 40 80 128 256), losses := [] }

theorem u786 : Upper (D 5) (R 5) [6,65,160,257,34,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 266 28 40 65 176 304), lower := (rows 7 67 164 266 28 40 65 128 256), losses := [] }

theorem u787 : Upper (D 5) (R 5) [6,65,160,258,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 266 28 40 80 161 289), lower := (rows 7 67 164 266 28 40 80 128 256), losses := [] }

theorem u788 : Upper (D 5) (R 5) [6,65,160,258,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 266 28 40 96 145 273), lower := (rows 7 67 164 266 28 40 96 128 256), losses := [] }

theorem u789 : Upper (D 5) (R 5) [6,65,160,258,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 266 28 48 65 168 296), lower := (rows 7 67 164 266 28 48 65 128 256), losses := [] }

theorem u790 : Upper (D 5) (R 5) [6,65,160,258,12,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b790
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 266 28 48 72 161 289), lower := (rows 7 67 164 266 28 48 72 128 256), losses := [] }

theorem u791 : Upper (D 5) (R 5) [6,65,160,258,12,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 266 28 48 96 137 265), lower := (rows 7 67 164 266 28 48 96 128 256), losses := [] }

theorem u792 : Upper (D 5) (R 5) [6,65,160,258,12,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b792
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 266 49 40 68 152 280), lower := (rows 7 67 164 266 49 40 68 128 256), losses := [] }

theorem u793 : Upper (D 5) (R 5) [6,65,160,258,33,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 266 49 40 72 148 276), lower := (rows 7 67 164 266 49 40 72 128 256), losses := [] }

theorem u794 : Upper (D 5) (R 5) [6,65,160,258,33,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b794
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 266 49 40 80 140 268), lower := (rows 7 67 164 266 49 40 80 128 256), losses := [] }

theorem u795 : Upper (D 5) (R 5) [6,65,160,258,33,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b795
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 268 25 40 66 176 304), lower := (rows 7 67 164 268 25 40 66 128 256), losses := [] }

theorem u796 : Upper (D 5) (R 5) [6,65,160,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 268 25 40 80 162 290), lower := (rows 7 67 164 268 25 40 80 128 256), losses := [] }

theorem u797 : Upper (D 5) (R 5) [6,65,160,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 268 25 40 96 146 274), lower := (rows 7 67 164 268 25 40 96 128 256), losses := [] }

theorem u798 : Upper (D 5) (R 5) [6,65,160,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 268 26 40 65 176 304), lower := (rows 7 67 164 268 26 40 65 128 256), losses := [] }

theorem u799 : Upper (D 5) (R 5) [6,65,160,260,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b799
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 268 26 40 80 161 289), lower := (rows 7 67 164 268 26 40 80 128 256), losses := [] }

theorem u800 : Upper (D 5) (R 5) [6,65,160,260,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 268 26 40 96 145 273), lower := (rows 7 67 164 268 26 40 96 128 256), losses := [] }

theorem u801 : Upper (D 5) (R 5) [6,65,160,260,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 268 26 48 65 168 296), lower := (rows 7 67 164 268 26 48 65 128 256), losses := [] }

theorem u802 : Upper (D 5) (R 5) [6,65,160,260,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 164 268 26 48 72 161 289), lower := (rows 7 67 164 268 26 48 72 128 256), losses := [] }

theorem u803 : Upper (D 5) (R 5) [6,65,160,260,10,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 164 268 26 48 96 137 265), lower := (rows 7 67 164 268 26 48 96 128 256), losses := [] }

theorem u804 : Upper (D 5) (R 5) [6,65,160,260,10,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 49 40 66 152 280), lower := (rows 7 67 164 268 49 40 66 128 256), losses := [] }

theorem u805 : Upper (D 5) (R 5) [6,65,160,260,33,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 268 49 40 72 146 274), lower := (rows 7 67 164 268 49 40 72 128 256), losses := [] }

theorem u806 : Upper (D 5) (R 5) [6,65,160,260,33,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 268 49 40 80 138 266), lower := (rows 7 67 164 268 49 40 80 128 256), losses := [] }

theorem u807 : Upper (D 5) (R 5) [6,65,160,260,33,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 50 40 65 152 280), lower := (rows 7 67 164 268 50 40 65 128 256), losses := [] }

theorem u808 : Upper (D 5) (R 5) [6,65,160,260,34,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 268 50 40 72 145 273), lower := (rows 7 67 164 268 50 40 72 128 256), losses := [] }

theorem u809 : Upper (D 5) (R 5) [6,65,160,260,34,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 83, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 268 50 40 80 137 265), lower := (rows 7 67 164 268 50 40 80 128 256), losses := [] }

theorem u810 : Upper (D 5) (R 5) [6,65,160,260,34,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 268 56 34 65 152 280), lower := (rows 7 67 164 268 56 34 65 128 256), losses := [] }

theorem u811 : Upper (D 5) (R 5) [6,65,160,260,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 268 56 34 72 145 273), lower := (rows 7 67 164 268 56 34 72 128 256), losses := [] }

theorem u812 : Upper (D 5) (R 5) [6,65,160,260,40,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 2 }], pairs := [(3,1)], upper := (rows 7 67 164 268 56 34 80 137 265), lower := (rows 7 67 164 268 56 34 80 128 256), losses := [] }

theorem u813 : Upper (D 5) (R 5) [6,65,160,260,40,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 28 33 66 168 296), lower := (rows 7 67 164 280 28 33 66 128 256), losses := [] }

theorem u814 : Upper (D 5) (R 5) [6,65,160,272,12,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 28 33 72 162 290), lower := (rows 7 67 164 280 28 33 72 128 256), losses := [] }

theorem u815 : Upper (D 5) (R 5) [6,65,160,272,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 28 33 96 138 266), lower := (rows 7 67 164 280 28 33 96 128 256), losses := [] }

theorem u816 : Upper (D 5) (R 5) [6,65,160,272,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 28 34 65 168 296), lower := (rows 7 67 164 280 28 34 65 128 256), losses := [] }

theorem u817 : Upper (D 5) (R 5) [6,65,160,272,12,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 28 34 72 161 289), lower := (rows 7 67 164 280 28 34 72 128 256), losses := [] }

theorem u818 : Upper (D 5) (R 5) [6,65,160,272,12,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 164 280 28 34 96 137 265), lower := (rows 7 67 164 280 28 34 96 128 256), losses := [] }

theorem u819 : Upper (D 5) (R 5) [6,65,160,272,12,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 49 40 66 140 268), lower := (rows 7 67 164 280 49 40 66 128 256), losses := [] }

theorem u820 : Upper (D 5) (R 5) [6,65,160,272,33,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 280 49 40 68 138 266), lower := (rows 7 67 164 280 49 40 68 128 256), losses := [] }

theorem u821 : Upper (D 5) (R 5) [6,65,160,272,33,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 164 280 49 40 72 134 262), lower := (rows 7 67 164 280 49 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 22 24 16 120 120 131 259), good := (rows 390 486 228 380 508 104 104 128 256) }] }

theorem u822 : Upper (D 5) (R 5) [6,65,160,272,33,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 50 40 65 140 268), lower := (rows 7 67 164 280 50 40 65 128 256), losses := [] }

theorem u823 : Upper (D 5) (R 5) [6,65,160,272,34,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 164 280 50 40 68 137 265), lower := (rows 7 67 164 280 50 40 68 128 256), losses := [] }

theorem u824 : Upper (D 5) (R 5) [6,65,160,272,34,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 133, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 67 164 280 50 40 72 133 261), lower := (rows 7 67 164 280 50 40 72 128 256), losses := [] }

theorem u825 : Upper (D 5) (R 5) [6,65,160,272,34,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 412, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 280 56 34 65 140 268), lower := (rows 7 67 164 280 56 34 65 128 256), losses := [] }

theorem u826 : Upper (D 5) (R 5) [6,65,160,272,40,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 56 34 68 137 265), lower := (rows 7 67 164 280 56 34 68 128 256), losses := [] }

theorem u827 : Upper (D 5) (R 5) [6,65,160,272,40,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b827
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 167, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 67 164 280 56 34 72 133 261), lower := (rows 7 67 164 280 56 34 72 128 256), losses := [] }

theorem u828 : Upper (D 5) (R 5) [6,65,160,272,40,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 296 25 48 66 140 268), lower := (rows 7 67 164 296 25 48 66 128 256), losses := [] }

theorem u829 : Upper (D 5) (R 5) [6,65,160,288,9,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 296 25 48 68 138 266), lower := (rows 7 67 164 296 25 48 68 128 256), losses := [] }

theorem u830 : Upper (D 5) (R 5) [6,65,160,288,9,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 164 296 25 48 72 134 262), lower := (rows 7 67 164 296 25 48 72 128 256), losses := [] }

theorem u831 : Upper (D 5) (R 5) [6,65,160,288,9,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 296 26 48 65 140 268), lower := (rows 7 67 164 296 26 48 65 128 256), losses := [] }

theorem u832 : Upper (D 5) (R 5) [6,65,160,288,10,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 296 26 48 68 137 265), lower := (rows 7 67 164 296 26 48 68 128 256), losses := [] }

theorem u833 : Upper (D 5) (R 5) [6,65,160,288,10,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 165, targets := 8 }], pairs := [(0,3)], upper := (rows 7 67 164 296 26 48 72 133 261), lower := (rows 7 67 164 296 26 48 72 128 256), losses := [] }

theorem u834 : Upper (D 5) (R 5) [6,65,160,288,10,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 140 25 304 33 66 164 292), lower := (rows 7 74 140 25 304 33 66 128 256), losses := [] }

theorem u835 : Upper (D 5) (R 5) [6,72,136,17,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 140 25 304 33 68 162 290), lower := (rows 7 74 140 25 304 33 68 128 256), losses := [] }

theorem u836 : Upper (D 5) (R 5) [6,72,136,17,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 140 25 304 33 96 134 262), lower := (rows 7 74 140 25 304 33 96 128 256), losses := [] }

theorem u837 : Upper (D 5) (R 5) [6,72,136,17,288,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b837
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 74 140 25 304 34 65 164 292), lower := (rows 7 74 140 25 304 34 65 128 256), losses := [] }

theorem u838 : Upper (D 5) (R 5) [6,72,136,17,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 140 25 304 34 68 161 289), lower := (rows 7 74 140 25 304 34 68 128 256), losses := [] }

theorem u839 : Upper (D 5) (R 5) [6,72,136,17,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b839
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P05
