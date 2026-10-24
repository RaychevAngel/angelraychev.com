import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 28 104 176 33 96 133 261), lower := (rows 259 194 28 104 176 33 96 128 256), losses := [] }

theorem u780 : Upper (D 8) (R 8) [258,192,24,96,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 259 194 44 88 176 33 65 164 292), lower := (rows 259 194 44 88 176 33 65 128 256), losses := [] }

theorem u781 : Upper (D 8) (R 8) [258,192,40,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 194 44 88 176 33 68 161 289), lower := (rows 259 194 44 88 176 33 68 128 256), losses := [] }

theorem u782 : Upper (D 8) (R 8) [258,192,40,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b782 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 44 88 176 33 96 133 261), lower := (rows 259 194 44 88 176 33 96 128 256), losses := [] }

theorem u783 : Upper (D 8) (R 8) [258,192,40,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 94, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 28 42 112 160 65 192 448), lower := (rows 289 7 28 42 112 160 65 128 256), losses := [] }

theorem u784 : Upper (D 8) (R 8) [288,5,24,34,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 257, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 28 42 112 160 192 193 321), lower := (rows 289 7 28 42 112 160 192 128 256), losses := [] }

theorem u785 : Upper (D 8) (R 8) [288,5,24,34,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 94, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 44 26 112 160 65 192 448), lower := (rows 289 7 44 26 112 160 65 128 256), losses := [] }

theorem u786 : Upper (D 8) (R 8) [288,5,40,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 257, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 26 112 160 192 193 321), lower := (rows 289 7 44 26 112 160 192 128 256), losses := [] }

theorem u787 : Upper (D 8) (R 8) [288,5,40,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 289 7 44 74 145 160 80 224 352), lower := (rows 289 7 44 74 145 160 80 128 256), losses := [] }

theorem u788 : Upper (D 8) (R 8) [288,5,40,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b788 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 44 74 145 160 96 208 336), lower := (rows 289 7 44 74 145 160 96 128 256), losses := [] }

theorem u789 : Upper (D 8) (R 8) [288,5,40,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 289 7 76 42 145 160 80 224 352), lower := (rows 289 7 76 42 145 160 80 128 256), losses := [] }

theorem u790 : Upper (D 8) (R 8) [288,5,72,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b790 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 76 42 145 160 96 208 336), lower := (rows 289 7 76 42 145 160 96 128 256), losses := [] }

theorem u791 : Upper (D 8) (R 8) [288,5,72,34,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 289 7 76 56 145 96 66 160 416), lower := (rows 289 7 76 56 145 96 66 128 256), losses := [] }

theorem u792 : Upper (D 8) (R 8) [288,5,72,48,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b792 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 110, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 76 56 145 96 96 130 386), lower := (rows 289 7 76 56 145 96 96 128 256), losses := [] }

theorem u793 : Upper (D 8) (R 8) [288,5,72,48,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 56 145 96 192 162 290), lower := (rows 289 7 76 56 145 96 192 128 256), losses := [] }

theorem u794 : Upper (D 8) (R 8) [288,5,72,48,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 7 76 168 145 96 66 176 304), lower := (rows 289 7 76 168 145 96 66 128 256), losses := [] }

theorem u795 : Upper (D 8) (R 8) [288,5,72,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b795 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 7 76 168 145 96 80 162 290), lower := (rows 289 7 76 168 145 96 80 128 256), losses := [] }

theorem u796 : Upper (D 8) (R 8) [288,5,72,160,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b796 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 145 96 96 146 274), lower := (rows 289 7 76 168 145 96 96 128 256), losses := [] }

theorem u797 : Upper (D 8) (R 8) [288,5,72,160,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 100 26 56 160 65 192 448), lower := (rows 289 7 100 26 56 160 65 128 256), losses := [] }

theorem u798 : Upper (D 8) (R 8) [288,5,96,18,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 257, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 26 56 160 192 193 321), lower := (rows 289 7 100 26 56 160 192 128 256), losses := [] }

theorem u799 : Upper (D 8) (R 8) [288,5,96,18,40,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 144, camps := [], pairs := [], upper := (rows 289 7 100 42 81 160 72 144 400), lower := (rows 289 7 100 42 81 160 72 128 256), losses := [] }

theorem u800 : Upper (D 8) (R 8) [288,5,96,34,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b800 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 289 7 100 42 81 160 80 136 392), lower := (rows 289 7 100 42 81 160 80 128 256), losses := [] }

theorem u801 : Upper (D 8) (R 8) [288,5,96,34,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b801 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 42 81 160 192 152 280), lower := (rows 289 7 100 42 81 160 192 128 256), losses := [] }

theorem u802 : Upper (D 8) (R 8) [288,5,96,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 80, camps := [], pairs := [], upper := (rows 289 7 100 42 145 160 72 208 336), lower := (rows 289 7 100 42 145 160 72 128 256), losses := [] }

theorem u803 : Upper (D 8) (R 8) [288,5,96,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b803 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 289 7 100 42 145 160 80 200 328), lower := (rows 289 7 100 42 145 160 80 128 256), losses := [] }

theorem u804 : Upper (D 8) (R 8) [288,5,96,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b804 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 100 42 152 160 65 208 336), lower := (rows 289 7 100 42 152 160 65 128 256), losses := [] }

theorem u805 : Upper (D 8) (R 8) [288,5,96,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 289 7 100 42 152 160 80 193 321), lower := (rows 289 7 100 42 152 160 80 128 256), losses := [] }

theorem u806 : Upper (D 8) (R 8) [288,5,96,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b806 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 289 7 100 56 81 160 66 136 392), lower := (rows 289 7 100 56 81 160 66 128 256), losses := [] }

theorem u807 : Upper (D 8) (R 8) [288,5,96,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b807 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 289 7 100 56 81 160 72 130 386), lower := (rows 289 7 100 56 81 160 72 128 256), losses := [] }

theorem u808 : Upper (D 8) (R 8) [288,5,96,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b808 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 56 81 160 192 138 266), lower := (rows 289 7 100 56 81 160 192 128 256), losses := [] }

theorem u809 : Upper (D 8) (R 8) [288,5,96,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 7 100 73 146 160 72 176 304), lower := (rows 289 7 100 73 146 160 72 128 256), losses := [] }

theorem u810 : Upper (D 8) (R 8) [288,5,96,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b810 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 289 7 100 73 146 160 80 168 296), lower := (rows 289 7 100 73 146 160 80 128 256), losses := [] }

theorem u811 : Upper (D 8) (R 8) [288,5,96,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b811 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 100 73 146 160 96 152 280), lower := (rows 289 7 100 73 146 160 96 128 256), losses := [] }

theorem u812 : Upper (D 8) (R 8) [288,5,96,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 7 100 73 152 160 66 176 304), lower := (rows 289 7 100 73 152 160 66 128 256), losses := [] }

theorem u813 : Upper (D 8) (R 8) [288,5,96,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b813 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 7 100 73 152 160 80 162 290), lower := (rows 289 7 100 73 152 160 80 128 256), losses := [] }

theorem u814 : Upper (D 8) (R 8) [288,5,96,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b814 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 7 100 73 152 160 96 146 274), lower := (rows 289 7 100 73 152 160 96 128 256), losses := [] }

theorem u815 : Upper (D 8) (R 8) [288,5,96,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 289 7 196 56 81 160 66 168 296), lower := (rows 289 7 196 56 81 160 66 128 256), losses := [] }

theorem u816 : Upper (D 8) (R 8) [288,5,192,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b816 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 7 196 56 81 160 72 162 290), lower := (rows 289 7 196 56 81 160 72 128 256), losses := [] }

theorem u817 : Upper (D 8) (R 8) [288,5,192,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b817 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 289 7 196 56 81 160 96 138 266), lower := (rows 289 7 196 56 81 160 96 128 256), losses := [] }

theorem u818 : Upper (D 8) (R 8) [288,5,192,48,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 289 14 38 73 145 160 80 224 352), lower := (rows 289 14 38 73 145 160 80 128 256), losses := [] }

theorem u819 : Upper (D 8) (R 8) [288,12,34,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b819 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 289 14 38 73 145 160 96 208 336), lower := (rows 289 14 38 73 145 160 96 128 256), losses := [] }

theorem u820 : Upper (D 8) (R 8) [288,12,34,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 289 14 52 73 145 96 66 160 416), lower := (rows 289 14 52 73 145 96 66 128 256), losses := [] }

theorem u821 : Upper (D 8) (R 8) [288,12,48,65,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b821 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 110, targets := 128 }], pairs := [(1,7)], upper := (rows 289 14 52 73 145 96 96 130 386), lower := (rows 289 14 52 73 145 96 96 128 256), losses := [] }

theorem u822 : Upper (D 8) (R 8) [288,12,48,65,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 73 145 96 192 162 290), lower := (rows 289 14 52 73 145 96 192 128 256), losses := [] }

theorem u823 : Upper (D 8) (R 8) [288,12,48,65,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 14 69 168 145 96 66 176 304), lower := (rows 289 14 69 168 145 96 66 128 256), losses := [] }

theorem u824 : Upper (D 8) (R 8) [288,12,65,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b824 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 14 69 168 145 96 80 162 290), lower := (rows 289 14 69 168 145 96 80 128 256), losses := [] }

theorem u825 : Upper (D 8) (R 8) [288,12,65,160,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b825 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 145 96 96 146 274), lower := (rows 289 14 69 168 145 96 96 128 256), losses := [] }

theorem u826 : Upper (D 8) (R 8) [288,12,65,160,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 289 38 69 88 145 160 66 168 296), lower := (rows 289 38 69 88 145 160 66 128 256), losses := [] }

theorem u827 : Upper (D 8) (R 8) [288,36,65,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b827 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 38 69 88 145 160 72 162 290), lower := (rows 289 38 69 88 145 160 72 128 256), losses := [] }

theorem u828 : Upper (D 8) (R 8) [288,36,65,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b828 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 38 69 88 145 160 96 138 266), lower := (rows 289 38 69 88 145 160 96 128 256), losses := [] }

theorem u829 : Upper (D 8) (R 8) [288,36,65,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 24, camps := [], pairs := [], upper := (rows 289 38 69 104 145 160 66 152 280), lower := (rows 289 38 69 104 145 160 66 128 256), losses := [] }

theorem u830 : Upper (D 8) (R 8) [288,36,65,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b830 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 289 38 69 104 145 160 72 146 274), lower := (rows 289 38 69 104 145 160 72 128 256), losses := [] }

theorem u831 : Upper (D 8) (R 8) [288,36,65,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b831 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 289 38 69 104 145 160 80 138 266), lower := (rows 289 38 69 104 145 160 80 128 256), losses := [] }

theorem u832 : Upper (D 8) (R 8) [288,36,65,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b832 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 38 69 104 146 160 65 152 280), lower := (rows 289 38 69 104 146 160 65 128 256), losses := [] }

theorem u833 : Upper (D 8) (R 8) [288,36,65,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 69 104 146 160 72 145 273), lower := (rows 289 38 69 104 146 160 72 128 256), losses := [] }

theorem u834 : Upper (D 8) (R 8) [288,36,65,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b834 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 38 69 104 146 160 80 137 265), lower := (rows 289 38 69 104 146 160 80 128 256), losses := [] }

theorem u835 : Upper (D 8) (R 8) [288,36,65,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b835 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 289 38 69 104 152 160 65 146 274), lower := (rows 289 38 69 104 152 160 65 128 256), losses := [] }

theorem u836 : Upper (D 8) (R 8) [288,36,65,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 69 104 152 160 66 145 273), lower := (rows 289 38 69 104 152 160 66 128 256), losses := [] }

theorem u837 : Upper (D 8) (R 8) [288,36,65,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b837 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 69 104 152 160 80 131 259), lower := (rows 289 38 69 104 152 160 80 128 256), losses := [] }

theorem u838 : Upper (D 8) (R 8) [288,36,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b838 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 38 104 152 160 65 176 304), lower := (rows 321 7 38 104 152 160 65 128 256), losses := [] }

theorem u839 : Upper (D 8) (R 8) [320,5,34,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P08
