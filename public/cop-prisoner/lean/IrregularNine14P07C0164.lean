import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9840 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 37 290 70 88 146 160 65 137 265), lower := (rows 37 290 70 88 146 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 13 20 0 65 193 321), good := (rows 477 258 478 472 146 128 457 128 256) }] }

theorem u9840 : Upper (D 7) (R 7) [36,288,66,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9841 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 37 290 70 88 146 160 72 129 257), lower := (rows 37 290 70 88 146 160 72 128 256), losses := [] }

theorem u9841 : Upper (D 7) (R 7) [36,288,66,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9841 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9842 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 37 290 70 137 146 40 65 208 336), lower := (rows 37 290 70 137 146 40 65 128 256), losses := [] }

theorem u9842 : Upper (D 7) (R 7) [36,288,66,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9842 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9843 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 290 70 137 146 40 80 193 321), lower := (rows 37 290 70 137 146 40 80 128 256), losses := [] }

theorem u9843 : Upper (D 7) (R 7) [36,288,66,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9843 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9844 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,1),(3,5)], upper := (rows 37 290 70 137 146 48 65 200 328), lower := (rows 37 290 70 137 146 48 65 128 256), losses := [] }

theorem u9844 : Upper (D 7) (R 7) [36,288,66,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9844 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9845 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 290 70 137 146 48 72 193 321), lower := (rows 37 290 70 137 146 48 72 128 256), losses := [] }

theorem u9845 : Upper (D 7) (R 7) [36,288,66,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9845 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9846 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 37 290 70 137 208 33 66 152 280), lower := (rows 37 290 70 137 208 33 66 128 256), losses := [] }

theorem u9846 : Upper (D 7) (R 7) [36,288,66,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9847 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 290 70 137 208 33 72 146 274), lower := (rows 37 290 70 137 208 33 72 128 256), losses := [] }

theorem u9847 : Upper (D 7) (R 7) [36,288,66,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9847 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9848 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 290 70 137 208 33 80 138 266), lower := (rows 37 290 70 137 208 33 80 128 256), losses := [] }

theorem u9848 : Upper (D 7) (R 7) [36,288,66,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9848 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9849 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 37 290 70 137 208 40 65 146 274), lower := (rows 37 290 70 137 208 40 65 128 256), losses := [] }

theorem u9849 : Upper (D 7) (R 7) [36,288,66,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9849 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9850 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 290 70 137 208 40 66 145 273), lower := (rows 37 290 70 137 208 40 66 128 256), losses := [] }

theorem u9850 : Upper (D 7) (R 7) [36,288,66,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9850 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9851 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 290 70 137 208 40 80 131 259), lower := (rows 37 290 70 137 208 40 80 128 256), losses := [] }

theorem u9851 : Upper (D 7) (R 7) [36,288,66,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9851 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9852 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 290 70 137 208 48 65 138 266), lower := (rows 37 290 70 137 208 48 65 128 256), losses := [] }

theorem u9852 : Upper (D 7) (R 7) [36,288,66,129,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9852 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9853 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 290 70 137 208 48 66 137 265), lower := (rows 37 290 70 137 208 48 66 128 256), losses := [] }

theorem u9853 : Upper (D 7) (R 7) [36,288,66,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9853 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9854 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 290 70 137 208 48 72 131 259), lower := (rows 37 290 70 137 208 48 72 128 256), losses := [] }

theorem u9854 : Upper (D 7) (R 7) [36,288,66,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9854 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9855 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 152, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 290 70 138 208 33 65 152 280), lower := (rows 37 290 70 138 208 33 65 128 256), losses := [] }

theorem u9855 : Upper (D 7) (R 7) [36,288,66,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9856 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 290 70 138 208 33 72 145 273), lower := (rows 37 290 70 138 208 33 72 128 256), losses := [] }

theorem u9856 : Upper (D 7) (R 7) [36,288,66,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9856 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9857 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 290 70 138 208 33 80 137 265), lower := (rows 37 290 70 138 208 33 80 128 256), losses := [] }

theorem u9857 : Upper (D 7) (R 7) [36,288,66,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9857 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9858 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 37 290 70 138 208 40 65 145 273), lower := (rows 37 290 70 138 208 40 65 128 256), losses := [] }

theorem u9858 : Upper (D 7) (R 7) [36,288,66,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9858 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9859 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 290 70 138 208 40 80 129 257), lower := (rows 37 290 70 138 208 40 80 128 256), losses := [] }

theorem u9859 : Upper (D 7) (R 7) [36,288,66,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9859 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9860 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 37 290 70 138 208 48 65 137 265), lower := (rows 37 290 70 138 208 48 65 128 256), losses := [] }

theorem u9860 : Upper (D 7) (R 7) [36,288,66,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9860 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9861 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 290 70 138 208 48 72 129 257), lower := (rows 37 290 70 138 208 48 72 128 256), losses := [] }

theorem u9861 : Upper (D 7) (R 7) [36,288,66,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9861 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9862 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 76 11 82 160 65 144 400), lower := (rows 37 290 76 11 82 160 65 128 256), losses := [] }

theorem u9862 : Upper (D 7) (R 7) [36,288,72,3,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9863 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 76 11 82 160 80 129 385), lower := (rows 37 290 76 11 82 160 80 128 256), losses := [] }

theorem u9863 : Upper (D 7) (R 7) [36,288,72,3,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9863 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9864 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(0,1),(2,5),(4,0),(4,5)], upper := (rows 37 290 76 11 82 160 192 145 273), lower := (rows 37 290 76 11 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 108 26 114 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 16 224 224 128 256), good := (rows 101 352 109 9 112 224 224 224 256) }] }

theorem u9864 : Upper (D 7) (R 7) [36,288,72,3,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9865 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 76 11 145 160 66 208 336), lower := (rows 37 290 76 11 145 160 66 128 256), losses := [] }

theorem u9865 : Upper (D 7) (R 7) [36,288,72,3,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9866 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 290 76 11 145 160 80 194 322), lower := (rows 37 290 76 11 145 160 80 128 256), losses := [] }

theorem u9866 : Upper (D 7) (R 7) [36,288,72,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9866 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9867 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 76 11 146 160 65 208 336), lower := (rows 37 290 76 11 146 160 65 128 256), losses := [] }

theorem u9867 : Upper (D 7) (R 7) [36,288,72,3,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9868 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 37 290 76 11 146 160 80 193 321), lower := (rows 37 290 76 11 146 160 80 128 256), losses := [] }

theorem u9868 : Upper (D 7) (R 7) [36,288,72,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9868 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9869 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 290 76 11 208 160 65 146 274), lower := (rows 37 290 76 11 208 160 65 128 256), losses := [] }

theorem u9869 : Upper (D 7) (R 7) [36,288,72,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9870 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 76 11 208 160 66 145 273), lower := (rows 37 290 76 11 208 160 66 128 256), losses := [] }

theorem u9870 : Upper (D 7) (R 7) [36,288,72,3,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9871 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 290 76 11 208 160 80 131 259), lower := (rows 37 290 76 11 208 160 80 128 256), losses := [] }

theorem u9871 : Upper (D 7) (R 7) [36,288,72,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9871 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9872 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 76 25 82 160 65 130 386), lower := (rows 37 290 76 25 82 160 65 128 256), losses := [] }

theorem u9872 : Upper (D 7) (R 7) [36,288,72,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9873 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 76 25 82 160 66 129 385), lower := (rows 37 290 76 25 82 160 66 128 256), losses := [] }

theorem u9873 : Upper (D 7) (R 7) [36,288,72,17,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9874 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7),(4,0)], upper := (rows 37 290 76 25 82 160 192 131 259), lower := (rows 37 290 76 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 108 24 114 224 224 224 256) }] }

theorem u9874 : Upper (D 7) (R 7) [36,288,72,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9875 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 25 146 160 65 194 322), lower := (rows 37 290 76 25 146 160 65 128 256), losses := [] }

theorem u9875 : Upper (D 7) (R 7) [36,288,72,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9876 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,7),(2,0),(2,5)], upper := (rows 37 290 76 25 146 160 66 193 321), lower := (rows 37 290 76 25 146 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 82 128 256), good := (rows 36 354 76 124 242 160 66 160 256) },{ target := 5, region := (rows 1 2 12 8 16 0 82 136 264), good := (rows 5 322 460 477 210 128 66 128 256) }] }

theorem u9876 : Upper (D 7) (R 7) [36,288,72,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9877 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 76 26 81 160 65 130 386), lower := (rows 37 290 76 26 81 160 65 128 256), losses := [] }

theorem u9877 : Upper (D 7) (R 7) [36,288,72,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9878 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 76 26 81 160 66 129 385), lower := (rows 37 290 76 26 81 160 66 128 256), losses := [] }

theorem u9878 : Upper (D 7) (R 7) [36,288,72,18,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9879 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(3,6)], upper := (rows 37 290 76 26 81 160 192 131 259), lower := (rows 37 290 76 26 81 160 192 128 256), losses := [] }

theorem u9879 : Upper (D 7) (R 7) [36,288,72,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9880 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 290 76 26 145 160 65 194 322), lower := (rows 37 290 76 26 145 160 65 128 256), losses := [{ target := 0, region := (rows 0 71 4 24 16 245 64 196 324), good := (rows 422 290 494 58 186 160 482 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 93 128 256), good := (rows 101 288 77 125 241 160 65 160 256) }] }

theorem u9880 : Upper (D 7) (R 7) [36,288,72,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9881 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 290 76 26 145 160 66 193 321), lower := (rows 37 290 76 26 145 160 66 128 256), losses := [] }

theorem u9881 : Upper (D 7) (R 7) [36,288,72,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9882 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,1),(0,6),(1,6),(1,7)], upper := (rows 37 290 76 26 208 160 65 131 259), lower := (rows 37 290 76 26 208 160 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 77 128 256), good := (rows 101 288 77 125 240 160 65 160 256) }] }

theorem u9882 : Upper (D 7) (R 7) [36,288,72,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9883 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 290 76 26 208 160 66 129 257), lower := (rows 37 290 76 26 208 160 66 128 256), losses := [] }

theorem u9883 : Upper (D 7) (R 7) [36,288,72,18,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9884 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 8, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 137 82 34 65 144 400), lower := (rows 37 290 76 137 82 34 65 128 256), losses := [] }

theorem u9884 : Upper (D 7) (R 7) [36,288,72,129,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9885 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 290 76 137 82 34 80 129 385), lower := (rows 37 290 76 137 82 34 80 128 256), losses := [] }

theorem u9885 : Upper (D 7) (R 7) [36,288,72,129,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9885 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9886 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 290 76 137 82 34 192 145 273), lower := (rows 37 290 76 137 82 34 192 128 256), losses := [] }

theorem u9886 : Upper (D 7) (R 7) [36,288,72,129,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9887 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 290 76 137 82 48 65 130 386), lower := (rows 37 290 76 137 82 48 65 128 256), losses := [] }

theorem u9887 : Upper (D 7) (R 7) [36,288,72,129,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9887 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9888 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 290 76 137 82 48 66 129 385), lower := (rows 37 290 76 137 82 48 66 128 256), losses := [] }

theorem u9888 : Upper (D 7) (R 7) [36,288,72,129,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9888 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9889 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 290 76 137 82 48 192 131 259), lower := (rows 37 290 76 137 82 48 192 128 256), losses := [] }

theorem u9889 : Upper (D 7) (R 7) [36,288,72,129,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9890 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 8, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 290 76 137 146 34 65 208 336), lower := (rows 37 290 76 137 146 34 65 128 256), losses := [] }

theorem u9890 : Upper (D 7) (R 7) [36,288,72,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9891 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7)], upper := (rows 37 290 76 137 146 34 80 193 321), lower := (rows 37 290 76 137 146 34 80 128 256), losses := [] }

theorem u9891 : Upper (D 7) (R 7) [36,288,72,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9891 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9892 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 290 76 137 146 48 65 194 322), lower := (rows 37 290 76 137 146 48 65 128 256), losses := [] }

theorem u9892 : Upper (D 7) (R 7) [36,288,72,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9892 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9893 : Route 9 := (fun mask => (mask,id))

def c9893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u9893 : Upper (D 7) (R 7) [36,288,72,129,130,16,2] 13 := by
  apply FastRouting.sound _ _ [36,288,72,129,130,16,2] 13 (by decide) (choices 1) [1,64] r9893 c9893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u769
  · exact u770

def b9894 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 290 76 137 208 34 65 146 274), lower := (rows 37 290 76 137 208 34 65 128 256), losses := [] }

theorem u9894 : Upper (D 7) (R 7) [36,288,72,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9895 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 34, targets := 129 },{ cop := 8, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,5)], upper := (rows 37 290 76 137 208 34 66 145 273), lower := (rows 37 290 76 137 208 34 66 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 21 0 98 137 265), good := (rows 477 322 476 413 208 66 66 128 256) }] }

theorem u9895 : Upper (D 7) (R 7) [36,288,72,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9896 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 37 290 76 137 208 34 80 131 259), lower := (rows 37 290 76 137 208 34 80 128 256), losses := [] }

theorem u9896 : Upper (D 7) (R 7) [36,288,72,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9896 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9897 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 290 76 138 19 48 65 192 448), lower := (rows 37 290 76 138 19 48 65 128 256), losses := [] }

theorem u9897 : Upper (D 7) (R 7) [36,288,72,130,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9897 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9898 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 290 76 138 19 48 192 193 321), lower := (rows 37 290 76 138 19 48 192 128 256), losses := [] }

theorem u9898 : Upper (D 7) (R 7) [36,288,72,130,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9898 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9899 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 290 76 138 82 33 65 144 400), lower := (rows 37 290 76 138 82 33 65 128 256), losses := [] }

theorem u9899 : Upper (D 7) (R 7) [36,288,72,130,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9899
end Delivery.IrregularNine14.P07
