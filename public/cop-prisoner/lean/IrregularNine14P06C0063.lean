import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3780 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 11 131 276 44 112 33 68 194 322), lower := (rows 11 131 276 44 112 33 68 128 256), losses := [] }

theorem u3780 : Upper (D 6) (R 6) [10,129,272,36,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3781 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 276 44 112 34 65 196 324), lower := (rows 11 131 276 44 112 34 65 128 256), losses := [] }

theorem u3781 : Upper (D 6) (R 6) [10,129,272,36,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 11 131 276 44 112 34 68 193 321), lower := (rows 11 131 276 44 112 34 68 128 256), losses := [] }

theorem u3782 : Upper (D 6) (R 6) [10,129,272,36,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(2,0),(2,5)], upper := (rows 11 131 276 104 49 36 66 196 324), lower := (rows 11 131 276 104 49 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 52 67 144 272), good := (rows 74 194 444 104 508 36 66 128 256) }] }

theorem u3783 : Upper (D 6) (R 6) [10,129,272,96,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 276 104 49 36 68 194 322), lower := (rows 11 131 276 104 49 36 68 128 256), losses := [] }

theorem u3784 : Upper (D 6) (R 6) [10,129,272,96,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 131 276 104 50 36 65 196 324), lower := (rows 11 131 276 104 50 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 72 19 111 64 200 328), good := (rows 446 182 308 492 50 36 508 128 256) }] }

theorem u3785 : Upper (D 6) (R 6) [10,129,272,96,34,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3786 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 276 104 50 36 68 193 321), lower := (rows 11 131 276 104 50 36 68 128 256), losses := [] }

theorem u3786 : Upper (D 6) (R 6) [10,129,272,96,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3787 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 13 84 96 66 176 304), lower := (rows 11 131 292 13 84 96 66 128 256), losses := [] }

theorem u3787 : Upper (D 6) (R 6) [10,129,288,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 292 13 84 96 80 162 290), lower := (rows 11 131 292 13 84 96 80 128 256), losses := [] }

theorem u3788 : Upper (D 6) (R 6) [10,129,288,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3788 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 13 84 96 96 146 274), lower := (rows 11 131 292 13 84 96 96 128 256), losses := [] }

theorem u3789 : Upper (D 6) (R 6) [10,129,288,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3790 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 25 84 96 66 164 292), lower := (rows 11 131 292 25 84 96 66 128 256), losses := [] }

theorem u3790 : Upper (D 6) (R 6) [10,129,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 25 84 96 68 162 290), lower := (rows 11 131 292 25 84 96 68 128 256), losses := [] }

theorem u3791 : Upper (D 6) (R 6) [10,129,288,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 25 84 96 96 134 262), lower := (rows 11 131 292 25 84 96 96 128 256), losses := [] }

theorem u3792 : Upper (D 6) (R 6) [10,129,288,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 81 96 66 164 292), lower := (rows 11 131 292 28 81 96 66 128 256), losses := [] }

theorem u3793 : Upper (D 6) (R 6) [10,129,288,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3794 : PairBound 9 := { available := 34, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 4, region := 162, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 11 131 292 28 81 96 68 162 290), lower := (rows 11 131 292 28 81 96 68 128 256), losses := [] }

theorem u3794 : Upper (D 6) (R 6) [10,129,288,20,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3795 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 28 81 96 96 134 262), lower := (rows 11 131 292 28 81 96 96 128 256), losses := [] }

theorem u3795 : Upper (D 6) (R 6) [10,129,288,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3796 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 82 96 65 164 292), lower := (rows 11 131 292 28 82 96 65 128 256), losses := [] }

theorem u3796 : Upper (D 6) (R 6) [10,129,288,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3797 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 28 82 96 68 161 289), lower := (rows 11 131 292 28 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 260 8 17 381 332 128 256), good := (rows 122 178 356 124 114 96 100 128 356) }] }

theorem u3797 : Upper (D 6) (R 6) [10,129,288,20,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3798 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 28 82 96 96 133 261), lower := (rows 11 131 292 28 82 96 96 128 256), losses := [] }

theorem u3798 : Upper (D 6) (R 6) [10,129,288,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3799 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 112 33 66 196 324), lower := (rows 11 131 292 28 112 33 66 128 256), losses := [] }

theorem u3799 : Upper (D 6) (R 6) [10,129,288,20,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3800 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 28 112 33 68 194 322), lower := (rows 11 131 292 28 112 33 68 128 256), losses := [] }

theorem u3800 : Upper (D 6) (R 6) [10,129,288,20,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 28 112 34 65 196 324), lower := (rows 11 131 292 28 112 34 65 128 256), losses := [] }

theorem u3801 : Upper (D 6) (R 6) [10,129,288,20,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 28 112 34 68 193 321), lower := (rows 11 131 292 28 112 34 68 128 256), losses := [] }

theorem u3802 : Upper (D 6) (R 6) [10,129,288,20,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3803 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 41 84 96 66 148 276), lower := (rows 11 131 292 41 84 96 66 128 256), losses := [] }

theorem u3803 : Upper (D 6) (R 6) [10,129,288,33,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 41 84 96 68 146 274), lower := (rows 11 131 292 41 84 96 68 128 256), losses := [] }

theorem u3804 : Upper (D 6) (R 6) [10,129,288,33,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3805 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 292 41 84 96 80 134 262), lower := (rows 11 131 292 41 84 96 80 128 256), losses := [] }

theorem u3805 : Upper (D 6) (R 6) [10,129,288,33,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3805 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3806 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 5, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 131 292 56 22 96 65 196 324), lower := (rows 11 131 292 56 22 96 65 128 256), losses := [] }

theorem u3806 : Upper (D 6) (R 6) [10,129,288,48,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 292 56 22 96 68 193 321), lower := (rows 11 131 292 56 22 96 68 128 256), losses := [] }

theorem u3807 : Upper (D 6) (R 6) [10,129,288,48,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 292 56 84 33 66 196 324), lower := (rows 11 131 292 56 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 49 32 67 177 305), good := (rows 478 466 444 444 476 508 66 128 256) }] }

theorem u3808 : Upper (D 6) (R 6) [10,129,288,48,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 56 84 33 68 194 322), lower := (rows 11 131 292 56 84 33 68 128 256), losses := [] }

theorem u3809 : Upper (D 6) (R 6) [10,129,288,48,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 292 56 84 34 65 196 324), lower := (rows 11 131 292 56 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 80 35 64 208 336), good := (rows 46 162 292 444 476 34 508 128 256) }] }

theorem u3810 : Upper (D 6) (R 6) [10,129,288,48,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3811 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 56 84 34 68 193 321), lower := (rows 11 131 292 56 84 34 68 128 256), losses := [] }

theorem u3811 : Upper (D 6) (R 6) [10,129,288,48,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3812 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 11 131 292 76 21 48 66 224 352), lower := (rows 11 131 292 76 21 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 52 24 16 48 67 144 272), good := (rows 74 194 292 76 508 444 66 128 256) }] }

theorem u3812 : Upper (D 6) (R 6) [10,129,288,68,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3812 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 76 21 48 96 194 322), lower := (rows 11 131 292 76 21 48 96 128 256), losses := [] }

theorem u3813 : Upper (D 6) (R 6) [10,129,288,68,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3813 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3814 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 131 292 76 21 96 66 176 304), lower := (rows 11 131 292 76 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 123 67 144 272), good := (rows 106 226 292 108 508 96 98 128 256) }] }

theorem u3814 : Upper (D 6) (R 6) [10,129,288,68,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 292 76 21 96 80 162 290), lower := (rows 11 131 292 76 21 96 80 128 256), losses := [] }

theorem u3815 : Upper (D 6) (R 6) [10,129,288,68,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3815 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 147, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 76 21 96 96 146 274), lower := (rows 11 131 292 76 21 96 96 128 256), losses := [] }

theorem u3816 : Upper (D 6) (R 6) [10,129,288,68,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3817 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 292 76 22 33 80 224 352), lower := (rows 11 131 292 76 22 33 80 128 256), losses := [] }

theorem u3817 : Upper (D 6) (R 6) [10,129,288,68,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3817 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 131 292 76 22 33 96 208 336), lower := (rows 11 131 292 76 22 33 96 128 256), losses := [] }

theorem u3818 : Upper (D 6) (R 6) [10,129,288,68,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3819 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 131 292 76 22 48 65 224 352), lower := (rows 11 131 292 76 22 48 65 128 256), losses := [] }

theorem u3819 : Upper (D 6) (R 6) [10,129,288,68,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3819 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3820 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 76 22 48 96 193 321), lower := (rows 11 131 292 76 22 48 96 128 256), losses := [] }

theorem u3820 : Upper (D 6) (R 6) [10,129,288,68,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3820 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 131 292 76 22 96 65 176 304), lower := (rows 11 131 292 76 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 109 104 19 104 64 193 321), good := (rows 446 406 300 492 22 492 508 128 256) }] }

theorem u3821 : Upper (D 6) (R 6) [10,129,288,68,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3821 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 292 76 22 96 80 161 289), lower := (rows 11 131 292 76 22 96 80 128 256), losses := [] }

theorem u3822 : Upper (D 6) (R 6) [10,129,288,68,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3822 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 292 76 22 96 96 145 273), lower := (rows 11 131 292 76 22 96 96 128 256), losses := [] }

theorem u3823 : Upper (D 6) (R 6) [10,129,288,68,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 76 50 96 65 148 276), lower := (rows 11 131 292 76 50 96 65 128 256), losses := [] }

theorem u3824 : Upper (D 6) (R 6) [10,129,288,68,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3825 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 50 96 68 145 273), lower := (rows 11 131 292 76 50 96 68 128 256), losses := [] }

theorem u3825 : Upper (D 6) (R 6) [10,129,288,68,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3825 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3826 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 131 292 76 50 96 80 133 261), lower := (rows 11 131 292 76 50 96 80 128 256), losses := [] }

theorem u3826 : Upper (D 6) (R 6) [10,129,288,68,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3826 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3827 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 131 292 76 82 48 65 164 292), lower := (rows 11 131 292 76 82 48 65 128 256), losses := [] }

theorem u3827 : Upper (D 6) (R 6) [10,129,288,68,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3827 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3828 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 292 76 82 48 68 161 289), lower := (rows 11 131 292 76 82 48 68 128 256), losses := [] }

theorem u3828 : Upper (D 6) (R 6) [10,129,288,68,66,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3828 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3829 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 292 76 82 48 96 133 261), lower := (rows 11 131 292 76 82 48 96 128 256), losses := [] }

theorem u3829 : Upper (D 6) (R 6) [10,129,288,68,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3830 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 112 33 66 148 276), lower := (rows 11 131 292 76 112 33 66 128 256), losses := [] }

theorem u3830 : Upper (D 6) (R 6) [10,129,288,68,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 76 112 33 68 146 274), lower := (rows 11 131 292 76 112 33 68 128 256), losses := [] }

theorem u3831 : Upper (D 6) (R 6) [10,129,288,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 292 76 112 33 80 134 262), lower := (rows 11 131 292 76 112 33 80 128 256), losses := [] }

theorem u3832 : Upper (D 6) (R 6) [10,129,288,68,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3832 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 268, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 76 112 34 65 148 276), lower := (rows 11 131 292 76 112 34 65 128 256), losses := [] }

theorem u3833 : Upper (D 6) (R 6) [10,129,288,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3833 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3834 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 76 112 34 68 145 273), lower := (rows 11 131 292 76 112 34 68 128 256), losses := [] }

theorem u3834 : Upper (D 6) (R 6) [10,129,288,68,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3835 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 292 76 112 34 80 133 261), lower := (rows 11 131 292 76 112 34 80 128 256), losses := [] }

theorem u3835 : Upper (D 6) (R 6) [10,129,288,68,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3835 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3836 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 21 96 66 164 292), lower := (rows 11 131 292 88 21 96 66 128 256), losses := [] }

theorem u3836 : Upper (D 6) (R 6) [10,129,288,80,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3837 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 131 292 88 21 96 68 162 290), lower := (rows 11 131 292 88 21 96 68 128 256), losses := [] }

theorem u3837 : Upper (D 6) (R 6) [10,129,288,80,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3837 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3838 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 292 88 21 96 96 134 262), lower := (rows 11 131 292 88 21 96 96 128 256), losses := [] }

theorem u3838 : Upper (D 6) (R 6) [10,129,288,80,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3839 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 22 96 65 164 292), lower := (rows 11 131 292 88 22 96 65 128 256), losses := [] }

theorem u3839 : Upper (D 6) (R 6) [10,129,288,80,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3839
end Delivery.IrregularNine14.P06
