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

def b5820 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 137 22 288 80 196 324), lower := (rows 35 67 44 137 22 288 80 128 256), losses := [] }

theorem u5820 : Upper (D 6) (R 6) [34,65,40,129,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5820 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 84 288 66 148 276), lower := (rows 35 67 44 137 84 288 66 128 256), losses := [] }

theorem u5821 : Upper (D 6) (R 6) [34,65,40,129,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5821 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 137 84 288 68 146 274), lower := (rows 35 67 44 137 84 288 68 128 256), losses := [] }

theorem u5822 : Upper (D 6) (R 6) [34,65,40,129,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5822 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5823 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 84 288 80 134 262), lower := (rows 35 67 44 137 84 288 80 128 256), losses := [] }

theorem u5823 : Upper (D 6) (R 6) [34,65,40,129,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5823 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5824 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 276 48 66 196 324), lower := (rows 35 67 44 137 276 48 66 128 256), losses := [] }

theorem u5824 : Upper (D 6) (R 6) [34,65,40,129,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5824 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 137 276 48 68 194 322), lower := (rows 35 67 44 137 276 48 68 128 256), losses := [] }

theorem u5825 : Upper (D 6) (R 6) [34,65,40,129,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5825 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5826 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 138 84 288 65 148 276), lower := (rows 35 67 44 138 84 288 65 128 256), losses := [] }

theorem u5826 : Upper (D 6) (R 6) [34,65,40,130,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5826 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5827 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 138 84 288 68 145 273), lower := (rows 35 67 44 138 84 288 68 128 256), losses := [] }

theorem u5827 : Upper (D 6) (R 6) [34,65,40,130,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5827 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5828 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 138 84 288 80 133 261), lower := (rows 35 67 44 138 84 288 80 128 256), losses := [] }

theorem u5828 : Upper (D 6) (R 6) [34,65,40,130,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5828 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5829 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 138 276 48 65 196 324), lower := (rows 35 67 44 138 276 48 65 128 256), losses := [] }

theorem u5829 : Upper (D 6) (R 6) [34,65,40,130,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5830 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 138 276 48 68 193 321), lower := (rows 35 67 44 138 276 48 68 128 256), losses := [] }

theorem u5830 : Upper (D 6) (R 6) [34,65,40,130,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5830 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5831 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 152 22 288 65 196 324), lower := (rows 35 67 44 152 22 288 65 128 256), losses := [] }

theorem u5831 : Upper (D 6) (R 6) [34,65,40,144,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5831 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5832 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 44 152 22 288 68 193 321), lower := (rows 35 67 44 152 22 288 68 128 256), losses := [] }

theorem u5832 : Upper (D 6) (R 6) [34,65,40,144,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5832 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 152 84 288 65 134 262), lower := (rows 35 67 44 152 84 288 65 128 256), losses := [] }

theorem u5833 : Upper (D 6) (R 6) [34,65,40,144,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5833 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5834 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 152 84 288 66 133 261), lower := (rows 35 67 44 152 84 288 66 128 256), losses := [] }

theorem u5834 : Upper (D 6) (R 6) [34,65,40,144,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5834 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5835 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 44 152 84 288 68 131 259), lower := (rows 35 67 44 152 84 288 68 128 256), losses := [] }

theorem u5835 : Upper (D 6) (R 6) [34,65,40,144,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5835 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5836 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 200 22 288 65 148 276), lower := (rows 35 67 44 200 22 288 65 128 256), losses := [] }

theorem u5836 : Upper (D 6) (R 6) [34,65,40,192,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5836 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5837 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 67 44 200 22 288 68 145 273), lower := (rows 35 67 44 200 22 288 68 128 256), losses := [] }

theorem u5837 : Upper (D 6) (R 6) [34,65,40,192,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5837 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5838 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1)], upper := (rows 35 67 44 200 22 288 80 133 261), lower := (rows 35 67 44 200 22 288 80 128 256), losses := [] }

theorem u5838 : Upper (D 6) (R 6) [34,65,40,192,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5838 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5839 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 200 276 48 65 134 262), lower := (rows 35 67 44 200 276 48 65 128 256), losses := [] }

theorem u5839 : Upper (D 6) (R 6) [34,65,40,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5839 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 200 276 48 66 133 261), lower := (rows 35 67 44 200 276 48 66 128 256), losses := [] }

theorem u5840 : Upper (D 6) (R 6) [34,65,40,192,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5840 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 200 276 48 68 131 259), lower := (rows 35 67 44 200 276 48 68 128 256), losses := [] }

theorem u5841 : Upper (D 6) (R 6) [34,65,40,192,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5841 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 133 26 52 288 68 200 328), lower := (rows 35 67 133 26 52 288 68 128 256), losses := [{ target := 5, region := (rows 1 6 4 24 16 0 84 152 280), good := (rows 3 67 199 474 478 256 70 128 256) }] }

theorem u5842 : Upper (D 6) (R 6) [34,65,129,18,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5842 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5843 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2)], upper := (rows 35 67 133 26 52 288 72 196 324), lower := (rows 35 67 133 26 52 288 72 128 256), losses := [] }

theorem u5843 : Upper (D 6) (R 6) [34,65,129,18,36,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5843 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5844 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 133 26 304 36 68 200 328), lower := (rows 35 67 133 26 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 119 100 100 135 263), good := (rows 506 506 508 410 368 500 500 128 256) }] }

theorem u5844 : Upper (D 6) (R 6) [34,65,129,18,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5845 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 26 304 36 72 196 324), lower := (rows 35 67 133 26 304 36 72 128 256), losses := [] }

theorem u5845 : Upper (D 6) (R 6) [34,65,129,18,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5845 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 164, targets := 2 }], pairs := [(2,1),(3,0)], upper := (rows 35 67 133 28 274 36 72 224 352), lower := (rows 35 67 133 28 274 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 44 108 237 365), good := (rows 498 466 508 508 274 492 488 128 256) }] }

theorem u5846 : Upper (D 6) (R 6) [34,65,129,20,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5846 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5847 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 28 274 36 96 200 328), lower := (rows 35 67 133 28 274 36 96 128 256), losses := [] }

theorem u5847 : Upper (D 6) (R 6) [34,65,129,20,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5848 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 304 36 66 200 328), lower := (rows 35 67 133 28 304 36 66 128 256), losses := [] }

theorem u5848 : Upper (D 6) (R 6) [34,65,129,20,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5849 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 132, targets := 32 }], pairs := [(2,5),(3,0)], upper := (rows 35 67 133 28 304 36 72 194 322), lower := (rows 35 67 133 28 304 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 21 44 125 131 259), good := (rows 506 466 508 124 376 124 104 128 256) }] }

theorem u5849 : Upper (D 6) (R 6) [34,65,129,20,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5849 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5850 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 336 36 66 168 296), lower := (rows 35 67 133 28 336 36 66 128 256), losses := [] }

theorem u5850 : Upper (D 6) (R 6) [34,65,129,20,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5851 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 28 336 36 72 162 290), lower := (rows 35 67 133 28 336 36 72 128 256), losses := [] }

theorem u5851 : Upper (D 6) (R 6) [34,65,129,20,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5851 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5852 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 28 336 36 96 138 266), lower := (rows 35 67 133 28 336 36 96 128 256), losses := [] }

theorem u5852 : Upper (D 6) (R 6) [34,65,129,20,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5853 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 28 336 40 66 164 292), lower := (rows 35 67 133 28 336 40 66 128 256), losses := [] }

theorem u5853 : Upper (D 6) (R 6) [34,65,129,20,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5853 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5854 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 132, targets := 64 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(2,6)], upper := (rows 35 67 133 28 336 40 68 162 290), lower := (rows 35 67 133 28 336 40 68 128 256), losses := [] }

theorem u5854 : Upper (D 6) (R 6) [34,65,129,20,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5854 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5855 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 133 28 336 40 96 134 262), lower := (rows 35 67 133 28 336 40 96 128 256), losses := [] }

theorem u5855 : Upper (D 6) (R 6) [34,65,129,20,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5855 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5856 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 44 84 288 66 152 280), lower := (rows 35 67 133 44 84 288 66 128 256), losses := [] }

theorem u5856 : Upper (D 6) (R 6) [34,65,129,36,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5856 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5857 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 67 133 44 84 288 72 146 274), lower := (rows 35 67 133 44 84 288 72 128 256), losses := [] }

theorem u5857 : Upper (D 6) (R 6) [34,65,129,36,68,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5857 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5858 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 44 84 288 80 138 266), lower := (rows 35 67 133 44 84 288 80 128 256), losses := [] }

theorem u5858 : Upper (D 6) (R 6) [34,65,129,36,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5858 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5859 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 44 88 288 66 148 276), lower := (rows 35 67 133 44 88 288 66 128 256), losses := [] }

theorem u5859 : Upper (D 6) (R 6) [34,65,129,36,72,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5859 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 44 88 288 68 146 274), lower := (rows 35 67 133 44 88 288 68 128 256), losses := [] }

theorem u5860 : Upper (D 6) (R 6) [34,65,129,36,72,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5860 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5861 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 44 88 288 80 134 262), lower := (rows 35 67 133 44 88 288 80 128 256), losses := [] }

theorem u5861 : Upper (D 6) (R 6) [34,65,129,36,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5861 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5862 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 56 84 288 66 140 268), lower := (rows 35 67 133 56 84 288 66 128 256), losses := [] }

theorem u5862 : Upper (D 6) (R 6) [34,65,129,48,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5862 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5863 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 56 84 288 68 138 266), lower := (rows 35 67 133 56 84 288 68 128 256), losses := [] }

theorem u5863 : Upper (D 6) (R 6) [34,65,129,48,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5863 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5864 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 133 56 84 288 72 134 262), lower := (rows 35 67 133 56 84 288 72 128 256), losses := [] }

theorem u5864 : Upper (D 6) (R 6) [34,65,129,48,68,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5864 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5865 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 133 56 274 36 68 200 328), lower := (rows 35 67 133 56 274 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 15 19 100 100 239 367), good := (rows 506 506 508 504 410 492 492 128 256) }] }

theorem u5865 : Upper (D 6) (R 6) [34,65,129,48,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5866 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 404, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 67 133 56 274 36 72 196 324), lower := (rows 35 67 133 56 274 36 72 128 256), losses := [] }

theorem u5866 : Upper (D 6) (R 6) [34,65,129,48,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5866 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5867 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 56 336 36 66 140 268), lower := (rows 35 67 133 56 336 36 66 128 256), losses := [] }

theorem u5867 : Upper (D 6) (R 6) [34,65,129,48,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5868 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 133 56 336 36 68 138 266), lower := (rows 35 67 133 56 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 127 23 100 100 131 259), good := (rows 506 506 508 120 376 124 124 128 256) }] }

theorem u5868 : Upper (D 6) (R 6) [34,65,129,48,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 67 133 56 336 36 72 134 262), lower := (rows 35 67 133 56 336 36 72 128 256), losses := [] }

theorem u5869 : Upper (D 6) (R 6) [34,65,129,48,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5869 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5870 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 76 274 36 72 176 304), lower := (rows 35 67 133 76 274 36 72 128 256), losses := [] }

theorem u5870 : Upper (D 6) (R 6) [34,65,129,68,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5870 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5871 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 76 274 36 80 168 296), lower := (rows 35 67 133 76 274 36 80 128 256), losses := [] }

theorem u5871 : Upper (D 6) (R 6) [34,65,129,68,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5871 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5872 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 76 274 36 96 152 280), lower := (rows 35 67 133 76 274 36 96 128 256), losses := [] }

theorem u5872 : Upper (D 6) (R 6) [34,65,129,68,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5873 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 76 276 48 66 168 296), lower := (rows 35 67 133 76 276 48 66 128 256), losses := [] }

theorem u5873 : Upper (D 6) (R 6) [34,65,129,68,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5873 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5874 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 76 276 48 72 162 290), lower := (rows 35 67 133 76 276 48 72 128 256), losses := [] }

theorem u5874 : Upper (D 6) (R 6) [34,65,129,68,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5874 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5875 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 133 76 276 48 96 138 266), lower := (rows 35 67 133 76 276 48 96 128 256), losses := [] }

theorem u5875 : Upper (D 6) (R 6) [34,65,129,68,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5875 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5876 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 76 280 36 66 176 304), lower := (rows 35 67 133 76 280 36 66 128 256), losses := [] }

theorem u5876 : Upper (D 6) (R 6) [34,65,129,68,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5877 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 76 280 36 80 162 290), lower := (rows 35 67 133 76 280 36 80 128 256), losses := [] }

theorem u5877 : Upper (D 6) (R 6) [34,65,129,68,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5877 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5878 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 76 280 36 96 146 274), lower := (rows 35 67 133 76 280 36 96 128 256), losses := [] }

theorem u5878 : Upper (D 6) (R 6) [34,65,129,68,264,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5879 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 76 280 48 66 164 292), lower := (rows 35 67 133 76 280 48 66 128 256), losses := [] }

theorem u5879 : Upper (D 6) (R 6) [34,65,129,68,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5879 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5879
end Delivery.IrregularNine14.P06
