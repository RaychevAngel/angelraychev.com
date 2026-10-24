import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5700 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 8, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 131 292 13 82 96 68 162 290), lower := (rows 25 131 292 13 82 96 68 128 256), losses := [] }

theorem u5700 : Upper (D 6) (R 6) [24,129,288,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5701 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 25 131 292 13 82 96 96 134 262), lower := (rows 25 131 292 13 82 96 96 128 256), losses := [] }

theorem u5701 : Upper (D 6) (R 6) [24,129,288,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5702 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 5, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 25 131 292 14 50 96 65 196 324), lower := (rows 25 131 292 14 50 96 65 128 256), losses := [] }

theorem u5702 : Upper (D 6) (R 6) [24,129,288,6,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5703 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 100, targets := 3 },{ cop := 3, region := 112, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 131 292 14 50 96 68 193 321), lower := (rows 25 131 292 14 50 96 68 128 256), losses := [] }

theorem u5703 : Upper (D 6) (R 6) [24,129,288,6,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 81 96 66 164 292), lower := (rows 25 131 292 14 81 96 66 128 256), losses := [] }

theorem u5704 : Upper (D 6) (R 6) [24,129,288,6,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 364, targets := 1 },{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 25 131 292 14 81 96 68 162 290), lower := (rows 25 131 292 14 81 96 68 128 256), losses := [] }

theorem u5705 : Upper (D 6) (R 6) [24,129,288,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 131 292 14 81 96 96 134 262), lower := (rows 25 131 292 14 81 96 96 128 256), losses := [] }

theorem u5706 : Upper (D 6) (R 6) [24,129,288,6,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5707 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 14 82 96 65 164 292), lower := (rows 25 131 292 14 82 96 65 128 256), losses := [] }

theorem u5707 : Upper (D 6) (R 6) [24,129,288,6,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 81, targets := 32 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(4,5)], upper := (rows 25 131 292 14 82 96 68 161 289), lower := (rows 25 131 292 14 82 96 68 128 256), losses := [] }

theorem u5708 : Upper (D 6) (R 6) [24,129,288,6,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5709 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 131 292 14 82 96 96 133 261), lower := (rows 25 131 292 14 82 96 96 128 256), losses := [] }

theorem u5709 : Upper (D 6) (R 6) [24,129,288,6,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5710 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 81, targets := 32 },{ cop := 0, region := 226, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 131 292 14 84 33 66 224 352), lower := (rows 25 131 292 14 84 33 66 128 256), losses := [] }

theorem u5710 : Upper (D 6) (R 6) [24,129,288,6,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5711 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 131 292 14 84 33 96 194 322), lower := (rows 25 131 292 14 84 33 96 128 256), losses := [] }

theorem u5711 : Upper (D 6) (R 6) [24,129,288,6,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5712 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 81, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 131 292 14 84 34 65 224 352), lower := (rows 25 131 292 14 84 34 65 128 256), losses := [] }

theorem u5712 : Upper (D 6) (R 6) [24,129,288,6,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5713 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 131 292 14 84 34 96 193 321), lower := (rows 25 131 292 14 84 34 96 128 256), losses := [] }

theorem u5713 : Upper (D 6) (R 6) [24,129,288,6,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5714 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 81, targets := 2 },{ cop := 3, region := 81, targets := 32 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 131 292 14 84 96 65 162 290), lower := (rows 25 131 292 14 84 96 65 128 256), losses := [] }

theorem u5714 : Upper (D 6) (R 6) [24,129,288,6,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 81, targets := 32 },{ cop := 0, region := 226, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 131 292 14 84 96 66 161 289), lower := (rows 25 131 292 14 84 96 66 128 256), losses := [] }

theorem u5715 : Upper (D 6) (R 6) [24,129,288,6,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 25 131 292 14 84 96 96 131 259), lower := (rows 25 131 292 14 84 96 96 128 256), losses := [] }

theorem u5716 : Upper (D 6) (R 6) [24,129,288,6,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5717 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 25 131 292 14 112 33 66 196 324), lower := (rows 25 131 292 14 112 33 66 128 256), losses := [] }

theorem u5717 : Upper (D 6) (R 6) [24,129,288,6,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5718 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 80, targets := 3 },{ cop := 3, region := 113, targets := 2 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 25 131 292 14 112 33 68 194 322), lower := (rows 25 131 292 14 112 33 68 128 256), losses := [] }

theorem u5718 : Upper (D 6) (R 6) [24,129,288,6,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5719 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 4, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 25 131 292 14 112 34 65 196 324), lower := (rows 25 131 292 14 112 34 65 128 256), losses := [] }

theorem u5719 : Upper (D 6) (R 6) [24,129,288,6,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5720 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 25 131 292 14 112 34 68 193 321), lower := (rows 25 131 292 14 112 34 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 20 32 76 137 265), good := (rows 473 385 372 477 112 32 84 128 256) }] }

theorem u5720 : Upper (D 6) (R 6) [24,129,288,6,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 260, targets := 65 },{ cop := 1, region := 104, targets := 4 }], pairs := [(2,0),(2,6),(3,2)], upper := (rows 25 131 292 42 84 96 65 134 262), lower := (rows 25 131 292 42 84 96 65 128 256), losses := [] }

theorem u5721 : Upper (D 6) (R 6) [24,129,288,34,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 104, targets := 5 }], pairs := [(0,1),(3,0),(3,2)], upper := (rows 25 131 292 42 84 96 66 133 261), lower := (rows 25 131 292 42 84 96 66 128 256), losses := [{ target := 1, region := (rows 9 0 77 8 112 112 64 139 267), good := (rows 445 389 308 445 116 116 500 128 256) }] }

theorem u5722 : Upper (D 6) (R 6) [24,129,288,34,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5723 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 131 292 42 84 96 68 131 259), lower := (rows 25 131 292 42 84 96 68 128 256), losses := [] }

theorem u5723 : Upper (D 6) (R 6) [24,129,288,34,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5724 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 309, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 131 292 74 84 33 66 164 292), lower := (rows 25 131 292 74 84 33 66 128 256), losses := [] }

theorem u5724 : Upper (D 6) (R 6) [24,129,288,66,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 131 292 74 84 33 68 162 290), lower := (rows 25 131 292 74 84 33 68 128 256), losses := [] }

theorem u5725 : Upper (D 6) (R 6) [24,129,288,66,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 131 292 74 84 33 96 134 262), lower := (rows 25 131 292 74 84 33 96 128 256), losses := [] }

theorem u5726 : Upper (D 6) (R 6) [24,129,288,66,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5727 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 131 292 74 84 34 65 164 292), lower := (rows 25 131 292 74 84 34 65 128 256), losses := [] }

theorem u5727 : Upper (D 6) (R 6) [24,129,288,66,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 131 292 74 84 34 68 161 289), lower := (rows 25 131 292 74 84 34 68 128 256), losses := [] }

theorem u5728 : Upper (D 6) (R 6) [24,129,288,66,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5729 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 131 292 74 84 34 96 133 261), lower := (rows 25 131 292 74 84 34 96 128 256), losses := [] }

theorem u5729 : Upper (D 6) (R 6) [24,129,288,66,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5730 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 131 292 76 112 34 65 134 262), lower := (rows 25 131 292 76 112 34 65 128 256), losses := [] }

theorem u5730 : Upper (D 6) (R 6) [24,129,288,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5731 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 131 292 76 112 34 66 133 261), lower := (rows 25 131 292 76 112 34 66 128 256), losses := [] }

theorem u5731 : Upper (D 6) (R 6) [24,129,288,68,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5732 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 131 292 76 112 34 68 131 259), lower := (rows 25 131 292 76 112 34 68 128 256), losses := [] }

theorem u5732 : Upper (D 6) (R 6) [24,129,288,68,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5733 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 262 11 52 96 65 224 352), lower := (rows 25 134 262 11 52 96 65 128 256), losses := [] }

theorem u5733 : Upper (D 6) (R 6) [24,132,258,3,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5734 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 25 134 262 11 52 96 96 193 321), lower := (rows 25 134 262 11 52 96 96 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 22 511 511 137 265), good := (rows 505 244 372 505 116 96 96 224 352) }] }

theorem u5734 : Upper (D 6) (R 6) [24,132,258,3,36,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5735 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 262 11 112 33 68 224 352), lower := (rows 25 134 262 11 112 33 68 128 256), losses := [] }

theorem u5735 : Upper (D 6) (R 6) [24,132,258,3,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 25 134 262 11 112 36 96 193 321), lower := (rows 25 134 262 11 112 36 96 128 256), losses := [] }

theorem u5736 : Upper (D 6) (R 6) [24,132,258,3,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 25 134 262 41 81 34 68 224 352), lower := (rows 25 134 262 41 81 34 68 128 256), losses := [{ target := 1, region := (rows 41 0 4 40 48 32 70 160 288), good := (rows 25 196 324 441 81 505 68 128 256) }] }

theorem u5737 : Upper (D 6) (R 6) [24,132,258,33,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 89, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 134 262 41 81 34 96 196 324), lower := (rows 25 134 262 41 81 34 96 128 256), losses := [] }

theorem u5738 : Upper (D 6) (R 6) [24,132,258,33,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5739 : Route 9 := (fun mask => (mask,id))

def c5739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5739 : Upper (D 6) (R 6) [24,132,258,34,36,64,1] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,36,64,1] 13 (by decide) (choices 1) [1,64] r5739 c5739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u429
  · exact u430

def r5740 : Route 9 := (fun mask => (mask,id))

def c5740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5740 : Upper (D 6) (R 6) [24,132,258,34,68,1,1] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,68,1,1] 13 (by decide) (choices 1) [32,64] r5740 c5740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u431
  · exact u432

def r5741 : Route 9 := (fun mask => (mask,id))

def c5741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5741 : Upper (D 6) (R 6) [24,132,258,34,68,1,32] 13 := by
  apply FastRouting.sound _ _ [24,132,258,34,68,1,32] 13 (by decide) (choices 1) [1,64] r5741 c5741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u433
  · exact u434

def b5742 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 25 134 262 42 84 96 96 129 257), lower := (rows 25 134 262 42 84 96 96 128 256), losses := [] }

theorem u5742 : Upper (D 6) (R 6) [24,132,258,34,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 81, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 262 42 112 33 65 196 324), lower := (rows 25 134 262 42 112 33 65 128 256), losses := [] }

theorem u5743 : Upper (D 6) (R 6) [24,132,258,34,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 25 134 262 42 112 33 68 193 321), lower := (rows 25 134 262 42 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 32 70 128 256), good := (rows 24 198 326 122 112 32 68 128 256) }] }

theorem u5744 : Upper (D 6) (R 6) [24,132,258,34,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5745 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 11 84 34 65 224 352), lower := (rows 25 134 292 11 84 34 65 128 256), losses := [] }

theorem u5745 : Upper (D 6) (R 6) [24,132,288,3,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5746 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 25 134 292 11 84 34 96 193 321), lower := (rows 25 134 292 11 84 34 96 128 256), losses := [] }

theorem u5746 : Upper (D 6) (R 6) [24,132,288,3,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5747 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 11 84 96 65 162 290), lower := (rows 25 134 292 11 84 96 65 128 256), losses := [] }

theorem u5747 : Upper (D 6) (R 6) [24,132,288,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5748 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 11 84 96 66 161 289), lower := (rows 25 134 292 11 84 96 66 128 256), losses := [] }

theorem u5748 : Upper (D 6) (R 6) [24,132,288,3,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5749 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 25 134 292 11 84 96 96 131 259), lower := (rows 25 134 292 11 84 96 96 128 256), losses := [] }

theorem u5749 : Upper (D 6) (R 6) [24,132,288,3,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 134 292 11 112 34 65 196 324), lower := (rows 25 134 292 11 112 34 65 128 256), losses := [] }

theorem u5750 : Upper (D 6) (R 6) [24,132,288,3,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5751 : Route 9 := (fun mask => (mask,id))

def c5751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5751 : Upper (D 6) (R 6) [24,132,288,3,96,2,4] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,96,2,4] 13 (by decide) (choices 1) [1,64] r5751 c5751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u435
  · exact u436

def b5752 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 13 50 96 65 194 322), lower := (rows 25 134 292 13 50 96 65 128 256), losses := [] }

theorem u5752 : Upper (D 6) (R 6) [24,132,288,5,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(4,0),(4,2)], upper := (rows 25 134 292 13 50 96 66 193 321), lower := (rows 25 134 292 13 50 96 66 128 256), losses := [] }

theorem u5753 : Upper (D 6) (R 6) [24,132,288,5,34,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 13 81 34 66 224 352), lower := (rows 25 134 292 13 81 34 66 128 256), losses := [] }

theorem u5754 : Upper (D 6) (R 6) [24,132,288,5,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5755 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 134 292 13 81 34 96 194 322), lower := (rows 25 134 292 13 81 34 96 128 256), losses := [] }

theorem u5755 : Upper (D 6) (R 6) [24,132,288,5,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 13 82 34 65 224 352), lower := (rows 25 134 292 13 82 34 65 128 256), losses := [] }

theorem u5756 : Upper (D 6) (R 6) [24,132,288,5,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5757 : Route 9 := (fun mask => (mask,id))

def c5757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5757 : Upper (D 6) (R 6) [24,132,288,5,66,2,32] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,66,2,32] 13 (by decide) (choices 1) [1,64] r5757 c5757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u437
  · exact u438

def b5758 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 13 82 96 65 162 290), lower := (rows 25 134 292 13 82 96 65 128 256), losses := [] }

theorem u5758 : Upper (D 6) (R 6) [24,132,288,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5759 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 134 292 13 82 96 66 161 289), lower := (rows 25 134 292 13 82 96 66 128 256), losses := [] }

theorem u5759 : Upper (D 6) (R 6) [24,132,288,5,66,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P06
