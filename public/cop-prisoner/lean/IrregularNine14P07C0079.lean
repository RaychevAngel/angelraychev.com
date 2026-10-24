import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4740 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 146 288 192 164 292), lower := (rows 35 67 13 88 146 288 192 128 256), losses := [] }

theorem u4740 : Upper (D 7) (R 7) [34,65,9,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4740 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4741 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 176 288 66 132 388), lower := (rows 35 67 13 88 176 288 66 128 256), losses := [] }

theorem u4741 : Upper (D 7) (R 7) [34,65,9,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4741 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4742 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 88 176 288 68 130 386), lower := (rows 35 67 13 88 176 288 68 128 256), losses := [] }

theorem u4742 : Upper (D 7) (R 7) [34,65,9,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4742 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4743 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 176 288 192 134 262), lower := (rows 35 67 13 88 176 288 192 128 256), losses := [] }

theorem u4743 : Upper (D 7) (R 7) [34,65,9,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4743 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4744 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 88 274 160 68 160 416), lower := (rows 35 67 13 88 274 160 68 128 256), losses := [] }

theorem u4744 : Upper (D 7) (R 7) [34,65,9,80,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4744 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4745 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 88 274 160 96 132 388), lower := (rows 35 67 13 88 274 160 96 128 256), losses := [] }

theorem u4745 : Upper (D 7) (R 7) [34,65,9,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4746 : PairBound 9 := { available := 36, camps := [], pairs := [(0,6),(1,5),(2,7),(3,7)], upper := (rows 35 67 13 88 274 160 192 164 292), lower := (rows 35 67 13 88 274 160 192 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 15 88 274 192 192 192 256) },{ target := 6, region := (rows 3 2 4 8 16 228 0 132 260), good := (rows 35 35 429 56 275 160 160 160 256) },{ target := 7, region := (rows 1 2 7 10 19 32 64 0 257), good := (rows 319 351 285 88 286 32 64 0 256) }] }

theorem u4746 : Upper (D 7) (R 7) [34,65,9,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4747 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 88 304 160 66 132 388), lower := (rows 35 67 13 88 304 160 66 128 256), losses := [] }

theorem u4747 : Upper (D 7) (R 7) [34,65,9,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4748 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 304 160 68 130 386), lower := (rows 35 67 13 88 304 160 68 128 256), losses := [] }

theorem u4748 : Upper (D 7) (R 7) [34,65,9,80,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4748 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4749 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(3,5)], upper := (rows 35 67 13 88 304 160 192 134 262), lower := (rows 35 67 13 88 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 98 12 120 376 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 97 97 13 120 376 224 224 224 256) },{ target := 5, region := (rows 1 7 4 24 16 0 228 132 260), good := (rows 67 67 463 88 344 192 192 192 256) }] }

theorem u4749 : Upper (D 7) (R 7) [34,65,9,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4750 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 88 400 160 66 164 292), lower := (rows 35 67 13 88 400 160 66 128 256), losses := [] }

theorem u4750 : Upper (D 7) (R 7) [34,65,9,80,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4751 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 88 400 160 68 162 290), lower := (rows 35 67 13 88 400 160 68 128 256), losses := [] }

theorem u4751 : Upper (D 7) (R 7) [34,65,9,80,384,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4751 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4752 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 4, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 67 13 88 400 160 96 134 262), lower := (rows 35 67 13 88 400 160 96 128 256), losses := [] }

theorem u4752 : Upper (D 7) (R 7) [34,65,9,80,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4753 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 13 138 52 288 80 192 448), lower := (rows 35 67 13 138 52 288 80 128 256), losses := [] }

theorem u4753 : Upper (D 7) (R 7) [34,65,9,130,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4753 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4754 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 496, targets := 3 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 67 13 138 52 288 192 208 336), lower := (rows 35 67 13 138 52 288 192 128 256), losses := [{ target := 5, region := (rows 1 6 4 24 16 0 216 144 272), good := (rows 3 67 79 202 478 256 192 192 256) }] }

theorem u4754 : Upper (D 7) (R 7) [34,65,9,130,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4754 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4755 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 67 13 138 84 288 80 160 416), lower := (rows 35 67 13 138 84 288 80 128 256), losses := [] }

theorem u4755 : Upper (D 7) (R 7) [34,65,9,130,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4755 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4756 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 138 84 288 96 144 400), lower := (rows 35 67 13 138 84 288 96 128 256), losses := [] }

theorem u4756 : Upper (D 7) (R 7) [34,65,9,130,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4756 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4757 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(4,0),(4,1)], upper := (rows 35 67 13 138 84 288 192 176 304), lower := (rows 35 67 13 138 84 288 192 128 256), losses := [] }

theorem u4757 : Upper (D 7) (R 7) [34,65,9,130,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4757 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4758 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 138 176 288 68 208 336), lower := (rows 35 67 13 138 176 288 68 128 256), losses := [] }

theorem u4758 : Upper (D 7) (R 7) [34,65,9,130,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4758 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4759 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 13 138 176 288 80 196 324), lower := (rows 35 67 13 138 176 288 80 128 256), losses := [] }

theorem u4759 : Upper (D 7) (R 7) [34,65,9,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4759 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4760 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 138 208 288 68 176 304), lower := (rows 35 67 13 138 208 288 68 128 256), losses := [] }

theorem u4760 : Upper (D 7) (R 7) [34,65,9,130,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4760 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4761 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 13 138 208 288 80 164 292), lower := (rows 35 67 13 138 208 288 80 128 256), losses := [] }

theorem u4761 : Upper (D 7) (R 7) [34,65,9,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4761 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4762 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 138 208 288 96 148 276), lower := (rows 35 67 13 138 208 288 96 128 256), losses := [] }

theorem u4762 : Upper (D 7) (R 7) [34,65,9,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4762 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4763 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 138 400 48 68 224 352), lower := (rows 35 67 13 138 400 48 68 128 256), losses := [] }

theorem u4763 : Upper (D 7) (R 7) [34,65,9,130,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4763 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4764 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 138 400 48 96 196 324), lower := (rows 35 67 13 138 400 48 96 128 256), losses := [] }

theorem u4764 : Upper (D 7) (R 7) [34,65,9,130,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4764 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4765 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 152 274 36 96 192 448), lower := (rows 35 67 13 152 274 36 96 128 256), losses := [] }

theorem u4765 : Upper (D 7) (R 7) [34,65,9,144,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4765 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4766 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 274 36 192 224 352), lower := (rows 35 67 13 152 274 36 192 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 200 128 256), good := (rows 3 67 79 216 274 6 192 192 256) }] }

theorem u4766 : Upper (D 7) (R 7) [34,65,9,144,258,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4766 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4767 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 274 160 68 224 352), lower := (rows 35 67 13 152 274 160 68 128 256), losses := [] }

theorem u4767 : Upper (D 7) (R 7) [34,65,9,144,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4767 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4768 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 152 274 160 96 196 324), lower := (rows 35 67 13 152 274 160 96 128 256), losses := [] }

theorem u4768 : Upper (D 7) (R 7) [34,65,9,144,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4769 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 304 160 66 196 324), lower := (rows 35 67 13 152 304 160 66 128 256), losses := [] }

theorem u4769 : Upper (D 7) (R 7) [34,65,9,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4770 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 304 160 68 194 322), lower := (rows 35 67 13 152 304 160 68 128 256), losses := [] }

theorem u4770 : Upper (D 7) (R 7) [34,65,9,144,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4770 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4771 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 336 36 66 160 416), lower := (rows 35 67 13 152 336 36 66 128 256), losses := [] }

theorem u4771 : Upper (D 7) (R 7) [34,65,9,144,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4771 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4772 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 152 336 36 96 130 386), lower := (rows 35 67 13 152 336 36 96 128 256), losses := [] }

theorem u4772 : Upper (D 7) (R 7) [34,65,9,144,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4772 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4773 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 336 36 192 162 290), lower := (rows 35 67 13 152 336 36 192 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 200 128 256), good := (rows 3 67 79 216 336 6 192 192 256) }] }

theorem u4773 : Upper (D 7) (R 7) [34,65,9,144,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4773 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4774 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 152 336 160 66 164 292), lower := (rows 35 67 13 152 336 160 66 128 256), losses := [] }

theorem u4774 : Upper (D 7) (R 7) [34,65,9,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4775 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 152 336 160 68 162 290), lower := (rows 35 67 13 152 336 160 68 128 256), losses := [] }

theorem u4775 : Upper (D 7) (R 7) [34,65,9,144,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4775 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4776 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 13 152 336 160 96 134 262), lower := (rows 35 67 13 152 336 160 96 128 256), losses := [] }

theorem u4776 : Upper (D 7) (R 7) [34,65,9,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4777 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 168 84 288 66 144 400), lower := (rows 35 67 13 168 84 288 66 128 256), losses := [] }

theorem u4777 : Upper (D 7) (R 7) [34,65,9,160,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4777 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4778 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 168 84 288 80 130 386), lower := (rows 35 67 13 168 84 288 80 128 256), losses := [] }

theorem u4778 : Upper (D 7) (R 7) [34,65,9,160,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4778 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4779 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 67 13 168 84 288 192 146 274), lower := (rows 35 67 13 168 84 288 192 128 256), losses := [] }

theorem u4779 : Upper (D 7) (R 7) [34,65,9,160,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4779 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4780 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 168 146 288 68 208 336), lower := (rows 35 67 13 168 146 288 68 128 256), losses := [] }

theorem u4780 : Upper (D 7) (R 7) [34,65,9,160,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4780 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4781 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 13 168 146 288 80 196 324), lower := (rows 35 67 13 168 146 288 80 128 256), losses := [] }

theorem u4781 : Upper (D 7) (R 7) [34,65,9,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4781 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4782 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 168 208 288 66 148 276), lower := (rows 35 67 13 168 208 288 66 128 256), losses := [] }

theorem u4782 : Upper (D 7) (R 7) [34,65,9,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4782 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4783 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 168 208 288 68 146 274), lower := (rows 35 67 13 168 208 288 68 128 256), losses := [] }

theorem u4783 : Upper (D 7) (R 7) [34,65,9,160,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4783 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4784 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 13 168 208 288 80 134 262), lower := (rows 35 67 13 168 208 288 80 128 256), losses := [] }

theorem u4784 : Upper (D 7) (R 7) [34,65,9,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4784 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4785 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 52 288 66 144 400), lower := (rows 35 67 13 200 52 288 66 128 256), losses := [] }

theorem u4785 : Upper (D 7) (R 7) [34,65,9,192,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4785 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4786 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 13 200 52 288 80 130 386), lower := (rows 35 67 13 200 52 288 80 128 256), losses := [] }

theorem u4786 : Upper (D 7) (R 7) [34,65,9,192,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4786 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4787 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 200 52 288 192 146 274), lower := (rows 35 67 13 200 52 288 192 128 256), losses := [] }

theorem u4787 : Upper (D 7) (R 7) [34,65,9,192,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4787 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4788 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 200 146 288 68 176 304), lower := (rows 35 67 13 200 146 288 68 128 256), losses := [] }

theorem u4788 : Upper (D 7) (R 7) [34,65,9,192,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4788 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4789 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 200 146 288 80 164 292), lower := (rows 35 67 13 200 146 288 80 128 256), losses := [] }

theorem u4789 : Upper (D 7) (R 7) [34,65,9,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4789 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4790 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 200 146 288 96 148 276), lower := (rows 35 67 13 200 146 288 96 128 256), losses := [] }

theorem u4790 : Upper (D 7) (R 7) [34,65,9,192,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4790 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4791 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 148 288 66 176 304), lower := (rows 35 67 13 200 148 288 66 128 256), losses := [] }

theorem u4791 : Upper (D 7) (R 7) [34,65,9,192,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4791 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4792 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 200 148 288 80 162 290), lower := (rows 35 67 13 200 148 288 80 128 256), losses := [] }

theorem u4792 : Upper (D 7) (R 7) [34,65,9,192,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4792 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4793 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 200 148 288 96 146 274), lower := (rows 35 67 13 200 148 288 96 128 256), losses := [] }

theorem u4793 : Upper (D 7) (R 7) [34,65,9,192,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4793 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4794 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 200 176 288 66 148 276), lower := (rows 35 67 13 200 176 288 66 128 256), losses := [] }

theorem u4794 : Upper (D 7) (R 7) [34,65,9,192,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4794 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4795 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 200 176 288 68 146 274), lower := (rows 35 67 13 200 176 288 68 128 256), losses := [] }

theorem u4795 : Upper (D 7) (R 7) [34,65,9,192,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4795 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4796 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 200 176 288 80 134 262), lower := (rows 35 67 13 200 176 288 80 128 256), losses := [] }

theorem u4796 : Upper (D 7) (R 7) [34,65,9,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4796 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4797 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 200 274 160 68 176 304), lower := (rows 35 67 13 200 274 160 68 128 256), losses := [] }

theorem u4797 : Upper (D 7) (R 7) [34,65,9,192,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4797 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4798 : Route 9 := (fun mask => (mask,id))

def c4798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4798 : Upper (D 7) (R 7) [34,65,9,192,258,128,16] 13 := by
  apply FastRouting.sound _ _ [34,65,9,192,258,128,16] 13 (by decide) (choices 1) [4,32] r4798 c4798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u372
  · exact u373

def b4799 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 67 13 200 274 160 96 148 276), lower := (rows 35 67 13 200 274 160 96 128 256), losses := [] }

theorem u4799 : Upper (D 7) (R 7) [34,65,9,192,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4799
end Delivery.IrregularNine14.P07
