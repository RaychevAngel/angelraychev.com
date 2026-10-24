import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9720 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(4,5)], upper := (rows 37 290 28 11 82 160 192 193 321), lower := (rows 37 290 28 11 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 224 224 128 256), good := (rows 100 370 28 30 114 224 224 224 256) }] }

theorem u9720 : Upper (D 7) (R 7) [36,288,24,3,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9721 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 28 73 82 160 65 130 386), lower := (rows 37 290 28 73 82 160 65 128 256), losses := [] }

theorem u9721 : Upper (D 7) (R 7) [36,288,24,65,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9722 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 28 73 82 160 66 129 385), lower := (rows 37 290 28 73 82 160 66 128 256), losses := [] }

theorem u9722 : Upper (D 7) (R 7) [36,288,24,65,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9723 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(0,6),(1,6),(1,7),(4,0)], upper := (rows 37 290 28 73 82 160 192 131 259), lower := (rows 37 290 28 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 28 104 114 224 224 224 256) }] }

theorem u9723 : Upper (D 7) (R 7) [36,288,24,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9724 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 69 25 26 160 66 192 448), lower := (rows 37 290 69 25 26 160 66 128 256), losses := [] }

theorem u9724 : Upper (D 7) (R 7) [36,288,65,17,10,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9725 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 290 69 25 26 160 192 194 322), lower := (rows 37 290 69 25 26 160 192 128 256), losses := [] }

theorem u9725 : Upper (D 7) (R 7) [36,288,65,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9726 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 69 25 82 160 66 136 392), lower := (rows 37 290 69 25 82 160 66 128 256), losses := [] }

theorem u9726 : Upper (D 7) (R 7) [36,288,65,17,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9727 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 69 25 82 160 72 130 386), lower := (rows 37 290 69 25 82 160 72 128 256), losses := [] }

theorem u9727 : Upper (D 7) (R 7) [36,288,65,17,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9727 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9728 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 290 69 25 82 160 192 138 266), lower := (rows 37 290 69 25 82 160 192 128 256), losses := [] }

theorem u9728 : Upper (D 7) (R 7) [36,288,65,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9729 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 290 69 25 146 160 66 200 328), lower := (rows 37 290 69 25 146 160 66 128 256), losses := [] }

theorem u9729 : Upper (D 7) (R 7) [36,288,65,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9730 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 290 69 25 146 160 72 194 322), lower := (rows 37 290 69 25 146 160 72 128 256), losses := [] }

theorem u9730 : Upper (D 7) (R 7) [36,288,65,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9730 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9731 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 69 26 88 160 65 130 386), lower := (rows 37 290 69 26 88 160 65 128 256), losses := [] }

theorem u9731 : Upper (D 7) (R 7) [36,288,65,18,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9732 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 290 69 26 88 160 66 129 385), lower := (rows 37 290 69 26 88 160 66 128 256), losses := [] }

theorem u9732 : Upper (D 7) (R 7) [36,288,65,18,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9733 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(0,6),(1,6),(2,1)], upper := (rows 37 290 69 26 88 160 192 131 259), lower := (rows 37 290 69 26 88 160 192 128 256), losses := [] }

theorem u9733 : Upper (D 7) (R 7) [36,288,65,18,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9734 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 37 290 69 26 145 40 66 192 448), lower := (rows 37 290 69 26 145 40 66 128 256), losses := [] }

theorem u9734 : Upper (D 7) (R 7) [36,288,65,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9734 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9735 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 290 69 26 145 40 192 194 322), lower := (rows 37 290 69 26 145 40 192 128 256), losses := [] }

theorem u9735 : Upper (D 7) (R 7) [36,288,65,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9735 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9736 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 290 69 26 145 160 66 200 328), lower := (rows 37 290 69 26 145 160 66 128 256), losses := [] }

theorem u9736 : Upper (D 7) (R 7) [36,288,65,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9737 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 37 290 69 26 145 160 72 194 322), lower := (rows 37 290 69 26 145 160 72 128 256), losses := [{ target := 1, region := (rows 9 0 76 8 16 176 72 128 256), good := (rows 37 288 69 125 177 160 77 160 256) }] }

theorem u9737 : Upper (D 7) (R 7) [36,288,65,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9737 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9738 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 442, targets := 1 },{ cop := 5, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 290 69 26 152 160 65 194 322), lower := (rows 37 290 69 26 152 160 65 128 256), losses := [] }

theorem u9738 : Upper (D 7) (R 7) [36,288,65,18,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9739 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 290 69 26 152 160 66 193 321), lower := (rows 37 290 69 26 152 160 66 128 256), losses := [] }

theorem u9739 : Upper (D 7) (R 7) [36,288,65,18,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9740 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 290 69 26 208 34 65 136 392), lower := (rows 37 290 69 26 208 34 65 128 256), losses := [] }

theorem u9740 : Upper (D 7) (R 7) [36,288,65,18,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9741 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 }], pairs := [(1,0),(1,6),(1,7)], upper := (rows 37 290 69 26 208 34 72 129 385), lower := (rows 37 290 69 26 208 34 72 128 256), losses := [] }

theorem u9741 : Upper (D 7) (R 7) [36,288,65,18,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9741 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9742 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 290 69 26 208 34 192 137 265), lower := (rows 37 290 69 26 208 34 192 128 256), losses := [] }

theorem u9742 : Upper (D 7) (R 7) [36,288,65,18,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9743 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 290 69 26 208 40 65 130 386), lower := (rows 37 290 69 26 208 40 65 128 256), losses := [] }

theorem u9743 : Upper (D 7) (R 7) [36,288,65,18,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9743 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9744 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 37 290 69 26 208 40 66 129 385), lower := (rows 37 290 69 26 208 40 66 128 256), losses := [] }

theorem u9744 : Upper (D 7) (R 7) [36,288,65,18,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9744 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9745 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 69 26 208 40 192 131 259), lower := (rows 37 290 69 26 208 40 192 128 256), losses := [] }

theorem u9745 : Upper (D 7) (R 7) [36,288,65,18,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9745 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9746 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 290 69 26 208 160 65 138 266), lower := (rows 37 290 69 26 208 160 65 128 256), losses := [] }

theorem u9746 : Upper (D 7) (R 7) [36,288,65,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9747 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 26 208 160 66 137 265), lower := (rows 37 290 69 26 208 160 66 128 256), losses := [] }

theorem u9747 : Upper (D 7) (R 7) [36,288,65,18,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9748 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(0,6),(1,6)], upper := (rows 37 290 69 26 208 160 72 131 259), lower := (rows 37 290 69 26 208 160 72 128 256), losses := [] }

theorem u9748 : Upper (D 7) (R 7) [36,288,65,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9748 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9749 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 69 74 145 160 66 152 280), lower := (rows 37 290 69 74 145 160 66 128 256), losses := [] }

theorem u9749 : Upper (D 7) (R 7) [36,288,65,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9750 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 69 74 145 160 72 146 274), lower := (rows 37 290 69 74 145 160 72 128 256), losses := [] }

theorem u9750 : Upper (D 7) (R 7) [36,288,65,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9750 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9751 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 290 69 74 145 160 80 138 266), lower := (rows 37 290 69 74 145 160 80 128 256), losses := [] }

theorem u9751 : Upper (D 7) (R 7) [36,288,65,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9751 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9752 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 290 69 74 146 48 65 136 392), lower := (rows 37 290 69 74 146 48 65 128 256), losses := [] }

theorem u9752 : Upper (D 7) (R 7) [36,288,65,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9753 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 290 69 74 146 48 72 129 385), lower := (rows 37 290 69 74 146 48 72 128 256), losses := [] }

theorem u9753 : Upper (D 7) (R 7) [36,288,65,66,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9753 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9754 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 37 290 69 74 146 48 192 137 265), lower := (rows 37 290 69 74 146 48 192 128 256), losses := [] }

theorem u9754 : Upper (D 7) (R 7) [36,288,65,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9754 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9755 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 290 69 74 146 160 65 152 280), lower := (rows 37 290 69 74 146 160 65 128 256), losses := [] }

theorem u9755 : Upper (D 7) (R 7) [36,288,65,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9756 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 69 74 146 160 72 145 273), lower := (rows 37 290 69 74 146 160 72 128 256), losses := [] }

theorem u9756 : Upper (D 7) (R 7) [36,288,65,66,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9756 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9757 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(2,1),(3,5)], upper := (rows 37 290 69 74 146 160 80 137 265), lower := (rows 37 290 69 74 146 160 80 128 256), losses := [] }

theorem u9757 : Upper (D 7) (R 7) [36,288,65,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9757 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9758 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 290 69 74 152 48 65 130 386), lower := (rows 37 290 69 74 152 48 65 128 256), losses := [] }

theorem u9758 : Upper (D 7) (R 7) [36,288,65,66,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9758 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9759 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 69 74 152 48 66 129 385), lower := (rows 37 290 69 74 152 48 66 128 256), losses := [] }

theorem u9759 : Upper (D 7) (R 7) [36,288,65,66,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9759 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9760 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,1),(1,6),(2,1)], upper := (rows 37 290 69 74 152 48 192 131 259), lower := (rows 37 290 69 74 152 48 192 128 256), losses := [] }

theorem u9760 : Upper (D 7) (R 7) [36,288,65,66,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9760 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9761 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 290 69 74 152 160 65 146 274), lower := (rows 37 290 69 74 152 160 65 128 256), losses := [] }

theorem u9761 : Upper (D 7) (R 7) [36,288,65,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9762 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 37 290 69 74 152 160 66 145 273), lower := (rows 37 290 69 74 152 160 66 128 256), losses := [] }

theorem u9762 : Upper (D 7) (R 7) [36,288,65,66,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9763 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,6),(1,6)], upper := (rows 37 290 69 74 152 160 80 131 259), lower := (rows 37 290 69 74 152 160 80 128 256), losses := [] }

theorem u9763 : Upper (D 7) (R 7) [36,288,65,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9763 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9764 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 290 69 88 146 160 65 138 266), lower := (rows 37 290 69 88 146 160 65 128 256), losses := [] }

theorem u9764 : Upper (D 7) (R 7) [36,288,65,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9765 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 290 69 88 146 160 66 137 265), lower := (rows 37 290 69 88 146 160 66 128 256), losses := [] }

theorem u9765 : Upper (D 7) (R 7) [36,288,65,80,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9766 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 290 69 88 146 160 72 131 259), lower := (rows 37 290 69 88 146 160 72 128 256), losses := [] }

theorem u9766 : Upper (D 7) (R 7) [36,288,65,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9766 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9767 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 136, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 37 290 69 137 146 48 66 200 328), lower := (rows 37 290 69 137 146 48 66 128 256), losses := [] }

theorem u9767 : Upper (D 7) (R 7) [36,288,65,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9767 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9768 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 37 290 69 137 146 48 72 194 322), lower := (rows 37 290 69 137 146 48 72 128 256), losses := [] }

theorem u9768 : Upper (D 7) (R 7) [36,288,65,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9768 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9769 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 290 69 138 208 34 65 152 280), lower := (rows 37 290 69 138 208 34 65 128 256), losses := [] }

theorem u9769 : Upper (D 7) (R 7) [36,288,65,130,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9770 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 290 69 138 208 34 72 145 273), lower := (rows 37 290 69 138 208 34 72 128 256), losses := [] }

theorem u9770 : Upper (D 7) (R 7) [36,288,65,130,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9770 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9771 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 290 69 138 208 34 80 137 265), lower := (rows 37 290 69 138 208 34 80 128 256), losses := [] }

theorem u9771 : Upper (D 7) (R 7) [36,288,65,130,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9771 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9772 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 290 69 138 208 40 65 146 274), lower := (rows 37 290 69 138 208 40 65 128 256), losses := [] }

theorem u9772 : Upper (D 7) (R 7) [36,288,65,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9772 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9773 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 37 290 69 138 208 40 66 145 273), lower := (rows 37 290 69 138 208 40 66 128 256), losses := [] }

theorem u9773 : Upper (D 7) (R 7) [36,288,65,130,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9773 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9774 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 290 69 138 208 40 80 131 259), lower := (rows 37 290 69 138 208 40 80 128 256), losses := [] }

theorem u9774 : Upper (D 7) (R 7) [36,288,65,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9774 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9775 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 290 70 11 88 160 65 144 400), lower := (rows 37 290 70 11 88 160 65 128 256), losses := [] }

theorem u9775 : Upper (D 7) (R 7) [36,288,66,3,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9776 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 11 88 160 80 129 385), lower := (rows 37 290 70 11 88 160 80 128 256), losses := [] }

theorem u9776 : Upper (D 7) (R 7) [36,288,66,3,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9776 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9777 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,0),(2,5),(4,1),(4,5)], upper := (rows 37 290 70 11 88 160 192 145 273), lower := (rows 37 290 70 11 88 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 224 224 128 256), good := (rows 100 358 102 14 120 224 224 224 256) }] }

theorem u9777 : Upper (D 7) (R 7) [36,288,66,3,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9778 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 290 70 11 145 160 72 208 336), lower := (rows 37 290 70 11 145 160 72 128 256), losses := [] }

theorem u9778 : Upper (D 7) (R 7) [36,288,66,3,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9778 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9779 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 290 70 11 145 160 80 200 328), lower := (rows 37 290 70 11 145 160 80 128 256), losses := [] }

theorem u9779 : Upper (D 7) (R 7) [36,288,66,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9779 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9779
end Delivery.IrregularNine14.P07
