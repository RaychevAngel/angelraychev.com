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

def b10680 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 42 82 160 80 132 388), lower := (rows 97 259 13 42 82 160 80 128 256), losses := [] }

theorem u10680 : Upper (D 7) (R 7) [96,257,9,34,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10680 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10681 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 42 82 160 192 148 276), lower := (rows 97 259 13 42 82 160 192 128 256), losses := [] }

theorem u10681 : Upper (D 7) (R 7) [96,257,9,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10682 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 97 259 13 42 84 160 66 144 400), lower := (rows 97 259 13 42 84 160 66 128 256), losses := [] }

theorem u10682 : Upper (D 7) (R 7) [96,257,9,34,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10683 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 85, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 42 84 160 80 130 386), lower := (rows 97 259 13 42 84 160 80 128 256), losses := [] }

theorem u10683 : Upper (D 7) (R 7) [96,257,9,34,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10683 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10684 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 42 84 160 192 146 274), lower := (rows 97 259 13 42 84 160 192 128 256), losses := [] }

theorem u10684 : Upper (D 7) (R 7) [96,257,9,34,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10685 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 97 259 13 42 148 160 66 208 336), lower := (rows 97 259 13 42 148 160 66 128 256), losses := [] }

theorem u10685 : Upper (D 7) (R 7) [96,257,9,34,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10686 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 13 42 148 160 80 194 322), lower := (rows 97 259 13 42 148 160 80 128 256), losses := [] }

theorem u10686 : Upper (D 7) (R 7) [96,257,9,34,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10686 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10687 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 97 259 13 42 208 160 66 148 276), lower := (rows 97 259 13 42 208 160 66 128 256), losses := [] }

theorem u10687 : Upper (D 7) (R 7) [96,257,9,34,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10688 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 42 208 160 68 146 274), lower := (rows 97 259 13 42 208 160 68 128 256), losses := [] }

theorem u10688 : Upper (D 7) (R 7) [96,257,9,34,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10688 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10689 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 270, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 42 208 160 80 134 262), lower := (rows 97 259 13 42 208 160 80 128 256), losses := [] }

theorem u10689 : Upper (D 7) (R 7) [96,257,9,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10689 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10690 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 1 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(3,0),(4,5)], upper := (rows 97 259 13 56 22 160 66 192 448), lower := (rows 97 259 13 56 22 160 66 128 256), losses := [] }

theorem u10690 : Upper (D 7) (R 7) [96,257,9,48,6,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10691 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 56 22 160 192 194 322), lower := (rows 97 259 13 56 22 160 192 128 256), losses := [] }

theorem u10691 : Upper (D 7) (R 7) [96,257,9,48,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10692 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 97 259 13 56 82 160 66 132 388), lower := (rows 97 259 13 56 82 160 66 128 256), losses := [] }

theorem u10692 : Upper (D 7) (R 7) [96,257,9,48,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10693 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 56 82 160 68 130 386), lower := (rows 97 259 13 56 82 160 68 128 256), losses := [] }

theorem u10693 : Upper (D 7) (R 7) [96,257,9,48,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10693 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10694 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 13 56 82 160 192 134 262), lower := (rows 97 259 13 56 82 160 192 128 256), losses := [] }

theorem u10694 : Upper (D 7) (R 7) [96,257,9,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10695 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 56 148 34 66 192 448), lower := (rows 97 259 13 56 148 34 66 128 256), losses := [] }

theorem u10695 : Upper (D 7) (R 7) [96,257,9,48,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10696 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 97 259 13 56 148 34 192 194 322), lower := (rows 97 259 13 56 148 34 192 128 256), losses := [] }

theorem u10696 : Upper (D 7) (R 7) [96,257,9,48,132,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10697 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 386, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 56 208 34 66 132 388), lower := (rows 97 259 13 56 208 34 66 128 256), losses := [] }

theorem u10697 : Upper (D 7) (R 7) [96,257,9,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10698 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 56 208 34 68 130 386), lower := (rows 97 259 13 56 208 34 68 128 256), losses := [] }

theorem u10698 : Upper (D 7) (R 7) [96,257,9,48,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10698 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10699 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 259 13 56 208 34 192 134 262), lower := (rows 97 259 13 56 208 34 192 128 256), losses := [] }

theorem u10699 : Upper (D 7) (R 7) [96,257,9,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10700 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 22 48 96 192 448), lower := (rows 97 259 13 138 22 48 96 128 256), losses := [] }

theorem u10700 : Upper (D 7) (R 7) [96,257,9,130,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10700 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10701 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 258, targets := 128 },{ cop := 4, region := 232, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(3,0)], upper := (rows 97 259 13 138 22 48 192 224 352), lower := (rows 97 259 13 138 22 48 192 128 256), losses := [] }

theorem u10701 : Upper (D 7) (R 7) [96,257,9,130,6,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10701 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10702 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 13 138 22 96 192 176 304), lower := (rows 97 259 13 138 22 96 192 128 256), losses := [] }

theorem u10702 : Upper (D 7) (R 7) [96,257,9,130,6,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10703 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,7),(4,0),(4,7)], upper := (rows 97 259 13 138 50 160 68 208 336), lower := (rows 97 259 13 138 50 160 68 128 256), losses := [] }

theorem u10703 : Upper (D 7) (R 7) [96,257,9,130,34,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10703 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10704 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 50 160 80 196 324), lower := (rows 97 259 13 138 50 160 80 128 256), losses := [] }

theorem u10704 : Upper (D 7) (R 7) [96,257,9,130,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10704 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10705 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0)], upper := (rows 97 259 13 138 148 34 80 224 352), lower := (rows 97 259 13 138 148 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 20 42 84 133 261), good := (rows 480 426 508 170 468 42 80 128 256) }] }

theorem u10705 : Upper (D 7) (R 7) [96,257,9,130,132,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10705 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10706 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 13 138 148 34 96 208 336), lower := (rows 97 259 13 138 148 34 96 128 256), losses := [] }

theorem u10706 : Upper (D 7) (R 7) [96,257,9,130,132,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10707 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 148 48 96 194 322), lower := (rows 97 259 13 138 148 48 96 128 256), losses := [] }

theorem u10707 : Upper (D 7) (R 7) [96,257,9,130,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10707 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10708 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,0),(4,6)], upper := (rows 97 259 13 138 176 34 68 208 336), lower := (rows 97 259 13 138 176 34 68 128 256), losses := [] }

theorem u10708 : Upper (D 7) (R 7) [96,257,9,130,160,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10708 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10709 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 138 176 34 80 196 324), lower := (rows 97 259 13 138 176 34 80 128 256), losses := [] }

theorem u10709 : Upper (D 7) (R 7) [96,257,9,130,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10709 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10710 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 97 259 13 138 176 36 66 208 336), lower := (rows 97 259 13 138 176 36 66 128 256), losses := [] }

theorem u10710 : Upper (D 7) (R 7) [96,257,9,130,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10710 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10711 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 259 13 138 176 36 80 194 322), lower := (rows 97 259 13 138 176 36 80 128 256), losses := [] }

theorem u10711 : Upper (D 7) (R 7) [96,257,9,130,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10711 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10712 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 140 176 34 66 208 336), lower := (rows 97 259 13 140 176 34 66 128 256), losses := [] }

theorem u10712 : Upper (D 7) (R 7) [96,257,9,132,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10713 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 259 13 140 176 34 80 194 322), lower := (rows 97 259 13 140 176 34 80 128 256), losses := [] }

theorem u10713 : Upper (D 7) (R 7) [96,257,9,132,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10713 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10714 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 13 152 22 34 96 192 448), lower := (rows 97 259 13 152 22 34 96 128 256), losses := [] }

theorem u10714 : Upper (D 7) (R 7) [96,257,9,144,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10715 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 291, targets := 128 },{ cop := 4, region := 232, targets := 1 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,0)], upper := (rows 97 259 13 152 22 34 192 224 352), lower := (rows 97 259 13 152 22 34 192 128 256), losses := [] }

theorem u10715 : Upper (D 7) (R 7) [96,257,9,144,6,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10716 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 322, targets := 32 },{ cop := 2, region := 322, targets := 128 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 97 259 13 152 50 160 66 196 324), lower := (rows 97 259 13 152 50 160 66 128 256), losses := [{ target := 7, region := (rows 17 14 12 8 16 32 94 0 268), good := (rows 97 323 335 351 115 32 66 0 256) }] }

theorem u10716 : Upper (D 7) (R 7) [96,257,9,144,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10717 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 97 259 13 152 50 160 68 194 322), lower := (rows 97 259 13 152 50 160 68 128 256), losses := [] }

theorem u10717 : Upper (D 7) (R 7) [96,257,9,144,34,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10717 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10718 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 152 52 34 66 192 448), lower := (rows 97 259 13 152 52 34 66 128 256), losses := [] }

theorem u10718 : Upper (D 7) (R 7) [96,257,9,144,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10719 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 291, targets := 128 },{ cop := 0, region := 258, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,0)], upper := (rows 97 259 13 152 52 34 192 194 322), lower := (rows 97 259 13 152 52 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 34 251 162 290), good := (rows 480 482 76 216 508 482 192 192 256) }] }

theorem u10719 : Upper (D 7) (R 7) [96,257,9,144,36,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10720 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 97 259 13 168 22 34 80 192 448), lower := (rows 97 259 13 168 22 34 80 128 256), losses := [] }

theorem u10720 : Upper (D 7) (R 7) [96,257,9,160,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10720 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10721 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,5)], upper := (rows 97 259 13 168 22 34 192 208 336), lower := (rows 97 259 13 168 22 34 192 128 256), losses := [] }

theorem u10721 : Upper (D 7) (R 7) [96,257,9,160,6,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10722 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 168 82 34 68 144 400), lower := (rows 97 259 13 168 82 34 68 128 256), losses := [] }

theorem u10722 : Upper (D 7) (R 7) [96,257,9,160,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10722 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10723 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 168 82 34 80 132 388), lower := (rows 97 259 13 168 82 34 80 128 256), losses := [] }

theorem u10723 : Upper (D 7) (R 7) [96,257,9,160,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10723 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10724 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(4,5)], upper := (rows 97 259 13 168 82 34 192 148 276), lower := (rows 97 259 13 168 82 34 192 128 256), losses := [] }

theorem u10724 : Upper (D 7) (R 7) [96,257,9,160,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10725 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 168 84 34 66 144 400), lower := (rows 97 259 13 168 84 34 66 128 256), losses := [] }

theorem u10725 : Upper (D 7) (R 7) [96,257,9,160,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10726 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 85, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 13 168 84 34 80 130 386), lower := (rows 97 259 13 168 84 34 80 128 256), losses := [] }

theorem u10726 : Upper (D 7) (R 7) [96,257,9,160,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10726 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10727 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 97 259 13 168 84 34 192 146 274), lower := (rows 97 259 13 168 84 34 192 128 256), losses := [] }

theorem u10727 : Upper (D 7) (R 7) [96,257,9,160,68,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10728 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 259 13 168 208 34 66 148 276), lower := (rows 97 259 13 168 208 34 66 128 256), losses := [] }

theorem u10728 : Upper (D 7) (R 7) [96,257,9,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10729 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 259 13 168 208 34 68 146 274), lower := (rows 97 259 13 168 208 34 68 128 256), losses := [] }

theorem u10729 : Upper (D 7) (R 7) [96,257,9,160,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10729 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10730 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 13 168 208 34 80 134 262), lower := (rows 97 259 13 168 208 34 80 128 256), losses := [] }

theorem u10730 : Upper (D 7) (R 7) [96,257,9,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10730 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10731 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 259 14 28 145 34 96 192 448), lower := (rows 97 259 14 28 145 34 96 128 256), losses := [] }

theorem u10731 : Upper (D 7) (R 7) [96,257,10,20,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10732 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 28 145 34 192 224 352), lower := (rows 97 259 14 28 145 34 192 128 256), losses := [] }

theorem u10732 : Upper (D 7) (R 7) [96,257,10,20,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10733 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 28 176 34 65 192 448), lower := (rows 97 259 14 28 176 34 65 128 256), losses := [] }

theorem u10733 : Upper (D 7) (R 7) [96,257,10,20,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10734 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 259 14 28 176 34 192 193 321), lower := (rows 97 259 14 28 176 34 192 128 256), losses := [] }

theorem u10734 : Upper (D 7) (R 7) [96,257,10,20,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10735 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 172, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 259 14 44 82 160 65 144 400), lower := (rows 97 259 14 44 82 160 65 128 256), losses := [] }

theorem u10735 : Upper (D 7) (R 7) [96,257,10,36,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10736 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 14 44 82 160 80 129 385), lower := (rows 97 259 14 44 82 160 80 128 256), losses := [] }

theorem u10736 : Upper (D 7) (R 7) [96,257,10,36,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10736 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10737 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 259 14 44 82 160 192 145 273), lower := (rows 97 259 14 44 82 160 192 128 256), losses := [] }

theorem u10737 : Upper (D 7) (R 7) [96,257,10,36,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10738 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(1,5),(4,5)], upper := (rows 97 259 14 44 145 48 66 192 448), lower := (rows 97 259 14 44 145 48 66 128 256), losses := [] }

theorem u10738 : Upper (D 7) (R 7) [96,257,10,36,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10738 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10739 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 259 14 44 145 48 192 194 322), lower := (rows 97 259 14 44 145 48 192 128 256), losses := [] }

theorem u10739 : Upper (D 7) (R 7) [96,257,10,36,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10739 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10739
end Delivery.IrregularNine14.P07
