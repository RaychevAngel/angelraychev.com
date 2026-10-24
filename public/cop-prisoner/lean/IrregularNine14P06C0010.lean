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

def b600 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 100 26 273 36 65 136 260), lower := (rows 35 194 100 26 273 36 65 136 256), losses := [] }

theorem u600 : Upper (D 6) (R 6) [34,192,96,18,257,4,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b600 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 100 26 280 36 65 129 260), lower := (rows 35 194 100 26 280 36 65 129 256), losses := [] }

theorem u601 : Upper (D 6) (R 6) [34,192,96,18,264,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 194 100 26 280 36 65 132 257), lower := (rows 35 194 100 26 280 36 65 132 256), losses := [] }

theorem u602 : Upper (D 6) (R 6) [34,192,96,18,264,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 194 100 28 274 40 65 129 260), lower := (rows 35 194 100 28 274 40 65 129 256), losses := [] }

theorem u603 : Upper (D 6) (R 6) [34,192,96,20,258,8,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b603 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 194 100 28 274 40 65 132 257), lower := (rows 35 194 100 28 274 40 65 132 256), losses := [] }

theorem u604 : Upper (D 6) (R 6) [34,192,96,20,258,8,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b604 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 308, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 194 262 25 84 36 65 136 288), lower := (rows 35 194 262 25 84 36 65 136 256), losses := [] }

theorem u605 : Upper (D 6) (R 6) [34,192,258,17,68,4,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b605 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 194 262 25 84 36 65 160 264), lower := (rows 35 194 262 25 84 36 65 160 256), losses := [] }

theorem u606 : Upper (D 6) (R 6) [34,192,258,17,68,4,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 194 324 13 26 36 65 144 288), lower := (rows 35 194 324 13 26 36 65 144 256), losses := [] }

theorem u607 : Upper (D 6) (R 6) [34,192,320,5,10,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b607 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 194 324 13 26 36 65 160 272), lower := (rows 35 194 324 13 26 36 65 160 256), losses := [] }

theorem u608 : Upper (D 6) (R 6) [34,192,320,5,10,4,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 265, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 50 133 265 22 96 68 130 320), lower := (rows 41 50 133 265 22 96 68 130 256), losses := [] }

theorem u609 : Upper (D 6) (R 6) [40,48,129,257,6,64,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 133 265 22 96 68 192 258), lower := (rows 41 50 133 265 22 96 68 192 256), losses := [] }

theorem u610 : Upper (D 6) (R 6) [40,48,129,257,6,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 4, camps := [{ cop := 7, region := 365, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 328 82 36 65 130 260), lower := (rows 41 50 133 328 82 36 65 130 256), losses := [] }

theorem u611 : Upper (D 6) (R 6) [40,48,129,320,66,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 347, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 50 133 328 82 36 65 132 258), lower := (rows 41 50 133 328 82 36 65 132 256), losses := [] }

theorem u612 : Upper (D 6) (R 6) [40,48,129,320,66,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 100 140 276 34 65 129 258), lower := (rows 41 82 100 140 276 34 65 129 256), losses := [] }

theorem u613 : Upper (D 6) (R 6) [40,80,96,132,260,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 41 82 100 140 276 34 65 130 257), lower := (rows 41 82 100 140 276 34 65 130 256), losses := [] }

theorem u614 : Upper (D 6) (R 6) [40,80,96,132,260,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 329, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 82 133 265 22 36 96 130 320), lower := (rows 41 82 133 265 22 36 96 130 256), losses := [] }

theorem u615 : Upper (D 6) (R 6) [40,80,129,257,6,4,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 2, camps := [{ cop := 8, region := 237, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 265 22 36 96 192 258), lower := (rows 41 82 133 265 22 36 96 192 256), losses := [] }

theorem u616 : Upper (D 6) (R 6) [40,80,129,257,6,4,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 82 133 328 22 36 96 129 258), lower := (rows 41 82 133 328 22 36 96 129 256), losses := [] }

theorem u617 : Upper (D 6) (R 6) [40,80,129,320,6,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 329, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 82 133 328 22 36 96 130 257), lower := (rows 41 82 133 328 22 36 96 130 256), losses := [] }

theorem u618 : Upper (D 6) (R 6) [40,80,129,320,6,4,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 4, camps := [{ cop := 7, region := 365, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 133 328 50 36 65 130 260), lower := (rows 41 82 133 328 50 36 65 130 256), losses := [] }

theorem u619 : Upper (D 6) (R 6) [40,80,129,320,34,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 347, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 82 133 328 50 36 65 132 258), lower := (rows 41 82 133 328 50 36 65 132 256), losses := [] }

theorem u620 : Upper (D 6) (R 6) [40,80,129,320,34,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 272, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 82 164 14 276 96 65 129 258), lower := (rows 41 82 164 14 276 96 65 129 256), losses := [] }

theorem u621 : Upper (D 6) (R 6) [40,80,160,6,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 172, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(3,0)], upper := (rows 41 82 164 14 276 96 65 130 257), lower := (rows 41 82 164 14 276 96 65 130 256), losses := [] }

theorem u622 : Upper (D 6) (R 6) [40,80,160,6,260,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 264, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 41 82 164 268 22 96 65 129 258), lower := (rows 41 82 164 268 22 96 65 129 256), losses := [] }

theorem u623 : Upper (D 6) (R 6) [40,80,160,260,6,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 82 164 268 22 96 65 130 257), lower := (rows 41 82 164 268 22 96 65 130 256), losses := [] }

theorem u624 : Upper (D 6) (R 6) [40,80,160,260,6,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 41 98 133 28 273 34 68 130 320), lower := (rows 41 98 133 28 273 34 68 130 256), losses := [] }

theorem u625 : Upper (D 6) (R 6) [40,96,129,20,257,2,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 133 28 273 34 68 192 258), lower := (rows 41 98 133 28 273 34 68 192 256), losses := [] }

theorem u626 : Upper (D 6) (R 6) [40,96,129,20,257,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 41 98 133 88 274 36 65 130 260), lower := (rows 41 98 133 88 274 36 65 130 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 64 146 292), good := (rows 296 506 420 216 410 292 64 154 256) }] }

theorem u627 : Upper (D 6) (R 6) [40,96,129,80,258,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 41 98 133 88 274 36 65 132 258), lower := (rows 41 98 133 88 274 36 65 132 256), losses := [] }

theorem u628 : Upper (D 6) (R 6) [40,96,129,80,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 306, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 134 13 274 48 68 129 320), lower := (rows 41 98 134 13 274 48 68 129 256), losses := [] }

theorem u629 : Upper (D 6) (R 6) [40,96,130,5,258,16,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b629 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 98 134 13 274 48 68 192 257), lower := (rows 41 98 134 13 274 48 68 192 256), losses := [] }

theorem u630 : Upper (D 6) (R 6) [40,96,130,5,258,16,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b630 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 65 }], pairs := [(4,0),(4,6)], upper := (rows 41 98 134 76 274 48 65 129 260), lower := (rows 41 98 134 76 274 48 65 129 256), losses := [] }

theorem u631 : Upper (D 6) (R 6) [40,96,130,68,258,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b631 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 98 134 76 274 48 65 132 257), lower := (rows 41 98 134 76 274 48 65 132 256), losses := [] }

theorem u632 : Upper (D 6) (R 6) [40,96,130,68,258,16,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b632 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 65 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,2),(4,0),(4,6)], upper := (rows 41 98 134 88 274 36 65 129 260), lower := (rows 41 98 134 88 274 36 65 129 256), losses := [] }

theorem u633 : Upper (D 6) (R 6) [40,96,130,80,258,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 347, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 134 88 274 36 65 132 257), lower := (rows 41 98 134 88 274 36 65 132 256), losses := [] }

theorem u634 : Upper (D 6) (R 6) [40,96,130,80,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 134 266 21 36 65 144 320), lower := (rows 41 98 134 266 21 36 65 144 256), losses := [] }

theorem u635 : Upper (D 6) (R 6) [40,96,130,258,5,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b635 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 98 134 266 21 36 65 192 272), lower := (rows 41 98 134 266 21 36 65 192 256), losses := [] }

theorem u636 : Upper (D 6) (R 6) [40,96,130,258,5,4,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 41 98 134 266 84 36 65 129 272), lower := (rows 41 98 134 266 84 36 65 129 256), losses := [] }

theorem u637 : Upper (D 6) (R 6) [40,96,130,258,68,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 134 266 84 36 65 144 257), lower := (rows 41 98 134 266 84 36 65 144 256), losses := [] }

theorem u638 : Upper (D 6) (R 6) [40,96,130,258,68,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b638 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 377, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 98 134 328 21 36 65 130 272), lower := (rows 41 98 134 328 21 36 65 130 256), losses := [] }

theorem u639 : Upper (D 6) (R 6) [40,96,130,320,5,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 41 98 134 328 21 36 65 144 258), lower := (rows 41 98 134 328 21 36 65 144 256), losses := [] }

theorem u640 : Upper (D 6) (R 6) [40,96,130,320,5,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b640 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 146, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 41 131 261 14 50 96 68 144 320), lower := (rows 41 131 261 14 50 96 68 144 256), losses := [] }

theorem u641 : Upper (D 6) (R 6) [40,129,257,6,34,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b641 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 131 261 14 50 96 68 192 272), lower := (rows 41 131 261 14 50 96 68 192 256), losses := [] }

theorem u642 : Upper (D 6) (R 6) [40,129,257,6,34,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 348, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 41 131 262 74 21 36 80 160 320), lower := (rows 41 131 262 74 21 36 80 160 256), losses := [] }

theorem u643 : Upper (D 6) (R 6) [40,129,258,66,5,4,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b643 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 131 262 74 21 36 80 192 288), lower := (rows 41 131 262 74 21 36 80 192 256), losses := [] }

theorem u644 : Upper (D 6) (R 6) [40,129,258,66,5,4,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b644 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 41 134 262 26 21 96 96 129 320), lower := (rows 41 134 262 26 21 96 96 129 256), losses := [] }

theorem u645 : Upper (D 6) (R 6) [40,132,258,18,5,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 134 262 26 21 96 96 192 257), lower := (rows 41 134 262 26 21 96 96 192 256), losses := [] }

theorem u646 : Upper (D 6) (R 6) [40,132,258,18,5,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 260, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 134 262 74 21 48 65 160 320), lower := (rows 41 134 262 74 21 48 65 160 256), losses := [] }

theorem u647 : Upper (D 6) (R 6) [40,132,258,66,5,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b647 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 309, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 134 262 74 21 48 65 192 288), lower := (rows 41 134 262 74 21 48 65 192 256), losses := [] }

theorem u648 : Upper (D 6) (R 6) [40,132,258,66,5,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b648 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 260, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 134 262 74 21 48 96 129 320), lower := (rows 41 134 262 74 21 48 96 129 256), losses := [] }

theorem u649 : Upper (D 6) (R 6) [40,132,258,66,5,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b649 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 134 262 74 21 48 96 192 257), lower := (rows 41 134 262 74 21 48 96 192 256), losses := [] }

theorem u650 : Upper (D 6) (R 6) [40,132,258,66,5,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b650 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 292 76 19 34 80 129 320), lower := (rows 41 134 292 76 19 34 80 129 256), losses := [] }

theorem u651 : Upper (D 6) (R 6) [40,132,288,68,3,2,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b651 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 260, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 41 134 292 76 19 34 80 192 257), lower := (rows 41 134 292 76 19 34 80 192 256), losses := [] }

theorem u652 : Upper (D 6) (R 6) [40,132,288,68,3,2,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b652 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 260, targets := 2 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 41 134 324 28 19 96 66 129 288), lower := (rows 41 134 324 28 19 96 66 129 256), losses := [] }

theorem u653 : Upper (D 6) (R 6) [40,132,320,20,3,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 332, targets := 32 },{ cop := 8, region := 230, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 41 134 324 28 19 96 66 160 257), lower := (rows 41 134 324 28 19 96 66 160 256), losses := [] }

theorem u654 : Upper (D 6) (R 6) [40,132,320,20,3,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 308, targets := 1 },{ cop := 3, region := 293, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 146 324 74 22 36 65 129 288), lower := (rows 41 146 324 74 22 36 65 129 256), losses := [] }

theorem u655 : Upper (D 6) (R 6) [40,144,320,66,6,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 146, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 146 324 74 22 36 65 160 257), lower := (rows 41 146 324 74 22 36 65 160 256), losses := [] }

theorem u656 : Upper (D 6) (R 6) [40,144,320,66,6,4,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 131 261 26 52 34 68 136 320), lower := (rows 97 131 261 26 52 34 68 136 256), losses := [] }

theorem u657 : Upper (D 6) (R 6) [96,129,257,18,36,2,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b657 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 316, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 97 131 261 26 52 34 68 192 264), lower := (rows 97 131 261 26 52 34 68 192 256), losses := [] }

theorem u658 : Upper (D 6) (R 6) [96,129,257,18,36,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 131 261 42 84 36 66 136 272), lower := (rows 97 131 261 42 84 36 66 136 256), losses := [] }

theorem u659 : Upper (D 6) (R 6) [96,129,257,34,68,4,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b659 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P06
