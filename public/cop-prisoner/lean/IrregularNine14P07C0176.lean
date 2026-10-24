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

def b10560 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 392 82 33 80 134 262), lower := (rows 97 162 13 392 82 33 80 128 256), losses := [] }

theorem u10560 : Upper (D 7) (R 7) [96,160,9,384,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10560 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10561 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 81, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 162 13 392 82 34 65 148 276), lower := (rows 97 162 13 392 82 34 65 128 256), losses := [] }

theorem u10561 : Upper (D 7) (R 7) [96,160,9,384,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10562 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6)], upper := (rows 97 162 13 392 82 34 68 145 273), lower := (rows 97 162 13 392 82 34 68 128 256), losses := [] }

theorem u10562 : Upper (D 7) (R 7) [96,160,9,384,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10562 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10563 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 162 13 392 82 34 80 133 261), lower := (rows 97 162 13 392 82 34 80 128 256), losses := [] }

theorem u10563 : Upper (D 7) (R 7) [96,160,9,384,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10563 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10564 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 392 82 36 65 146 274), lower := (rows 97 162 13 392 82 36 65 128 256), losses := [] }

theorem u10564 : Upper (D 7) (R 7) [96,160,9,384,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10564 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10565 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 392 82 36 66 145 273), lower := (rows 97 162 13 392 82 36 66 128 256), losses := [] }

theorem u10565 : Upper (D 7) (R 7) [96,160,9,384,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10565 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10566 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 13 392 82 36 80 131 259), lower := (rows 97 162 13 392 82 36 80 128 256), losses := [] }

theorem u10566 : Upper (D 7) (R 7) [96,160,9,384,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10566 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10567 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 162 13 392 84 34 65 146 274), lower := (rows 97 162 13 392 84 34 65 128 256), losses := [] }

theorem u10567 : Upper (D 7) (R 7) [96,160,9,384,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10568 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 392 84 34 66 145 273), lower := (rows 97 162 13 392 84 34 66 128 256), losses := [] }

theorem u10568 : Upper (D 7) (R 7) [96,160,9,384,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10569 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 162 13 392 84 34 80 131 259), lower := (rows 97 162 13 392 84 34 80 128 256), losses := [] }

theorem u10569 : Upper (D 7) (R 7) [96,160,9,384,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10569 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10570 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 437, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 162 28 74 145 33 66 388 260), lower := (rows 97 162 28 74 145 33 66 128 256), losses := [] }

theorem u10570 : Upper (D 7) (R 7) [96,160,24,66,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10571 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 394, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 28 74 145 33 68 386 258), lower := (rows 97 162 28 74 145 33 68 128 256), losses := [] }

theorem u10571 : Upper (D 7) (R 7) [96,160,24,66,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10571 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10572 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 130 },{ cop := 4, region := 34, targets := 64 }], pairs := [(0,1),(0,7),(1,6)], upper := (rows 97 162 28 74 145 33 320 134 262), lower := (rows 97 162 28 74 145 33 320 128 256), losses := [] }

theorem u10572 : Upper (D 7) (R 7) [96,160,24,66,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10572 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10573 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 162 28 74 145 288 65 134 262), lower := (rows 97 162 28 74 145 288 65 128 256), losses := [] }

theorem u10573 : Upper (D 7) (R 7) [96,160,24,66,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10573 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10574 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 162 28 74 145 288 66 133 261), lower := (rows 97 162 28 74 145 288 66 128 256), losses := [] }

theorem u10574 : Upper (D 7) (R 7) [96,160,24,66,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10574 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10575 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 146, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 97 162 28 74 145 288 68 131 259), lower := (rows 97 162 28 74 145 288 68 128 256), losses := [] }

theorem u10575 : Upper (D 7) (R 7) [96,160,24,66,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10575 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10576 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 437, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 162 28 74 273 33 66 132 388), lower := (rows 97 162 28 74 273 33 66 128 256), losses := [] }

theorem u10576 : Upper (D 7) (R 7) [96,160,24,66,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10577 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 138, targets := 1 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 28 74 273 33 68 130 386), lower := (rows 97 162 28 74 273 33 68 128 256), losses := [] }

theorem u10577 : Upper (D 7) (R 7) [96,160,24,66,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10577 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10578 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 309, targets := 128 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 162 28 74 273 33 192 134 262), lower := (rows 97 162 28 74 273 33 192 128 256), losses := [] }

theorem u10578 : Upper (D 7) (R 7) [96,160,24,66,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10579 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 73, targets := 128 },{ cop := 2, region := 162, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7)], upper := (rows 97 162 28 74 273 34 65 132 388), lower := (rows 97 162 28 74 273 34 65 128 256), losses := [] }

theorem u10579 : Upper (D 7) (R 7) [96,160,24,66,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10580 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 97 162 28 74 273 34 68 129 385), lower := (rows 97 162 28 74 273 34 68 128 256), losses := [] }

theorem u10580 : Upper (D 7) (R 7) [96,160,24,66,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10580 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10581 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 309, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 97 162 28 74 273 34 192 133 261), lower := (rows 97 162 28 74 273 34 192 128 256), losses := [] }

theorem u10581 : Upper (D 7) (R 7) [96,160,24,66,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10582 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 138, targets := 1 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 28 74 273 36 65 130 386), lower := (rows 97 162 28 74 273 36 65 128 256), losses := [] }

theorem u10582 : Upper (D 7) (R 7) [96,160,24,66,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10582 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10583 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 162 28 74 273 36 66 129 385), lower := (rows 97 162 28 74 273 36 66 128 256), losses := [] }

theorem u10583 : Upper (D 7) (R 7) [96,160,24,66,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10583 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10584 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 28 74 273 36 192 131 259), lower := (rows 97 162 28 74 273 36 192 128 256), losses := [] }

theorem u10584 : Upper (D 7) (R 7) [96,160,24,66,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10584 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10585 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 404, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 162 28 74 274 33 65 132 388), lower := (rows 97 162 28 74 274 33 65 128 256), losses := [] }

theorem u10585 : Upper (D 7) (R 7) [96,160,24,66,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10586 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 162 28 74 274 33 68 129 385), lower := (rows 97 162 28 74 274 33 68 128 256), losses := [] }

theorem u10586 : Upper (D 7) (R 7) [96,160,24,66,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10586 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10587 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 309, targets := 128 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 162 28 74 274 33 192 133 261), lower := (rows 97 162 28 74 274 33 192 128 256), losses := [] }

theorem u10587 : Upper (D 7) (R 7) [96,160,24,66,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10588 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 404, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 162 28 74 276 33 65 130 386), lower := (rows 97 162 28 74 276 33 65 128 256), losses := [] }

theorem u10588 : Upper (D 7) (R 7) [96,160,24,66,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10589 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 437, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 162 28 74 276 33 66 129 385), lower := (rows 97 162 28 74 276 33 66 128 256), losses := [] }

theorem u10589 : Upper (D 7) (R 7) [96,160,24,66,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10590 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 309, targets := 128 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 97 162 28 74 276 33 192 131 259), lower := (rows 97 162 28 74 276 33 192 128 256), losses := [] }

theorem u10590 : Upper (D 7) (R 7) [96,160,24,66,260,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10591 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 404, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 162 28 74 400 33 65 134 262), lower := (rows 97 162 28 74 400 33 65 128 256), losses := [] }

theorem u10591 : Upper (D 7) (R 7) [96,160,24,66,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10592 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 162 28 74 400 33 66 133 261), lower := (rows 97 162 28 74 400 33 66 128 256), losses := [] }

theorem u10592 : Upper (D 7) (R 7) [96,160,24,66,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10593 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 162 28 74 400 33 68 131 259), lower := (rows 97 162 28 74 400 33 68 128 256), losses := [] }

theorem u10593 : Upper (D 7) (R 7) [96,160,24,66,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10593 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10594 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 128 },{ cop := 4, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7)], upper := (rows 97 162 28 74 400 34 65 133 261), lower := (rows 97 162 28 74 400 34 65 128 256), losses := [] }

theorem u10594 : Upper (D 7) (R 7) [96,160,24,66,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10595 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 162 28 74 400 34 68 129 257), lower := (rows 97 162 28 74 400 34 68 128 256), losses := [] }

theorem u10595 : Upper (D 7) (R 7) [96,160,24,66,384,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10595 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10596 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 76, targets := 162 }], pairs := [(2,1),(2,5),(2,7),(3,1)], upper := (rows 97 162 28 76 273 34 65 130 386), lower := (rows 97 162 28 76 273 34 65 128 256), losses := [] }

theorem u10596 : Upper (D 7) (R 7) [96,160,24,68,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10597 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 28 76 273 34 66 129 385), lower := (rows 97 162 28 76 273 34 66 128 256), losses := [] }

theorem u10597 : Upper (D 7) (R 7) [96,160,24,68,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10598 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 65, targets := 2 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 97 162 28 76 273 34 192 131 259), lower := (rows 97 162 28 76 273 34 192 128 256), losses := [] }

theorem u10598 : Upper (D 7) (R 7) [96,160,24,68,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10599 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 72, targets := 33 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 162 28 200 273 33 66 134 262), lower := (rows 97 162 28 200 273 33 66 128 256), losses := [] }

theorem u10599 : Upper (D 7) (R 7) [96,160,24,192,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10600 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 138, targets := 1 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 28 200 273 33 68 130 258), lower := (rows 97 162 28 200 273 33 68 128 256), losses := [] }

theorem u10600 : Upper (D 7) (R 7) [96,160,24,192,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10600 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10601 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 2 },{ cop := 2, region := 162, targets := 65 }], pairs := [(0,1),(1,0),(1,6),(3,1)], upper := (rows 97 162 28 200 273 34 65 134 262), lower := (rows 97 162 28 200 273 34 65 128 256), losses := [] }

theorem u10601 : Upper (D 7) (R 7) [96,160,24,192,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10602 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 28 200 273 34 66 133 261), lower := (rows 97 162 28 200 273 34 66 128 256), losses := [] }

theorem u10602 : Upper (D 7) (R 7) [96,160,24,192,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10603 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 28 200 273 34 68 131 259), lower := (rows 97 162 28 200 273 34 68 128 256), losses := [] }

theorem u10603 : Upper (D 7) (R 7) [96,160,24,192,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10603 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10604 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 162 28 200 276 33 65 130 258), lower := (rows 97 162 28 200 276 33 65 128 256), losses := [] }

theorem u10604 : Upper (D 7) (R 7) [96,160,24,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10605 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 72, targets := 33 },{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 162 28 200 276 33 66 131 259), lower := (rows 97 162 28 200 276 33 66 128 256), losses := [] }

theorem u10605 : Upper (D 7) (R 7) [96,160,24,192,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10606 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 70 137 273 34 68 152 280), lower := (rows 97 162 70 137 273 34 68 128 256), losses := [] }

theorem u10606 : Upper (D 7) (R 7) [96,160,66,129,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10606 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10607 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 73, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 162 70 137 273 34 72 148 276), lower := (rows 97 162 70 137 273 34 72 128 256), losses := [] }

theorem u10607 : Upper (D 7) (R 7) [96,160,66,129,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10607 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10608 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,6)], upper := (rows 97 162 70 137 273 34 80 140 268), lower := (rows 97 162 70 137 273 34 80 128 256), losses := [] }

theorem u10608 : Upper (D 7) (R 7) [96,160,66,129,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10608 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10609 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 162 70 137 273 48 66 140 268), lower := (rows 97 162 70 137 273 48 66 128 256), losses := [] }

theorem u10609 : Upper (D 7) (R 7) [96,160,66,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10609 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10610 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 162 70 137 273 48 68 138 266), lower := (rows 97 162 70 137 273 48 68 128 256), losses := [] }

theorem u10610 : Upper (D 7) (R 7) [96,160,66,129,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10610 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10611 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 134, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 97 162 70 137 273 48 72 134 262), lower := (rows 97 162 70 137 273 48 72 128 256), losses := [] }

theorem u10611 : Upper (D 7) (R 7) [96,160,66,129,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10611 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10612 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 441, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 97 162 70 137 276 33 66 152 280), lower := (rows 97 162 70 137 276 33 66 128 256), losses := [] }

theorem u10612 : Upper (D 7) (R 7) [96,160,66,129,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10613 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 162 70 137 276 33 72 146 274), lower := (rows 97 162 70 137 276 33 72 128 256), losses := [] }

theorem u10613 : Upper (D 7) (R 7) [96,160,66,129,260,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10613 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10614 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 138, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 97 162 70 137 276 33 80 138 266), lower := (rows 97 162 70 137 276 33 80 128 256), losses := [] }

theorem u10614 : Upper (D 7) (R 7) [96,160,66,129,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10614 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10615 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 73, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,1)], upper := (rows 97 162 70 137 276 34 65 152 280), lower := (rows 97 162 70 137 276 34 65 128 256), losses := [] }

theorem u10615 : Upper (D 7) (R 7) [96,160,66,129,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10616 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 162 70 137 276 34 72 145 273), lower := (rows 97 162 70 137 276 34 72 128 256), losses := [] }

theorem u10616 : Upper (D 7) (R 7) [96,160,66,129,260,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10616 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10617 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 },{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6),(3,1),(3,5)], upper := (rows 97 162 70 137 276 34 80 137 265), lower := (rows 97 162 70 137 276 34 80 128 256), losses := [] }

theorem u10617 : Upper (D 7) (R 7) [96,160,66,129,260,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10617 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10618 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 138, targets := 64 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 97 162 70 137 276 48 65 138 266), lower := (rows 97 162 70 137 276 48 65 128 256), losses := [] }

theorem u10618 : Upper (D 7) (R 7) [96,160,66,129,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10618 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10619 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 162 70 137 276 48 66 137 265), lower := (rows 97 162 70 137 276 48 66 128 256), losses := [] }

theorem u10619 : Upper (D 7) (R 7) [96,160,66,129,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10619 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10619
end Delivery.IrregularNine14.P07
