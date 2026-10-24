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

def b8580 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 131 268 13 22 34 80 224 352), lower := (rows 97 131 268 13 22 34 80 128 256), losses := [] }

theorem u8580 : Upper (D 6) (R 6) [96,129,264,5,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8580 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8581 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 268 13 22 34 96 208 336), lower := (rows 97 131 268 13 22 34 96 128 256), losses := [] }

theorem u8581 : Upper (D 6) (R 6) [96,129,264,5,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8582 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 268 13 52 34 66 208 336), lower := (rows 97 131 268 13 52 34 66 128 256), losses := [] }

theorem u8582 : Upper (D 6) (R 6) [96,129,264,5,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8583 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 268 13 52 34 80 194 322), lower := (rows 97 131 268 13 52 34 80 128 256), losses := [] }

theorem u8583 : Upper (D 6) (R 6) [96,129,264,5,36,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8583 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8584 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 131 268 14 21 34 80 224 352), lower := (rows 97 131 268 14 21 34 80 128 256), losses := [] }

theorem u8584 : Upper (D 6) (R 6) [96,129,264,6,5,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8584 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8585 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 268 14 21 34 96 208 336), lower := (rows 97 131 268 14 21 34 96 128 256), losses := [] }

theorem u8585 : Upper (D 6) (R 6) [96,129,264,6,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8586 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 268 25 22 34 68 224 352), lower := (rows 97 131 268 25 22 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 92 153 281), good := (rows 480 418 460 508 502 34 68 128 256) }] }

theorem u8586 : Upper (D 6) (R 6) [96,129,264,17,6,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8587 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 268 25 22 34 96 196 324), lower := (rows 97 131 268 25 22 34 96 128 256), losses := [] }

theorem u8587 : Upper (D 6) (R 6) [96,129,264,17,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8588 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 65, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 97 131 268 25 50 36 66 196 324), lower := (rows 97 131 268 25 50 36 66 128 256), losses := [] }

theorem u8588 : Upper (D 6) (R 6) [96,129,264,17,34,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8589 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 268 25 50 36 68 194 322), lower := (rows 97 131 268 25 50 36 68 128 256), losses := [] }

theorem u8589 : Upper (D 6) (R 6) [96,129,264,17,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 268 25 52 34 66 196 324), lower := (rows 97 131 268 25 52 34 66 128 256), losses := [] }

theorem u8590 : Upper (D 6) (R 6) [96,129,264,17,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 131 268 25 52 34 68 194 322), lower := (rows 97 131 268 25 52 34 68 128 256), losses := [] }

theorem u8591 : Upper (D 6) (R 6) [96,129,264,17,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8592 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 163, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 268 26 21 34 68 224 352), lower := (rows 97 131 268 26 21 34 68 128 256), losses := [] }

theorem u8592 : Upper (D 6) (R 6) [96,129,264,18,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8593 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 131 268 26 21 34 96 196 324), lower := (rows 97 131 268 26 21 34 96 128 256), losses := [] }

theorem u8593 : Upper (D 6) (R 6) [96,129,264,18,5,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 194, targets := 36 },{ cop := 3, region := 65, targets := 4 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 97 131 268 42 21 36 66 208 336), lower := (rows 97 131 268 42 21 36 66 128 256), losses := [] }

theorem u8594 : Upper (D 6) (R 6) [96,129,264,34,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 138, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 97 131 268 42 21 36 80 194 322), lower := (rows 97 131 268 42 21 36 80 128 256), losses := [] }

theorem u8595 : Upper (D 6) (R 6) [96,129,264,34,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8595 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 131 268 42 82 36 65 148 276), lower := (rows 97 131 268 42 82 36 65 128 256), losses := [] }

theorem u8596 : Upper (D 6) (R 6) [96,129,264,34,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8597 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 268 42 82 36 68 145 273), lower := (rows 97 131 268 42 82 36 68 128 256), losses := [] }

theorem u8597 : Upper (D 6) (R 6) [96,129,264,34,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8598 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 42 82 36 80 133 261), lower := (rows 97 131 268 42 82 36 80 128 256), losses := [] }

theorem u8598 : Upper (D 6) (R 6) [96,129,264,34,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8598 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 3, region := 65, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 131 268 42 84 36 65 146 274), lower := (rows 97 131 268 42 84 36 65 128 256), losses := [] }

theorem u8599 : Upper (D 6) (R 6) [96,129,264,34,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 4 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 97 131 268 42 84 36 66 145 273), lower := (rows 97 131 268 42 84 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 52 74 128 256), good := (rows 96 194 380 106 116 52 66 128 256) }] }

theorem u8600 : Upper (D 6) (R 6) [96,129,264,34,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 42 84 36 80 131 259), lower := (rows 97 131 268 42 84 36 80 128 256), losses := [] }

theorem u8601 : Upper (D 6) (R 6) [96,129,264,34,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8601 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 131 268 44 82 34 65 148 276), lower := (rows 97 131 268 44 82 34 65 128 256), losses := [] }

theorem u8602 : Upper (D 6) (R 6) [96,129,264,36,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8603 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 179, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 97 131 268 44 82 34 68 145 273), lower := (rows 97 131 268 44 82 34 68 128 256), losses := [] }

theorem u8603 : Upper (D 6) (R 6) [96,129,264,36,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8604 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 44 82 34 80 133 261), lower := (rows 97 131 268 44 82 34 80 128 256), losses := [] }

theorem u8604 : Upper (D 6) (R 6) [96,129,264,36,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8604 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8605 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 81, targets := 2 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 131 268 44 84 34 65 146 274), lower := (rows 97 131 268 44 84 34 65 128 256), losses := [] }

theorem u8605 : Upper (D 6) (R 6) [96,129,264,36,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8606 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 268 44 84 34 66 145 273), lower := (rows 97 131 268 44 84 34 66 128 256), losses := [] }

theorem u8606 : Upper (D 6) (R 6) [96,129,264,36,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8607 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 44 84 34 80 131 259), lower := (rows 97 131 268 44 84 34 80 128 256), losses := [] }

theorem u8607 : Upper (D 6) (R 6) [96,129,264,36,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8607 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 268 56 21 34 66 196 324), lower := (rows 97 131 268 56 21 34 66 128 256), losses := [] }

theorem u8608 : Upper (D 6) (R 6) [96,129,264,48,5,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 163, targets := 4 },{ cop := 0, region := 130, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 97 131 268 56 21 34 68 194 322), lower := (rows 97 131 268 56 21 34 68 128 256), losses := [] }

theorem u8609 : Upper (D 6) (R 6) [96,129,264,48,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 131 268 56 82 36 65 134 262), lower := (rows 97 131 268 56 82 36 65 128 256), losses := [] }

theorem u8610 : Upper (D 6) (R 6) [96,129,264,48,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8611 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 97 131 268 56 82 36 66 133 261), lower := (rows 97 131 268 56 82 36 66 128 256), losses := [] }

theorem u8611 : Upper (D 6) (R 6) [96,129,264,48,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8612 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 154, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 97 131 268 56 82 36 68 131 259), lower := (rows 97 131 268 56 82 36 68 128 256), losses := [] }

theorem u8612 : Upper (D 6) (R 6) [96,129,264,48,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8613 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 65, targets := 6 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 131 268 56 84 34 65 134 262), lower := (rows 97 131 268 56 84 34 65 128 256), losses := [] }

theorem u8613 : Upper (D 6) (R 6) [96,129,264,48,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8614 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 268 56 84 34 66 133 261), lower := (rows 97 131 268 56 84 34 66 128 256), losses := [] }

theorem u8614 : Upper (D 6) (R 6) [96,129,264,48,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8615 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 131 268 56 84 34 68 131 259), lower := (rows 97 131 268 56 84 34 68 128 256), losses := [] }

theorem u8615 : Upper (D 6) (R 6) [96,129,264,48,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8616 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 131 292 13 22 34 72 208 336), lower := (rows 97 131 292 13 22 34 72 128 256), losses := [] }

theorem u8616 : Upper (D 6) (R 6) [96,129,288,5,6,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8616 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8617 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 97 131 292 13 22 34 80 200 328), lower := (rows 97 131 292 13 22 34 80 128 256), losses := [] }

theorem u8617 : Upper (D 6) (R 6) [96,129,288,5,6,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8617 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8618 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 292 13 84 34 66 152 280), lower := (rows 97 131 292 13 84 34 66 128 256), losses := [] }

theorem u8618 : Upper (D 6) (R 6) [96,129,288,5,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8619 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 73, targets := 2 }], pairs := [(0,1),(3,1)], upper := (rows 97 131 292 13 84 34 72 146 274), lower := (rows 97 131 292 13 84 34 72 128 256), losses := [] }

theorem u8619 : Upper (D 6) (R 6) [96,129,288,5,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8619 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8620 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 13 84 34 80 138 266), lower := (rows 97 131 292 13 84 34 80 128 256), losses := [] }

theorem u8620 : Upper (D 6) (R 6) [96,129,288,5,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8620 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8621 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 292 13 88 34 66 148 276), lower := (rows 97 131 292 13 88 34 66 128 256), losses := [] }

theorem u8621 : Upper (D 6) (R 6) [96,129,288,5,72,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8622 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 131 292 13 88 34 68 146 274), lower := (rows 97 131 292 13 88 34 68 128 256), losses := [] }

theorem u8622 : Upper (D 6) (R 6) [96,129,288,5,72,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8623 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 13 88 34 80 134 262), lower := (rows 97 131 292 13 88 34 80 128 256), losses := [] }

theorem u8623 : Upper (D 6) (R 6) [96,129,288,5,72,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8623 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8624 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(2,0),(4,1)], upper := (rows 97 131 292 14 25 34 68 208 336), lower := (rows 97 131 292 14 25 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 42 92 144 272), good := (rows 96 162 356 110 508 34 68 128 256) },{ target := 1, region := (rows 5 0 4 8 24 32 76 152 280), good := (rows 97 129 357 477 473 32 69 128 256) }] }

theorem u8624 : Upper (D 6) (R 6) [96,129,288,6,9,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8625 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 97 131 292 14 25 34 80 196 324), lower := (rows 97 131 292 14 25 34 80 128 256), losses := [] }

theorem u8625 : Upper (D 6) (R 6) [96,129,288,6,9,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8625 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8626 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 97 131 292 14 82 40 65 148 276), lower := (rows 97 131 292 14 82 40 65 128 256), losses := [] }

theorem u8626 : Upper (D 6) (R 6) [96,129,288,6,66,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8626 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8627 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 146, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 97 131 292 14 82 40 68 145 273), lower := (rows 97 131 292 14 82 40 68 128 256), losses := [] }

theorem u8627 : Upper (D 6) (R 6) [96,129,288,6,66,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8627 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8628 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 131 292 14 82 40 80 133 261), lower := (rows 97 131 292 14 82 40 80 128 256), losses := [] }

theorem u8628 : Upper (D 6) (R 6) [96,129,288,6,66,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8628 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8629 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 131 292 14 84 34 65 152 280), lower := (rows 97 131 292 14 84 34 65 128 256), losses := [] }

theorem u8629 : Upper (D 6) (R 6) [96,129,288,6,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8630 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 131 292 14 84 34 72 145 273), lower := (rows 97 131 292 14 84 34 72 128 256), losses := [] }

theorem u8630 : Upper (D 6) (R 6) [96,129,288,6,68,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8630 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8631 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 14 84 34 80 137 265), lower := (rows 97 131 292 14 84 34 80 128 256), losses := [] }

theorem u8631 : Upper (D 6) (R 6) [96,129,288,6,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8631 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8632 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 81, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 97 131 292 14 84 40 65 146 274), lower := (rows 97 131 292 14 84 40 65 128 256), losses := [] }

theorem u8632 : Upper (D 6) (R 6) [96,129,288,6,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8632 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8633 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 97 131 292 14 84 40 66 145 273), lower := (rows 97 131 292 14 84 40 66 128 256), losses := [] }

theorem u8633 : Upper (D 6) (R 6) [96,129,288,6,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8633 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 }], pairs := [(1,6)], upper := (rows 97 131 292 14 84 40 80 131 259), lower := (rows 97 131 292 14 84 40 80 128 256), losses := [] }

theorem u8634 : Upper (D 6) (R 6) [96,129,288,6,68,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8634 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8635 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 113, targets := 4 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 97 131 292 14 88 34 65 148 276), lower := (rows 97 131 292 14 88 34 65 128 256), losses := [] }

theorem u8635 : Upper (D 6) (R 6) [96,129,288,6,72,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8636 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,1),(4,5)], upper := (rows 97 131 292 14 88 34 68 145 273), lower := (rows 97 131 292 14 88 34 68 128 256), losses := [] }

theorem u8636 : Upper (D 6) (R 6) [96,129,288,6,72,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8637 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 292 14 88 34 80 133 261), lower := (rows 97 131 292 14 88 34 80 128 256), losses := [] }

theorem u8637 : Upper (D 6) (R 6) [96,129,288,6,72,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8637 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8638 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 284, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 97 131 292 25 84 34 66 140 268), lower := (rows 97 131 292 25 84 34 66 128 256), losses := [] }

theorem u8638 : Upper (D 6) (R 6) [96,129,288,17,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8639 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 131 292 25 84 34 68 138 266), lower := (rows 97 131 292 25 84 34 68 128 256), losses := [] }

theorem u8639 : Upper (D 6) (R 6) [96,129,288,17,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8639
end Delivery.IrregularNine14.P06
