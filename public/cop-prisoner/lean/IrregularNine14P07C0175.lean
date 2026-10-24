import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10500 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 200 273 34 68 146 274), lower := (rows 97 162 13 200 273 34 68 128 256), losses := [] }

theorem u10500 : Upper (D 7) (R 7) [96,160,9,192,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10500 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10501 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 200 273 34 80 134 262), lower := (rows 97 162 13 200 273 34 80 128 256), losses := [] }

theorem u10501 : Upper (D 7) (R 7) [96,160,9,192,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10501 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10502 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 72, targets := 33 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(3,0),(3,5)], upper := (rows 97 162 13 200 273 48 66 134 262), lower := (rows 97 162 13 200 273 48 66 128 256), losses := [] }

theorem u10502 : Upper (D 7) (R 7) [96,160,9,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10502 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10503 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 162 13 200 273 48 68 130 258), lower := (rows 97 162 13 200 273 48 68 128 256), losses := [] }

theorem u10503 : Upper (D 7) (R 7) [96,160,9,192,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10503 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10504 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 162 13 200 274 34 65 148 276), lower := (rows 97 162 13 200 274 34 65 128 256), losses := [] }

theorem u10504 : Upper (D 7) (R 7) [96,160,9,192,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10505 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 200 274 34 68 145 273), lower := (rows 97 162 13 200 274 34 68 128 256), losses := [] }

theorem u10505 : Upper (D 7) (R 7) [96,160,9,192,258,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10505 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10506 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 162 13 200 274 34 80 133 261), lower := (rows 97 162 13 200 274 34 80 128 256), losses := [] }

theorem u10506 : Upper (D 7) (R 7) [96,160,9,192,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10506 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10507 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 162 13 200 274 48 65 134 262), lower := (rows 97 162 13 200 274 48 65 128 256), losses := [] }

theorem u10507 : Upper (D 7) (R 7) [96,160,9,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10507 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10508 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 162 13 200 274 48 66 133 261), lower := (rows 97 162 13 200 274 48 66 128 256), losses := [] }

theorem u10508 : Upper (D 7) (R 7) [96,160,9,192,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10508 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10509 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 162 13 200 274 48 68 131 259), lower := (rows 97 162 13 200 274 48 68 128 256), losses := [] }

theorem u10509 : Upper (D 7) (R 7) [96,160,9,192,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10509 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10510 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 162 13 200 276 34 65 146 274), lower := (rows 97 162 13 200 276 34 65 128 256), losses := [] }

theorem u10510 : Upper (D 7) (R 7) [96,160,9,192,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10511 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 200 276 34 66 145 273), lower := (rows 97 162 13 200 276 34 66 128 256), losses := [] }

theorem u10511 : Upper (D 7) (R 7) [96,160,9,192,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10512 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 200 276 34 80 131 259), lower := (rows 97 162 13 200 276 34 80 128 256), losses := [] }

theorem u10512 : Upper (D 7) (R 7) [96,160,9,192,260,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10512 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10513 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 13 266 82 33 68 144 400), lower := (rows 97 162 13 266 82 33 68 128 256), losses := [] }

theorem u10513 : Upper (D 7) (R 7) [96,160,9,258,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10513 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10514 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 266 82 33 80 132 388), lower := (rows 97 162 13 266 82 33 80 128 256), losses := [] }

theorem u10514 : Upper (D 7) (R 7) [96,160,9,258,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10514 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10515 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 301, targets := 128 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 97 162 13 266 82 33 192 148 276), lower := (rows 97 162 13 266 82 33 192 128 256), losses := [] }

theorem u10515 : Upper (D 7) (R 7) [96,160,9,258,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10516 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 13 266 82 36 65 144 400), lower := (rows 97 162 13 266 82 36 65 128 256), losses := [] }

theorem u10516 : Upper (D 7) (R 7) [96,160,9,258,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10516 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10517 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 13 266 82 36 80 129 385), lower := (rows 97 162 13 266 82 36 80 128 256), losses := [] }

theorem u10517 : Upper (D 7) (R 7) [96,160,9,258,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10517 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10518 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 266 82 36 192 145 273), lower := (rows 97 162 13 266 82 36 192 128 256), losses := [] }

theorem u10518 : Upper (D 7) (R 7) [96,160,9,258,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10518 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10519 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 162 13 266 145 36 66 208 336), lower := (rows 97 162 13 266 145 36 66 128 256), losses := [] }

theorem u10519 : Upper (D 7) (R 7) [96,160,9,258,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10519 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10520 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 97 162 13 266 145 36 80 194 322), lower := (rows 97 162 13 266 145 36 80 128 256), losses := [] }

theorem u10520 : Upper (D 7) (R 7) [96,160,9,258,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10520 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10521 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 97 162 13 266 148 33 66 208 336), lower := (rows 97 162 13 266 148 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 74 132 260), good := (rows 96 226 476 330 404 32 66 128 256) }] }

theorem u10521 : Upper (D 7) (R 7) [96,160,9,258,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10522 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 394, targets := 1 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 97 162 13 266 148 33 80 194 322), lower := (rows 97 162 13 266 148 33 80 128 256), losses := [] }

theorem u10522 : Upper (D 7) (R 7) [96,160,9,258,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10522 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10523 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 97 162 13 266 208 33 66 148 276), lower := (rows 97 162 13 266 208 33 66 128 256), losses := [] }

theorem u10523 : Upper (D 7) (R 7) [96,160,9,258,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10524 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 266 208 33 68 146 274), lower := (rows 97 162 13 266 208 33 68 128 256), losses := [] }

theorem u10524 : Upper (D 7) (R 7) [96,160,9,258,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10524 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10525 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 266 208 33 80 134 262), lower := (rows 97 162 13 266 208 33 80 128 256), losses := [] }

theorem u10525 : Upper (D 7) (R 7) [96,160,9,258,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10525 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10526 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 266 208 36 65 146 274), lower := (rows 97 162 13 266 208 36 65 128 256), losses := [] }

theorem u10526 : Upper (D 7) (R 7) [96,160,9,258,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10526 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10527 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 162 13 266 208 36 66 145 273), lower := (rows 97 162 13 266 208 36 66 128 256), losses := [] }

theorem u10527 : Upper (D 7) (R 7) [96,160,9,258,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10527 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10528 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 13 266 208 36 80 131 259), lower := (rows 97 162 13 266 208 36 80 128 256), losses := [] }

theorem u10528 : Upper (D 7) (R 7) [96,160,9,258,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10528 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10529 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 146, targets := 1 },{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 97 162 13 268 82 34 65 144 400), lower := (rows 97 162 13 268 82 34 65 128 256), losses := [] }

theorem u10529 : Upper (D 7) (R 7) [96,160,9,260,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10530 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 396, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 162 13 268 82 34 80 129 385), lower := (rows 97 162 13 268 82 34 80 128 256), losses := [] }

theorem u10530 : Upper (D 7) (R 7) [96,160,9,260,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10530 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10531 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 301, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 97 162 13 268 82 34 192 145 273), lower := (rows 97 162 13 268 82 34 192 128 256), losses := [] }

theorem u10531 : Upper (D 7) (R 7) [96,160,9,260,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10532 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 268 145 34 66 208 336), lower := (rows 97 162 13 268 145 34 66 128 256), losses := [] }

theorem u10532 : Upper (D 7) (R 7) [96,160,9,260,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10533 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 81, targets := 2 },{ cop := 7, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 97 162 13 268 145 34 80 194 322), lower := (rows 97 162 13 268 145 34 80 128 256), losses := [] }

theorem u10533 : Upper (D 7) (R 7) [96,160,9,260,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10533 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10534 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 146, targets := 1 },{ cop := 1, region := 81, targets := 2 }], pairs := [(0,1),(1,0),(4,0),(4,1)], upper := (rows 97 162 13 268 208 34 65 146 274), lower := (rows 97 162 13 268 208 34 65 128 256), losses := [] }

theorem u10534 : Upper (D 7) (R 7) [96,160,9,260,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10535 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 268 208 34 66 145 273), lower := (rows 97 162 13 268 208 34 66 128 256), losses := [] }

theorem u10535 : Upper (D 7) (R 7) [96,160,9,260,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10536 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 162 13 268 208 34 80 131 259), lower := (rows 97 162 13 268 208 34 80 128 256), losses := [] }

theorem u10536 : Upper (D 7) (R 7) [96,160,9,260,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10536 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10537 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 280 82 36 65 130 386), lower := (rows 97 162 13 280 82 36 65 128 256), losses := [] }

theorem u10537 : Upper (D 7) (R 7) [96,160,9,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10537 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10538 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 280 82 36 66 129 385), lower := (rows 97 162 13 280 82 36 66 128 256), losses := [] }

theorem u10538 : Upper (D 7) (R 7) [96,160,9,272,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10538 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10539 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 280 82 36 192 131 259), lower := (rows 97 162 13 280 82 36 192 128 256), losses := [] }

theorem u10539 : Upper (D 7) (R 7) [96,160,9,272,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10539 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10540 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 162 13 280 84 34 65 130 386), lower := (rows 97 162 13 280 84 34 65 128 256), losses := [] }

theorem u10540 : Upper (D 7) (R 7) [96,160,9,272,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10541 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 280 84 34 66 129 385), lower := (rows 97 162 13 280 84 34 66 128 256), losses := [] }

theorem u10541 : Upper (D 7) (R 7) [96,160,9,272,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10542 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 },{ cop := 1, region := 65, targets := 2 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(3,6)], upper := (rows 97 162 13 280 84 34 192 131 259), lower := (rows 97 162 13 280 84 34 192 128 256), losses := [{ target := 6, region := (rows 1 215 4 24 16 255 0 133 261), good := (rows 419 162 431 314 446 34 162 162 256) }] }

theorem u10542 : Upper (D 7) (R 7) [96,160,9,272,68,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10543 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 280 145 34 66 196 324), lower := (rows 97 162 13 280 145 34 66 128 256), losses := [] }

theorem u10543 : Upper (D 7) (R 7) [96,160,9,272,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10544 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 13 280 145 34 68 194 322), lower := (rows 97 162 13 280 145 34 68 128 256), losses := [{ target := 0, region := (rows 0 215 4 24 16 255 68 197 325), good := (rows 482 162 494 314 442 34 486 162 256) }] }

theorem u10544 : Upper (D 7) (R 7) [96,160,9,272,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10544 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10545 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 34, targets := 65 },{ cop := 1, region := 65, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 280 148 34 65 194 322), lower := (rows 97 162 13 280 148 34 65 128 256), losses := [] }

theorem u10545 : Upper (D 7) (R 7) [96,160,9,272,132,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10546 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 280 148 34 66 193 321), lower := (rows 97 162 13 280 148 34 66 128 256), losses := [] }

theorem u10546 : Upper (D 7) (R 7) [96,160,9,272,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10547 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 2 },{ cop := 2, region := 162, targets := 65 }], pairs := [(0,1),(1,0),(1,6),(4,1)], upper := (rows 97 162 13 280 208 34 65 134 262), lower := (rows 97 162 13 280 208 34 65 128 256), losses := [] }

theorem u10547 : Upper (D 7) (R 7) [96,160,9,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10548 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 280 208 34 66 133 261), lower := (rows 97 162 13 280 208 34 66 128 256), losses := [] }

theorem u10548 : Upper (D 7) (R 7) [96,160,9,272,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10549 : Route 9 := (fun mask => (mask,id))

def c10549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10549 : Upper (D 7) (R 7) [96,160,9,272,192,2,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,192,2,4] 13 (by decide) (choices 1) [1,2] r10549 c10549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u795
  · exact u796

def b10550 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 280 208 36 65 130 258), lower := (rows 97 162 13 280 208 36 65 128 256), losses := [] }

theorem u10550 : Upper (D 7) (R 7) [96,160,9,272,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10550 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10551 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,6),(4,0),(4,5)], upper := (rows 97 162 13 280 208 36 66 131 259), lower := (rows 97 162 13 280 208 36 66 128 256), losses := [] }

theorem u10551 : Upper (D 7) (R 7) [96,160,9,272,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10551 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10552 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 328 145 34 66 148 276), lower := (rows 97 162 13 328 145 34 66 128 256), losses := [] }

theorem u10552 : Upper (D 7) (R 7) [96,160,9,320,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10553 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 146, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 328 145 34 68 146 274), lower := (rows 97 162 13 328 145 34 68 128 256), losses := [] }

theorem u10553 : Upper (D 7) (R 7) [96,160,9,320,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10553 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10554 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 2 },{ cop := 2, region := 162, targets := 64 }], pairs := [(0,1),(1,6),(4,1)], upper := (rows 97 162 13 328 145 34 80 134 262), lower := (rows 97 162 13 328 145 34 80 128 256), losses := [] }

theorem u10554 : Upper (D 7) (R 7) [96,160,9,320,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10554 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10555 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 178, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 162 13 328 148 34 65 146 274), lower := (rows 97 162 13 328 148 34 65 128 256), losses := [] }

theorem u10555 : Upper (D 7) (R 7) [96,160,9,320,132,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10556 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 328 148 34 66 145 273), lower := (rows 97 162 13 328 148 34 66 128 256), losses := [] }

theorem u10556 : Upper (D 7) (R 7) [96,160,9,320,132,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10557 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 178, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 328 148 34 80 131 259), lower := (rows 97 162 13 328 148 34 80 128 256), losses := [] }

theorem u10557 : Upper (D 7) (R 7) [96,160,9,320,132,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10557 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10558 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 429, targets := 2 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 97 162 13 392 82 33 66 148 276), lower := (rows 97 162 13 392 82 33 66 128 256), losses := [] }

theorem u10558 : Upper (D 7) (R 7) [96,160,9,384,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10559 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 392 82 33 68 146 274), lower := (rows 97 162 13 392 82 33 68 128 256), losses := [] }

theorem u10559 : Upper (D 7) (R 7) [96,160,9,384,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10559 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10559
end Delivery.IrregularNine14.P07
