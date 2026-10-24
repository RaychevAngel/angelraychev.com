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

def b11520 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 262, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 97 290 70 137 146 48 72 133 261), lower := (rows 97 290 70 137 146 48 72 128 256), losses := [] }

theorem u11520 : Upper (D 7) (R 7) [96,288,66,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11520 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11521 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 290 70 137 148 33 66 152 280), lower := (rows 97 290 70 137 148 33 66 128 256), losses := [] }

theorem u11521 : Upper (D 7) (R 7) [96,288,66,129,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11522 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 290 70 137 148 33 72 146 274), lower := (rows 97 290 70 137 148 33 72 128 256), losses := [] }

theorem u11522 : Upper (D 7) (R 7) [96,288,66,129,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11522 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11523 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 97 290 70 137 148 33 80 138 266), lower := (rows 97 290 70 137 148 33 80 128 256), losses := [] }

theorem u11523 : Upper (D 7) (R 7) [96,288,66,129,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11523 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11524 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 290 70 137 148 40 65 146 274), lower := (rows 97 290 70 137 148 40 65 128 256), losses := [] }

theorem u11524 : Upper (D 7) (R 7) [96,288,66,129,132,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11524 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11525 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 290 70 137 148 40 66 145 273), lower := (rows 97 290 70 137 148 40 66 128 256), losses := [] }

theorem u11525 : Upper (D 7) (R 7) [96,288,66,129,132,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11525 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11526 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 137 148 40 80 131 259), lower := (rows 97 290 70 137 148 40 80 128 256), losses := [] }

theorem u11526 : Upper (D 7) (R 7) [96,288,66,129,132,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11526 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11527 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 290 70 137 148 48 65 138 266), lower := (rows 97 290 70 137 148 48 65 128 256), losses := [] }

theorem u11527 : Upper (D 7) (R 7) [96,288,66,129,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11528 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 185, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 290 70 137 148 48 66 137 265), lower := (rows 97 290 70 137 148 48 66 128 256), losses := [] }

theorem u11528 : Upper (D 7) (R 7) [96,288,66,129,132,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11529 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 137 148 48 72 131 259), lower := (rows 97 290 70 137 148 48 72 128 256), losses := [] }

theorem u11529 : Upper (D 7) (R 7) [96,288,66,129,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11529 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11530 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 152, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0)], upper := (rows 97 290 70 138 148 33 65 152 280), lower := (rows 97 290 70 138 148 33 65 128 256), losses := [] }

theorem u11530 : Upper (D 7) (R 7) [96,288,66,130,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11531 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 290 70 138 148 33 72 145 273), lower := (rows 97 290 70 138 148 33 72 128 256), losses := [] }

theorem u11531 : Upper (D 7) (R 7) [96,288,66,130,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11531 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11532 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 290 70 138 148 33 80 137 265), lower := (rows 97 290 70 138 148 33 80 128 256), losses := [] }

theorem u11532 : Upper (D 7) (R 7) [96,288,66,130,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11532 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11533 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 290 70 138 148 40 65 145 273), lower := (rows 97 290 70 138 148 40 65 128 256), losses := [] }

theorem u11533 : Upper (D 7) (R 7) [96,288,66,130,132,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11533 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11534 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 138 148 40 80 129 257), lower := (rows 97 290 70 138 148 40 80 128 256), losses := [] }

theorem u11534 : Upper (D 7) (R 7) [96,288,66,130,132,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11534 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11535 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(3,6)], upper := (rows 97 290 70 138 148 48 65 137 265), lower := (rows 97 290 70 138 148 48 65 128 256), losses := [] }

theorem u11535 : Upper (D 7) (R 7) [96,288,66,130,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11535 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11536 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 138 148 48 72 129 257), lower := (rows 97 290 70 138 148 48 72 128 256), losses := [] }

theorem u11536 : Upper (D 7) (R 7) [96,288,66,130,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11536 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11537 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 290 76 137 146 34 65 148 276), lower := (rows 97 290 76 137 146 34 65 128 256), losses := [] }

theorem u11537 : Upper (D 7) (R 7) [96,288,72,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11538 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 97 290 76 137 146 34 68 145 273), lower := (rows 97 290 76 137 146 34 68 128 256), losses := [] }

theorem u11538 : Upper (D 7) (R 7) [96,288,72,129,130,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11538 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11539 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 290 76 137 146 34 80 133 261), lower := (rows 97 290 76 137 146 34 80 128 256), losses := [] }

theorem u11539 : Upper (D 7) (R 7) [96,288,72,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11539 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11540 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 290 76 137 146 48 65 134 262), lower := (rows 97 290 76 137 146 48 65 128 256), losses := [] }

theorem u11540 : Upper (D 7) (R 7) [96,288,72,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11540 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11541 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 290 76 137 146 48 66 133 261), lower := (rows 97 290 76 137 146 48 66 128 256), losses := [] }

theorem u11541 : Upper (D 7) (R 7) [96,288,72,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11541 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11542 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 97 290 76 137 146 48 68 131 259), lower := (rows 97 290 76 137 146 48 68 128 256), losses := [] }

theorem u11542 : Upper (D 7) (R 7) [96,288,72,129,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11542 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11543 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,1),(2,0),(2,5),(4,1)], upper := (rows 97 290 76 138 145 33 66 148 276), lower := (rows 97 290 76 138 145 33 66 128 256), losses := [] }

theorem u11543 : Upper (D 7) (R 7) [96,288,72,130,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11544 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 290 76 138 145 33 68 146 274), lower := (rows 97 290 76 138 145 33 68 128 256), losses := [] }

theorem u11544 : Upper (D 7) (R 7) [96,288,72,130,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11544 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11545 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 76 138 145 33 80 134 262), lower := (rows 97 290 76 138 145 33 80 128 256), losses := [] }

theorem u11545 : Upper (D 7) (R 7) [96,288,72,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11545 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11546 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 76 138 145 48 65 134 262), lower := (rows 97 290 76 138 145 48 65 128 256), losses := [] }

theorem u11546 : Upper (D 7) (R 7) [96,288,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11546 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11547 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 97 290 76 138 145 48 66 133 261), lower := (rows 97 290 76 138 145 48 66 128 256), losses := [] }

theorem u11547 : Upper (D 7) (R 7) [96,288,72,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11547 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11548 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 76 138 145 48 68 131 259), lower := (rows 97 290 76 138 145 48 68 128 256), losses := [] }

theorem u11548 : Upper (D 7) (R 7) [96,288,72,130,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11548 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11549 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 76 138 148 33 65 146 274), lower := (rows 97 290 76 138 148 33 65 128 256), losses := [] }

theorem u11549 : Upper (D 7) (R 7) [96,288,72,130,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11550 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 290 76 138 148 33 66 145 273), lower := (rows 97 290 76 138 148 33 66 128 256), losses := [] }

theorem u11550 : Upper (D 7) (R 7) [96,288,72,130,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11551 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 290 76 138 148 33 80 131 259), lower := (rows 97 290 76 138 148 33 80 128 256), losses := [] }

theorem u11551 : Upper (D 7) (R 7) [96,288,72,130,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11551 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11552 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 386, targets := 1 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 97 386 7 25 148 34 72 224 352), lower := (rows 97 386 7 25 148 34 72 128 256), losses := [{ target := 0, region := (rows 0 79 4 8 20 127 72 201 329), good := (rows 482 418 438 506 182 34 490 128 256) },{ target := 1, region := (rows 1 0 4 12 20 32 92 129 257), good := (rows 481 384 477 473 220 32 72 128 256) }] }

theorem u11552 : Upper (D 7) (R 7) [96,384,3,17,132,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11552 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11553 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 7 25 148 34 96 200 328), lower := (rows 97 386 7 25 148 34 96 128 256), losses := [] }

theorem u11553 : Upper (D 7) (R 7) [96,384,3,17,132,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11554 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 7 25 148 40 96 194 322), lower := (rows 97 386 7 25 148 40 96 128 256), losses := [] }

theorem u11554 : Upper (D 7) (R 7) [96,384,3,17,132,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11554 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11555 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 97 386 7 25 152 34 68 224 352), lower := (rows 97 386 7 25 152 34 68 128 256), losses := [] }

theorem u11555 : Upper (D 7) (R 7) [96,384,3,17,136,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11555 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11556 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 7 25 152 34 96 196 324), lower := (rows 97 386 7 25 152 34 96 128 256), losses := [] }

theorem u11556 : Upper (D 7) (R 7) [96,384,3,17,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11557 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 386 7 26 145 36 72 224 352), lower := (rows 97 386 7 26 145 36 72 128 256), losses := [] }

theorem u11557 : Upper (D 7) (R 7) [96,384,3,18,129,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11557 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11558 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 7 26 145 36 96 200 328), lower := (rows 97 386 7 26 145 36 96 128 256), losses := [] }

theorem u11558 : Upper (D 7) (R 7) [96,384,3,18,129,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11558 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11559 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 7 26 145 40 96 196 324), lower := (rows 97 386 7 26 145 40 96 128 256), losses := [] }

theorem u11559 : Upper (D 7) (R 7) [96,384,3,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11559 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11560 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 386 7 26 148 33 72 224 352), lower := (rows 97 386 7 26 148 33 72 128 256), losses := [] }

theorem u11560 : Upper (D 7) (R 7) [96,384,3,18,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11560 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11561 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 7 26 148 33 96 200 328), lower := (rows 97 386 7 26 148 33 96 128 256), losses := [] }

theorem u11561 : Upper (D 7) (R 7) [96,384,3,18,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11562 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 386 7 26 176 33 68 200 328), lower := (rows 97 386 7 26 176 33 68 128 256), losses := [] }

theorem u11562 : Upper (D 7) (R 7) [96,384,3,18,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11562 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11563 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(2,5)], upper := (rows 97 386 7 26 176 33 72 196 324), lower := (rows 97 386 7 26 176 33 72 128 256), losses := [] }

theorem u11563 : Upper (D 7) (R 7) [96,384,3,18,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11563 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11564 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 386 7 26 176 36 65 200 328), lower := (rows 97 386 7 26 176 36 65 128 256), losses := [] }

theorem u11564 : Upper (D 7) (R 7) [96,384,3,18,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11564 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11565 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 386 7 26 176 36 72 193 321), lower := (rows 97 386 7 26 176 36 72 128 256), losses := [] }

theorem u11565 : Upper (D 7) (R 7) [96,384,3,18,160,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11565 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11566 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 144, targets := 2 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 97 386 7 28 145 34 72 224 352), lower := (rows 97 386 7 28 145 34 72 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 21 32 76 129 257), good := (rows 497 384 477 92 401 32 72 128 256) }] }

theorem u11566 : Upper (D 7) (R 7) [96,384,3,20,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11566 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11567 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 7 28 145 34 96 200 328), lower := (rows 97 386 7 28 145 34 96 128 256), losses := [] }

theorem u11567 : Upper (D 7) (R 7) [96,384,3,20,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11568 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 7 28 145 40 96 194 322), lower := (rows 97 386 7 28 145 40 96 128 256), losses := [] }

theorem u11568 : Upper (D 7) (R 7) [96,384,3,20,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11568 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11569 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 394, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 97 386 7 42 145 48 68 200 328), lower := (rows 97 386 7 42 145 48 68 128 256), losses := [] }

theorem u11569 : Upper (D 7) (R 7) [96,384,3,34,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11569 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11570 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 386 7 42 145 48 72 196 324), lower := (rows 97 386 7 42 145 48 72 128 256), losses := [] }

theorem u11570 : Upper (D 7) (R 7) [96,384,3,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11570 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11571 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 81, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 97 386 7 44 88 160 65 146 274), lower := (rows 97 386 7 44 88 160 65 128 256), losses := [] }

theorem u11571 : Upper (D 7) (R 7) [96,384,3,36,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11572 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(3,0),(3,1),(4,0)], upper := (rows 97 386 7 44 88 160 66 145 273), lower := (rows 97 386 7 44 88 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 162 70 128 256), good := (rows 96 482 126 124 88 160 98 160 256) },{ target := 1, region := (rows 81 0 4 12 16 178 64 144 272), good := (rows 97 416 45 44 505 160 97 160 256) }] }

theorem u11572 : Upper (D 7) (R 7) [96,384,3,36,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11573 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 81, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 386 7 44 88 160 80 131 259), lower := (rows 97 386 7 44 88 160 80 128 256), losses := [] }

theorem u11573 : Upper (D 7) (R 7) [96,384,3,36,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11573 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11574 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5)], upper := (rows 97 386 7 44 145 48 66 200 328), lower := (rows 97 386 7 44 145 48 66 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 16 48 70 0 264), good := (rows 97 322 71 365 49 48 66 0 256) }] }

theorem u11574 : Upper (D 7) (R 7) [96,384,3,36,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11574 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11575 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 386 7 44 145 48 72 194 322), lower := (rows 97 386 7 44 145 48 72 128 256), losses := [] }

theorem u11575 : Upper (D 7) (R 7) [96,384,3,36,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11575 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11576 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 97 386 7 56 145 34 68 200 328), lower := (rows 97 386 7 56 145 34 68 128 256), losses := [] }

theorem u11576 : Upper (D 7) (R 7) [96,384,3,48,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11576 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11577 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 56 145 34 72 196 324), lower := (rows 97 386 7 56 145 34 72 128 256), losses := [] }

theorem u11577 : Upper (D 7) (R 7) [96,384,3,48,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11577 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11578 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 97 386 7 56 145 36 66 200 328), lower := (rows 97 386 7 56 145 36 66 128 256), losses := [] }

theorem u11578 : Upper (D 7) (R 7) [96,384,3,48,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11578 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11579 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 386 7 56 145 36 72 194 322), lower := (rows 97 386 7 56 145 36 72 128 256), losses := [] }

theorem u11579 : Upper (D 7) (R 7) [96,384,3,48,129,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11579 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11579
end Delivery.IrregularNine14.P07
