import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8640 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 152 304 40 65 130 258), lower := (rows 37 194 69 152 304 40 65 128 256), losses := [] }

theorem u8640 : Upper (D 7) (R 7) [36,192,65,144,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8640 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8641 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 69 152 304 40 66 131 259), lower := (rows 37 194 69 152 304 40 66 128 256), losses := [] }

theorem u8641 : Upper (D 7) (R 7) [36,192,65,144,288,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8641 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8642 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 168 274 48 65 138 266), lower := (rows 37 194 69 168 274 48 65 128 256), losses := [] }

theorem u8642 : Upper (D 7) (R 7) [36,192,65,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8642 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8643 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 194 69 168 274 48 66 137 265), lower := (rows 37 194 69 168 274 48 66 128 256), losses := [] }

theorem u8643 : Upper (D 7) (R 7) [36,192,65,160,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8643 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8644 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7)], upper := (rows 37 194 69 168 274 48 72 131 259), lower := (rows 37 194 69 168 274 48 72 128 256), losses := [] }

theorem u8644 : Upper (D 7) (R 7) [36,192,65,160,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8644 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8645 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 312, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 194 69 168 280 48 65 130 258), lower := (rows 37 194 69 168 280 48 65 128 256), losses := [] }

theorem u8645 : Upper (D 7) (R 7) [36,192,65,160,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8645 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8646 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 69 168 280 48 66 131 259), lower := (rows 37 194 69 168 280 48 66 128 256), losses := [] }

theorem u8646 : Upper (D 7) (R 7) [36,192,65,160,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8646 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8647 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 194 76 11 50 288 65 144 400), lower := (rows 37 194 76 11 50 288 65 128 256), losses := [] }

theorem u8647 : Upper (D 7) (R 7) [36,192,72,3,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8647 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8648 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 76 11 50 288 80 129 385), lower := (rows 37 194 76 11 50 288 80 128 256), losses := [] }

theorem u8648 : Upper (D 7) (R 7) [36,192,72,3,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8648 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8649 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 11 50 288 192 145 273), lower := (rows 37 194 76 11 50 288 192 128 256), losses := [] }

theorem u8649 : Upper (D 7) (R 7) [36,192,72,3,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8649 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8650 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 194 76 11 176 288 65 146 274), lower := (rows 37 194 76 11 176 288 65 128 256), losses := [] }

theorem u8650 : Upper (D 7) (R 7) [36,192,72,3,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8650 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8651 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 76 11 176 288 66 145 273), lower := (rows 37 194 76 11 176 288 66 128 256), losses := [] }

theorem u8651 : Upper (D 7) (R 7) [36,192,72,3,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8651 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8652 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 76 11 176 288 80 131 259), lower := (rows 37 194 76 11 176 288 80 128 256), losses := [] }

theorem u8652 : Upper (D 7) (R 7) [36,192,72,3,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8652 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8653 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 11 273 160 66 176 304), lower := (rows 37 194 76 11 273 160 66 128 256), losses := [] }

theorem u8653 : Upper (D 7) (R 7) [36,192,72,3,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8654 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 },{ cop := 3, region := 432, targets := 64 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 194 76 11 273 160 80 162 290), lower := (rows 37 194 76 11 273 160 80 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 28 174 0 138 266), good := (rows 53 418 445 443 273 160 16 160 256) }] }

theorem u8654 : Upper (D 7) (R 7) [36,192,72,3,257,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8654 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8655 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 272, targets := 32 },{ cop := 3, region := 272, targets := 64 },{ cop := 3, region := 272, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 194 76 11 273 160 96 146 274), lower := (rows 37 194 76 11 273 160 96 128 256), losses := [] }

theorem u8655 : Upper (D 7) (R 7) [36,192,72,3,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8656 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 304, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 11 274 160 65 176 304), lower := (rows 37 194 76 11 274 160 65 128 256), losses := [] }

theorem u8656 : Upper (D 7) (R 7) [36,192,72,3,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8657 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 3, region := 432, targets := 64 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 194 76 11 274 160 80 161 289), lower := (rows 37 194 76 11 274 160 80 128 256), losses := [] }

theorem u8657 : Upper (D 7) (R 7) [36,192,72,3,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8657 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8658 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 272, targets := 32 },{ cop := 3, region := 272, targets := 64 },{ cop := 3, region := 272, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 194 76 11 274 160 96 145 273), lower := (rows 37 194 76 11 274 160 96 128 256), losses := [] }

theorem u8658 : Upper (D 7) (R 7) [36,192,72,3,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8659 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 304, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 11 304 160 65 146 274), lower := (rows 37 194 76 11 304 160 65 128 256), losses := [] }

theorem u8659 : Upper (D 7) (R 7) [36,192,72,3,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8660 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 11 304 160 66 145 273), lower := (rows 37 194 76 11 304 160 66 128 256), losses := [] }

theorem u8660 : Upper (D 7) (R 7) [36,192,72,3,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8661 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(1,5),(3,5),(4,6)], upper := (rows 37 194 76 11 304 160 80 131 259), lower := (rows 37 194 76 11 304 160 80 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 16 0 80 137 265), good := (rows 399 194 462 395 336 128 80 128 256) }] }

theorem u8661 : Upper (D 7) (R 7) [36,192,72,3,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8661 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8662 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 194 76 11 400 48 65 162 290), lower := (rows 37 194 76 11 400 48 65 128 256), losses := [] }

theorem u8662 : Upper (D 7) (R 7) [36,192,72,3,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8662 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8663 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 76 11 400 48 66 161 289), lower := (rows 37 194 76 11 400 48 66 128 256), losses := [] }

theorem u8663 : Upper (D 7) (R 7) [36,192,72,3,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8663 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8664 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 400, targets := 32 },{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 76 11 400 48 96 131 259), lower := (rows 37 194 76 11 400 48 96 128 256), losses := [] }

theorem u8664 : Upper (D 7) (R 7) [36,192,72,3,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8664 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8665 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 25 50 288 65 130 386), lower := (rows 37 194 76 25 50 288 65 128 256), losses := [] }

theorem u8665 : Upper (D 7) (R 7) [36,192,72,17,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8665 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8666 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 25 50 288 66 129 385), lower := (rows 37 194 76 25 50 288 66 128 256), losses := [] }

theorem u8666 : Upper (D 7) (R 7) [36,192,72,17,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8666 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8667 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 25 50 288 192 131 259), lower := (rows 37 194 76 25 50 288 192 128 256), losses := [] }

theorem u8667 : Upper (D 7) (R 7) [36,192,72,17,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8667 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8668 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 25 176 288 65 130 258), lower := (rows 37 194 76 25 176 288 65 128 256), losses := [] }

theorem u8668 : Upper (D 7) (R 7) [36,192,72,17,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8668 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8669 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 76 25 176 288 66 131 259), lower := (rows 37 194 76 25 176 288 66 128 256), losses := [] }

theorem u8669 : Upper (D 7) (R 7) [36,192,72,17,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8669 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8670 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 304, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 25 274 34 65 160 416), lower := (rows 37 194 76 25 274 34 65 128 256), losses := [] }

theorem u8670 : Upper (D 7) (R 7) [36,192,72,17,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8671 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 194 76 25 274 34 96 129 385), lower := (rows 37 194 76 25 274 34 96 128 256), losses := [] }

theorem u8671 : Upper (D 7) (R 7) [36,192,72,17,258,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8672 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 25 274 34 192 161 289), lower := (rows 37 194 76 25 274 34 192 128 256), losses := [] }

theorem u8672 : Upper (D 7) (R 7) [36,192,72,17,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8673 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 304, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 25 274 160 65 162 290), lower := (rows 37 194 76 25 274 160 65 128 256), losses := [] }

theorem u8673 : Upper (D 7) (R 7) [36,192,72,17,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8674 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(0,1),(0,6),(1,0),(1,5)], upper := (rows 37 194 76 25 274 160 66 161 289), lower := (rows 37 194 76 25 274 160 66 128 256), losses := [] }

theorem u8674 : Upper (D 7) (R 7) [36,192,72,17,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8675 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 76 25 274 160 96 131 259), lower := (rows 37 194 76 25 274 160 96 128 256), losses := [{ target := 0, region := (rows 0 162 12 8 16 162 243 128 256), good := (rows 102 226 76 92 370 226 98 226 256) },{ target := 1, region := (rows 17 0 28 24 16 162 243 128 256), good := (rows 101 224 76 93 381 224 96 224 256) }] }

theorem u8675 : Upper (D 7) (R 7) [36,192,72,17,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8676 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 25 304 34 65 130 386), lower := (rows 37 194 76 25 304 34 65 128 256), losses := [] }

theorem u8676 : Upper (D 7) (R 7) [36,192,72,17,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8677 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 25 304 34 66 129 385), lower := (rows 37 194 76 25 304 34 66 128 256), losses := [] }

theorem u8677 : Upper (D 7) (R 7) [36,192,72,17,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8678 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 76 25 304 34 192 131 259), lower := (rows 37 194 76 25 304 34 192 128 256), losses := [] }

theorem u8678 : Upper (D 7) (R 7) [36,192,72,17,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8679 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 25 304 160 65 130 258), lower := (rows 37 194 76 25 304 160 65 128 256), losses := [] }

theorem u8679 : Upper (D 7) (R 7) [36,192,72,17,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8680 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 76 25 304 160 66 131 259), lower := (rows 37 194 76 25 304 160 66 128 256), losses := [{ target := 0, region := (rows 0 162 12 8 16 162 243 128 256), good := (rows 102 226 76 92 370 226 98 226 256) }] }

theorem u8680 : Upper (D 7) (R 7) [36,192,72,17,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8681 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 304, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 194 76 25 400 34 65 162 290), lower := (rows 37 194 76 25 400 34 65 128 256), losses := [] }

theorem u8681 : Upper (D 7) (R 7) [36,192,72,17,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8682 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 25 400 34 66 161 289), lower := (rows 37 194 76 25 400 34 66 128 256), losses := [] }

theorem u8682 : Upper (D 7) (R 7) [36,192,72,17,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8683 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(2,7)], upper := (rows 37 194 76 25 400 34 96 131 259), lower := (rows 37 194 76 25 400 34 96 128 256), losses := [{ target := 0, region := (rows 0 146 12 8 16 186 255 128 256), good := (rows 100 226 108 126 498 98 96 226 256) },{ target := 1, region := (rows 1 0 12 8 16 32 97 128 256), good := (rows 101 192 76 93 400 96 96 128 256) },{ target := 7, region := (rows 1 2 12 8 16 34 99 0 256), good := (rows 101 98 76 93 272 98 96 0 256) }] }

theorem u8683 : Upper (D 7) (R 7) [36,192,72,17,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8684 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 76 26 145 288 65 162 290), lower := (rows 37 194 76 26 145 288 65 128 256), losses := [] }

theorem u8684 : Upper (D 7) (R 7) [36,192,72,18,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8684 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8685 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 76 26 145 288 66 161 289), lower := (rows 37 194 76 26 145 288 66 128 256), losses := [] }

theorem u8685 : Upper (D 7) (R 7) [36,192,72,18,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8685 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8686 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 76 26 145 288 96 131 259), lower := (rows 37 194 76 26 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 288 353 128 256), good := (rows 100 194 76 30 222 352 96 128 352) }] }

theorem u8686 : Upper (D 7) (R 7) [36,192,72,18,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8686 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8687 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(2,5)], upper := (rows 37 194 76 26 273 160 65 162 290), lower := (rows 37 194 76 26 273 160 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 162 93 128 256), good := (rows 101 224 77 125 337 160 65 160 256) },{ target := 5, region := (rows 1 2 12 8 16 0 81 128 256), good := (rows 69 194 76 94 337 128 65 128 256) }] }

theorem u8687 : Upper (D 7) (R 7) [36,192,72,18,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8688 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 26 273 160 66 161 289), lower := (rows 37 194 76 26 273 160 66 128 256), losses := [] }

theorem u8688 : Upper (D 7) (R 7) [36,192,72,18,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8689 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 76 26 273 160 96 131 259), lower := (rows 37 194 76 26 273 160 96 128 256), losses := [{ target := 0, region := (rows 0 162 12 8 16 162 235 128 256), good := (rows 102 226 76 126 336 226 98 226 256) },{ target := 1, region := (rows 9 0 12 8 16 162 235 128 256), good := (rows 101 224 77 125 337 224 96 224 256) }] }

theorem u8689 : Upper (D 7) (R 7) [36,192,72,18,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8690 : Route 9 := (fun mask => (mask,id))

def c8690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8690 : Upper (D 7) (R 7) [36,192,72,18,288,128,1] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,288,128,1] 13 (by decide) (choices 1) [1,2] r8690 c8690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u680
  · exact u681

def b8691 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 76 26 304 160 66 129 257), lower := (rows 37 194 76 26 304 160 66 128 256), losses := [] }

theorem u8691 : Upper (D 7) (R 7) [36,192,72,18,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8692 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 42 145 288 65 146 274), lower := (rows 37 194 76 42 145 288 65 128 256), losses := [] }

theorem u8692 : Upper (D 7) (R 7) [36,192,72,34,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8692 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8693 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 76 42 145 288 66 145 273), lower := (rows 37 194 76 42 145 288 66 128 256), losses := [] }

theorem u8693 : Upper (D 7) (R 7) [36,192,72,34,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8693 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8694 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 76 42 145 288 80 131 259), lower := (rows 37 194 76 42 145 288 80 128 256), losses := [] }

theorem u8694 : Upper (D 7) (R 7) [36,192,72,34,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8694 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8695 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 76 42 273 48 65 130 386), lower := (rows 37 194 76 42 273 48 65 128 256), losses := [] }

theorem u8695 : Upper (D 7) (R 7) [36,192,72,34,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8695 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8696 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 76 42 273 48 66 129 385), lower := (rows 37 194 76 42 273 48 66 128 256), losses := [] }

theorem u8696 : Upper (D 7) (R 7) [36,192,72,34,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8696 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8697 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 76 42 273 48 192 131 259), lower := (rows 37 194 76 42 273 48 192 128 256), losses := [] }

theorem u8697 : Upper (D 7) (R 7) [36,192,72,34,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8697 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8698 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 76 56 145 34 65 386 258), lower := (rows 37 194 76 56 145 34 65 128 256), losses := [] }

theorem u8698 : Upper (D 7) (R 7) [36,192,72,48,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8699 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 76 56 145 34 66 385 257), lower := (rows 37 194 76 56 145 34 66 128 256), losses := [] }

theorem u8699 : Upper (D 7) (R 7) [36,192,72,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8699
end Delivery.IrregularNine14.P07
