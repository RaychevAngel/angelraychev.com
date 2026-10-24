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

def b5640 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 52 288 192 145 273), lower := (rows 35 194 14 73 52 288 192 128 256), losses := [] }

theorem u5640 : Upper (D 7) (R 7) [34,192,10,65,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5640 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5641 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 194 14 73 145 288 68 176 304), lower := (rows 35 194 14 73 145 288 68 128 256), losses := [] }

theorem u5641 : Upper (D 7) (R 7) [34,192,10,65,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5641 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5642 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 14 73 145 288 80 164 292), lower := (rows 35 194 14 73 145 288 80 128 256), losses := [] }

theorem u5642 : Upper (D 7) (R 7) [34,192,10,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5642 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5643 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 14 73 145 288 96 148 276), lower := (rows 35 194 14 73 145 288 96 128 256), losses := [] }

theorem u5643 : Upper (D 7) (R 7) [34,192,10,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5643 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5644 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 194 14 73 148 288 65 176 304), lower := (rows 35 194 14 73 148 288 65 128 256), losses := [] }

theorem u5644 : Upper (D 7) (R 7) [34,192,10,65,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5644 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5645 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 14 73 148 288 80 161 289), lower := (rows 35 194 14 73 148 288 80 128 256), losses := [] }

theorem u5645 : Upper (D 7) (R 7) [34,192,10,65,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5645 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5646 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 14 73 148 288 96 145 273), lower := (rows 35 194 14 73 148 288 96 128 256), losses := [] }

theorem u5646 : Upper (D 7) (R 7) [34,192,10,65,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5646 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5647 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 194 14 73 176 288 65 148 276), lower := (rows 35 194 14 73 176 288 65 128 256), losses := [] }

theorem u5647 : Upper (D 7) (R 7) [34,192,10,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5647 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5648 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 194 14 73 176 288 68 145 273), lower := (rows 35 194 14 73 176 288 68 128 256), losses := [] }

theorem u5648 : Upper (D 7) (R 7) [34,192,10,65,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5648 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5649 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 14 73 176 288 80 133 261), lower := (rows 35 194 14 73 176 288 80 128 256), losses := [] }

theorem u5649 : Upper (D 7) (R 7) [34,192,10,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5649 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5650 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 194 14 73 273 48 68 160 416), lower := (rows 35 194 14 73 273 48 68 128 256), losses := [] }

theorem u5650 : Upper (D 7) (R 7) [34,192,10,65,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5650 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5651 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 14 73 273 48 96 132 388), lower := (rows 35 194 14 73 273 48 96 128 256), losses := [] }

theorem u5651 : Upper (D 7) (R 7) [34,192,10,65,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5651 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5652 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 273 48 192 164 292), lower := (rows 35 194 14 73 273 48 192 128 256), losses := [] }

theorem u5652 : Upper (D 7) (R 7) [34,192,10,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5652 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5653 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 14 88 145 33 68 416 288), lower := (rows 35 194 14 88 145 33 68 128 256), losses := [] }

theorem u5653 : Upper (D 7) (R 7) [34,192,10,80,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5653 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5654 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 88 145 33 96 388 260), lower := (rows 35 194 14 88 145 33 96 128 256), losses := [] }

theorem u5654 : Upper (D 7) (R 7) [34,192,10,80,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5655 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 14 88 145 33 320 164 292), lower := (rows 35 194 14 88 145 33 320 128 256), losses := [] }

theorem u5655 : Upper (D 7) (R 7) [34,192,10,80,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5655 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5656 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 88 176 33 65 388 260), lower := (rows 35 194 14 88 176 33 65 128 256), losses := [] }

theorem u5656 : Upper (D 7) (R 7) [34,192,10,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5657 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 14 88 176 33 68 385 257), lower := (rows 35 194 14 88 176 33 68 128 256), losses := [] }

theorem u5657 : Upper (D 7) (R 7) [34,192,10,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5657 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5658 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 14 88 176 33 320 133 261), lower := (rows 35 194 14 88 176 33 320 128 256), losses := [] }

theorem u5658 : Upper (D 7) (R 7) [34,192,10,80,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5658 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5659 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 194 14 88 273 33 68 160 416), lower := (rows 35 194 14 88 273 33 68 128 256), losses := [] }

theorem u5659 : Upper (D 7) (R 7) [34,192,10,80,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5659 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5660 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 88 273 33 96 132 388), lower := (rows 35 194 14 88 273 33 96 128 256), losses := [] }

theorem u5660 : Upper (D 7) (R 7) [34,192,10,80,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5661 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 273 33 192 164 292), lower := (rows 35 194 14 88 273 33 192 128 256), losses := [] }

theorem u5661 : Upper (D 7) (R 7) [34,192,10,80,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5662 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 194 14 88 276 33 65 160 416), lower := (rows 35 194 14 88 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 79 74 113 32 64 161 289), good := (rows 446 222 14 94 276 436 478 128 256) }] }

theorem u5662 : Upper (D 7) (R 7) [34,192,10,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5663 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 35 194 14 88 276 33 96 129 385), lower := (rows 35 194 14 88 276 33 96 128 256), losses := [{ target := 5, region := (rows 1 66 79 74 113 0 64 161 289), good := (rows 415 222 14 94 276 405 478 128 256) }] }

theorem u5663 : Upper (D 7) (R 7) [34,192,10,80,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5664 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 276 33 192 161 289), lower := (rows 35 194 14 88 276 33 192 128 256), losses := [] }

theorem u5664 : Upper (D 7) (R 7) [34,192,10,80,260,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5665 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 88 304 33 65 132 388), lower := (rows 35 194 14 88 304 33 65 128 256), losses := [] }

theorem u5665 : Upper (D 7) (R 7) [34,192,10,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5666 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 194 14 88 304 33 68 129 385), lower := (rows 35 194 14 88 304 33 68 128 256), losses := [] }

theorem u5666 : Upper (D 7) (R 7) [34,192,10,80,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5666 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5667 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 304 33 192 133 261), lower := (rows 35 194 14 88 304 33 192 128 256), losses := [] }

theorem u5667 : Upper (D 7) (R 7) [34,192,10,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5668 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 194 14 88 400 33 65 164 292), lower := (rows 35 194 14 88 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 79 74 113 32 64 161 289), good := (rows 446 222 14 94 400 436 478 128 256) }] }

theorem u5668 : Upper (D 7) (R 7) [34,192,10,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5669 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 14 88 400 33 68 161 289), lower := (rows 35 194 14 88 400 33 68 128 256), losses := [] }

theorem u5669 : Upper (D 7) (R 7) [34,192,10,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5669 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5670 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6)], upper := (rows 35 194 14 88 400 33 96 133 261), lower := (rows 35 194 14 88 400 33 96 128 256), losses := [{ target := 5, region := (rows 1 66 79 74 113 0 64 161 289), good := (rows 415 222 14 94 400 405 478 128 256) }] }

theorem u5670 : Upper (D 7) (R 7) [34,192,10,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5671 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 104 145 288 65 148 276), lower := (rows 35 194 14 104 145 288 65 128 256), losses := [] }

theorem u5671 : Upper (D 7) (R 7) [34,192,10,96,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5671 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5672 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 194 14 104 145 288 68 145 273), lower := (rows 35 194 14 104 145 288 68 128 256), losses := [] }

theorem u5672 : Upper (D 7) (R 7) [34,192,10,96,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5672 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5673 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 14 104 145 288 80 133 261), lower := (rows 35 194 14 104 145 288 80 128 256), losses := [] }

theorem u5673 : Upper (D 7) (R 7) [34,192,10,96,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5673 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5674 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 104 148 288 65 145 273), lower := (rows 35 194 14 104 148 288 65 128 256), losses := [] }

theorem u5674 : Upper (D 7) (R 7) [34,192,10,96,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5674 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5675 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 14 104 148 288 80 129 257), lower := (rows 35 194 14 104 148 288 80 128 256), losses := [] }

theorem u5675 : Upper (D 7) (R 7) [34,192,10,96,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5675 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5676 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 14 104 273 48 65 132 388), lower := (rows 35 194 14 104 273 48 65 128 256), losses := [] }

theorem u5676 : Upper (D 7) (R 7) [34,192,10,96,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5676 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5677 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 194 14 104 273 48 68 129 385), lower := (rows 35 194 14 104 273 48 68 128 256), losses := [] }

theorem u5677 : Upper (D 7) (R 7) [34,192,10,96,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5677 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5678 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 273 48 192 133 261), lower := (rows 35 194 14 104 273 48 192 128 256), losses := [] }

theorem u5678 : Upper (D 7) (R 7) [34,192,10,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5678 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5679 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 4, region := 424, targets := 2 }], pairs := [(0,7),(3,1),(4,7)], upper := (rows 35 194 14 280 81 33 68 160 416), lower := (rows 35 194 14 280 81 33 68 128 256), losses := [] }

theorem u5679 : Upper (D 7) (R 7) [34,192,10,272,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5679 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5680 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 280 81 33 96 132 388), lower := (rows 35 194 14 280 81 33 96 128 256), losses := [] }

theorem u5680 : Upper (D 7) (R 7) [34,192,10,272,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5681 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 280 81 33 192 164 292), lower := (rows 35 194 14 280 81 33 192 128 256), losses := [] }

theorem u5681 : Upper (D 7) (R 7) [34,192,10,272,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5682 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(4,7)], upper := (rows 35 194 14 280 84 33 65 160 416), lower := (rows 35 194 14 280 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 87 73 82 32 64 161 289), good := (rows 446 222 30 284 94 428 478 128 256) }] }

theorem u5682 : Upper (D 7) (R 7) [34,192,10,272,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5683 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(4,7)], upper := (rows 35 194 14 280 84 33 96 129 385), lower := (rows 35 194 14 280 84 33 96 128 256), losses := [{ target := 5, region := (rows 1 66 87 73 82 0 64 161 289), good := (rows 415 222 30 284 94 397 478 128 256) }] }

theorem u5683 : Upper (D 7) (R 7) [34,192,10,272,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5684 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 280 84 33 192 161 289), lower := (rows 35 194 14 280 84 33 192 128 256), losses := [] }

theorem u5684 : Upper (D 7) (R 7) [34,192,10,272,68,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5685 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 280 112 33 65 132 388), lower := (rows 35 194 14 280 112 33 65 128 256), losses := [] }

theorem u5685 : Upper (D 7) (R 7) [34,192,10,272,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5686 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,7)], upper := (rows 35 194 14 280 112 33 68 129 385), lower := (rows 35 194 14 280 112 33 68 128 256), losses := [] }

theorem u5686 : Upper (D 7) (R 7) [34,192,10,272,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5686 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5687 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 280 112 33 192 133 261), lower := (rows 35 194 14 280 112 33 192 128 256), losses := [] }

theorem u5687 : Upper (D 7) (R 7) [34,192,10,272,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5688 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 4, region := 130, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 35 194 14 296 81 33 68 144 400), lower := (rows 35 194 14 296 81 33 68 128 256), losses := [] }

theorem u5688 : Upper (D 7) (R 7) [34,192,10,288,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5688 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5689 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 194 14 296 81 33 80 132 388), lower := (rows 35 194 14 296 81 33 80 128 256), losses := [] }

theorem u5689 : Upper (D 7) (R 7) [34,192,10,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5689 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5690 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 296 81 33 192 148 276), lower := (rows 35 194 14 296 81 33 192 128 256), losses := [] }

theorem u5690 : Upper (D 7) (R 7) [34,192,10,288,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5691 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 4, region := 130, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 194 14 296 84 33 65 144 400), lower := (rows 35 194 14 296 84 33 65 128 256), losses := [] }

theorem u5691 : Upper (D 7) (R 7) [34,192,10,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5692 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 194 14 296 84 33 80 129 385), lower := (rows 35 194 14 296 84 33 80 128 256), losses := [] }

theorem u5692 : Upper (D 7) (R 7) [34,192,10,288,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5692 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5693 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 296 84 33 192 145 273), lower := (rows 35 194 14 296 84 33 192 128 256), losses := [] }

theorem u5693 : Upper (D 7) (R 7) [34,192,10,288,68,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5694 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 194 14 328 145 33 68 176 304), lower := (rows 35 194 14 328 145 33 68 128 256), losses := [] }

theorem u5694 : Upper (D 7) (R 7) [34,192,10,320,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5694 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5695 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 328 145 33 80 164 292), lower := (rows 35 194 14 328 145 33 80 128 256), losses := [] }

theorem u5695 : Upper (D 7) (R 7) [34,192,10,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5695 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5696 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 194 14 328 145 33 96 148 276), lower := (rows 35 194 14 328 145 33 96 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 97 144 272), good := (rows 98 194 14 328 478 96 96 128 256) }] }

theorem u5696 : Upper (D 7) (R 7) [34,192,10,320,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5697 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 194 14 328 176 33 65 148 276), lower := (rows 35 194 14 328 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 74 79 74 49 32 64 225 353), good := (rows 446 462 14 462 432 436 478 128 256) }] }

theorem u5697 : Upper (D 7) (R 7) [34,192,10,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5698 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 194 14 328 176 33 68 145 273), lower := (rows 35 194 14 328 176 33 68 128 256), losses := [] }

theorem u5698 : Upper (D 7) (R 7) [34,192,10,320,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5698 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5699 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 328 176 33 80 133 261), lower := (rows 35 194 14 328 176 33 80 128 256), losses := [] }

theorem u5699 : Upper (D 7) (R 7) [34,192,10,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5699 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5699
end Delivery.IrregularNine14.P07
