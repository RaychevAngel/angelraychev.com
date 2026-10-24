import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0002

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2640 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 152 81 288 68 161 289), lower := (rows 11 38 70 152 81 288 68 128 256), losses := [] }

theorem u2640 : Upper (D 6) (R 6) [10,36,66,144,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2640 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 152 81 288 96 133 261), lower := (rows 11 38 70 152 81 288 96 128 256), losses := [] }

theorem u2641 : Upper (D 6) (R 6) [10,36,66,144,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2641 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 38 70 152 276 33 65 224 352), lower := (rows 11 38 70 152 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 31 22 97 97 231 359), good := (rows 505 508 508 152 412 489 489 128 256) }] }

theorem u2642 : Upper (D 6) (R 6) [10,36,66,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 152 276 33 96 193 321), lower := (rows 11 38 70 152 276 33 96 128 256), losses := [] }

theorem u2643 : Upper (D 6) (R 6) [10,36,66,144,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 70 152 304 33 65 196 324), lower := (rows 11 38 70 152 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 18 32 64 132 260), good := (rows 26 446 478 152 304 32 64 128 256) }] }

theorem u2644 : Upper (D 6) (R 6) [10,36,66,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 304 33 68 193 321), lower := (rows 11 38 70 152 304 33 68 128 256), losses := [] }

theorem u2645 : Upper (D 6) (R 6) [10,36,66,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 70 152 336 33 65 164 292), lower := (rows 11 38 70 152 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 32 64 130 258), good := (rows 394 446 478 152 336 32 64 128 256) }] }

theorem u2646 : Upper (D 6) (R 6) [10,36,66,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 152 336 33 68 161 289), lower := (rows 11 38 70 152 336 33 68 128 256), losses := [] }

theorem u2647 : Upper (D 6) (R 6) [10,36,66,144,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 152 336 33 96 133 261), lower := (rows 11 38 70 152 336 33 96 128 256), losses := [] }

theorem u2648 : Upper (D 6) (R 6) [10,36,66,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 81 33 68 400 272), lower := (rows 11 38 70 168 81 33 68 128 256), losses := [] }

theorem u2649 : Upper (D 6) (R 6) [10,36,66,160,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 70 168 81 33 80 388 260), lower := (rows 11 38 70 168 81 33 80 128 256), losses := [] }

theorem u2650 : Upper (D 6) (R 6) [10,36,66,160,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2650 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 81 33 320 148 276), lower := (rows 11 38 70 168 81 33 320 128 256), losses := [] }

theorem u2651 : Upper (D 6) (R 6) [10,36,66,160,65,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2651 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 273 33 68 208 336), lower := (rows 11 38 70 168 273 33 68 128 256), losses := [] }

theorem u2652 : Upper (D 6) (R 6) [10,36,66,160,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 273 33 80 196 324), lower := (rows 11 38 70 168 273 33 80 128 256), losses := [] }

theorem u2653 : Upper (D 6) (R 6) [10,36,66,160,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2653 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 168 276 33 65 208 336), lower := (rows 11 38 70 168 276 33 65 128 256), losses := [] }

theorem u2654 : Upper (D 6) (R 6) [10,36,66,160,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 168 276 33 80 193 321), lower := (rows 11 38 70 168 276 33 80 128 256), losses := [] }

theorem u2655 : Upper (D 6) (R 6) [10,36,66,160,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2655 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 168 336 33 65 148 276), lower := (rows 11 38 70 168 336 33 65 128 256), losses := [] }

theorem u2656 : Upper (D 6) (R 6) [10,36,66,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 168 336 33 68 145 273), lower := (rows 11 38 70 168 336 33 68 128 256), losses := [] }

theorem u2657 : Upper (D 6) (R 6) [10,36,66,160,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 70 168 336 33 80 133 261), lower := (rows 11 38 70 168 336 33 80 128 256), losses := [] }

theorem u2658 : Upper (D 6) (R 6) [10,36,66,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2658 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 38 70 200 49 288 65 148 276), lower := (rows 11 38 70 200 49 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 144 272), good := (rows 79 6 70 200 477 256 69 128 256) }] }

theorem u2659 : Upper (D 6) (R 6) [10,36,66,192,33,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2659 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 200 49 288 68 145 273), lower := (rows 11 38 70 200 49 288 68 128 256), losses := [] }

theorem u2660 : Upper (D 6) (R 6) [10,36,66,192,33,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2660 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5)], upper := (rows 11 38 70 200 49 288 80 133 261), lower := (rows 11 38 70 200 49 288 80 128 256), losses := [] }

theorem u2661 : Upper (D 6) (R 6) [10,36,66,192,33,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2661 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 304, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 200 273 33 68 176 304), lower := (rows 11 38 70 200 273 33 68 128 256), losses := [] }

theorem u2662 : Upper (D 6) (R 6) [10,36,66,192,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 36, camps := [], pairs := [(3,0),(3,1)], upper := (rows 11 38 70 200 273 33 80 164 292), lower := (rows 11 38 70 200 273 33 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 80 130 258), good := (rows 394 430 462 200 336 32 80 128 256) },{ target := 1, region := (rows 1 0 4 15 17 49 113 130 258), good := (rows 505 492 460 200 377 121 112 128 256) }] }

theorem u2663 : Upper (D 6) (R 6) [10,36,66,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2663 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 200 273 33 96 148 276), lower := (rows 11 38 70 200 273 33 96 128 256), losses := [] }

theorem u2664 : Upper (D 6) (R 6) [10,36,66,192,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,0)], upper := (rows 11 38 70 200 273 48 65 164 292), lower := (rows 11 38 70 200 273 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 48 64 130 258), good := (rows 394 430 462 200 304 48 64 128 256) }] }

theorem u2665 : Upper (D 6) (R 6) [10,36,66,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2665 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 200 273 48 68 161 289), lower := (rows 11 38 70 200 273 48 68 128 256), losses := [] }

theorem u2666 : Upper (D 6) (R 6) [10,36,66,192,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2666 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 200 273 48 96 133 261), lower := (rows 11 38 70 200 273 48 96 128 256), losses := [] }

theorem u2667 : Upper (D 6) (R 6) [10,36,66,192,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2667 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 70 200 276 33 65 176 304), lower := (rows 11 38 70 200 276 33 65 128 256), losses := [] }

theorem u2668 : Upper (D 6) (R 6) [10,36,66,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 200 276 33 80 161 289), lower := (rows 11 38 70 200 276 33 80 128 256), losses := [] }

theorem u2669 : Upper (D 6) (R 6) [10,36,66,192,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2669 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 200 276 33 96 145 273), lower := (rows 11 38 70 200 276 33 96 128 256), losses := [] }

theorem u2670 : Upper (D 6) (R 6) [10,36,66,192,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 70 200 304 33 65 148 276), lower := (rows 11 38 70 200 304 33 65 128 256), losses := [] }

theorem u2671 : Upper (D 6) (R 6) [10,36,66,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 304, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 200 304 33 68 145 273), lower := (rows 11 38 70 200 304 33 68 128 256), losses := [] }

theorem u2672 : Upper (D 6) (R 6) [10,36,66,192,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 200 304 33 80 133 261), lower := (rows 11 38 70 200 304 33 80 128 256), losses := [] }

theorem u2673 : Upper (D 6) (R 6) [10,36,66,192,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2673 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 392 81 33 68 176 304), lower := (rows 11 38 70 392 81 33 68 128 256), losses := [] }

theorem u2674 : Upper (D 6) (R 6) [10,36,66,384,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 70 392 81 33 80 164 292), lower := (rows 11 38 70 392 81 33 80 128 256), losses := [] }

theorem u2675 : Upper (D 6) (R 6) [10,36,66,384,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2675 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 392 81 33 96 148 276), lower := (rows 11 38 70 392 81 33 96 128 256), losses := [] }

theorem u2676 : Upper (D 6) (R 6) [10,36,66,384,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 70 392 112 33 65 148 276), lower := (rows 11 38 70 392 112 33 65 128 256), losses := [] }

theorem u2677 : Upper (D 6) (R 6) [10,36,66,384,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 392 112 33 68 145 273), lower := (rows 11 38 70 392 112 33 68 128 256), losses := [] }

theorem u2678 : Upper (D 6) (R 6) [10,36,66,384,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 70 392 112 33 80 133 261), lower := (rows 11 38 70 392 112 33 80 128 256), losses := [] }

theorem u2679 : Upper (D 6) (R 6) [10,36,66,384,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2679 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 38 84 73 146 288 65 164 292), lower := (rows 11 38 84 73 146 288 65 128 256), losses := [] }

theorem u2680 : Upper (D 6) (R 6) [10,36,80,65,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2680 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 84 73 146 288 68 161 289), lower := (rows 11 38 84 73 146 288 68 128 256), losses := [] }

theorem u2681 : Upper (D 6) (R 6) [10,36,80,65,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2681 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 84 73 146 288 96 133 261), lower := (rows 11 38 84 73 146 288 96 128 256), losses := [] }

theorem u2682 : Upper (D 6) (R 6) [10,36,80,65,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2682 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 84 73 400 34 65 164 292), lower := (rows 11 38 84 73 400 34 65 128 256), losses := [] }

theorem u2683 : Upper (D 6) (R 6) [10,36,80,65,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 68 },{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 38 84 73 400 34 68 161 289), lower := (rows 11 38 84 73 400 34 68 128 256), losses := [] }

theorem u2684 : Upper (D 6) (R 6) [10,36,80,65,384,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2685 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 84 73 400 34 96 133 261), lower := (rows 11 38 84 73 400 34 96 128 256), losses := [] }

theorem u2685 : Upper (D 6) (R 6) [10,36,80,65,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 400, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 104 400 33 65 134 262), lower := (rows 11 38 84 104 400 33 65 128 256), losses := [] }

theorem u2686 : Upper (D 6) (R 6) [10,36,80,96,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 104 400 33 66 133 261), lower := (rows 11 38 84 104 400 33 66 128 256), losses := [] }

theorem u2687 : Upper (D 6) (R 6) [10,36,80,96,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 104 400 33 68 131 259), lower := (rows 11 38 84 104 400 33 68 128 256), losses := [] }

theorem u2688 : Upper (D 6) (R 6) [10,36,80,96,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 84 168 274 33 65 196 324), lower := (rows 11 38 84 168 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 32 64 132 260), good := (rows 26 446 468 168 282 32 64 128 256) }] }

theorem u2689 : Upper (D 6) (R 6) [10,36,80,160,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2690 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 168 274 33 68 193 321), lower := (rows 11 38 84 168 274 33 68 128 256), losses := [] }

theorem u2690 : Upper (D 6) (R 6) [10,36,80,160,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2691 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 170, targets := 1 },{ cop := 4, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 38 84 200 273 34 65 164 292), lower := (rows 11 38 84 200 273 34 65 128 256), losses := [] }

theorem u2691 : Upper (D 6) (R 6) [10,36,80,192,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 68 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 38 84 200 273 34 68 161 289), lower := (rows 11 38 84 200 273 34 68 128 256), losses := [] }

theorem u2692 : Upper (D 6) (R 6) [10,36,80,192,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 84 200 273 34 96 133 261), lower := (rows 11 38 84 200 273 34 96 128 256), losses := [] }

theorem u2693 : Upper (D 6) (R 6) [10,36,80,192,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 11 38 84 200 274 33 65 164 292), lower := (rows 11 38 84 200 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 19 32 64 130 258), good := (rows 410 438 84 204 402 48 84 128 256) }] }

theorem u2694 : Upper (D 6) (R 6) [10,36,80,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 200 274 33 68 161 289), lower := (rows 11 38 84 200 274 33 68 128 256), losses := [] }

theorem u2695 : Upper (D 6) (R 6) [10,36,80,192,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2696 : Route 9 := (fun mask => (mask,id))

def c2696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2696 : Upper (D 6) (R 6) [10,36,80,192,258,1,32] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,258,1,32] 13 (by decide) (choices 1) [1,4] r2696 c2696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u172
  · exact u173

def b2697 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 84 200 276 33 65 162 290), lower := (rows 11 38 84 200 276 33 65 128 256), losses := [] }

theorem u2697 : Upper (D 6) (R 6) [10,36,80,192,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 38 84 200 276 33 66 161 289), lower := (rows 11 38 84 200 276 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 8 18 33 64 161 289), good := (rows 441 436 84 204 276 417 84 128 256) }] }

theorem u2698 : Upper (D 6) (R 6) [10,36,80,192,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2699 : Route 9 := (fun mask => (mask,id))

def c2699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2699 : Upper (D 6) (R 6) [10,36,80,192,260,1,32] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,260,1,32] 13 (by decide) (choices 1) [1,2] r2699 c2699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u174
  · exact u175

#print axioms u2699
end Delivery.IrregularNine14.P06
