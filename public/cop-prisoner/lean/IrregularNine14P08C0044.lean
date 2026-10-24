import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0005

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2640 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 88 176 160 69 133 261), lower := (rows 35 322 44 88 176 160 64 128 256), losses := [] }

theorem u2640 : Upper (D 8) (R 8) [34,320,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 137 84 33 240 176 432), lower := (rows 35 322 44 137 84 33 64 128 256), losses := [] }

theorem u2641 : Upper (D 8) (R 8) [34,320,40,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 322 44 137 84 48 225 161 417), lower := (rows 35 322 44 137 84 48 64 128 256), losses := [] }

theorem u2642 : Upper (D 8) (R 8) [34,320,40,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2642 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 84 160 113 177 305), lower := (rows 35 322 44 137 84 160 64 128 256), losses := [] }

theorem u2643 : Upper (D 8) (R 8) [34,320,40,129,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 112 33 212 148 404), lower := (rows 35 322 44 137 112 33 64 128 256), losses := [] }

theorem u2644 : Upper (D 8) (R 8) [34,320,40,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 322 44 137 112 36 209 145 401), lower := (rows 35 322 44 137 112 36 64 128 256), losses := [] }

theorem u2645 : Upper (D 8) (R 8) [34,320,40,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2645 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 322 44 137 112 48 197 133 389), lower := (rows 35 322 44 137 112 48 64 128 256), losses := [] }

theorem u2646 : Upper (D 8) (R 8) [34,320,40,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2646 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 112 160 85 149 277), lower := (rows 35 322 44 137 112 160 64 128 256), losses := [] }

theorem u2647 : Upper (D 8) (R 8) [34,320,40,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 137 176 33 84 212 340), lower := (rows 35 322 44 137 176 33 64 128 256), losses := [] }

theorem u2648 : Upper (D 8) (R 8) [34,320,40,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 322 44 137 176 36 81 209 337), lower := (rows 35 322 44 137 176 36 64 128 256), losses := [] }

theorem u2649 : Upper (D 8) (R 8) [34,320,40,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2649 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 322 44 137 176 48 69 197 325), lower := (rows 35 322 44 137 176 48 64 128 256), losses := [] }

theorem u2650 : Upper (D 8) (R 8) [34,320,40,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2650 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 44 137 176 96 85 149 277), lower := (rows 35 322 44 137 176 96 64 128 256), losses := [] }

theorem u2651 : Upper (D 8) (R 8) [34,320,40,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 137 208 33 116 180 308), lower := (rows 35 322 44 137 208 33 64 128 256), losses := [] }

theorem u2652 : Upper (D 8) (R 8) [34,320,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 44 137 208 36 113 177 305), lower := (rows 35 322 44 137 208 36 64 128 256), losses := [] }

theorem u2653 : Upper (D 8) (R 8) [34,320,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2653 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 322 44 137 208 48 101 165 293), lower := (rows 35 322 44 137 208 48 64 128 256), losses := [] }

theorem u2654 : Upper (D 8) (R 8) [34,320,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2654 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 140 112 33 209 145 401), lower := (rows 35 322 44 140 112 33 64 128 256), losses := [] }

theorem u2655 : Upper (D 8) (R 8) [34,320,40,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 44 140 112 48 193 129 385), lower := (rows 35 322 44 140 112 48 64 128 256), losses := [] }

theorem u2656 : Upper (D 8) (R 8) [34,320,40,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2656 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 44 140 112 160 81 145 273), lower := (rows 35 322 44 140 112 160 64 128 256), losses := [] }

theorem u2657 : Upper (D 8) (R 8) [34,320,40,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 112 33 197 133 389), lower := (rows 35 322 44 152 112 33 64 128 256), losses := [] }

theorem u2658 : Upper (D 8) (R 8) [34,320,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 44 152 112 36 193 129 385), lower := (rows 35 322 44 152 112 36 64 128 256), losses := [] }

theorem u2659 : Upper (D 8) (R 8) [34,320,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2659 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 152 112 160 69 133 261), lower := (rows 35 322 44 152 112 160 64 128 256), losses := [] }

theorem u2660 : Upper (D 8) (R 8) [34,320,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 200 145 33 116 180 308), lower := (rows 35 322 44 200 145 33 64 128 256), losses := [] }

theorem u2661 : Upper (D 8) (R 8) [34,320,40,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 44 200 145 36 113 177 305), lower := (rows 35 322 44 200 145 36 64 128 256), losses := [] }

theorem u2662 : Upper (D 8) (R 8) [34,320,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2662 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 322 44 200 145 48 101 165 293), lower := (rows 35 322 44 200 145 48 64 128 256), losses := [] }

theorem u2663 : Upper (D 8) (R 8) [34,320,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2663 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 200 176 33 85 149 277), lower := (rows 35 322 44 200 176 33 64 128 256), losses := [] }

theorem u2664 : Upper (D 8) (R 8) [34,320,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 44 200 176 36 81 145 273), lower := (rows 35 322 44 200 176 36 64 128 256), losses := [] }

theorem u2665 : Upper (D 8) (R 8) [34,320,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2665 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 322 44 200 176 48 69 133 261), lower := (rows 35 322 44 200 176 48 64 128 256), losses := [] }

theorem u2666 : Upper (D 8) (R 8) [34,320,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2666 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 137 176 33 116 180 308), lower := (rows 35 322 76 137 176 33 64 128 256), losses := [] }

theorem u2667 : Upper (D 8) (R 8) [34,320,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 76 137 176 36 113 177 305), lower := (rows 35 322 76 137 176 36 64 128 256), losses := [] }

theorem u2668 : Upper (D 8) (R 8) [34,320,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2668 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 322 76 137 176 48 101 165 293), lower := (rows 35 322 76 137 176 48 64 128 256), losses := [] }

theorem u2669 : Upper (D 8) (R 8) [34,320,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2669 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 168 145 33 116 180 308), lower := (rows 35 322 76 168 145 33 64 128 256), losses := [] }

theorem u2670 : Upper (D 8) (R 8) [34,320,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 76 168 145 36 113 177 305), lower := (rows 35 322 76 168 145 36 64 128 256), losses := [] }

theorem u2671 : Upper (D 8) (R 8) [34,320,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2671 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 322 76 168 145 48 101 165 293), lower := (rows 35 322 76 168 145 48 64 128 256), losses := [] }

theorem u2672 : Upper (D 8) (R 8) [34,320,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2672 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 100 137 148 33 120 184 312), lower := (rows 35 322 100 137 148 33 64 128 256), losses := [] }

theorem u2673 : Upper (D 8) (R 8) [34,320,96,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 322 100 137 148 40 113 177 305), lower := (rows 35 322 100 137 148 40 64 128 256), losses := [] }

theorem u2674 : Upper (D 8) (R 8) [34,320,96,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2674 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 322 100 137 148 48 105 169 297), lower := (rows 35 322 100 137 148 48 64 128 256), losses := [] }

theorem u2675 : Upper (D 8) (R 8) [34,320,96,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2675 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 100 137 176 33 92 156 284), lower := (rows 35 322 100 137 176 33 64 128 256), losses := [] }

theorem u2676 : Upper (D 8) (R 8) [34,320,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 322 100 137 176 36 89 153 281), lower := (rows 35 322 100 137 176 36 64 128 256), losses := [] }

theorem u2677 : Upper (D 8) (R 8) [34,320,96,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2677 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 322 100 137 176 40 85 149 277), lower := (rows 35 322 100 137 176 40 64 128 256), losses := [] }

theorem u2678 : Upper (D 8) (R 8) [34,320,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2678 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 322 100 137 176 48 77 141 269), lower := (rows 35 322 100 137 176 48 64 128 256), losses := [] }

theorem u2679 : Upper (D 8) (R 8) [34,320,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2679 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 100 140 176 33 89 153 281), lower := (rows 35 322 100 140 176 33 64 128 256), losses := [] }

theorem u2680 : Upper (D 8) (R 8) [34,320,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 100 140 176 40 81 145 273), lower := (rows 35 322 100 140 176 40 64 128 256), losses := [] }

theorem u2681 : Upper (D 8) (R 8) [34,320,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2681 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 322 100 140 176 48 73 137 265), lower := (rows 35 322 100 140 176 48 64 128 256), losses := [] }

theorem u2682 : Upper (D 8) (R 8) [34,320,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2682 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 28 168 304 33 224 224 480), lower := (rows 67 7 28 168 304 33 64 128 256), losses := [] }

theorem u2683 : Upper (D 8) (R 8) [66,5,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2684 : Route 9 := (fun mask => (mask,id))

def c2684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2684 : Upper (D 8) (R 8) [66,5,24,160,288,64] 13 := by
  apply FastRouting.sound _ _ [66,5,24,160,288,64] 13 (by decide) (choices 1) [1,32,128] r2684 c2684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u315
  · exact u316
  · exact u317

def b2685 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 28 168 304 160 97 225 353), lower := (rows 67 7 28 168 304 160 64 128 256), losses := [] }

theorem u2685 : Upper (D 8) (R 8) [66,5,24,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 112 33 480 416 416), lower := (rows 67 7 44 152 112 33 64 128 256), losses := [] }

theorem u2686 : Upper (D 8) (R 8) [66,5,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 112 160 353 417 289), lower := (rows 67 7 44 152 112 160 64 128 256), losses := [] }

theorem u2687 : Upper (D 8) (R 8) [66,5,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2687 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 7 44 152 112 288 225 161 417), lower := (rows 67 7 44 152 112 288 64 128 256), losses := [] }

theorem u2688 : Upper (D 8) (R 8) [66,5,40,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2688 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 304 33 224 224 480), lower := (rows 67 7 44 152 304 33 64 128 256), losses := [] }

theorem u2689 : Upper (D 8) (R 8) [66,5,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2690 : Route 9 := (fun mask => (mask,id))

def c2690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2690 : Upper (D 8) (R 8) [66,5,40,144,288,64] 13 := by
  apply FastRouting.sound _ _ [66,5,40,144,288,64] 13 (by decide) (choices 1) [1,32,128] r2690 c2690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u318
  · exact u319
  · exact u320

def b2691 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 304 160 97 225 353), lower := (rows 67 7 44 152 304 160 64 128 256), losses := [] }

theorem u2691 : Upper (D 8) (R 8) [66,5,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 152 336 33 224 160 416), lower := (rows 67 7 44 152 336 33 64 128 256), losses := [] }

theorem u2692 : Upper (D 8) (R 8) [66,5,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 152 336 160 97 161 289), lower := (rows 67 7 44 152 336 160 64 128 256), losses := [] }

theorem u2693 : Upper (D 8) (R 8) [66,5,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 112 33 224 160 416), lower := (rows 67 7 44 280 112 33 64 128 256), losses := [] }

theorem u2694 : Upper (D 8) (R 8) [66,5,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2695 : Route 9 := (fun mask => (mask,id))

def c2695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2695 : Upper (D 8) (R 8) [66,5,40,272,96,128] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272,96,128] 13 (by decide) (choices 1) [1,32,128] r2695 c2695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u321
  · exact u322
  · exact u323

def b2696 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 176 33 224 224 480), lower := (rows 67 7 44 280 176 33 64 128 256), losses := [] }

theorem u2696 : Upper (D 8) (R 8) [66,5,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2697 : Route 9 := (fun mask => (mask,id))

def c2697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2697 : Upper (D 8) (R 8) [66,5,40,272,160,64] 13 := by
  apply FastRouting.sound _ _ [66,5,40,272,160,64] 13 (by decide) (choices 1) [1,32,128] r2697 c2697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u324
  · exact u325
  · exact u326

def b2698 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 7 44 280 176 160 97 225 353), lower := (rows 67 7 44 280 176 160 64 128 256), losses := [] }

theorem u2698 : Upper (D 8) (R 8) [66,5,40,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 67 7 44 280 208 33 224 160 416), lower := (rows 67 7 44 280 208 33 64 128 256), losses := [] }

theorem u2699 : Upper (D 8) (R 8) [66,5,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P08
