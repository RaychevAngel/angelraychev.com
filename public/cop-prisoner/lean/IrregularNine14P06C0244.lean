import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0055

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14640 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 76 145 34 340 404 276), lower := (rows 11 98 37 76 145 34 64 128 256), losses := [] }

theorem u14640 : Upper (D 6) (R 6) [10,96,33,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14641 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 37 76 145 36 338 402 274), lower := (rows 11 98 37 76 145 36 64 128 256), losses := [] }

theorem u14641 : Upper (D 6) (R 6) [10,96,33,68,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14642 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 145 48 326 390 262), lower := (rows 11 98 37 76 145 48 64 128 256), losses := [] }

theorem u14642 : Upper (D 6) (R 6) [10,96,33,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14642 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14643 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 145 288 86 150 278), lower := (rows 11 98 37 76 145 288 64 128 256), losses := [] }

theorem u14643 : Upper (D 6) (R 6) [10,96,33,68,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14643 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14644 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 76 146 33 340 404 276), lower := (rows 11 98 37 76 146 33 64 128 256), losses := [] }

theorem u14644 : Upper (D 6) (R 6) [10,96,33,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14645 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 37 76 146 36 337 401 273), lower := (rows 11 98 37 76 146 36 64 128 256), losses := [] }

theorem u14645 : Upper (D 6) (R 6) [10,96,33,68,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14646 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 146 48 325 389 261), lower := (rows 11 98 37 76 146 48 64 128 256), losses := [] }

theorem u14646 : Upper (D 6) (R 6) [10,96,33,68,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14646 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14647 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 146 288 85 149 277), lower := (rows 11 98 37 76 146 288 64 128 256), losses := [] }

theorem u14647 : Upper (D 6) (R 6) [10,96,33,68,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14647 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14648 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 76 148 33 338 402 274), lower := (rows 11 98 37 76 148 33 64 128 256), losses := [] }

theorem u14648 : Upper (D 6) (R 6) [10,96,33,68,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14649 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 76 148 34 337 401 273), lower := (rows 11 98 37 76 148 34 64 128 256), losses := [] }

theorem u14649 : Upper (D 6) (R 6) [10,96,33,68,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14650 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 148 48 323 387 259), lower := (rows 11 98 37 76 148 48 64 128 256), losses := [] }

theorem u14650 : Upper (D 6) (R 6) [10,96,33,68,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14650 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14651 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 148 288 83 147 275), lower := (rows 11 98 37 76 148 288 64 128 256), losses := [] }

theorem u14651 : Upper (D 6) (R 6) [10,96,33,68,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14651 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14652 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 76 400 33 86 150 278), lower := (rows 11 98 37 76 400 33 64 128 256), losses := [] }

theorem u14652 : Upper (D 6) (R 6) [10,96,33,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14653 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 76 400 34 85 149 277), lower := (rows 11 98 37 76 400 34 64 128 256), losses := [] }

theorem u14653 : Upper (D 6) (R 6) [10,96,33,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14654 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 400, targets := 36 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 37 76 400 36 83 147 275), lower := (rows 11 98 37 76 400 36 64 128 256), losses := [] }

theorem u14654 : Upper (D 6) (R 6) [10,96,33,68,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14655 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 76 400 48 71 135 263), lower := (rows 11 98 37 76 400 48 64 128 256), losses := [] }

theorem u14655 : Upper (D 6) (R 6) [10,96,33,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14655 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14656 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 88 148 33 326 390 262), lower := (rows 11 98 37 88 148 33 64 128 256), losses := [] }

theorem u14656 : Upper (D 6) (R 6) [10,96,33,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14657 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 88 148 34 325 389 261), lower := (rows 11 98 37 88 148 34 64 128 256), losses := [] }

theorem u14657 : Upper (D 6) (R 6) [10,96,33,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14658 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 88 148 36 323 387 259), lower := (rows 11 98 37 88 148 36 64 128 256), losses := [] }

theorem u14658 : Upper (D 6) (R 6) [10,96,33,80,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14659 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 88 148 288 71 135 263), lower := (rows 11 98 37 88 148 288 64 128 256), losses := [] }

theorem u14659 : Upper (D 6) (R 6) [10,96,33,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14659 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14660 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 88 400 33 70 134 262), lower := (rows 11 98 37 88 400 33 64 128 256), losses := [] }

theorem u14660 : Upper (D 6) (R 6) [10,96,33,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14661 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 88 400 34 69 133 261), lower := (rows 11 98 37 88 400 34 64 128 256), losses := [] }

theorem u14661 : Upper (D 6) (R 6) [10,96,33,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14662 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 88 400 36 71 135 263), lower := (rows 11 98 37 88 400 36 64 128 256), losses := [] }

theorem u14662 : Upper (D 6) (R 6) [10,96,33,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14663 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 137 84 34 340 404 276), lower := (rows 11 98 37 137 84 34 64 128 256), losses := [] }

theorem u14663 : Upper (D 6) (R 6) [10,96,33,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14664 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 137 84 36 338 402 274), lower := (rows 11 98 37 137 84 36 64 128 256), losses := [] }

theorem u14664 : Upper (D 6) (R 6) [10,96,33,129,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14665 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 137 84 48 326 390 262), lower := (rows 11 98 37 137 84 48 64 128 256), losses := [] }

theorem u14665 : Upper (D 6) (R 6) [10,96,33,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14665 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14666 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 37 137 84 288 86 150 278), lower := (rows 11 98 37 137 84 288 64 128 256), losses := [] }

theorem u14666 : Upper (D 6) (R 6) [10,96,33,129,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14666 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14667 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 137 274 36 84 212 340), lower := (rows 11 98 37 137 274 36 64 128 256), losses := [] }

theorem u14667 : Upper (D 6) (R 6) [10,96,33,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14668 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 37 137 274 48 68 196 324), lower := (rows 11 98 37 137 274 48 64 128 256), losses := [] }

theorem u14668 : Upper (D 6) (R 6) [10,96,33,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14669 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 137 274 96 84 148 276), lower := (rows 11 98 37 137 274 96 64 128 256), losses := [] }

theorem u14669 : Upper (D 6) (R 6) [10,96,33,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14670 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 137 276 34 84 212 340), lower := (rows 11 98 37 137 276 34 64 128 256), losses := [] }

theorem u14670 : Upper (D 6) (R 6) [10,96,33,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14671 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 137 276 36 82 210 338), lower := (rows 11 98 37 137 276 36 64 128 256), losses := [] }

theorem u14671 : Upper (D 6) (R 6) [10,96,33,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14672 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 37 137 276 48 70 198 326), lower := (rows 11 98 37 137 276 48 64 128 256), losses := [] }

theorem u14672 : Upper (D 6) (R 6) [10,96,33,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14672 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14673 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 137 276 96 86 150 278), lower := (rows 11 98 37 137 276 96 64 128 256), losses := [] }

theorem u14673 : Upper (D 6) (R 6) [10,96,33,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14674 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 137 336 34 84 148 276), lower := (rows 11 98 37 137 336 34 64 128 256), losses := [] }

theorem u14674 : Upper (D 6) (R 6) [10,96,33,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14675 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 137 336 36 86 150 278), lower := (rows 11 98 37 137 336 36 64 128 256), losses := [] }

theorem u14675 : Upper (D 6) (R 6) [10,96,33,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14676 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 137 336 48 70 134 262), lower := (rows 11 98 37 137 336 48 64 128 256), losses := [] }

theorem u14676 : Upper (D 6) (R 6) [10,96,33,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14676 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14677 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 140 22 33 336 464 336), lower := (rows 11 98 37 140 22 33 64 128 256), losses := [] }

theorem u14677 : Upper (D 6) (R 6) [10,96,33,132,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14678 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 140 22 48 321 449 321), lower := (rows 11 98 37 140 22 48 64 128 256), losses := [] }

theorem u14678 : Upper (D 6) (R 6) [10,96,33,132,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14678 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14679 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 140 22 96 337 401 273), lower := (rows 11 98 37 140 22 96 64 128 256), losses := [] }

theorem u14679 : Upper (D 6) (R 6) [10,96,33,132,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14680 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 201, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 98 37 140 22 288 81 209 337), lower := (rows 11 98 37 140 22 288 64 128 256), losses := [] }

theorem u14680 : Upper (D 6) (R 6) [10,96,33,132,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14680 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14681 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 140 81 34 340 404 276), lower := (rows 11 98 37 140 81 34 64 128 256), losses := [] }

theorem u14681 : Upper (D 6) (R 6) [10,96,33,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14682 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 98 37 140 81 36 338 402 274), lower := (rows 11 98 37 140 81 36 64 128 256), losses := [] }

theorem u14682 : Upper (D 6) (R 6) [10,96,33,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14683 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 140 81 48 326 390 262), lower := (rows 11 98 37 140 81 48 64 128 256), losses := [] }

theorem u14683 : Upper (D 6) (R 6) [10,96,33,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14683 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14684 : Route 9 := (fun mask => (mask,id))

def c14684 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14684 : Upper (D 6) (R 6) [10,96,33,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,65,256] 13 (by decide) (choices 1) [2,4,16] r14684 c14684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3331
  · exact u3332
  · exact u3333

def b14685 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 140 84 33 338 402 274), lower := (rows 11 98 37 140 84 33 64 128 256), losses := [] }

theorem u14685 : Upper (D 6) (R 6) [10,96,33,132,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14686 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 140 84 34 337 401 273), lower := (rows 11 98 37 140 84 34 64 128 256), losses := [] }

theorem u14686 : Upper (D 6) (R 6) [10,96,33,132,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14687 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 140 84 48 323 387 259), lower := (rows 11 98 37 140 84 48 64 128 256), losses := [] }

theorem u14687 : Upper (D 6) (R 6) [10,96,33,132,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14687 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14688 : Route 9 := (fun mask => (mask,id))

def c14688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14688 : Upper (D 6) (R 6) [10,96,33,132,68,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132,68,256] 13 (by decide) (choices 1) [1,2,16] r14688 c14688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3334
  · exact u3335
  · exact u3336

def b14689 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 140 273 34 84 212 340), lower := (rows 11 98 37 140 273 34 64 128 256), losses := [] }

theorem u14689 : Upper (D 6) (R 6) [10,96,33,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14690 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 98 37 140 273 36 82 210 338), lower := (rows 11 98 37 140 273 36 64 128 256), losses := [] }

theorem u14690 : Upper (D 6) (R 6) [10,96,33,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14691 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 98 37 140 273 48 70 198 326), lower := (rows 11 98 37 140 273 48 64 128 256), losses := [] }

theorem u14691 : Upper (D 6) (R 6) [10,96,33,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14691 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14692 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 140 273 96 86 150 278), lower := (rows 11 98 37 140 273 96 64 128 256), losses := [] }

theorem u14692 : Upper (D 6) (R 6) [10,96,33,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14693 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 140 274 33 84 212 340), lower := (rows 11 98 37 140 274 33 64 128 256), losses := [] }

theorem u14693 : Upper (D 6) (R 6) [10,96,33,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14694 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 98 37 140 274 36 81 209 337), lower := (rows 11 98 37 140 274 36 64 128 256), losses := [] }

theorem u14694 : Upper (D 6) (R 6) [10,96,33,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14695 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 98 37 140 274 48 69 197 325), lower := (rows 11 98 37 140 274 48 64 128 256), losses := [] }

theorem u14695 : Upper (D 6) (R 6) [10,96,33,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14695 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14696 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 140 274 96 85 149 277), lower := (rows 11 98 37 140 274 96 64 128 256), losses := [] }

theorem u14696 : Upper (D 6) (R 6) [10,96,33,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14697 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 140 276 33 82 210 338), lower := (rows 11 98 37 140 276 33 64 128 256), losses := [] }

theorem u14697 : Upper (D 6) (R 6) [10,96,33,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14698 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 140 276 34 81 209 337), lower := (rows 11 98 37 140 276 34 64 128 256), losses := [] }

theorem u14698 : Upper (D 6) (R 6) [10,96,33,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14699 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 66, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 98 37 140 276 48 67 195 323), lower := (rows 11 98 37 140 276 48 64 128 256), losses := [{ target := 2, region := (rows 9 22 0 8 16 48 77 141 269), good := (rows 459 98 483 459 498 50 64 128 256) }] }

theorem u14699 : Upper (D 6) (R 6) [10,96,33,132,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14699 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14699
end Delivery.IrregularNine14.P06
