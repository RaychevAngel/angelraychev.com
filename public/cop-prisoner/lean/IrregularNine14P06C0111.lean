import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6660 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 26 273 36 72 196 324), lower := (rows 35 131 100 26 273 36 72 128 256), losses := [] }

theorem u6660 : Upper (D 6) (R 6) [34,129,96,18,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6660 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6661 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 131 100 26 336 36 65 140 268), lower := (rows 35 131 100 26 336 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 95 8 24 127 67 136 264), good := (rows 101 229 100 508 372 36 101 128 256) }] }

theorem u6661 : Upper (D 6) (R 6) [34,129,96,18,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6662 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 26 336 36 68 137 265), lower := (rows 35 131 100 26 336 36 68 128 256), losses := [] }

theorem u6662 : Upper (D 6) (R 6) [34,129,96,18,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6663 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 26 336 36 72 133 261), lower := (rows 35 131 100 26 336 36 72 128 256), losses := [] }

theorem u6663 : Upper (D 6) (R 6) [34,129,96,18,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6663 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 100 28 273 36 66 200 328), lower := (rows 35 131 100 28 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 144 272), good := (rows 102 230 100 444 508 36 102 128 256) }] }

theorem u6664 : Upper (D 6) (R 6) [34,129,96,20,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6665 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 28 273 36 72 194 322), lower := (rows 35 131 100 28 273 36 72 128 256), losses := [] }

theorem u6665 : Upper (D 6) (R 6) [34,129,96,20,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6665 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6666 : PairBound 9 := { available := 72, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 35 131 100 28 274 36 65 200 328), lower := (rows 35 131 100 28 274 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 144 272), good := (rows 101 229 100 444 508 36 101 128 256) }] }

theorem u6666 : Upper (D 6) (R 6) [34,129,96,20,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6667 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 28 274 36 72 193 321), lower := (rows 35 131 100 28 274 36 72 128 256), losses := [] }

theorem u6667 : Upper (D 6) (R 6) [34,129,96,20,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6667 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6668 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 402, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 131 100 73 274 36 68 152 280), lower := (rows 35 131 100 73 274 36 68 128 256), losses := [] }

theorem u6668 : Upper (D 6) (R 6) [34,129,96,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6669 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 274 36 72 148 276), lower := (rows 35 131 100 73 274 36 72 128 256), losses := [] }

theorem u6669 : Upper (D 6) (R 6) [34,129,96,65,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6669 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6670 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 73 274 36 80 140 268), lower := (rows 35 131 100 73 274 36 80 128 256), losses := [] }

theorem u6670 : Upper (D 6) (R 6) [34,129,96,65,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6670 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6671 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 73 276 36 66 152 280), lower := (rows 35 131 100 73 276 36 66 128 256), losses := [] }

theorem u6671 : Upper (D 6) (R 6) [34,129,96,65,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6672 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 276 36 72 146 274), lower := (rows 35 131 100 73 276 36 72 128 256), losses := [] }

theorem u6672 : Upper (D 6) (R 6) [34,129,96,65,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6672 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6673 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 73 276 36 80 138 266), lower := (rows 35 131 100 73 276 36 80 128 256), losses := [] }

theorem u6673 : Upper (D 6) (R 6) [34,129,96,65,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6673 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6674 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 73 276 48 66 140 268), lower := (rows 35 131 100 73 276 48 66 128 256), losses := [] }

theorem u6674 : Upper (D 6) (R 6) [34,129,96,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6674 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6675 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 73 276 48 68 138 266), lower := (rows 35 131 100 73 276 48 68 128 256), losses := [] }

theorem u6675 : Upper (D 6) (R 6) [34,129,96,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6675 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6676 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6)], upper := (rows 35 131 100 73 276 48 72 134 262), lower := (rows 35 131 100 73 276 48 72 128 256), losses := [] }

theorem u6676 : Upper (D 6) (R 6) [34,129,96,65,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6676 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6677 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 73 280 36 66 148 276), lower := (rows 35 131 100 73 280 36 66 128 256), losses := [] }

theorem u6677 : Upper (D 6) (R 6) [34,129,96,65,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6678 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 131 100 73 280 36 68 146 274), lower := (rows 35 131 100 73 280 36 68 128 256), losses := [] }

theorem u6678 : Upper (D 6) (R 6) [34,129,96,65,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6679 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 73 280 36 80 134 262), lower := (rows 35 131 100 73 280 36 80 128 256), losses := [] }

theorem u6679 : Upper (D 6) (R 6) [34,129,96,65,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6679 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6680 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 74 273 36 68 152 280), lower := (rows 35 131 100 74 273 36 68 128 256), losses := [] }

theorem u6680 : Upper (D 6) (R 6) [34,129,96,66,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6681 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 273 36 72 148 276), lower := (rows 35 131 100 74 273 36 72 128 256), losses := [] }

theorem u6681 : Upper (D 6) (R 6) [34,129,96,66,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6681 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6682 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 74 273 36 80 140 268), lower := (rows 35 131 100 74 273 36 80 128 256), losses := [] }

theorem u6682 : Upper (D 6) (R 6) [34,129,96,66,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6682 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6683 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 74 276 36 65 152 280), lower := (rows 35 131 100 74 276 36 65 128 256), losses := [] }

theorem u6683 : Upper (D 6) (R 6) [34,129,96,66,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 276 36 72 145 273), lower := (rows 35 131 100 74 276 36 72 128 256), losses := [] }

theorem u6684 : Upper (D 6) (R 6) [34,129,96,66,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6684 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6685 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 74 276 36 80 137 265), lower := (rows 35 131 100 74 276 36 80 128 256), losses := [] }

theorem u6685 : Upper (D 6) (R 6) [34,129,96,66,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6685 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6686 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 74 276 48 65 140 268), lower := (rows 35 131 100 74 276 48 65 128 256), losses := [] }

theorem u6686 : Upper (D 6) (R 6) [34,129,96,66,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6686 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6687 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 74 276 48 68 137 265), lower := (rows 35 131 100 74 276 48 68 128 256), losses := [] }

theorem u6687 : Upper (D 6) (R 6) [34,129,96,66,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6687 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6688 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 131 100 74 276 48 72 133 261), lower := (rows 35 131 100 74 276 48 72 128 256), losses := [] }

theorem u6688 : Upper (D 6) (R 6) [34,129,96,66,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6688 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6689 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 74 280 36 65 148 276), lower := (rows 35 131 100 74 280 36 65 128 256), losses := [] }

theorem u6689 : Upper (D 6) (R 6) [34,129,96,66,264,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6690 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 74 280 36 68 145 273), lower := (rows 35 131 100 74 280 36 68 128 256), losses := [] }

theorem u6690 : Upper (D 6) (R 6) [34,129,96,66,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6691 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 74 280 36 80 133 261), lower := (rows 35 131 100 74 280 36 80 128 256), losses := [] }

theorem u6691 : Upper (D 6) (R 6) [34,129,96,66,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6691 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6692 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 100 88 273 36 66 140 268), lower := (rows 35 131 100 88 273 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 95 24 16 127 67 152 280), good := (rows 102 230 100 508 508 36 102 128 256) }] }

theorem u6692 : Upper (D 6) (R 6) [34,129,96,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6693 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 88 273 36 68 138 266), lower := (rows 35 131 100 88 273 36 68 128 256), losses := [] }

theorem u6693 : Upper (D 6) (R 6) [34,129,96,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 88 273 36 72 134 262), lower := (rows 35 131 100 88 273 36 72 128 256), losses := [] }

theorem u6694 : Upper (D 6) (R 6) [34,129,96,80,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6694 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6695 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 35 131 100 88 274 36 65 140 268), lower := (rows 35 131 100 88 274 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 95 24 16 127 67 152 280), good := (rows 101 229 100 508 508 36 101 128 256) }] }

theorem u6695 : Upper (D 6) (R 6) [34,129,96,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6696 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 88 274 36 68 137 265), lower := (rows 35 131 100 88 274 36 68 128 256), losses := [] }

theorem u6696 : Upper (D 6) (R 6) [34,129,96,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6697 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 88 274 36 72 133 261), lower := (rows 35 131 100 88 274 36 72 128 256), losses := [] }

theorem u6697 : Upper (D 6) (R 6) [34,129,96,80,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6697 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6698 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 52 96 72 208 336), lower := (rows 35 131 261 14 52 96 72 128 256), losses := [] }

theorem u6698 : Upper (D 6) (R 6) [34,129,257,6,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6698 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6699 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 52 96 80 200 328), lower := (rows 35 131 261 14 52 96 80 128 256), losses := [] }

theorem u6699 : Upper (D 6) (R 6) [34,129,257,6,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6699 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6700 : Route 9 := (fun mask => (mask,id))

def c6700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6700 : Upper (D 6) (R 6) [34,129,257,6,40,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,6,40,64,4] 13 (by decide) (choices 1) [16,64] r6700 c6700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u499
  · exact u500

def b6701 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 56 96 80 196 324), lower := (rows 35 131 261 14 56 96 80 128 256), losses := [] }

theorem u6701 : Upper (D 6) (R 6) [34,129,257,6,40,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6701 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6702 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 261 14 84 96 72 176 304), lower := (rows 35 131 261 14 84 96 72 128 256), losses := [] }

theorem u6702 : Upper (D 6) (R 6) [34,129,257,6,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6702 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6703 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 14 84 96 80 168 296), lower := (rows 35 131 261 14 84 96 80 128 256), losses := [] }

theorem u6703 : Upper (D 6) (R 6) [34,129,257,6,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6703 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6704 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 261 14 84 96 96 152 280), lower := (rows 35 131 261 14 84 96 96 128 256), losses := [] }

theorem u6704 : Upper (D 6) (R 6) [34,129,257,6,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6705 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 3 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 261 14 88 96 68 176 304), lower := (rows 35 131 261 14 88 96 68 128 256), losses := [] }

theorem u6705 : Upper (D 6) (R 6) [34,129,257,6,72,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6706 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 14 88 96 80 164 292), lower := (rows 35 131 261 14 88 96 80 128 256), losses := [] }

theorem u6706 : Upper (D 6) (R 6) [34,129,257,6,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6706 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6707 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 261 14 88 96 96 148 276), lower := (rows 35 131 261 14 88 96 96 128 256), losses := [] }

theorem u6707 : Upper (D 6) (R 6) [34,129,257,6,72,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6708 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 131, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 131 261 26 28 96 68 224 352), lower := (rows 35 131 261 26 28 96 68 128 256), losses := [] }

theorem u6708 : Upper (D 6) (R 6) [34,129,257,18,12,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6709 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 131 261 26 28 96 96 196 324), lower := (rows 35 131 261 26 28 96 96 128 256), losses := [] }

theorem u6709 : Upper (D 6) (R 6) [34,129,257,18,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6710 : Route 9 := (fun mask => (mask,id))

def c6710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6710 : Upper (D 6) (R 6) [34,129,257,18,36,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,36,64,4] 13 (by decide) (choices 1) [8,64] r6710 c6710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u501
  · exact u502

def r6711 : Route 9 := (fun mask => (mask,id))

def c6711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6711 : Upper (D 6) (R 6) [34,129,257,18,36,64,8] 13 := by
  apply FastRouting.sound _ _ [34,129,257,18,36,64,8] 13 (by decide) (choices 1) [4,64] r6711 c6711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u503
  · exact u504

def b6712 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 261 26 84 96 68 168 296), lower := (rows 35 131 261 26 84 96 68 128 256), losses := [] }

theorem u6712 : Upper (D 6) (R 6) [34,129,257,18,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6713 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 261 26 84 96 72 164 292), lower := (rows 35 131 261 26 84 96 72 128 256), losses := [] }

theorem u6713 : Upper (D 6) (R 6) [34,129,257,18,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6713 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6714 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 261 26 84 96 96 140 268), lower := (rows 35 131 261 26 84 96 96 128 256), losses := [] }

theorem u6714 : Upper (D 6) (R 6) [34,129,257,18,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6715 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 261 26 112 36 68 200 328), lower := (rows 35 131 261 26 112 36 68 128 256), losses := [] }

theorem u6715 : Upper (D 6) (R 6) [34,129,257,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6716 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 131 261 26 112 36 72 196 324), lower := (rows 35 131 261 26 112 36 72 128 256), losses := [] }

theorem u6716 : Upper (D 6) (R 6) [34,129,257,18,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6716 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6717 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 131 261 28 56 96 66 196 324), lower := (rows 35 131 261 28 56 96 66 128 256), losses := [] }

theorem u6717 : Upper (D 6) (R 6) [34,129,257,20,40,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6718 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 131 261 28 56 96 68 194 322), lower := (rows 35 131 261 28 56 96 68 128 256), losses := [] }

theorem u6718 : Upper (D 6) (R 6) [34,129,257,20,40,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6719 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(4,0)], upper := (rows 35 131 261 28 82 36 72 224 352), lower := (rows 35 131 261 28 82 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 17 44 108 237 365), good := (rows 498 402 508 508 466 492 488 128 256) }] }

theorem u6719 : Upper (D 6) (R 6) [34,129,257,20,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6719 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6719
end Delivery.IrregularNine14.P06
