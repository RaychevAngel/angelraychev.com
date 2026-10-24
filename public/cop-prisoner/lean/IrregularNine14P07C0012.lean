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

def b720 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 152, targets := 64 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 37 194 324 56 145 34 65 136 258), lower := (rows 37 194 324 56 145 34 65 136 256), losses := [] }

theorem u720 : Upper (D 7) (R 7) [36,192,320,48,129,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b720 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 262, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 259 14 73 146 48 192 160 320), lower := (rows 37 259 14 73 146 48 192 160 256), losses := [] }

theorem u721 : Upper (D 7) (R 7) [36,257,10,65,130,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b721 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 37 259 14 73 146 48 192 192 288), lower := (rows 37 259 14 73 146 48 192 192 256), losses := [] }

theorem u722 : Upper (D 7) (R 7) [36,257,10,65,130,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b722 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 262, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 259 14 73 146 160 80 160 320), lower := (rows 37 259 14 73 146 160 80 160 256), losses := [] }

theorem u723 : Upper (D 7) (R 7) [36,257,10,65,130,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b723 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 37 259 14 73 146 160 80 192 288), lower := (rows 37 259 14 73 146 160 80 192 256), losses := [] }

theorem u724 : Upper (D 7) (R 7) [36,257,10,65,130,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b724 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 326, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 259 70 25 146 160 72 160 320), lower := (rows 37 259 70 25 146 160 72 160 256), losses := [] }

theorem u725 : Upper (D 7) (R 7) [36,257,66,17,130,128,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b725 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 37 259 70 25 146 160 72 192 288), lower := (rows 37 259 70 25 146 160 72 192 256), losses := [] }

theorem u726 : Upper (D 7) (R 7) [36,257,66,17,130,128,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b726 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 37 259 70 42 145 48 192 136 320), lower := (rows 37 259 70 42 145 48 192 136 256), losses := [] }

theorem u727 : Upper (D 7) (R 7) [36,257,66,34,129,16,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b727 [(5,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 259 70 42 145 48 192 192 264), lower := (rows 37 259 70 42 145 48 192 192 256), losses := [] }

theorem u728 : Upper (D 7) (R 7) [36,257,66,34,129,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 322, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 37 259 70 42 145 160 80 136 320), lower := (rows 37 259 70 42 145 160 80 136 256), losses := [] }

theorem u729 : Upper (D 7) (R 7) [36,257,66,34,129,128,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b729 [(6,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 259 70 42 145 160 80 192 264), lower := (rows 37 259 70 42 145 160 80 192 256), losses := [] }

theorem u730 : Upper (D 7) (R 7) [36,257,66,34,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b730 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 259 70 42 152 160 80 129 320), lower := (rows 37 259 70 42 152 160 80 129 256), losses := [] }

theorem u731 : Upper (D 7) (R 7) [36,257,66,34,136,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b731 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 259 70 42 152 160 80 192 257), lower := (rows 37 259 70 42 152 160 80 192 256), losses := [] }

theorem u732 : Upper (D 7) (R 7) [36,257,66,34,136,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b732 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 37 259 76 137 176 34 66 144 320), lower := (rows 37 259 76 137 176 34 66 144 256), losses := [] }

theorem u733 : Upper (D 7) (R 7) [36,257,72,129,160,2,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b733 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,6)], upper := (rows 37 259 76 137 176 34 66 192 272), lower := (rows 37 259 76 137 176 34 66 192 256), losses := [] }

theorem u734 : Upper (D 7) (R 7) [36,257,72,129,160,2,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 37 259 76 137 208 34 66 144 288), lower := (rows 37 259 76 137 208 34 66 144 256), losses := [] }

theorem u735 : Upper (D 7) (R 7) [36,257,72,129,192,2,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b735 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 342, targets := 32 },{ cop := 0, region := 136, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 76 137 208 34 66 160 272), lower := (rows 37 259 76 137 208 34 66 160 256), losses := [] }

theorem u736 : Upper (D 7) (R 7) [36,257,72,129,192,2,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 104, targets := 129 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,7)], upper := (rows 37 259 196 74 152 34 96 129 272), lower := (rows 37 259 196 74 152 34 96 129 256), losses := [] }

theorem u737 : Upper (D 7) (R 7) [36,257,192,66,136,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 148, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 259 196 74 152 34 96 144 257), lower := (rows 37 259 196 74 152 34 96 144 256), losses := [] }

theorem u738 : Upper (D 7) (R 7) [36,257,192,66,136,2,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b738 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 1, region := 176, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 259 196 88 176 34 65 130 264), lower := (rows 37 259 196 88 176 34 65 130 256), losses := [] }

theorem u739 : Upper (D 7) (R 7) [36,257,192,80,160,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 221, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 259 196 88 176 34 65 136 258), lower := (rows 37 259 196 88 176 34 65 136 256), losses := [] }

theorem u740 : Upper (D 7) (R 7) [36,257,192,80,160,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b740 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 266 22 42 81 160 192 129 320), lower := (rows 37 266 22 42 81 160 192 129 256), losses := [] }

theorem u741 : Upper (D 7) (R 7) [36,264,18,34,65,128,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 37 266 22 42 81 160 192 192 257), lower := (rows 37 266 22 42 81 160 192 192 256), losses := [] }

theorem u742 : Upper (D 7) (R 7) [36,264,18,34,65,128,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 266 70 11 145 160 80 160 320), lower := (rows 37 266 70 11 145 160 80 160 256), losses := [] }

theorem u743 : Upper (D 7) (R 7) [36,264,66,3,129,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b743 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6)], upper := (rows 37 266 70 11 145 160 80 192 288), lower := (rows 37 266 70 11 145 160 80 192 256), losses := [] }

theorem u744 : Upper (D 7) (R 7) [36,264,66,3,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b744 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 266 70 138 112 160 65 129 272), lower := (rows 37 266 70 138 112 160 65 129 256), losses := [] }

theorem u745 : Upper (D 7) (R 7) [36,264,66,130,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 184, targets := 1 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 37 266 70 138 112 160 65 144 257), lower := (rows 37 266 70 138 112 160 65 144 256), losses := [] }

theorem u746 : Upper (D 7) (R 7) [36,264,66,130,96,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b746 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 266 70 138 145 48 65 160 320), lower := (rows 37 266 70 138 145 48 65 160 256), losses := [] }

theorem u747 : Upper (D 7) (R 7) [36,264,66,130,129,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 266 70 138 145 48 65 192 288), lower := (rows 37 266 70 138 145 48 65 192 256), losses := [] }

theorem u748 : Upper (D 7) (R 7) [36,264,66,130,129,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b748 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 266 70 138 145 48 96 129 320), lower := (rows 37 266 70 138 145 48 96 129 256), losses := [] }

theorem u749 : Upper (D 7) (R 7) [36,264,66,130,129,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b749 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 33 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(3,0),(3,5)], upper := (rows 37 266 70 138 145 48 96 192 257), lower := (rows 37 266 70 138 145 48 96 192 256), losses := [] }

theorem u750 : Upper (D 7) (R 7) [36,264,66,130,129,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 3, region := 258, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,1)], upper := (rows 37 266 70 152 112 160 65 129 258), lower := (rows 37 266 70 152 112 160 65 129 256), losses := [] }

theorem u751 : Upper (D 7) (R 7) [36,264,66,144,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 37 266 70 152 112 160 65 130 257), lower := (rows 37 266 70 152 112 160 65 130 256), losses := [] }

theorem u752 : Upper (D 7) (R 7) [36,264,66,144,96,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 204, targets := 32 }], pairs := [(0,1),(2,1),(2,5),(3,5)], upper := (rows 37 266 84 74 19 160 192 129 288), lower := (rows 37 266 84 74 19 160 192 129 256), losses := [] }

theorem u753 : Upper (D 7) (R 7) [36,264,80,66,3,128,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(3,0)], upper := (rows 37 266 84 74 19 160 192 160 257), lower := (rows 37 266 84 74 19 160 192 160 256), losses := [] }

theorem u754 : Upper (D 7) (R 7) [36,264,80,66,3,128,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 37 266 196 88 146 34 65 129 288), lower := (rows 37 266 196 88 146 34 65 129 256), losses := [] }

theorem u755 : Upper (D 7) (R 7) [36,264,192,80,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 176, targets := 65 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,6)], upper := (rows 37 266 196 88 146 34 65 160 257), lower := (rows 37 266 196 88 146 34 65 160 256), losses := [] }

theorem u756 : Upper (D 7) (R 7) [36,264,192,80,130,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 221, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 266 196 88 176 34 65 129 258), lower := (rows 37 266 196 88 176 34 65 129 256), losses := [] }

theorem u757 : Upper (D 7) (R 7) [36,264,192,80,160,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 1, region := 176, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 266 196 88 176 34 65 130 257), lower := (rows 37 266 196 88 176 34 65 130 256), losses := [] }

theorem u758 : Upper (D 7) (R 7) [36,264,192,80,160,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 266 196 104 146 34 65 129 272), lower := (rows 37 266 196 104 146 34 65 129 256), losses := [] }

theorem u759 : Upper (D 7) (R 7) [36,264,192,96,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 104 146 34 65 144 257), lower := (rows 37 266 196 104 146 34 65 144 256), losses := [] }

theorem u760 : Upper (D 7) (R 7) [36,264,192,96,130,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b760 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 290 13 74 146 48 192 129 320), lower := (rows 37 290 13 74 146 48 192 129 256), losses := [] }

theorem u761 : Upper (D 7) (R 7) [36,288,9,66,130,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b761 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 290 13 74 146 48 192 192 257), lower := (rows 37 290 13 74 146 48 192 192 256), losses := [] }

theorem u762 : Upper (D 7) (R 7) [36,288,9,66,130,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b762 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 290 14 88 146 160 65 129 320), lower := (rows 37 290 14 88 146 160 65 129 256), losses := [] }

theorem u763 : Upper (D 7) (R 7) [36,288,10,80,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 258, targets := 64 },{ cop := 0, region := 258, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,6),(1,7),(4,0)], upper := (rows 37 290 14 88 146 160 65 192 257), lower := (rows 37 290 14 88 146 160 65 192 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 252 64 200 256), good := (rows 52 290 190 248 178 160 224 224 256) }] }

theorem u764 : Upper (D 7) (R 7) [36,288,10,80,130,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 290 70 25 146 40 192 129 320), lower := (rows 37 290 70 25 146 40 192 129 256), losses := [] }

theorem u765 : Upper (D 7) (R 7) [36,288,66,17,130,8,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b765 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 290 70 25 146 40 192 192 257), lower := (rows 37 290 70 25 146 40 192 192 256), losses := [] }

theorem u766 : Upper (D 7) (R 7) [36,288,66,17,130,8,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b766 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 290 70 25 146 160 72 129 320), lower := (rows 37 290 70 25 146 160 72 129 256), losses := [] }

theorem u767 : Upper (D 7) (R 7) [36,288,66,17,130,128,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b767 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 258, targets := 192 },{ cop := 2, region := 144, targets := 1 }], pairs := [(1,6),(1,7),(4,0)], upper := (rows 37 290 70 25 146 160 72 192 257), lower := (rows 37 290 70 25 146 160 72 192 256), losses := [] }

theorem u768 : Upper (D 7) (R 7) [36,288,66,17,130,128,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b768 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 136, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 290 76 137 146 48 66 129 320), lower := (rows 37 290 76 137 146 48 66 129 256), losses := [] }

theorem u769 : Upper (D 7) (R 7) [36,288,72,129,130,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b769 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 306, targets := 64 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 37 290 76 137 146 48 66 192 257), lower := (rows 37 290 76 137 146 48 66 192 256), losses := [] }

theorem u770 : Upper (D 7) (R 7) [36,288,72,129,130,16,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b770 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 290 196 74 146 40 65 129 272), lower := (rows 37 290 196 74 146 40 65 129 256), losses := [] }

theorem u771 : Upper (D 7) (R 7) [36,288,192,66,130,8,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b771 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 37 290 196 74 146 40 65 144 257), lower := (rows 37 290 196 74 146 40 65 144 256), losses := [] }

theorem u772 : Upper (D 7) (R 7) [36,288,192,66,130,8,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b772 [(5,3),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 290 196 74 152 34 65 129 272), lower := (rows 37 290 196 74 152 34 65 129 256), losses := [] }

theorem u773 : Upper (D 7) (R 7) [36,288,192,66,136,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 148, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 290 196 74 152 34 65 144 257), lower := (rows 37 290 196 74 152 34 65 144 256), losses := [] }

theorem u774 : Upper (D 7) (R 7) [36,288,192,66,136,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b774 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 216, targets := 32 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 37 322 7 73 152 48 192 130 288), lower := (rows 37 322 7 73 152 48 192 130 256), losses := [] }

theorem u775 : Upper (D 7) (R 7) [36,320,3,65,136,16,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 262, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 322 7 73 152 48 192 160 258), lower := (rows 37 322 7 73 152 48 192 160 256), losses := [] }

theorem u776 : Upper (D 7) (R 7) [36,320,3,65,136,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b776 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 221, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 322 13 152 112 34 192 129 258), lower := (rows 37 322 13 152 112 34 192 129 256), losses := [] }

theorem u777 : Upper (D 7) (R 7) [36,320,9,144,96,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,0)], upper := (rows 37 322 13 152 112 34 192 130 257), lower := (rows 37 322 13 152 112 34 192 130 256), losses := [] }

theorem u778 : Upper (D 7) (R 7) [36,320,9,144,96,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 7, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 322 13 200 146 34 96 129 272), lower := (rows 37 322 13 200 146 34 96 129 256), losses := [] }

theorem u779 : Upper (D 7) (R 7) [36,320,9,192,130,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P07
