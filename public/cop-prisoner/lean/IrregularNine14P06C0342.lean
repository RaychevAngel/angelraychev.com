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

def b20520 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 88 273 34 101 165 293), lower := (rows 35 70 140 88 273 34 64 128 256), losses := [] }

theorem u20520 : Upper (D 6) (R 6) [34,68,136,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20521 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 88 273 36 99 163 291), lower := (rows 35 70 140 88 273 36 64 128 256), losses := [] }

theorem u20521 : Upper (D 6) (R 6) [34,68,136,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20522 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 88 304 33 71 135 263), lower := (rows 35 70 140 88 304 33 64 128 256), losses := [] }

theorem u20522 : Upper (D 6) (R 6) [34,68,136,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20523 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 88 304 34 69 133 261), lower := (rows 35 70 140 88 304 34 64 128 256), losses := [] }

theorem u20523 : Upper (D 6) (R 6) [34,68,136,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20524 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 88 304 36 67 131 259), lower := (rows 35 70 140 88 304 36 64 128 256), losses := [] }

theorem u20524 : Upper (D 6) (R 6) [34,68,136,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20525 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 104 273 33 86 150 278), lower := (rows 35 70 140 104 273 33 64 128 256), losses := [] }

theorem u20525 : Upper (D 6) (R 6) [34,68,136,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20526 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 104 273 34 85 149 277), lower := (rows 35 70 140 104 273 34 64 128 256), losses := [] }

theorem u20526 : Upper (D 6) (R 6) [34,68,136,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20527 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 104 273 36 83 147 275), lower := (rows 35 70 140 104 273 36 64 128 256), losses := [] }

theorem u20527 : Upper (D 6) (R 6) [34,68,136,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20528 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 273 48 71 135 263), lower := (rows 35 70 140 104 273 48 64 128 256), losses := [] }

theorem u20528 : Upper (D 6) (R 6) [34,68,136,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20528 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20529 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 104 274 33 85 149 277), lower := (rows 35 70 140 104 274 33 64 128 256), losses := [] }

theorem u20529 : Upper (D 6) (R 6) [34,68,136,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20530 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 104 274 36 81 145 273), lower := (rows 35 70 140 104 274 36 64 128 256), losses := [] }

theorem u20530 : Upper (D 6) (R 6) [34,68,136,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20531 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 104 274 48 69 133 261), lower := (rows 35 70 140 104 274 48 64 128 256), losses := [] }

theorem u20531 : Upper (D 6) (R 6) [34,68,136,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20531 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20532 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 104 276 33 83 147 275), lower := (rows 35 70 140 104 276 33 64 128 256), losses := [] }

theorem u20532 : Upper (D 6) (R 6) [34,68,136,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20533 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 104 276 34 81 145 273), lower := (rows 35 70 140 104 276 34 64 128 256), losses := [] }

theorem u20533 : Upper (D 6) (R 6) [34,68,136,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20534 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 104 276 48 67 131 259), lower := (rows 35 70 140 104 276 48 64 128 256), losses := [] }

theorem u20534 : Upper (D 6) (R 6) [34,68,136,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20534 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20535 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 21 34 112 240 368), lower := (rows 35 70 140 265 21 34 64 128 256), losses := [] }

theorem u20535 : Upper (D 6) (R 6) [34,68,136,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20536 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 265 21 48 98 226 354), lower := (rows 35 70 140 265 21 48 64 128 256), losses := [] }

theorem u20536 : Upper (D 6) (R 6) [34,68,136,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20536 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20537 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 21 96 114 178 306), lower := (rows 35 70 140 265 21 96 64 128 256), losses := [] }

theorem u20537 : Upper (D 6) (R 6) [34,68,136,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20538 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 140 265 52 33 82 210 338), lower := (rows 35 70 140 265 52 33 64 128 256), losses := [] }

theorem u20538 : Upper (D 6) (R 6) [34,68,136,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20539 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 52 34 81 209 337), lower := (rows 35 70 140 265 52 34 64 128 256), losses := [] }

theorem u20539 : Upper (D 6) (R 6) [34,68,136,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20540 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 265 52 48 67 195 323), lower := (rows 35 70 140 265 52 48 64 128 256), losses := [] }

theorem u20540 : Upper (D 6) (R 6) [34,68,136,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20540 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20541 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 52 96 83 147 275), lower := (rows 35 70 140 265 52 96 64 128 256), losses := [] }

theorem u20541 : Upper (D 6) (R 6) [34,68,136,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20542 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 81 34 116 180 308), lower := (rows 35 70 140 265 81 34 64 128 256), losses := [] }

theorem u20542 : Upper (D 6) (R 6) [34,68,136,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20543 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 265 81 36 114 178 306), lower := (rows 35 70 140 265 81 36 64 128 256), losses := [] }

theorem u20543 : Upper (D 6) (R 6) [34,68,136,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20544 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 265 81 48 102 166 294), lower := (rows 35 70 140 265 81 48 64 128 256), losses := [] }

theorem u20544 : Upper (D 6) (R 6) [34,68,136,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20544 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20545 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 265 112 33 86 150 278), lower := (rows 35 70 140 265 112 33 64 128 256), losses := [] }

theorem u20545 : Upper (D 6) (R 6) [34,68,136,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20546 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 112 34 85 149 277), lower := (rows 35 70 140 265 112 34 64 128 256), losses := [] }

theorem u20546 : Upper (D 6) (R 6) [34,68,136,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20547 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 70 140 265 112 36 83 147 275), lower := (rows 35 70 140 265 112 36 64 128 256), losses := [] }

theorem u20547 : Upper (D 6) (R 6) [34,68,136,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20548 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 265 112 48 71 135 263), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u20548 : Upper (D 6) (R 6) [34,68,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20548 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20549 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 266 21 33 112 240 368), lower := (rows 35 70 140 266 21 33 64 128 256), losses := [] }

theorem u20549 : Upper (D 6) (R 6) [34,68,136,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20550 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 70 140 266 21 48 97 225 353), lower := (rows 35 70 140 266 21 48 64 128 256), losses := [] }

theorem u20550 : Upper (D 6) (R 6) [34,68,136,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20550 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20551 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 266 21 96 113 177 305), lower := (rows 35 70 140 266 21 96 64 128 256), losses := [] }

theorem u20551 : Upper (D 6) (R 6) [34,68,136,258,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20552 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 266 52 33 81 209 337), lower := (rows 35 70 140 266 52 33 64 128 256), losses := [] }

theorem u20552 : Upper (D 6) (R 6) [34,68,136,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20553 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 266 52 48 65 193 321), lower := (rows 35 70 140 266 52 48 64 128 256), losses := [] }

theorem u20553 : Upper (D 6) (R 6) [34,68,136,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20553 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20554 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 266 52 96 81 145 273), lower := (rows 35 70 140 266 52 96 64 128 256), losses := [] }

theorem u20554 : Upper (D 6) (R 6) [34,68,136,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20555 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 266 81 33 116 180 308), lower := (rows 35 70 140 266 81 33 64 128 256), losses := [] }

theorem u20555 : Upper (D 6) (R 6) [34,68,136,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20556 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 70 140 266 81 36 113 177 305), lower := (rows 35 70 140 266 81 36 64 128 256), losses := [] }

theorem u20556 : Upper (D 6) (R 6) [34,68,136,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20557 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 266 81 48 101 165 293), lower := (rows 35 70 140 266 81 48 64 128 256), losses := [] }

theorem u20557 : Upper (D 6) (R 6) [34,68,136,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20557 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20558 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 266 112 33 85 149 277), lower := (rows 35 70 140 266 112 33 64 128 256), losses := [] }

theorem u20558 : Upper (D 6) (R 6) [34,68,136,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20559 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 70 140 266 112 36 81 145 273), lower := (rows 35 70 140 266 112 36 64 128 256), losses := [] }

theorem u20559 : Upper (D 6) (R 6) [34,68,136,258,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20560 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 266 112 48 69 133 261), lower := (rows 35 70 140 266 112 48 64 128 256), losses := [] }

theorem u20560 : Upper (D 6) (R 6) [34,68,136,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20560 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20561 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 268 81 33 114 178 306), lower := (rows 35 70 140 268 81 33 64 128 256), losses := [] }

theorem u20561 : Upper (D 6) (R 6) [34,68,136,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20562 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 268 81 34 113 177 305), lower := (rows 35 70 140 268 81 34 64 128 256), losses := [] }

theorem u20562 : Upper (D 6) (R 6) [34,68,136,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20563 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 268 81 48 99 163 291), lower := (rows 35 70 140 268 81 48 64 128 256), losses := [] }

theorem u20563 : Upper (D 6) (R 6) [34,68,136,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20563 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20564 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 268 112 33 83 147 275), lower := (rows 35 70 140 268 112 33 64 128 256), losses := [] }

theorem u20564 : Upper (D 6) (R 6) [34,68,136,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20565 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 268 112 34 81 145 273), lower := (rows 35 70 140 268 112 34 64 128 256), losses := [] }

theorem u20565 : Upper (D 6) (R 6) [34,68,136,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20566 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 268 112 48 67 131 259), lower := (rows 35 70 140 268 112 48 64 128 256), losses := [] }

theorem u20566 : Upper (D 6) (R 6) [34,68,136,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20566 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20567 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 280 21 33 98 226 354), lower := (rows 35 70 140 280 21 33 64 128 256), losses := [] }

theorem u20567 : Upper (D 6) (R 6) [34,68,136,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20568 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 21 34 97 225 353), lower := (rows 35 70 140 280 21 34 64 128 256), losses := [] }

theorem u20568 : Upper (D 6) (R 6) [34,68,136,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20569 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 21 96 99 163 291), lower := (rows 35 70 140 280 21 96 64 128 256), losses := [] }

theorem u20569 : Upper (D 6) (R 6) [34,68,136,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20570 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 70 140 280 52 33 67 195 323), lower := (rows 35 70 140 280 52 33 64 128 256), losses := [] }

theorem u20570 : Upper (D 6) (R 6) [34,68,136,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20571 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 52 34 65 193 321), lower := (rows 35 70 140 280 52 34 64 128 256), losses := [] }

theorem u20571 : Upper (D 6) (R 6) [34,68,136,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20572 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 52 96 67 131 259), lower := (rows 35 70 140 280 52 96 64 128 256), losses := [] }

theorem u20572 : Upper (D 6) (R 6) [34,68,136,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20573 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 280 81 33 102 166 294), lower := (rows 35 70 140 280 81 33 64 128 256), losses := [] }

theorem u20573 : Upper (D 6) (R 6) [34,68,136,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20574 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 81 34 101 165 293), lower := (rows 35 70 140 280 81 34 64 128 256), losses := [] }

theorem u20574 : Upper (D 6) (R 6) [34,68,136,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20575 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 280 81 36 99 163 291), lower := (rows 35 70 140 280 81 36 64 128 256), losses := [] }

theorem u20575 : Upper (D 6) (R 6) [34,68,136,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20576 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 280 112 33 71 135 263), lower := (rows 35 70 140 280 112 33 64 128 256), losses := [] }

theorem u20576 : Upper (D 6) (R 6) [34,68,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20577 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 112 34 69 133 261), lower := (rows 35 70 140 280 112 34 64 128 256), losses := [] }

theorem u20577 : Upper (D 6) (R 6) [34,68,136,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20578 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 70 140 280 112 36 67 131 259), lower := (rows 35 70 140 280 112 36 64 128 256), losses := [] }

theorem u20578 : Upper (D 6) (R 6) [34,68,136,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20579 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 140 296 21 33 82 210 338), lower := (rows 35 70 140 296 21 33 64 128 256), losses := [] }

theorem u20579 : Upper (D 6) (R 6) [34,68,136,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20579
end Delivery.IrregularNine14.P06
