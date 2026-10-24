import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 138 176 96 89 153 281), lower := (rows 289 38 69 138 176 96 64 128 256), losses := [] }

theorem u6540 : Upper (D 8) (R 8) [288,36,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 138 208 33 120 184 312), lower := (rows 289 38 69 138 208 33 64 128 256), losses := [] }

theorem u6541 : Upper (D 8) (R 8) [288,36,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 38 69 138 208 40 113 177 305), lower := (rows 289 38 69 138 208 40 64 128 256), losses := [] }

theorem u6542 : Upper (D 8) (R 8) [288,36,65,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6542 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 289 38 69 138 208 48 105 169 297), lower := (rows 289 38 69 138 208 48 64 128 256), losses := [] }

theorem u6543 : Upper (D 8) (R 8) [288,36,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6543 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 168 208 33 90 154 282), lower := (rows 289 38 69 168 208 33 64 128 256), losses := [] }

theorem u6544 : Upper (D 8) (R 8) [288,36,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 38 69 168 208 34 89 153 281), lower := (rows 289 38 69 168 208 34 64 128 256), losses := [] }

theorem u6545 : Upper (D 8) (R 8) [288,36,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6545 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 38 69 168 208 40 83 147 275), lower := (rows 289 38 69 168 208 40 64 128 256), losses := [] }

theorem u6546 : Upper (D 8) (R 8) [288,36,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6546 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6547 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 38 69 168 208 48 75 139 267), lower := (rows 289 38 69 168 208 48 64 128 256), losses := [] }

theorem u6547 : Upper (D 8) (R 8) [288,36,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6547 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6548 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 56 152 33 193 193 449), lower := (rows 289 38 70 56 152 33 64 128 256), losses := [] }

theorem u6548 : Upper (D 8) (R 8) [288,36,66,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6549 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 70 56 152 96 193 129 385), lower := (rows 289 38 70 56 152 96 64 128 256), losses := [] }

theorem u6549 : Upper (D 8) (R 8) [288,36,66,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6550 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 137 176 33 88 216 344), lower := (rows 289 38 70 137 176 33 64 128 256), losses := [] }

theorem u6550 : Upper (D 8) (R 8) [288,36,66,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6551 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 38 70 137 176 40 81 209 337), lower := (rows 289 38 70 137 176 40 64 128 256), losses := [] }

theorem u6551 : Upper (D 8) (R 8) [288,36,66,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6551 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6552 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 289 38 70 137 176 48 73 201 329), lower := (rows 289 38 70 137 176 48 64 128 256), losses := [] }

theorem u6552 : Upper (D 8) (R 8) [288,36,66,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6552 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6553 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 70 137 176 96 89 153 281), lower := (rows 289 38 70 137 176 96 64 128 256), losses := [] }

theorem u6553 : Upper (D 8) (R 8) [288,36,66,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 56 146 33 193 193 449), lower := (rows 289 38 76 56 146 33 64 128 256), losses := [] }

theorem u6554 : Upper (D 8) (R 8) [288,36,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6555 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 56 146 96 193 129 385), lower := (rows 289 38 76 56 146 96 64 128 256), losses := [] }

theorem u6555 : Upper (D 8) (R 8) [288,36,72,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 38 76 137 81 34 240 176 432), lower := (rows 289 38 76 137 81 34 64 128 256), losses := [] }

theorem u6556 : Upper (D 8) (R 8) [288,36,72,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6556 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6557 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 38 76 137 81 48 226 162 418), lower := (rows 289 38 76 137 81 48 64 128 256), losses := [] }

theorem u6557 : Upper (D 8) (R 8) [288,36,72,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6557 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6558 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 137 81 160 114 178 306), lower := (rows 289 38 76 137 81 160 64 128 256), losses := [] }

theorem u6558 : Upper (D 8) (R 8) [288,36,72,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6559 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 112 33 210 146 402), lower := (rows 289 38 76 137 112 33 64 128 256), losses := [] }

theorem u6559 : Upper (D 8) (R 8) [288,36,72,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6560 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 38 76 137 112 34 209 145 401), lower := (rows 289 38 76 137 112 34 64 128 256), losses := [] }

theorem u6560 : Upper (D 8) (R 8) [288,36,72,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6560 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6561 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 76 137 112 48 195 131 387), lower := (rows 289 38 76 137 112 48 64 128 256), losses := [] }

theorem u6561 : Upper (D 8) (R 8) [288,36,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6561 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6562 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 137 112 160 83 147 275), lower := (rows 289 38 76 137 112 160 64 128 256), losses := [] }

theorem u6562 : Upper (D 8) (R 8) [288,36,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6563 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 176 33 82 210 338), lower := (rows 289 38 76 137 176 33 64 128 256), losses := [] }

theorem u6563 : Upper (D 8) (R 8) [288,36,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6564 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 38 76 137 176 34 81 209 337), lower := (rows 289 38 76 137 176 34 64 128 256), losses := [] }

theorem u6564 : Upper (D 8) (R 8) [288,36,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6564 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6565 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 289 38 76 137 176 48 67 195 323), lower := (rows 289 38 76 137 176 48 64 128 256), losses := [] }

theorem u6565 : Upper (D 8) (R 8) [288,36,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6565 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6566 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 176 96 83 147 275), lower := (rows 289 38 76 137 176 96 64 128 256), losses := [] }

theorem u6566 : Upper (D 8) (R 8) [288,36,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6567 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 208 33 114 178 306), lower := (rows 289 38 76 137 208 33 64 128 256), losses := [] }

theorem u6567 : Upper (D 8) (R 8) [288,36,72,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 38 76 137 208 34 113 177 305), lower := (rows 289 38 76 137 208 34 64 128 256), losses := [] }

theorem u6568 : Upper (D 8) (R 8) [288,36,72,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6568 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6569 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 38 76 137 208 48 99 163 291), lower := (rows 289 38 76 137 208 48 64 128 256), losses := [] }

theorem u6569 : Upper (D 8) (R 8) [288,36,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6569 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6570 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 168 81 33 210 146 402), lower := (rows 289 38 76 168 81 33 64 128 256), losses := [] }

theorem u6570 : Upper (D 8) (R 8) [288,36,72,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6571 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 38 76 168 81 34 209 145 401), lower := (rows 289 38 76 168 81 34 64 128 256), losses := [] }

theorem u6571 : Upper (D 8) (R 8) [288,36,72,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6571 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6572 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 76 168 81 48 195 131 387), lower := (rows 289 38 76 168 81 48 64 128 256), losses := [] }

theorem u6572 : Upper (D 8) (R 8) [288,36,72,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6572 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6573 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 168 81 160 83 147 275), lower := (rows 289 38 76 168 81 160 64 128 256), losses := [] }

theorem u6573 : Upper (D 8) (R 8) [288,36,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6574 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 168 145 33 82 210 338), lower := (rows 289 38 76 168 145 33 64 128 256), losses := [] }

theorem u6574 : Upper (D 8) (R 8) [288,36,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6575 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 38 76 168 145 34 81 209 337), lower := (rows 289 38 76 168 145 34 64 128 256), losses := [] }

theorem u6575 : Upper (D 8) (R 8) [288,36,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6575 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6576 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 289 38 76 168 145 48 67 195 323), lower := (rows 289 38 76 168 145 48 64 128 256), losses := [] }

theorem u6576 : Upper (D 8) (R 8) [288,36,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6576 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6577 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 168 145 96 83 147 275), lower := (rows 289 38 76 168 145 96 64 128 256), losses := [] }

theorem u6577 : Upper (D 8) (R 8) [288,36,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6578 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 168 208 33 83 147 275), lower := (rows 289 38 76 168 208 33 64 128 256), losses := [] }

theorem u6578 : Upper (D 8) (R 8) [288,36,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6579 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 76 168 208 34 81 145 273), lower := (rows 289 38 76 168 208 34 64 128 256), losses := [] }

theorem u6579 : Upper (D 8) (R 8) [288,36,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6579 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6580 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 76 168 208 48 67 131 259), lower := (rows 289 38 76 168 208 48 64 128 256), losses := [] }

theorem u6580 : Upper (D 8) (R 8) [288,36,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6580 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6581 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 289 38 196 73 145 34 120 184 312), lower := (rows 289 38 196 73 145 34 64 128 256), losses := [] }

theorem u6581 : Upper (D 8) (R 8) [288,36,192,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6581 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 38 196 73 145 40 114 178 306), lower := (rows 289 38 196 73 145 40 64 128 256), losses := [] }

theorem u6582 : Upper (D 8) (R 8) [288,36,192,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6582 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 73 152 33 114 178 306), lower := (rows 289 38 196 73 152 33 64 128 256), losses := [] }

theorem u6583 : Upper (D 8) (R 8) [288,36,192,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6584 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 38 196 73 152 34 113 177 305), lower := (rows 289 38 196 73 152 34 64 128 256), losses := [] }

theorem u6584 : Upper (D 8) (R 8) [288,36,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6584 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6585 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 38 196 73 152 48 99 163 291), lower := (rows 289 38 196 73 152 48 64 128 256), losses := [] }

theorem u6585 : Upper (D 8) (R 8) [288,36,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6585 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6586 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 73 176 33 90 154 282), lower := (rows 289 38 196 73 176 33 64 128 256), losses := [] }

theorem u6586 : Upper (D 8) (R 8) [288,36,192,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6587 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 38 196 73 176 34 89 153 281), lower := (rows 289 38 196 73 176 34 64 128 256), losses := [] }

theorem u6587 : Upper (D 8) (R 8) [288,36,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6587 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6588 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 38 196 73 176 40 83 147 275), lower := (rows 289 38 196 73 176 40 64 128 256), losses := [] }

theorem u6588 : Upper (D 8) (R 8) [288,36,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6588 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6589 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 38 196 73 176 48 75 139 267), lower := (rows 289 38 196 73 176 48 64 128 256), losses := [] }

theorem u6589 : Upper (D 8) (R 8) [288,36,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6589 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6590 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 88 176 33 75 139 267), lower := (rows 289 38 196 88 176 33 64 128 256), losses := [] }

theorem u6590 : Upper (D 8) (R 8) [288,36,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6591 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 38 196 88 176 34 73 137 265), lower := (rows 289 38 196 88 176 34 64 128 256), losses := [] }

theorem u6591 : Upper (D 8) (R 8) [288,36,192,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6591 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6592 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 196 88 176 40 67 131 259), lower := (rows 289 38 196 88 176 40 64 128 256), losses := [] }

theorem u6592 : Upper (D 8) (R 8) [288,36,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6592 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6593 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 67 76 137 146 36 112 176 304), lower := (rows 289 67 76 137 146 36 64 128 256), losses := [] }

theorem u6593 : Upper (D 8) (R 8) [288,65,72,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6593 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6594 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 289 67 76 137 176 34 116 180 308), lower := (rows 289 67 76 137 176 34 64 128 256), losses := [] }

theorem u6594 : Upper (D 8) (R 8) [288,65,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6594 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6595 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 67 76 137 176 36 114 178 306), lower := (rows 289 67 76 137 176 36 64 128 256), losses := [] }

theorem u6595 : Upper (D 8) (R 8) [288,65,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6595 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6596 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 289 67 76 137 176 48 102 166 294), lower := (rows 289 67 76 137 176 48 64 128 256), losses := [] }

theorem u6596 : Upper (D 8) (R 8) [288,65,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6596 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6597 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 289 67 76 168 145 34 116 180 308), lower := (rows 289 67 76 168 145 34 64 128 256), losses := [] }

theorem u6597 : Upper (D 8) (R 8) [288,65,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6597 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6598 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 67 76 168 145 36 114 178 306), lower := (rows 289 67 76 168 145 36 64 128 256), losses := [] }

theorem u6598 : Upper (D 8) (R 8) [288,65,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6598 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6599 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 289 67 76 168 145 48 102 166 294), lower := (rows 289 67 76 168 145 48 64 128 256), losses := [] }

theorem u6599 : Upper (D 8) (R 8) [288,65,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6599 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P08
