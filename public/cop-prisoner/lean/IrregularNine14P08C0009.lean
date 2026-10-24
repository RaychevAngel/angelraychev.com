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

def b540 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 67 290 13 56 148 96 96 129 385), lower := (rows 67 290 13 56 148 96 96 128 256), losses := [] }

theorem u540 : Upper (D 8) (R 8) [66,288,9,48,132,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 259, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 56 148 96 192 161 289), lower := (rows 67 290 13 56 148 96 192 128 256), losses := [] }

theorem u541 : Upper (D 8) (R 8) [66,288,9,48,132,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 290 13 168 208 33 68 176 304), lower := (rows 67 290 13 168 208 33 68 128 256), losses := [] }

theorem u542 : Upper (D 8) (R 8) [66,288,9,160,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b542 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 290 13 168 208 33 80 164 292), lower := (rows 67 290 13 168 208 33 80 128 256), losses := [] }

theorem u543 : Upper (D 8) (R 8) [66,288,9,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b543 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 13 168 208 33 96 148 276), lower := (rows 67 290 13 168 208 33 96 128 256), losses := [] }

theorem u544 : Upper (D 8) (R 8) [66,288,9,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 112 160 65 132 388), lower := (rows 67 290 28 41 112 160 65 128 256), losses := [] }

theorem u545 : Upper (D 8) (R 8) [66,288,24,33,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 28 41 112 160 68 129 385), lower := (rows 67 290 28 41 112 160 68 128 256), losses := [] }

theorem u546 : Upper (D 8) (R 8) [66,288,24,33,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b546 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 112 160 192 133 261), lower := (rows 67 290 28 41 112 160 192 128 256), losses := [] }

theorem u547 : Upper (D 8) (R 8) [66,288,24,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 208 160 65 164 292), lower := (rows 67 290 28 41 208 160 65 128 256), losses := [] }

theorem u548 : Upper (D 8) (R 8) [66,288,24,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 290 28 41 208 160 68 161 289), lower := (rows 67 290 28 41 208 160 68 128 256), losses := [] }

theorem u549 : Upper (D 8) (R 8) [66,288,24,33,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b549 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 41 208 160 96 133 261), lower := (rows 67 290 28 41 208 160 96 128 256), losses := [] }

theorem u550 : Upper (D 8) (R 8) [66,288,24,33,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 104 145 160 65 164 292), lower := (rows 67 290 28 104 145 160 65 128 256), losses := [] }

theorem u551 : Upper (D 8) (R 8) [66,288,24,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 290 28 104 145 160 68 161 289), lower := (rows 67 290 28 104 145 160 68 128 256), losses := [] }

theorem u552 : Upper (D 8) (R 8) [66,288,24,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b552 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 28 104 145 160 96 133 261), lower := (rows 67 290 28 104 145 160 96 128 256), losses := [] }

theorem u553 : Upper (D 8) (R 8) [66,288,24,96,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 56 84 160 65 136 392), lower := (rows 67 290 37 56 84 160 65 128 256), losses := [] }

theorem u554 : Upper (D 8) (R 8) [66,288,33,48,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 37 56 84 160 72 129 385), lower := (rows 67 290 37 56 84 160 72 128 256), losses := [] }

theorem u555 : Upper (D 8) (R 8) [66,288,33,48,68,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b555 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 9, camps := [], pairs := [(3,0)], upper := (rows 67 290 37 56 84 160 192 137 265), lower := (rows 67 290 37 56 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 224 224 128 256), good := (rows 98 354 124 120 124 224 224 224 256) }] }

theorem u556 : Upper (D 8) (R 8) [66,288,33,48,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 37 76 152 160 65 176 304), lower := (rows 67 290 37 76 152 160 65 128 256), losses := [] }

theorem u557 : Upper (D 8) (R 8) [66,288,33,68,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 290 37 76 152 160 80 161 289), lower := (rows 67 290 37 76 152 160 80 128 256), losses := [] }

theorem u558 : Upper (D 8) (R 8) [66,288,33,68,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b558 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 76 152 160 96 145 273), lower := (rows 67 290 37 76 152 160 96 128 256), losses := [] }

theorem u559 : Upper (D 8) (R 8) [66,288,33,68,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 88 148 160 65 168 296), lower := (rows 67 290 37 88 148 160 65 128 256), losses := [] }

theorem u560 : Upper (D 8) (R 8) [66,288,33,80,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 290 37 88 148 160 72 161 289), lower := (rows 67 290 37 88 148 160 72 128 256), losses := [] }

theorem u561 : Upper (D 8) (R 8) [66,288,33,80,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b561 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 88 148 160 96 137 265), lower := (rows 67 290 37 88 148 160 96 128 256), losses := [] }

theorem u562 : Upper (D 8) (R 8) [66,288,33,80,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 104 148 160 65 152 280), lower := (rows 67 290 37 104 148 160 65 128 256), losses := [] }

theorem u563 : Upper (D 8) (R 8) [66,288,33,96,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 290 37 104 148 160 72 145 273), lower := (rows 67 290 37 104 148 160 72 128 256), losses := [] }

theorem u564 : Upper (D 8) (R 8) [66,288,33,96,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b564 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 290 37 104 148 160 80 137 265), lower := (rows 67 290 37 104 148 160 80 128 256), losses := [] }

theorem u565 : Upper (D 8) (R 8) [66,288,33,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b565 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 37 104 152 160 65 148 276), lower := (rows 67 290 37 104 152 160 65 128 256), losses := [] }

theorem u566 : Upper (D 8) (R 8) [66,288,33,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 290 37 104 152 160 68 145 273), lower := (rows 67 290 37 104 152 160 68 128 256), losses := [] }

theorem u567 : Upper (D 8) (R 8) [66,288,33,96,136,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b567 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 290 37 104 152 160 80 133 261), lower := (rows 67 290 37 104 152 160 80 128 256), losses := [] }

theorem u568 : Upper (D 8) (R 8) [66,288,33,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b568 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 88 176 33 65 132 388), lower := (rows 67 290 44 88 176 33 65 128 256), losses := [] }

theorem u569 : Upper (D 8) (R 8) [66,288,40,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 290 44 88 176 33 68 129 385), lower := (rows 67 290 44 88 176 33 68 128 256), losses := [] }

theorem u570 : Upper (D 8) (R 8) [66,288,40,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b570 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 88 176 33 192 133 261), lower := (rows 67 290 44 88 176 33 192 128 256), losses := [] }

theorem u571 : Upper (D 8) (R 8) [66,288,40,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 290 44 200 145 33 68 176 304), lower := (rows 67 290 44 200 145 33 68 128 256), losses := [] }

theorem u572 : Upper (D 8) (R 8) [66,288,40,192,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b572 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 290 44 200 145 33 80 164 292), lower := (rows 67 290 44 200 145 33 80 128 256), losses := [] }

theorem u573 : Upper (D 8) (R 8) [66,288,40,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b573 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 290 44 200 145 33 96 148 276), lower := (rows 67 290 44 200 145 33 96 128 256), losses := [] }

theorem u574 : Upper (D 8) (R 8) [66,288,40,192,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 44 200 176 33 65 148 276), lower := (rows 67 290 44 200 176 33 65 128 256), losses := [] }

theorem u575 : Upper (D 8) (R 8) [66,288,40,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 290 44 200 176 33 68 145 273), lower := (rows 67 290 44 200 176 33 68 128 256), losses := [] }

theorem u576 : Upper (D 8) (R 8) [66,288,40,192,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b576 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 290 44 200 176 33 80 133 261), lower := (rows 67 290 44 200 176 33 80 128 256), losses := [] }

theorem u577 : Upper (D 8) (R 8) [66,288,40,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b577 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 44 88 176 33 65 164 292), lower := (rows 67 386 44 88 176 33 65 128 256), losses := [] }

theorem u578 : Upper (D 8) (R 8) [66,384,40,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 44 88 176 33 68 161 289), lower := (rows 67 386 44 88 176 33 68 128 256), losses := [] }

theorem u579 : Upper (D 8) (R 8) [66,384,40,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b579 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 88 176 33 96 133 261), lower := (rows 67 386 44 88 176 33 96 128 256), losses := [] }

theorem u580 : Upper (D 8) (R 8) [66,384,40,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 336 160 65 160 416), lower := (rows 97 7 14 56 336 160 65 128 256), losses := [] }

theorem u581 : Upper (D 8) (R 8) [96,5,10,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 56 336 160 96 129 385), lower := (rows 97 7 14 56 336 160 96 128 256), losses := [] }

theorem u582 : Upper (D 8) (R 8) [96,5,10,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 56 336 160 192 161 289), lower := (rows 97 7 14 56 336 160 192 128 256), losses := [] }

theorem u583 : Upper (D 8) (R 8) [96,5,10,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 296 208 160 65 176 304), lower := (rows 97 7 14 296 208 160 65 128 256), losses := [] }

theorem u584 : Upper (D 8) (R 8) [96,5,10,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 14 296 208 160 80 161 289), lower := (rows 97 7 14 296 208 160 80 128 256), losses := [] }

theorem u585 : Upper (D 8) (R 8) [96,5,10,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b585 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 296 208 160 96 145 273), lower := (rows 97 7 14 296 208 160 96 128 256), losses := [] }

theorem u586 : Upper (D 8) (R 8) [96,5,10,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 42 304 160 65 192 448), lower := (rows 97 7 28 42 304 160 65 128 256), losses := [] }

theorem u587 : Upper (D 8) (R 8) [96,5,24,34,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 28 42 304 160 192 193 321), lower := (rows 97 7 28 42 304 160 192 128 256), losses := [] }

theorem u588 : Upper (D 8) (R 8) [96,5,24,34,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 26 304 160 65 192 448), lower := (rows 97 7 44 26 304 160 65 128 256), losses := [] }

theorem u589 : Upper (D 8) (R 8) [96,5,40,18,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 26 304 160 192 193 321), lower := (rows 97 7 44 26 304 160 192 128 256), losses := [] }

theorem u590 : Upper (D 8) (R 8) [96,5,40,18,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 7 44 266 145 160 80 224 352), lower := (rows 97 7 44 266 145 160 80 128 256), losses := [] }

theorem u591 : Upper (D 8) (R 8) [96,5,40,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b591 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 266 145 160 96 208 336), lower := (rows 97 7 44 266 145 160 96 128 256), losses := [] }

theorem u592 : Upper (D 8) (R 8) [96,5,40,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 266 208 160 65 176 304), lower := (rows 97 7 44 266 208 160 65 128 256), losses := [] }

theorem u593 : Upper (D 8) (R 8) [96,5,40,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 44 266 208 160 80 161 289), lower := (rows 97 7 44 266 208 160 80 128 256), losses := [] }

theorem u594 : Upper (D 8) (R 8) [96,5,40,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b594 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 266 208 160 96 145 273), lower := (rows 97 7 44 266 208 160 96 128 256), losses := [] }

theorem u595 : Upper (D 8) (R 8) [96,5,40,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 7 140 56 273 160 66 224 352), lower := (rows 97 7 140 56 273 160 66 128 256), losses := [] }

theorem u596 : Upper (D 8) (R 8) [96,5,136,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b596 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 273 160 96 194 322), lower := (rows 97 7 140 56 273 160 96 128 256), losses := [] }

theorem u597 : Upper (D 8) (R 8) [96,5,136,48,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 336 160 65 162 290), lower := (rows 97 7 140 56 336 160 65 128 256), losses := [] }

theorem u598 : Upper (D 8) (R 8) [96,5,136,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 97 7 140 56 336 160 66 161 289), lower := (rows 97 7 140 56 336 160 66 128 256), losses := [] }

theorem u599 : Upper (D 8) (R 8) [96,5,136,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b599 [(6,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P08
