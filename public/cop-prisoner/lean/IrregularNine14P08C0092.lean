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

def b5520 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 84 392 49 33 98 162 290), lower := (rows 193 14 84 392 49 33 64 128 256), losses := [] }

theorem u5520 : Upper (D 8) (R 8) [192,12,80,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5521 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 84 392 49 34 97 161 289), lower := (rows 193 14 84 392 49 34 64 128 256), losses := [] }

theorem u5521 : Upper (D 8) (R 8) [192,12,80,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5521 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5522 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 100 168 49 33 338 402 274), lower := (rows 193 14 100 168 49 33 64 128 256), losses := [] }

theorem u5522 : Upper (D 8) (R 8) [192,12,96,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5523 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 193 14 100 168 49 34 337 401 273), lower := (rows 193 14 100 168 49 34 64 128 256), losses := [] }

theorem u5523 : Upper (D 8) (R 8) [192,12,96,160,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5523 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 193 14 100 168 49 48 323 387 259), lower := (rows 193 14 100 168 49 48 64 128 256), losses := [] }

theorem u5524 : Upper (D 8) (R 8) [192,12,96,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5524 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 193 14 100 168 49 288 83 147 275), lower := (rows 193 14 100 168 49 288 64 128 256), losses := [] }

theorem u5525 : Upper (D 8) (R 8) [192,12,96,160,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5525 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5526 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 100 168 273 33 114 178 306), lower := (rows 193 14 100 168 273 33 64 128 256), losses := [] }

theorem u5526 : Upper (D 8) (R 8) [192,12,96,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5527 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 100 168 273 34 113 177 305), lower := (rows 193 14 100 168 273 34 64 128 256), losses := [] }

theorem u5527 : Upper (D 8) (R 8) [192,12,96,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5527 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5528 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 100 168 273 48 99 163 291), lower := (rows 193 14 100 168 273 48 64 128 256), losses := [] }

theorem u5528 : Upper (D 8) (R 8) [192,12,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5528 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5529 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 100 168 274 33 113 177 305), lower := (rows 193 14 100 168 274 33 64 128 256), losses := [] }

theorem u5529 : Upper (D 8) (R 8) [192,12,96,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5530 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 100 168 274 48 97 161 289), lower := (rows 193 14 100 168 274 48 64 128 256), losses := [] }

theorem u5530 : Upper (D 8) (R 8) [192,12,96,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5530 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5531 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 100 168 304 33 83 147 275), lower := (rows 193 14 100 168 304 33 64 128 256), losses := [] }

theorem u5531 : Upper (D 8) (R 8) [192,12,96,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5532 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 14 100 168 304 34 81 145 273), lower := (rows 193 14 100 168 304 34 64 128 256), losses := [] }

theorem u5532 : Upper (D 8) (R 8) [192,12,96,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5532 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5533 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 193 14 100 168 304 48 67 131 259), lower := (rows 193 14 100 168 304 48 64 128 256), losses := [] }

theorem u5533 : Upper (D 8) (R 8) [192,12,96,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5533 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5534 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 14 100 265 49 34 240 176 432), lower := (rows 193 14 100 265 49 34 64 128 256), losses := [] }

theorem u5534 : Upper (D 8) (R 8) [192,12,96,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5534 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5535 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 193 14 100 265 49 48 226 162 418), lower := (rows 193 14 100 265 49 48 64 128 256), losses := [] }

theorem u5535 : Upper (D 8) (R 8) [192,12,96,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5535 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5536 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 265 49 160 114 178 306), lower := (rows 193 14 100 265 49 160 64 128 256), losses := [] }

theorem u5536 : Upper (D 8) (R 8) [192,12,96,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5537 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 265 50 33 240 176 432), lower := (rows 193 14 100 265 50 33 64 128 256), losses := [] }

theorem u5537 : Upper (D 8) (R 8) [192,12,96,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5538 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 100 265 50 48 225 161 417), lower := (rows 193 14 100 265 50 48 64 128 256), losses := [] }

theorem u5538 : Upper (D 8) (R 8) [192,12,96,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5538 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 100 265 50 160 113 177 305), lower := (rows 193 14 100 265 50 160 64 128 256), losses := [] }

theorem u5539 : Upper (D 8) (R 8) [192,12,96,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 265 146 33 112 176 304), lower := (rows 193 14 100 265 146 33 64 128 256), losses := [] }

theorem u5540 : Upper (D 8) (R 8) [192,12,96,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 100 265 146 48 97 161 289), lower := (rows 193 14 100 265 146 48 64 128 256), losses := [] }

theorem u5541 : Upper (D 8) (R 8) [192,12,96,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5541 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 265 176 33 114 178 306), lower := (rows 193 14 100 265 176 33 64 128 256), losses := [] }

theorem u5542 : Upper (D 8) (R 8) [192,12,96,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 100 265 176 34 113 177 305), lower := (rows 193 14 100 265 176 34 64 128 256), losses := [] }

theorem u5543 : Upper (D 8) (R 8) [192,12,96,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5543 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 100 265 176 48 99 163 291), lower := (rows 193 14 100 265 176 48 64 128 256), losses := [] }

theorem u5544 : Upper (D 8) (R 8) [192,12,96,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5544 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 100 280 49 33 226 162 418), lower := (rows 193 14 100 280 49 33 64 128 256), losses := [] }

theorem u5545 : Upper (D 8) (R 8) [192,12,96,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 100 280 49 34 225 161 417), lower := (rows 193 14 100 280 49 34 64 128 256), losses := [] }

theorem u5546 : Upper (D 8) (R 8) [192,12,96,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5546 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 280 49 160 99 163 291), lower := (rows 193 14 100 280 49 160 64 128 256), losses := [] }

theorem u5547 : Upper (D 8) (R 8) [192,12,96,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5548 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 280 50 33 225 161 417), lower := (rows 193 14 100 280 50 33 64 128 256), losses := [] }

theorem u5548 : Upper (D 8) (R 8) [192,12,96,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5549 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 193 14 100 280 50 160 97 161 289), lower := (rows 193 14 100 280 50 160 64 128 256), losses := [] }

theorem u5549 : Upper (D 8) (R 8) [192,12,96,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5550 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 280 176 33 99 163 291), lower := (rows 193 14 100 280 176 33 64 128 256), losses := [] }

theorem u5550 : Upper (D 8) (R 8) [192,12,96,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5551 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 100 280 176 34 97 161 289), lower := (rows 193 14 100 280 176 34 64 128 256), losses := [] }

theorem u5551 : Upper (D 8) (R 8) [192,12,96,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5551 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5552 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 100 296 49 33 210 146 402), lower := (rows 193 14 100 296 49 33 64 128 256), losses := [] }

theorem u5552 : Upper (D 8) (R 8) [192,12,96,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5553 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 14 100 296 49 34 209 145 401), lower := (rows 193 14 100 296 49 34 64 128 256), losses := [] }

theorem u5553 : Upper (D 8) (R 8) [192,12,96,288,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5553 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 14 100 296 49 48 195 131 387), lower := (rows 193 14 100 296 49 48 64 128 256), losses := [] }

theorem u5554 : Upper (D 8) (R 8) [192,12,96,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5554 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 100 296 49 160 83 147 275), lower := (rows 193 14 100 296 49 160 64 128 256), losses := [] }

theorem u5555 : Upper (D 8) (R 8) [192,12,96,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 296 146 33 113 177 305), lower := (rows 193 14 100 296 146 33 64 128 256), losses := [] }

theorem u5556 : Upper (D 8) (R 8) [192,12,96,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 100 296 146 48 97 161 289), lower := (rows 193 14 100 296 146 48 64 128 256), losses := [] }

theorem u5557 : Upper (D 8) (R 8) [192,12,96,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5557 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 100 296 176 33 83 147 275), lower := (rows 193 14 100 296 176 33 64 128 256), losses := [] }

theorem u5558 : Upper (D 8) (R 8) [192,12,96,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5559 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 193 14 100 296 176 34 81 145 273), lower := (rows 193 14 100 296 176 34 64 128 256), losses := [] }

theorem u5559 : Upper (D 8) (R 8) [192,12,96,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5559 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5560 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 193 14 100 296 176 48 67 131 259), lower := (rows 193 14 100 296 176 48 64 128 256), losses := [] }

theorem u5560 : Upper (D 8) (R 8) [192,12,96,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5560 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5561 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 100 392 49 33 114 178 306), lower := (rows 193 14 100 392 49 33 64 128 256), losses := [] }

theorem u5561 : Upper (D 8) (R 8) [192,12,96,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5562 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 100 392 49 34 113 177 305), lower := (rows 193 14 100 392 49 34 64 128 256), losses := [] }

theorem u5562 : Upper (D 8) (R 8) [192,12,96,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5562 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 100 392 49 48 99 163 291), lower := (rows 193 14 100 392 49 48 64 128 256), losses := [] }

theorem u5563 : Upper (D 8) (R 8) [192,12,96,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5563 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 193 14 100 392 50 33 113 177 305), lower := (rows 193 14 100 392 50 33 64 128 256), losses := [] }

theorem u5564 : Upper (D 8) (R 8) [192,12,96,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5565 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 100 392 50 48 97 161 289), lower := (rows 193 14 100 392 50 48 64 128 256), losses := [] }

theorem u5565 : Upper (D 8) (R 8) [192,12,96,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5565 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 148 33 368 432 304), lower := (rows 193 35 44 74 148 33 64 128 256), losses := [] }

theorem u5566 : Upper (D 8) (R 8) [192,33,40,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 35 44 74 148 48 353 417 289), lower := (rows 193 35 44 74 148 48 64 128 256), losses := [] }

theorem u5567 : Upper (D 8) (R 8) [192,33,40,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5567 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 35 44 74 148 288 113 177 305), lower := (rows 193 35 44 74 148 288 64 128 256), losses := [] }

theorem u5568 : Upper (D 8) (R 8) [192,33,40,66,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5568 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 176 33 340 404 276), lower := (rows 193 35 44 74 176 33 64 128 256), losses := [] }

theorem u5569 : Upper (D 8) (R 8) [192,33,40,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 193 35 44 74 176 36 337 401 273), lower := (rows 193 35 44 74 176 36 64 128 256), losses := [] }

theorem u5570 : Upper (D 8) (R 8) [192,33,40,66,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5570 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 193 35 44 74 176 48 325 389 261), lower := (rows 193 35 44 74 176 48 64 128 256), losses := [] }

theorem u5571 : Upper (D 8) (R 8) [192,33,40,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5571 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5572 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 193 35 44 74 176 288 85 149 277), lower := (rows 193 35 44 74 176 288 64 128 256), losses := [] }

theorem u5572 : Upper (D 8) (R 8) [192,33,40,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5572 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5573 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 193 35 44 74 273 36 240 176 432), lower := (rows 193 35 44 74 273 36 64 128 256), losses := [] }

theorem u5573 : Upper (D 8) (R 8) [192,33,40,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5573 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 193 35 44 74 273 48 228 164 420), lower := (rows 193 35 44 74 273 48 64 128 256), losses := [] }

theorem u5574 : Upper (D 8) (R 8) [192,33,40,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5574 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 74 273 160 116 180 308), lower := (rows 193 35 44 74 273 160 64 128 256), losses := [] }

theorem u5575 : Upper (D 8) (R 8) [192,33,40,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 276 33 240 176 432), lower := (rows 193 35 44 74 276 33 64 128 256), losses := [] }

theorem u5576 : Upper (D 8) (R 8) [192,33,40,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 35 44 74 276 48 225 161 417), lower := (rows 193 35 44 74 276 48 64 128 256), losses := [] }

theorem u5577 : Upper (D 8) (R 8) [192,33,40,66,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5577 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5578 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 193 35 44 74 276 160 113 177 305), lower := (rows 193 35 44 74 276 160 64 128 256), losses := [] }

theorem u5578 : Upper (D 8) (R 8) [192,33,40,66,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5579 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 193 35 44 74 304 33 212 148 404), lower := (rows 193 35 44 74 304 33 64 128 256), losses := [] }

theorem u5579 : Upper (D 8) (R 8) [192,33,40,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P08
