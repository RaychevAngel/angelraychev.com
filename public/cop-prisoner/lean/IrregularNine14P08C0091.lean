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

def b5460 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 14 37 104 304 48 195 131 387), lower := (rows 193 14 37 104 304 48 64 128 256), losses := [] }

theorem u5460 : Upper (D 8) (R 8) [192,12,33,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5460 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 304 160 83 147 275), lower := (rows 193 14 37 104 304 160 64 128 256), losses := [] }

theorem u5461 : Upper (D 8) (R 8) [192,12,33,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 400 33 114 178 306), lower := (rows 193 14 37 104 400 33 64 128 256), losses := [] }

theorem u5462 : Upper (D 8) (R 8) [192,12,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 37 104 400 34 113 177 305), lower := (rows 193 14 37 104 400 34 64 128 256), losses := [] }

theorem u5463 : Upper (D 8) (R 8) [192,12,33,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5463 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 37 104 400 48 99 163 291), lower := (rows 193 14 37 104 400 48 64 128 256), losses := [] }

theorem u5464 : Upper (D 8) (R 8) [192,12,33,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5464 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5465 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 266 112 33 240 176 432), lower := (rows 193 14 37 266 112 33 64 128 256), losses := [] }

theorem u5465 : Upper (D 8) (R 8) [192,12,33,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5466 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 266 112 48 225 161 417), lower := (rows 193 14 37 266 112 48 64 128 256), losses := [] }

theorem u5466 : Upper (D 8) (R 8) [192,12,33,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5466 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 266 112 160 113 177 305), lower := (rows 193 14 37 266 112 160 64 128 256), losses := [] }

theorem u5467 : Upper (D 8) (R 8) [192,12,33,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 280 50 33 224 224 480), lower := (rows 193 14 37 280 50 33 64 128 256), losses := [] }

theorem u5468 : Upper (D 8) (R 8) [192,12,33,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 280 50 96 225 161 417), lower := (rows 193 14 37 280 50 96 64 128 256), losses := [] }

theorem u5469 : Upper (D 8) (R 8) [192,12,33,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 280 112 33 226 162 418), lower := (rows 193 14 37 280 112 33 64 128 256), losses := [] }

theorem u5470 : Upper (D 8) (R 8) [192,12,33,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 280 112 34 225 161 417), lower := (rows 193 14 37 280 112 34 64 128 256), losses := [] }

theorem u5471 : Upper (D 8) (R 8) [192,12,33,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5471 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 280 112 160 99 163 291), lower := (rows 193 14 37 280 112 160 64 128 256), losses := [] }

theorem u5472 : Upper (D 8) (R 8) [192,12,33,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5473 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 296 82 33 240 176 432), lower := (rows 193 14 37 296 82 33 64 128 256), losses := [] }

theorem u5473 : Upper (D 8) (R 8) [192,12,33,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5474 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 296 82 48 225 161 417), lower := (rows 193 14 37 296 82 48 64 128 256), losses := [] }

theorem u5474 : Upper (D 8) (R 8) [192,12,33,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5474 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5475 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 296 82 160 113 177 305), lower := (rows 193 14 37 296 82 160 64 128 256), losses := [] }

theorem u5475 : Upper (D 8) (R 8) [192,12,33,288,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 296 112 33 210 146 402), lower := (rows 193 14 37 296 112 33 64 128 256), losses := [] }

theorem u5476 : Upper (D 8) (R 8) [192,12,33,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 193 14 37 296 112 34 209 145 401), lower := (rows 193 14 37 296 112 34 64 128 256), losses := [] }

theorem u5477 : Upper (D 8) (R 8) [192,12,33,288,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5477 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5478 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 193 14 37 296 112 48 195 131 387), lower := (rows 193 14 37 296 112 48 64 128 256), losses := [] }

theorem u5478 : Upper (D 8) (R 8) [192,12,33,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5478 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5479 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 296 112 160 83 147 275), lower := (rows 193 14 37 296 112 160 64 128 256), losses := [] }

theorem u5479 : Upper (D 8) (R 8) [192,12,33,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5480 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 328 50 33 240 176 432), lower := (rows 193 14 37 328 50 33 64 128 256), losses := [] }

theorem u5480 : Upper (D 8) (R 8) [192,12,33,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5481 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 37 328 50 48 225 161 417), lower := (rows 193 14 37 328 50 48 64 128 256), losses := [] }

theorem u5481 : Upper (D 8) (R 8) [192,12,33,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5481 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5482 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 346, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 328 50 160 113 177 305), lower := (rows 193 14 37 328 50 160 64 128 256), losses := [] }

theorem u5482 : Upper (D 8) (R 8) [192,12,33,320,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5483 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 328 146 33 112 176 304), lower := (rows 193 14 37 328 146 33 64 128 256), losses := [] }

theorem u5483 : Upper (D 8) (R 8) [192,12,33,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 37 328 146 48 97 161 289), lower := (rows 193 14 37 328 146 48 64 128 256), losses := [] }

theorem u5484 : Upper (D 8) (R 8) [192,12,33,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5484 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 328 176 33 114 178 306), lower := (rows 193 14 37 328 176 33 64 128 256), losses := [] }

theorem u5485 : Upper (D 8) (R 8) [192,12,33,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5486 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 193 14 37 328 176 34 113 177 305), lower := (rows 193 14 37 328 176 34 64 128 256), losses := [] }

theorem u5486 : Upper (D 8) (R 8) [192,12,33,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5486 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5487 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 37 328 176 48 99 163 291), lower := (rows 193 14 37 328 176 48 64 128 256), losses := [] }

theorem u5487 : Upper (D 8) (R 8) [192,12,33,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5487 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 193 14 38 265 49 48 224 224 480), lower := (rows 193 14 38 265 49 48 64 128 256), losses := [] }

theorem u5488 : Upper (D 8) (R 8) [192,12,34,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5488 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 265 49 96 240 176 432), lower := (rows 193 14 38 265 49 96 64 128 256), losses := [] }

theorem u5489 : Upper (D 8) (R 8) [192,12,34,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 265 112 33 240 176 432), lower := (rows 193 14 38 265 112 33 64 128 256), losses := [] }

theorem u5490 : Upper (D 8) (R 8) [192,12,34,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 38 265 112 48 225 161 417), lower := (rows 193 14 38 265 112 48 64 128 256), losses := [] }

theorem u5491 : Upper (D 8) (R 8) [192,12,34,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5491 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5492 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 38 265 112 160 113 177 305), lower := (rows 193 14 38 265 112 160 64 128 256), losses := [] }

theorem u5492 : Upper (D 8) (R 8) [192,12,34,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5493 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 280 49 33 224 224 480), lower := (rows 193 14 38 280 49 33 64 128 256), losses := [] }

theorem u5493 : Upper (D 8) (R 8) [192,12,34,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5494 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 280 49 96 225 161 417), lower := (rows 193 14 38 280 49 96 64 128 256), losses := [] }

theorem u5494 : Upper (D 8) (R 8) [192,12,34,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 193 14 38 280 112 33 225 161 417), lower := (rows 193 14 38 280 112 33 64 128 256), losses := [] }

theorem u5495 : Upper (D 8) (R 8) [192,12,34,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 38 280 112 160 97 161 289), lower := (rows 193 14 38 280 112 160 64 128 256), losses := [] }

theorem u5496 : Upper (D 8) (R 8) [192,12,34,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5497 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 52 104 273 33 226 162 418), lower := (rows 193 14 52 104 273 33 64 128 256), losses := [] }

theorem u5497 : Upper (D 8) (R 8) [192,12,48,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5498 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 52 104 273 34 225 161 417), lower := (rows 193 14 52 104 273 34 64 128 256), losses := [] }

theorem u5498 : Upper (D 8) (R 8) [192,12,48,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5498 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 52 104 273 160 99 163 291), lower := (rows 193 14 52 104 273 160 64 128 256), losses := [] }

theorem u5499 : Upper (D 8) (R 8) [192,12,48,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 193 14 52 104 274 33 225 161 417), lower := (rows 193 14 52 104 274 33 64 128 256), losses := [] }

theorem u5500 : Upper (D 8) (R 8) [192,12,48,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 52 104 274 160 97 161 289), lower := (rows 193 14 52 104 274 160 64 128 256), losses := [] }

theorem u5501 : Upper (D 8) (R 8) [192,12,48,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 193 14 52 104 400 33 99 163 291), lower := (rows 193 14 52 104 400 33 64 128 256), losses := [] }

theorem u5502 : Upper (D 8) (R 8) [192,12,48,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5503 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 52 104 400 34 97 161 289), lower := (rows 193 14 52 104 400 34 64 128 256), losses := [] }

theorem u5503 : Upper (D 8) (R 8) [192,12,48,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5503 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5504 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 84 168 49 33 354 418 290), lower := (rows 193 14 84 168 49 33 64 128 256), losses := [] }

theorem u5504 : Upper (D 8) (R 8) [192,12,80,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 193 14 84 168 49 34 353 417 289), lower := (rows 193 14 84 168 49 34 64 128 256), losses := [] }

theorem u5505 : Upper (D 8) (R 8) [192,12,80,160,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5505 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 193 14 84 168 49 288 99 163 291), lower := (rows 193 14 84 168 49 288 64 128 256), losses := [] }

theorem u5506 : Upper (D 8) (R 8) [192,12,80,160,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5506 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 168 273 33 98 162 290), lower := (rows 193 14 84 168 273 33 64 128 256), losses := [] }

theorem u5507 : Upper (D 8) (R 8) [192,12,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 84 168 273 34 97 161 289), lower := (rows 193 14 84 168 273 34 64 128 256), losses := [] }

theorem u5508 : Upper (D 8) (R 8) [192,12,80,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5508 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 193 14 84 168 304 33 99 163 291), lower := (rows 193 14 84 168 304 33 64 128 256), losses := [] }

theorem u5509 : Upper (D 8) (R 8) [192,12,80,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 84 168 304 34 97 161 289), lower := (rows 193 14 84 168 304 34 64 128 256), losses := [] }

theorem u5510 : Upper (D 8) (R 8) [192,12,80,160,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5510 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 193 14 84 265 49 34 224 160 416), lower := (rows 193 14 84 265 49 34 64 128 256), losses := [] }

theorem u5511 : Upper (D 8) (R 8) [192,12,80,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5511 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 84 265 49 160 98 162 290), lower := (rows 193 14 84 265 49 160 64 128 256), losses := [] }

theorem u5512 : Upper (D 8) (R 8) [192,12,80,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 84 265 176 33 98 162 290), lower := (rows 193 14 84 265 176 33 64 128 256), losses := [] }

theorem u5513 : Upper (D 8) (R 8) [192,12,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 84 265 176 34 97 161 289), lower := (rows 193 14 84 265 176 34 64 128 256), losses := [] }

theorem u5514 : Upper (D 8) (R 8) [192,12,80,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5514 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 84 296 49 33 226 162 418), lower := (rows 193 14 84 296 49 33 64 128 256), losses := [] }

theorem u5515 : Upper (D 8) (R 8) [192,12,80,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 193 14 84 296 49 34 225 161 417), lower := (rows 193 14 84 296 49 34 64 128 256), losses := [] }

theorem u5516 : Upper (D 8) (R 8) [192,12,80,288,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5516 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 84 296 49 160 99 163 291), lower := (rows 193 14 84 296 49 160 64 128 256), losses := [] }

theorem u5517 : Upper (D 8) (R 8) [192,12,80,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 84 296 176 33 99 163 291), lower := (rows 193 14 84 296 176 33 64 128 256), losses := [] }

theorem u5518 : Upper (D 8) (R 8) [192,12,80,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5519 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 193 14 84 296 176 34 97 161 289), lower := (rows 193 14 84 296 176 34 64 128 256), losses := [] }

theorem u5519 : Upper (D 8) (R 8) [192,12,80,288,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5519 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u5519
end Delivery.IrregularNine14.P08
