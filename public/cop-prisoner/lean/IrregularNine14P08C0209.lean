import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0069

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12540 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 152 304 226 226 226 482), lower := (rows 97 7 13 152 304 32 64 128 256), losses := [] }

theorem u12540 : Upper (D 8) (R 8) [96,5,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12541 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 152 336 162 226 162 418), lower := (rows 97 7 13 152 336 32 64 128 256), losses := [] }

theorem u12541 : Upper (D 8) (R 8) [96,5,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12542 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 50 496 464 464 464), lower := (rows 97 7 13 168 50 32 64 128 256), losses := [] }

theorem u12542 : Upper (D 8) (R 8) [96,5,9,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12543 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 82 432 496 432 432), lower := (rows 97 7 13 168 82 32 64 128 256), losses := [] }

theorem u12543 : Upper (D 8) (R 8) [96,5,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12544 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 146 368 368 496 368), lower := (rows 97 7 13 168 146 32 64 128 256), losses := [] }

theorem u12544 : Upper (D 8) (R 8) [96,5,9,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12545 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 208 306 370 434 306), lower := (rows 97 7 13 168 208 32 64 128 256), losses := [] }

theorem u12545 : Upper (D 8) (R 8) [96,5,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12546 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 274 240 240 240 496), lower := (rows 97 7 13 168 274 32 64 128 256), losses := [] }

theorem u12546 : Upper (D 8) (R 8) [96,5,9,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12547 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 304 242 210 210 466), lower := (rows 97 7 13 168 304 32 64 128 256), losses := [] }

theorem u12547 : Upper (D 8) (R 8) [96,5,9,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12548 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 336 178 242 178 434), lower := (rows 97 7 13 168 336 32 64 128 256), losses := [] }

theorem u12548 : Upper (D 8) (R 8) [96,5,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12549 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 168 400 114 114 242 370), lower := (rows 97 7 13 168 400 32 64 128 256), losses := [] }

theorem u12549 : Upper (D 8) (R 8) [96,5,9,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12550 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 50 432 496 432 432), lower := (rows 97 7 13 200 50 32 64 128 256), losses := [] }

theorem u12550 : Upper (D 8) (R 8) [96,5,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12551 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 146 304 368 432 304), lower := (rows 97 7 13 200 146 32 64 128 256), losses := [] }

theorem u12551 : Upper (D 8) (R 8) [96,5,9,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12552 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 176 306 370 434 306), lower := (rows 97 7 13 200 176 32 64 128 256), losses := [] }

theorem u12552 : Upper (D 8) (R 8) [96,5,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12553 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 274 176 240 176 432), lower := (rows 97 7 13 200 274 32 64 128 256), losses := [] }

theorem u12553 : Upper (D 8) (R 8) [96,5,9,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12554 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 304 178 242 178 434), lower := (rows 97 7 13 200 304 32 64 128 256), losses := [] }

theorem u12554 : Upper (D 8) (R 8) [96,5,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12555 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 200 400 50 114 178 306), lower := (rows 97 7 13 200 400 32 64 128 256), losses := [] }

theorem u12555 : Upper (D 8) (R 8) [96,5,9,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12556 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 176 240 240 240 496), lower := (rows 97 7 13 266 176 32 64 128 256), losses := [] }

theorem u12556 : Upper (D 8) (R 8) [96,5,9,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12557 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 266 208 176 240 176 432), lower := (rows 97 7 13 266 208 32 64 128 256), losses := [] }

theorem u12557 : Upper (D 8) (R 8) [96,5,9,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12558 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 280 50 224 224 224 480), lower := (rows 97 7 13 280 50 32 64 128 256), losses := [] }

theorem u12558 : Upper (D 8) (R 8) [96,5,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12559 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 280 82 160 224 160 416), lower := (rows 97 7 13 280 82 32 64 128 256), losses := [] }

theorem u12559 : Upper (D 8) (R 8) [96,5,9,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12560 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 280 146 224 224 224 480), lower := (rows 97 7 13 280 146 32 64 128 256), losses := [] }

theorem u12560 : Upper (D 8) (R 8) [96,5,9,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12561 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 280 176 226 226 226 482), lower := (rows 97 7 13 280 176 32 64 128 256), losses := [] }

theorem u12561 : Upper (D 8) (R 8) [96,5,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12562 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 280 208 162 226 162 418), lower := (rows 97 7 13 280 208 32 64 128 256), losses := [] }

theorem u12562 : Upper (D 8) (R 8) [96,5,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12563 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 50 240 208 208 464), lower := (rows 97 7 13 296 50 32 64 128 256), losses := [] }

theorem u12563 : Upper (D 8) (R 8) [96,5,9,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12564 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 82 176 240 176 432), lower := (rows 97 7 13 296 82 32 64 128 256), losses := [] }

theorem u12564 : Upper (D 8) (R 8) [96,5,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12565 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 146 240 240 240 496), lower := (rows 97 7 13 296 146 32 64 128 256), losses := [] }

theorem u12565 : Upper (D 8) (R 8) [96,5,9,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12566 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 176 242 210 210 466), lower := (rows 97 7 13 296 176 32 64 128 256), losses := [] }

theorem u12566 : Upper (D 8) (R 8) [96,5,9,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12567 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 208 178 242 178 434), lower := (rows 97 7 13 296 208 32 64 128 256), losses := [] }

theorem u12567 : Upper (D 8) (R 8) [96,5,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12568 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 328 50 176 240 176 432), lower := (rows 97 7 13 328 50 32 64 128 256), losses := [] }

theorem u12568 : Upper (D 8) (R 8) [96,5,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12569 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 328 146 176 240 176 432), lower := (rows 97 7 13 328 146 32 64 128 256), losses := [] }

theorem u12569 : Upper (D 8) (R 8) [96,5,9,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12570 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 328 176 178 242 178 434), lower := (rows 97 7 13 328 176 32 64 128 256), losses := [] }

theorem u12570 : Upper (D 8) (R 8) [96,5,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12571 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 50 240 240 240 496), lower := (rows 97 7 13 392 50 32 64 128 256), losses := [] }

theorem u12571 : Upper (D 8) (R 8) [96,5,9,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12572 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 82 176 240 176 432), lower := (rows 97 7 13 392 82 32 64 128 256), losses := [] }

theorem u12572 : Upper (D 8) (R 8) [96,5,9,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12573 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 146 112 112 240 368), lower := (rows 97 7 13 392 146 32 64 128 256), losses := [] }

theorem u12573 : Upper (D 8) (R 8) [96,5,9,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12574 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 176 114 114 242 370), lower := (rows 97 7 13 392 176 32 64 128 256), losses := [] }

theorem u12574 : Upper (D 8) (R 8) [96,5,9,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12575 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 208 50 114 178 306), lower := (rows 97 7 13 392 208 32 64 128 256), losses := [] }

theorem u12575 : Upper (D 8) (R 8) [96,5,9,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12576 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 176 480 480 480 480), lower := (rows 97 7 14 25 176 32 64 128 256), losses := [] }

theorem u12576 : Upper (D 8) (R 8) [96,5,10,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12577 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 208 416 480 416 416), lower := (rows 97 7 14 25 208 32 64 128 256), losses := [] }

theorem u12577 : Upper (D 8) (R 8) [96,5,10,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12578 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 304 224 224 224 480), lower := (rows 97 7 14 25 304 32 64 128 256), losses := [] }

theorem u12578 : Upper (D 8) (R 8) [96,5,10,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12579 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 336 160 224 160 416), lower := (rows 97 7 14 25 336 32 64 128 256), losses := [] }

theorem u12579 : Upper (D 8) (R 8) [96,5,10,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12580 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 400 224 224 224 480), lower := (rows 97 7 14 25 400 32 64 128 256), losses := [] }

theorem u12580 : Upper (D 8) (R 8) [96,5,10,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12581 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 176 496 464 464 464), lower := (rows 97 7 14 41 176 32 64 128 256), losses := [] }

theorem u12581 : Upper (D 8) (R 8) [96,5,10,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12582 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 208 432 496 432 432), lower := (rows 97 7 14 41 208 32 64 128 256), losses := [] }

theorem u12582 : Upper (D 8) (R 8) [96,5,10,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12583 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 304 240 208 208 464), lower := (rows 97 7 14 41 304 32 64 128 256), losses := [] }

theorem u12583 : Upper (D 8) (R 8) [96,5,10,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12584 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 336 176 240 176 432), lower := (rows 97 7 14 41 336 32 64 128 256), losses := [] }

theorem u12584 : Upper (D 8) (R 8) [96,5,10,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12585 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 400 240 240 240 496), lower := (rows 97 7 14 41 400 32 64 128 256), losses := [] }

theorem u12585 : Upper (D 8) (R 8) [96,5,10,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12586 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 56 49 480 448 448 448), lower := (rows 97 7 14 56 49 32 64 128 256), losses := [] }

theorem u12586 : Upper (D 8) (R 8) [96,5,10,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12587 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 56 81 416 480 416 416), lower := (rows 97 7 14 56 81 32 64 128 256), losses := [] }

theorem u12587 : Upper (D 8) (R 8) [96,5,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12588 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 56 112 417 449 385 385), lower := (rows 97 7 14 56 112 32 64 128 256), losses := [] }

theorem u12588 : Upper (D 8) (R 8) [96,5,10,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12589 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 56 145 480 480 480 480), lower := (rows 97 7 14 56 145 32 64 128 256), losses := [] }

theorem u12589 : Upper (D 8) (R 8) [96,5,10,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12590 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 56 176 481 449 449 449), lower := (rows 97 7 14 56 176 32 64 128 256), losses := [] }

theorem u12590 : Upper (D 8) (R 8) [96,5,10,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12591 : Route 9 := (fun mask => (mask,id))

def c12591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u12591 : Upper (D 8) (R 8) [96,5,10,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,192] 13 (by decide) (choices 1) [1,128,256] r12591 c12591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4145
  · exact u4146
  · exact u4147

def b12592 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 56 273 224 224 224 480), lower := (rows 97 7 14 56 273 32 64 128 256), losses := [] }

theorem u12592 : Upper (D 8) (R 8) [96,5,10,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12593 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 14 56 304 225 193 193 449), lower := (rows 97 7 14 56 304 32 64 128 256), losses := [] }

theorem u12593 : Upper (D 8) (R 8) [96,5,10,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12594 : Route 9 := (fun mask => (mask,id))

def c12594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12594 : Upper (D 8) (R 8) [96,5,10,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,320] 13 (by decide) (choices 1) [1,128] r12594 c12594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4148
  · exact u4149

def r12595 : Route 9 := (fun mask => (mask,id))

def c12595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12595 : Upper (D 8) (R 8) [96,5,10,48,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,384] 13 (by decide) (choices 1) [1,64,128] r12595 c12595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4150
  · exact u4151
  · exact u4152

def b12596 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 73 176 432 496 432 432), lower := (rows 97 7 14 73 176 32 64 128 256), losses := [] }

theorem u12596 : Upper (D 8) (R 8) [96,5,10,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12597 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 73 304 176 240 176 432), lower := (rows 97 7 14 73 304 32 64 128 256), losses := [] }

theorem u12597 : Upper (D 8) (R 8) [96,5,10,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12598 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 73 400 176 240 176 432), lower := (rows 97 7 14 73 400 32 64 128 256), losses := [] }

theorem u12598 : Upper (D 8) (R 8) [96,5,10,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12599 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 14 88 145 416 480 416 416), lower := (rows 97 7 14 88 145 32 64 128 256), losses := [] }

theorem u12599 : Upper (D 8) (R 8) [96,5,10,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12599
end Delivery.IrregularNine14.P08
