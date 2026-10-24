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

def b2520 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 262 69 104 176 40 209 145 401), lower := (rows 35 262 69 104 176 40 64 128 256), losses := [] }

theorem u2520 : Upper (D 8) (R 8) [34,260,65,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2520 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 262 69 104 176 48 201 137 393), lower := (rows 35 262 69 104 176 48 64 128 256), losses := [] }

theorem u2521 : Upper (D 8) (R 8) [34,260,65,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2521 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2522 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 69 104 176 160 89 153 281), lower := (rows 35 262 69 104 176 160 64 128 256), losses := [] }

theorem u2522 : Upper (D 8) (R 8) [34,260,65,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 69 168 208 33 120 184 312), lower := (rows 35 262 69 168 208 33 64 128 256), losses := [] }

theorem u2523 : Upper (D 8) (R 8) [34,260,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 262 69 168 208 40 113 177 305), lower := (rows 35 262 69 168 208 40 64 128 256), losses := [] }

theorem u2524 : Upper (D 8) (R 8) [34,260,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2524 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 262 69 168 208 48 105 169 297), lower := (rows 35 262 69 168 208 48 64 128 256), losses := [] }

theorem u2525 : Upper (D 8) (R 8) [34,260,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2525 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 25 176 33 224 224 480), lower := (rows 35 262 76 25 176 33 64 128 256), losses := [] }

theorem u2526 : Upper (D 8) (R 8) [34,260,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2527 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 25 176 96 225 161 417), lower := (rows 35 262 76 25 176 96 64 128 256), losses := [] }

theorem u2527 : Upper (D 8) (R 8) [34,260,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2528 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 25 176 160 97 225 353), lower := (rows 35 262 76 25 176 160 64 128 256), losses := [] }

theorem u2528 : Upper (D 8) (R 8) [34,260,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2529 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 56 145 33 224 224 480), lower := (rows 35 262 76 56 145 33 64 128 256), losses := [] }

theorem u2529 : Upper (D 8) (R 8) [34,260,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2530 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 56 145 96 225 161 417), lower := (rows 35 262 76 56 145 96 64 128 256), losses := [] }

theorem u2530 : Upper (D 8) (R 8) [34,260,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 56 145 160 97 225 353), lower := (rows 35 262 76 56 145 160 64 128 256), losses := [] }

theorem u2531 : Upper (D 8) (R 8) [34,260,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2532 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 112 33 240 176 432), lower := (rows 35 262 76 137 112 33 64 128 256), losses := [] }

theorem u2532 : Upper (D 8) (R 8) [34,260,72,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 76 137 112 48 225 161 417), lower := (rows 35 262 76 137 112 48 64 128 256), losses := [] }

theorem u2533 : Upper (D 8) (R 8) [34,260,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2533 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 262 76 137 112 160 113 177 305), lower := (rows 35 262 76 137 112 160 64 128 256), losses := [] }

theorem u2534 : Upper (D 8) (R 8) [34,260,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 176 33 112 240 368), lower := (rows 35 262 76 137 176 33 64 128 256), losses := [] }

theorem u2535 : Upper (D 8) (R 8) [34,260,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 262 76 137 176 48 97 225 353), lower := (rows 35 262 76 137 176 48 64 128 256), losses := [] }

theorem u2536 : Upper (D 8) (R 8) [34,260,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2536 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 137 176 96 113 177 305), lower := (rows 35 262 76 137 176 96 64 128 256), losses := [] }

theorem u2537 : Upper (D 8) (R 8) [34,260,72,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 208 33 112 176 304), lower := (rows 35 262 76 137 208 33 64 128 256), losses := [] }

theorem u2538 : Upper (D 8) (R 8) [34,260,72,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 76 137 208 48 97 161 289), lower := (rows 35 262 76 137 208 48 64 128 256), losses := [] }

theorem u2539 : Upper (D 8) (R 8) [34,260,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2539 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 168 112 33 209 145 401), lower := (rows 35 262 76 168 112 33 64 128 256), losses := [] }

theorem u2540 : Upper (D 8) (R 8) [34,260,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 76 168 112 48 193 129 385), lower := (rows 35 262 76 168 112 48 64 128 256), losses := [] }

theorem u2541 : Upper (D 8) (R 8) [34,260,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2541 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 76 168 112 160 81 145 273), lower := (rows 35 262 76 168 112 160 64 128 256), losses := [] }

theorem u2542 : Upper (D 8) (R 8) [34,260,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 168 145 33 112 240 368), lower := (rows 35 262 76 168 145 33 64 128 256), losses := [] }

theorem u2543 : Upper (D 8) (R 8) [34,260,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 262 76 168 145 48 97 225 353), lower := (rows 35 262 76 168 145 48 64 128 256), losses := [] }

theorem u2544 : Upper (D 8) (R 8) [34,260,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2544 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2545 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 168 145 96 113 177 305), lower := (rows 35 262 76 168 145 96 64 128 256), losses := [] }

theorem u2545 : Upper (D 8) (R 8) [34,260,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2546 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 168 208 33 113 177 305), lower := (rows 35 262 76 168 208 33 64 128 256), losses := [] }

theorem u2546 : Upper (D 8) (R 8) [34,260,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2547 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 76 168 208 48 97 161 289), lower := (rows 35 262 76 168 208 48 64 128 256), losses := [] }

theorem u2547 : Upper (D 8) (R 8) [34,260,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2547 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0)], upper := (rows 35 262 100 25 152 33 224 224 480), lower := (rows 35 262 100 25 152 33 64 128 256), losses := [] }

theorem u2548 : Upper (D 8) (R 8) [34,260,96,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 25 152 96 225 161 417), lower := (rows 35 262 100 25 152 96 64 128 256), losses := [] }

theorem u2549 : Upper (D 8) (R 8) [34,260,96,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 25 152 160 97 225 353), lower := (rows 35 262 100 25 152 160 64 128 256), losses := [] }

theorem u2550 : Upper (D 8) (R 8) [34,260,96,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2551 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 25 176 33 200 200 456), lower := (rows 35 262 100 25 176 33 64 128 256), losses := [] }

theorem u2551 : Upper (D 8) (R 8) [34,260,96,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2552 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 262 100 25 176 40 193 193 449), lower := (rows 35 262 100 25 176 40 64 128 256), losses := [] }

theorem u2552 : Upper (D 8) (R 8) [34,260,96,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2552 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 25 176 96 201 137 393), lower := (rows 35 262 100 25 176 96 64 128 256), losses := [] }

theorem u2553 : Upper (D 8) (R 8) [34,260,96,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 25 176 160 73 201 329), lower := (rows 35 262 100 25 176 160 64 128 256), losses := [] }

theorem u2554 : Upper (D 8) (R 8) [34,260,96,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2555 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 25 208 33 232 168 424), lower := (rows 35 262 100 25 208 33 64 128 256), losses := [] }

theorem u2555 : Upper (D 8) (R 8) [34,260,96,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2556 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 100 25 208 40 225 161 417), lower := (rows 35 262 100 25 208 40 64 128 256), losses := [] }

theorem u2556 : Upper (D 8) (R 8) [34,260,96,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2556 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2557 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 35 262 100 25 208 160 105 169 297), lower := (rows 35 262 100 25 208 160 64 128 256), losses := [] }

theorem u2557 : Upper (D 8) (R 8) [34,260,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 56 145 33 200 200 456), lower := (rows 35 262 100 56 145 33 64 128 256), losses := [] }

theorem u2558 : Upper (D 8) (R 8) [34,260,96,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 262 100 56 145 40 193 193 449), lower := (rows 35 262 100 56 145 40 64 128 256), losses := [] }

theorem u2559 : Upper (D 8) (R 8) [34,260,96,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2559 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 56 145 96 201 137 393), lower := (rows 35 262 100 56 145 96 64 128 256), losses := [] }

theorem u2560 : Upper (D 8) (R 8) [34,260,96,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 56 145 160 73 201 329), lower := (rows 35 262 100 56 145 160 64 128 256), losses := [] }

theorem u2561 : Upper (D 8) (R 8) [34,260,96,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 56 152 33 193 193 449), lower := (rows 35 262 100 56 152 33 64 128 256), losses := [] }

theorem u2562 : Upper (D 8) (R 8) [34,260,96,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 56 152 96 193 129 385), lower := (rows 35 262 100 56 152 96 64 128 256), losses := [] }

theorem u2563 : Upper (D 8) (R 8) [34,260,96,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 262 100 56 152 160 65 193 321), lower := (rows 35 262 100 56 152 160 64 128 256), losses := [] }

theorem u2564 : Upper (D 8) (R 8) [34,260,96,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 56 208 33 201 137 393), lower := (rows 35 262 100 56 208 33 64 128 256), losses := [] }

theorem u2565 : Upper (D 8) (R 8) [34,260,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 100 56 208 40 193 129 385), lower := (rows 35 262 100 56 208 40 64 128 256), losses := [] }

theorem u2566 : Upper (D 8) (R 8) [34,260,96,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2566 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 56 208 160 73 137 265), lower := (rows 35 262 100 56 208 160 64 128 256), losses := [] }

theorem u2567 : Upper (D 8) (R 8) [34,260,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 88 145 33 232 168 424), lower := (rows 35 262 100 88 145 33 64 128 256), losses := [] }

theorem u2568 : Upper (D 8) (R 8) [34,260,96,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 262 100 88 145 40 225 161 417), lower := (rows 35 262 100 88 145 40 64 128 256), losses := [] }

theorem u2569 : Upper (D 8) (R 8) [34,260,96,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2569 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 41, camps := [], pairs := [(2,0)], upper := (rows 35 262 100 88 145 160 105 169 297), lower := (rows 35 262 100 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 262 100 124 176 160 64 160 256) }] }

theorem u2570 : Upper (D 8) (R 8) [34,260,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 88 176 33 201 137 393), lower := (rows 35 262 100 88 176 33 64 128 256), losses := [] }

theorem u2571 : Upper (D 8) (R 8) [34,260,96,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 100 88 176 40 193 129 385), lower := (rows 35 262 100 88 176 40 64 128 256), losses := [] }

theorem u2572 : Upper (D 8) (R 8) [34,260,96,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2572 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 262 100 88 176 160 73 137 265), lower := (rows 35 262 100 88 176 160 64 128 256), losses := [] }

theorem u2573 : Upper (D 8) (R 8) [34,260,96,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2574 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 137 176 33 88 216 344), lower := (rows 35 262 100 137 176 33 64 128 256), losses := [] }

theorem u2574 : Upper (D 8) (R 8) [34,260,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2575 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 262 100 137 176 40 81 209 337), lower := (rows 35 262 100 137 176 40 64 128 256), losses := [] }

theorem u2575 : Upper (D 8) (R 8) [34,260,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2575 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 262 100 137 176 48 73 201 329), lower := (rows 35 262 100 137 176 48 64 128 256), losses := [] }

theorem u2576 : Upper (D 8) (R 8) [34,260,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2576 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 137 176 96 89 153 281), lower := (rows 35 262 100 137 176 96 64 128 256), losses := [] }

theorem u2577 : Upper (D 8) (R 8) [34,260,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 100 137 208 33 120 184 312), lower := (rows 35 262 100 137 208 33 64 128 256), losses := [] }

theorem u2578 : Upper (D 8) (R 8) [34,260,96,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 262 100 137 208 40 113 177 305), lower := (rows 35 262 100 137 208 40 64 128 256), losses := [] }

theorem u2579 : Upper (D 8) (R 8) [34,260,96,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2579 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P08
