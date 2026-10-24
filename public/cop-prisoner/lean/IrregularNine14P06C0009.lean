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

def b540 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 100 25 276 40 66 192 257), lower := (rows 35 134 100 25 276 40 66 192 256), losses := [] }

theorem u540 : Upper (D 6) (R 6) [34,132,96,17,260,8,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b540 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 358, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 262 25 28 96 96 129 320), lower := (rows 35 134 262 25 28 96 96 129 256), losses := [] }

theorem u541 : Upper (D 6) (R 6) [34,132,258,17,12,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 134 262 25 28 96 96 192 257), lower := (rows 35 134 262 25 28 96 96 192 256), losses := [] }

theorem u542 : Upper (D 6) (R 6) [34,132,258,17,12,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 134 262 25 84 40 65 160 320), lower := (rows 35 134 262 25 84 40 65 160 256), losses := [] }

theorem u543 : Upper (D 6) (R 6) [34,132,258,17,68,8,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b543 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 262 25 84 40 65 192 288), lower := (rows 35 134 262 25 84 40 65 192 256), losses := [] }

theorem u544 : Upper (D 6) (R 6) [34,132,258,17,68,8,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b544 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 25 84 40 96 129 320), lower := (rows 35 134 262 25 84 40 96 129 256), losses := [] }

theorem u545 : Upper (D 6) (R 6) [34,132,258,17,68,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b545 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 260, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 134 262 25 84 40 96 192 257), lower := (rows 35 134 262 25 84 40 96 192 256), losses := [] }

theorem u546 : Upper (D 6) (R 6) [34,132,258,17,68,8,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b546 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 262 44 88 96 65 129 272), lower := (rows 35 134 262 44 88 96 65 129 256), losses := [] }

theorem u547 : Upper (D 6) (R 6) [34,132,258,36,72,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 134 262 44 88 96 65 144 257), lower := (rows 35 134 262 44 88 96 65 144 256), losses := [] }

theorem u548 : Upper (D 6) (R 6) [34,132,258,36,72,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b548 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 134 268 26 21 96 65 160 320), lower := (rows 35 134 268 26 21 96 65 160 256), losses := [] }

theorem u549 : Upper (D 6) (R 6) [34,132,264,18,5,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 268 26 21 96 65 192 288), lower := (rows 35 134 268 26 21 96 65 192 256), losses := [] }

theorem u550 : Upper (D 6) (R 6) [34,132,264,18,5,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 134 268 26 21 96 96 129 320), lower := (rows 35 134 268 26 21 96 96 129 256), losses := [] }

theorem u551 : Upper (D 6) (R 6) [34,132,264,18,5,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 134 268 26 21 96 96 192 257), lower := (rows 35 134 268 26 21 96 96 192 256), losses := [] }

theorem u552 : Upper (D 6) (R 6) [34,132,264,18,5,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 268 26 52 96 65 129 320), lower := (rows 35 134 268 26 52 96 65 129 256), losses := [] }

theorem u553 : Upper (D 6) (R 6) [34,132,264,18,36,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 134 268 26 52 96 65 192 257), lower := (rows 35 134 268 26 52 96 65 192 256), losses := [] }

theorem u554 : Upper (D 6) (R 6) [34,132,264,18,36,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 134 268 26 84 33 96 129 320), lower := (rows 35 134 268 26 84 33 96 129 256), losses := [] }

theorem u555 : Upper (D 6) (R 6) [34,132,264,18,68,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 268 26 84 33 96 192 257), lower := (rows 35 134 268 26 84 33 96 192 256), losses := [] }

theorem u556 : Upper (D 6) (R 6) [34,132,264,18,68,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 268 26 84 96 65 129 288), lower := (rows 35 134 268 26 84 96 65 129 256), losses := [{ target := 0, region := (rows 0 130 205 9 112 112 64 128 377), good := (rows 318 134 268 318 372 372 380 398 256) }] }

theorem u557 : Upper (D 6) (R 6) [34,132,264,18,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 134 268 26 84 96 65 160 257), lower := (rows 35 134 268 26 84 96 65 160 256), losses := [] }

theorem u558 : Upper (D 6) (R 6) [34,132,264,18,68,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 155, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 292 25 28 96 66 129 320), lower := (rows 35 134 292 25 28 96 66 129 256), losses := [] }

theorem u559 : Upper (D 6) (R 6) [34,132,288,17,12,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 134 292 25 28 96 66 192 257), lower := (rows 35 134 292 25 28 96 66 192 256), losses := [] }

theorem u560 : Upper (D 6) (R 6) [34,132,288,17,12,64,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 292 26 84 96 65 129 264), lower := (rows 35 134 292 26 84 96 65 129 256), losses := [] }

theorem u561 : Upper (D 6) (R 6) [34,132,288,18,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 138, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 134 292 26 84 96 65 136 257), lower := (rows 35 134 292 26 84 96 65 136 256), losses := [] }

theorem u562 : Upper (D 6) (R 6) [34,132,288,18,68,64,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b562 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 260, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 134 324 25 28 96 66 129 288), lower := (rows 35 134 324 25 28 96 66 129 256), losses := [] }

theorem u563 : Upper (D 6) (R 6) [34,132,320,17,12,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 134 324 25 28 96 66 160 257), lower := (rows 35 134 324 25 28 96 66 160 256), losses := [] }

theorem u564 : Upper (D 6) (R 6) [34,132,320,17,12,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 130, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 138 70 25 336 36 96 129 260), lower := (rows 35 138 70 25 336 36 96 129 256), losses := [] }

theorem u565 : Upper (D 6) (R 6) [34,136,66,17,320,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 138 70 25 336 36 96 132 257), lower := (rows 35 138 70 25 336 36 96 132 256), losses := [] }

theorem u566 : Upper (D 6) (R 6) [34,136,66,17,320,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 100 25 274 36 65 132 320), lower := (rows 35 138 100 25 274 36 65 132 256), losses := [] }

theorem u567 : Upper (D 6) (R 6) [34,136,96,17,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 138 100 25 274 36 65 192 260), lower := (rows 35 138 100 25 274 36 65 192 256), losses := [] }

theorem u568 : Upper (D 6) (R 6) [34,136,96,17,258,4,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 100 25 336 36 66 129 260), lower := (rows 35 138 100 25 336 36 66 129 256), losses := [] }

theorem u569 : Upper (D 6) (R 6) [34,136,96,17,320,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 100 25 336 36 66 132 257), lower := (rows 35 138 100 25 336 36 66 132 256), losses := [] }

theorem u570 : Upper (D 6) (R 6) [34,136,96,17,320,4,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 100 88 274 36 65 129 260), lower := (rows 35 138 100 88 274 36 65 129 256), losses := [{ target := 0, region := (rows 0 2 76 72 19 110 64 128 366), good := (rows 306 446 364 380 306 292 380 144 256) }] }

theorem u571 : Upper (D 6) (R 6) [34,136,96,80,258,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 100 88 274 36 65 132 257), lower := (rows 35 138 100 88 274 36 65 132 256), losses := [] }

theorem u572 : Upper (D 6) (R 6) [34,136,96,80,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 138 261 25 22 96 68 160 320), lower := (rows 35 138 261 25 22 96 68 160 256), losses := [] }

theorem u573 : Upper (D 6) (R 6) [34,136,257,17,6,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 138 261 25 22 96 68 192 288), lower := (rows 35 138 261 25 22 96 68 192 256), losses := [] }

theorem u574 : Upper (D 6) (R 6) [34,136,257,17,6,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 138 262 13 81 96 68 144 288), lower := (rows 35 138 262 13 81 96 68 144 256), losses := [] }

theorem u575 : Upper (D 6) (R 6) [34,136,258,5,65,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b575 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 138 262 13 81 96 68 160 272), lower := (rows 35 138 262 13 81 96 68 160 256), losses := [] }

theorem u576 : Upper (D 6) (R 6) [34,136,258,5,65,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 35 138 276 13 22 96 96 129 320), lower := (rows 35 138 276 13 22 96 96 129 256), losses := [] }

theorem u577 : Upper (D 6) (R 6) [34,136,272,5,6,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 284, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 35 138 276 13 22 96 96 192 257), lower := (rows 35 138 276 13 22 96 96 192 256), losses := [] }

theorem u578 : Upper (D 6) (R 6) [34,136,272,5,6,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 44 328 22 33 68 129 272), lower := (rows 35 194 44 328 22 33 68 129 256), losses := [] }

theorem u579 : Upper (D 6) (R 6) [34,192,40,320,6,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 194 44 328 22 33 68 144 257), lower := (rows 35 194 44 328 22 33 68 144 256), losses := [] }

theorem u580 : Upper (D 6) (R 6) [34,192,40,320,6,1,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b580 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 194 76 25 274 36 96 129 260), lower := (rows 35 194 76 25 274 36 96 129 256), losses := [] }

theorem u581 : Upper (D 6) (R 6) [34,192,72,17,258,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 35 194 76 25 274 36 96 132 257), lower := (rows 35 194 76 25 274 36 96 132 256), losses := [] }

theorem u582 : Upper (D 6) (R 6) [34,192,72,17,258,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 194 76 26 273 36 96 129 260), lower := (rows 35 194 76 26 273 36 96 129 256), losses := [] }

theorem u583 : Upper (D 6) (R 6) [34,192,72,18,257,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 35 194 76 26 273 36 96 132 257), lower := (rows 35 194 76 26 273 36 96 132 256), losses := [] }

theorem u584 : Upper (D 6) (R 6) [34,192,72,18,257,4,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 76 26 304 36 65 129 260), lower := (rows 35 194 76 26 304 36 65 129 256), losses := [] }

theorem u585 : Upper (D 6) (R 6) [34,192,72,18,288,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 4 },{ cop := 0, region := 280, targets := 64 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 26 304 36 65 132 257), lower := (rows 35 194 76 26 304 36 65 132 256), losses := [] }

theorem u586 : Upper (D 6) (R 6) [34,192,72,18,288,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 76 56 274 36 65 129 260), lower := (rows 35 194 76 56 274 36 65 129 256), losses := [] }

theorem u587 : Upper (D 6) (R 6) [34,192,72,48,258,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 280, targets := 4 },{ cop := 0, region := 280, targets := 64 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 76 56 274 36 65 132 257), lower := (rows 35 194 76 56 274 36 65 132 256), losses := [] }

theorem u588 : Upper (D 6) (R 6) [34,192,72,48,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 300, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 194 76 266 21 36 65 144 288), lower := (rows 35 194 76 266 21 36 65 144 256), losses := [] }

theorem u589 : Upper (D 6) (R 6) [34,192,72,258,5,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b589 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 348, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 194 76 266 21 36 65 160 272), lower := (rows 35 194 76 266 21 36 65 160 256), losses := [] }

theorem u590 : Upper (D 6) (R 6) [34,192,72,258,5,4,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 268, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 35 194 76 266 21 48 96 129 260), lower := (rows 35 194 76 266 21 48 96 129 256), losses := [] }

theorem u591 : Upper (D 6) (R 6) [34,192,72,258,5,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b591 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 194 76 266 21 48 96 132 257), lower := (rows 35 194 76 266 21 48 96 132 256), losses := [] }

theorem u592 : Upper (D 6) (R 6) [34,192,72,258,5,16,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b592 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 76 296 21 36 65 130 272), lower := (rows 35 194 76 296 21 36 65 130 256), losses := [] }

theorem u593 : Upper (D 6) (R 6) [34,192,72,288,5,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 300, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 194 76 296 21 36 65 144 258), lower := (rows 35 194 76 296 21 36 65 144 256), losses := [] }

theorem u594 : Upper (D 6) (R 6) [34,192,72,288,5,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b594 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 316, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 76 296 22 36 65 129 272), lower := (rows 35 194 76 296 22 36 65 129 256), losses := [] }

theorem u595 : Upper (D 6) (R 6) [34,192,72,288,6,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 76 296 22 36 65 144 257), lower := (rows 35 194 76 296 22 36 65 144 256), losses := [] }

theorem u596 : Upper (D 6) (R 6) [34,192,72,288,6,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b596 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 194 100 25 274 36 65 132 264), lower := (rows 35 194 100 25 274 36 65 132 256), losses := [] }

theorem u597 : Upper (D 6) (R 6) [34,192,96,17,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 308, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 194 100 25 274 36 65 136 260), lower := (rows 35 194 100 25 274 36 65 136 256), losses := [] }

theorem u598 : Upper (D 6) (R 6) [34,192,96,17,258,4,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b598 [(7,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 194 100 26 273 36 65 132 264), lower := (rows 35 194 100 26 273 36 65 132 256), losses := [] }

theorem u599 : Upper (D 6) (R 6) [34,192,96,18,257,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P06
