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

def b540 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 304, targets := 129 },{ cop := 2, region := 97, targets := 2 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,7)], upper := (rows 37 74 134 152 304 96 65 129 258), lower := (rows 37 74 134 152 304 96 65 129 256), losses := [] }

theorem u540 : Upper (D 7) (R 7) [36,72,130,144,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 377, targets := 2 },{ cop := 7, region := 4, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 74 134 152 304 96 65 130 257), lower := (rows 37 74 134 152 304 96 65 130 256), losses := [] }

theorem u541 : Upper (D 7) (R 7) [36,72,130,144,288,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 129 },{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1),(4,0),(4,7)], upper := (rows 37 74 134 168 336 48 65 129 258), lower := (rows 37 74 134 168 336 48 65 129 256), losses := [] }

theorem u542 : Upper (D 7) (R 7) [36,72,130,160,320,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b542 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 132, targets := 97 }], pairs := [(2,0),(2,5),(2,6)], upper := (rows 37 74 134 168 336 48 65 130 257), lower := (rows 37 74 134 168 336 48 65 130 256), losses := [] }

theorem u543 : Upper (D 7) (R 7) [36,72,130,160,320,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b543 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 132, targets := 98 }], pairs := [(2,1),(2,5),(2,6)], upper := (rows 37 74 148 168 81 34 320 129 258), lower := (rows 37 74 148 168 81 34 320 129 256), losses := [] }

theorem u544 : Upper (D 7) (R 7) [36,72,144,160,65,2,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b544 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 148 168 81 34 320 130 257), lower := (rows 37 74 148 168 81 34 320 130 256), losses := [] }

theorem u545 : Upper (D 7) (R 7) [36,72,144,160,65,2,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b545 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 336, targets := 162 },{ cop := 3, region := 341, targets := 2 }], pairs := [(0,1),(4,1),(4,5),(4,7)], upper := (rows 37 74 148 168 273 34 65 130 320), lower := (rows 37 74 148 168 273 34 65 130 256), losses := [] }

theorem u546 : Upper (D 7) (R 7) [36,72,144,160,257,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 196, targets := 34 },{ cop := 6, region := 170, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 37 74 148 168 273 34 65 192 258), lower := (rows 37 74 148 168 273 34 65 192 256), losses := [] }

theorem u547 : Upper (D 7) (R 7) [36,72,144,160,257,2,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 237, targets := 2 },{ cop := 1, region := 272, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 74 148 168 274 96 65 129 258), lower := (rows 37 74 148 168 274 96 65 129 256), losses := [] }

theorem u548 : Upper (D 7) (R 7) [36,72,144,160,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 132, targets := 97 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,6)], upper := (rows 37 74 148 168 274 96 65 130 257), lower := (rows 37 74 148 168 274 96 65 130 256), losses := [] }

theorem u549 : Upper (D 7) (R 7) [36,72,144,160,258,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 129 },{ cop := 0, region := 136, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(3,1),(3,6),(4,0),(4,7)], upper := (rows 37 74 148 168 336 34 65 129 258), lower := (rows 37 74 148 168 336 34 65 129 256), losses := [] }

theorem u550 : Upper (D 7) (R 7) [36,72,144,160,320,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 336, targets := 162 },{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 74 148 168 336 34 65 130 257), lower := (rows 37 74 148 168 336 34 65 130 256), losses := [] }

theorem u551 : Upper (D 7) (R 7) [36,72,144,160,320,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 74 196 168 273 34 80 129 258), lower := (rows 37 74 196 168 273 34 80 129 256), losses := [] }

theorem u552 : Upper (D 7) (R 7) [36,72,192,160,257,2,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b552 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 74 196 168 273 34 80 130 257), lower := (rows 37 74 196 168 273 34 80 130 256), losses := [] }

theorem u553 : Upper (D 7) (R 7) [36,72,192,160,257,2,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b553 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 98, targets := 129 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 74 196 265 146 34 96 129 272), lower := (rows 37 74 196 265 146 34 96 129 256), losses := [] }

theorem u554 : Upper (D 7) (R 7) [36,72,192,257,130,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 265 146 34 96 144 257), lower := (rows 37 74 196 265 146 34 96 144 256), losses := [] }

theorem u555 : Upper (D 7) (R 7) [36,72,192,257,130,2,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b555 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 4, region := 296, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 37 74 196 280 146 34 65 129 288), lower := (rows 37 74 196 280 146 34 65 129 256), losses := [] }

theorem u556 : Upper (D 7) (R 7) [36,72,192,272,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(4,0)], upper := (rows 37 74 196 280 146 34 65 160 257), lower := (rows 37 74 196 280 146 34 65 160 256), losses := [] }

theorem u557 : Upper (D 7) (R 7) [36,72,192,272,130,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 196 280 176 34 65 129 258), lower := (rows 37 74 196 280 176 34 65 129 256), losses := [] }

theorem u558 : Upper (D 7) (R 7) [36,72,192,272,160,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 333, targets := 2 },{ cop := 1, region := 132, targets := 1 }], pairs := [(0,1),(2,0),(2,1),(3,1)], upper := (rows 37 74 196 280 176 34 65 130 257), lower := (rows 37 74 196 280 176 34 65 130 256), losses := [] }

theorem u559 : Upper (D 7) (R 7) [36,72,192,272,160,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 74 196 296 146 34 65 129 272), lower := (rows 37 74 196 296 146 34 65 129 256), losses := [] }

theorem u560 : Upper (D 7) (R 7) [36,72,192,288,130,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 74 196 296 146 34 65 144 257), lower := (rows 37 74 196 296 146 34 65 144 256), losses := [] }

theorem u561 : Upper (D 7) (R 7) [36,72,192,288,130,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b561 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 298, targets := 1 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 74 196 392 19 34 65 144 288), lower := (rows 37 74 196 392 19 34 65 144 256), losses := [] }

theorem u562 : Upper (D 7) (R 7) [36,72,192,384,3,2,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b562 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 424, targets := 65 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 37 74 196 392 19 34 65 160 272), lower := (rows 37 74 196 392 19 34 65 160 256), losses := [] }

theorem u563 : Upper (D 7) (R 7) [36,72,192,384,3,2,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 138 274 48 192 129 320), lower := (rows 37 98 13 138 274 48 192 129 256), losses := [] }

theorem u564 : Upper (D 7) (R 7) [36,96,9,130,258,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b564 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 13 138 274 48 192 192 257), lower := (rows 37 98 13 138 274 48 192 192 256), losses := [] }

theorem u565 : Upper (D 7) (R 7) [36,96,9,130,258,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 328 146 160 66 129 272), lower := (rows 37 98 13 328 146 160 66 129 256), losses := [] }

theorem u566 : Upper (D 7) (R 7) [36,96,9,320,130,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 13 328 146 160 66 144 257), lower := (rows 37 98 13 328 146 160 66 144 256), losses := [] }

theorem u567 : Upper (D 7) (R 7) [36,96,9,320,130,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b567 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 98 14 152 336 33 192 129 258), lower := (rows 37 98 14 152 336 33 192 129 256), losses := [] }

theorem u568 : Upper (D 7) (R 7) [36,96,10,144,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 194, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 152 336 33 192 130 257), lower := (rows 37 98 14 152 336 33 192 130 256), losses := [] }

theorem u569 : Upper (D 7) (R 7) [36,96,10,144,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 98 14 328 146 160 65 129 272), lower := (rows 37 98 14 328 146 160 65 129 256), losses := [] }

theorem u570 : Upper (D 7) (R 7) [36,96,10,320,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 14 328 146 160 65 144 257), lower := (rows 37 98 14 328 146 160 65 144 256), losses := [] }

theorem u571 : Upper (D 7) (R 7) [36,96,10,320,130,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b571 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 290, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 37 98 28 73 146 288 192 129 258), lower := (rows 37 98 28 73 146 288 192 129 256), losses := [] }

theorem u572 : Upper (D 7) (R 7) [36,96,24,65,130,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b572 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 289, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 28 73 146 288 192 130 257), lower := (rows 37 98 28 73 146 288 192 130 256), losses := [] }

theorem u573 : Upper (D 7) (R 7) [36,96,24,65,130,256,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b573 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 28 73 400 34 192 129 258), lower := (rows 37 98 28 73 400 34 192 129 256), losses := [] }

theorem u574 : Upper (D 7) (R 7) [36,96,24,65,384,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 242, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,0)], upper := (rows 37 98 28 73 400 34 192 130 257), lower := (rows 37 98 28 73 400 34 192 130 256), losses := [{ target := 1, region := (rows 35 0 222 138 208 32 208 128 427), good := (rows 293 381 348 349 476 301 476 477 256) }] }

theorem u575 : Upper (D 7) (R 7) [36,96,24,65,384,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 306, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 37 98 28 137 336 34 192 129 258), lower := (rows 37 98 28 137 336 34 192 129 256), losses := [] }

theorem u576 : Upper (D 7) (R 7) [36,96,24,129,320,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 137 336 34 192 130 257), lower := (rows 37 98 28 137 336 34 192 130 256), losses := [] }

theorem u577 : Upper (D 7) (R 7) [36,96,24,129,320,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 98 28 138 208 288 65 129 258), lower := (rows 37 98 28 138 208 288 65 129 256), losses := [] }

theorem u578 : Upper (D 7) (R 7) [36,96,24,130,192,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b578 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 28 138 208 288 65 130 257), lower := (rows 37 98 28 138 208 288 65 130 256), losses := [] }

theorem u579 : Upper (D 7) (R 7) [36,96,24,130,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b579 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 28 138 336 33 192 129 258), lower := (rows 37 98 28 138 336 33 192 129 256), losses := [] }

theorem u580 : Upper (D 7) (R 7) [36,96,24,130,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 138 336 33 192 130 257), lower := (rows 37 98 28 138 336 33 192 130 256), losses := [] }

theorem u581 : Upper (D 7) (R 7) [36,96,24,130,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 310, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 98 28 200 400 34 65 129 258), lower := (rows 37 98 28 200 400 34 65 129 256), losses := [] }

theorem u582 : Upper (D 7) (R 7) [36,96,24,192,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 170, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 37 98 28 200 400 34 65 130 257), lower := (rows 37 98 28 200 400 34 65 130 256), losses := [] }

theorem u583 : Upper (D 7) (R 7) [36,96,24,192,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 322, targets := 1 }], pairs := [(0,1),(0,6),(1,0)], upper := (rows 37 98 76 25 146 160 320 129 258), lower := (rows 37 98 76 25 146 160 320 129 256), losses := [] }

theorem u584 : Upper (D 7) (R 7) [36,96,72,17,130,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b584 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 324, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 25 146 160 320 130 257), lower := (rows 37 98 76 25 146 160 320 130 256), losses := [] }

theorem u585 : Upper (D 7) (R 7) [36,96,72,17,130,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b585 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 37 98 76 26 400 160 65 129 258), lower := (rows 37 98 76 26 400 160 65 129 256), losses := [] }

theorem u586 : Upper (D 7) (R 7) [36,96,72,18,384,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 98 76 26 400 160 65 130 257), lower := (rows 37 98 76 26 400 160 65 130 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 77 128 333), good := (rows 357 352 333 381 432 160 321 160 256) }] }

theorem u587 : Upper (D 7) (R 7) [36,96,72,18,384,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 37 98 76 138 145 48 320 129 258), lower := (rows 37 98 76 138 145 48 320 129 256), losses := [] }

theorem u588 : Upper (D 7) (R 7) [36,96,72,130,129,16,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b588 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 98 76 138 145 48 320 130 257), lower := (rows 37 98 76 138 145 48 320 130 256), losses := [] }

theorem u589 : Upper (D 7) (R 7) [36,96,72,130,129,16,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b589 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 138 145 288 65 130 272), lower := (rows 37 98 76 138 145 288 65 130 256), losses := [] }

theorem u590 : Upper (D 7) (R 7) [36,96,72,130,129,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b590 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 76 138 145 288 65 144 258), lower := (rows 37 98 76 138 145 288 65 144 256), losses := [] }

theorem u591 : Upper (D 7) (R 7) [36,96,72,130,129,256,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b591 [(5,8),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 272, targets := 65 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(4,0),(4,6)], upper := (rows 37 98 76 138 400 48 65 129 258), lower := (rows 37 98 76 138 400 48 65 129 256), losses := [] }

theorem u592 : Upper (D 7) (R 7) [36,96,72,130,384,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b592 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 138 400 48 65 130 257), lower := (rows 37 98 76 138 400 48 65 130 256), losses := [] }

theorem u593 : Upper (D 7) (R 7) [36,96,72,130,384,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b593 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 76 265 145 34 192 130 272), lower := (rows 37 98 76 265 145 34 192 130 256), losses := [] }

theorem u594 : Upper (D 7) (R 7) [36,96,72,257,129,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 37 98 76 265 145 34 192 144 258), lower := (rows 37 98 76 265 145 34 192 144 256), losses := [] }

theorem u595 : Upper (D 7) (R 7) [36,96,72,257,129,2,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b595 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(1,7),(4,6)], upper := (rows 37 98 76 266 145 160 65 130 272), lower := (rows 37 98 76 266 145 160 65 130 256), losses := [{ target := 6, region := (rows 5 2 4 8 20 190 0 138 277), good := (rows 309 162 445 426 433 160 257 162 256) }] }

theorem u596 : Upper (D 7) (R 7) [36,96,72,258,129,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 268, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 266 145 160 65 144 258), lower := (rows 37 98 76 266 145 160 65 144 256), losses := [] }

theorem u597 : Upper (D 7) (R 7) [36,96,72,258,129,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b597 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 4, region := 264, targets := 65 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 37 98 76 266 146 160 65 129 272), lower := (rows 37 98 76 266 146 160 65 129 256), losses := [] }

theorem u598 : Upper (D 7) (R 7) [36,96,72,258,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 76 266 146 160 65 144 257), lower := (rows 37 98 76 266 146 160 65 144 256), losses := [] }

theorem u599 : Upper (D 7) (R 7) [36,96,72,258,130,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b599 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P07
