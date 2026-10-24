import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 114, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(1,7),(3,6),(4,7)], upper := (rows 7 42 196 265 81 48 320 160 416), lower := (rows 7 42 196 265 81 48 320 128 256), losses := [] }

theorem u540 : Upper (D 9) (R 9) [6,40,192,257,65,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b540 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 80, targets := 416 },{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(4,5),(4,7),(4,8)], upper := (rows 7 42 196 265 81 160 80 416 288), lower := (rows 7 42 196 265 81 160 80 128 256), losses := [] }

theorem u541 : Upper (D 9) (R 9) [6,40,192,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b541 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 396, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 1 }], pairs := [(1,6),(2,0),(2,5),(3,5),(3,6)], upper := (rows 7 42 196 265 81 160 96 400 272), lower := (rows 7 42 196 265 81 160 96 128 256), losses := [] }

theorem u542 : Upper (D 9) (R 9) [6,40,192,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b542 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 160 },{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 164, targets := 1 }], pairs := [(1,6),(2,0),(3,6),(4,5),(4,7)], upper := (rows 7 42 196 265 81 160 320 176 304), lower := (rows 7 42 196 265 81 160 320 128 256), losses := [] }

theorem u543 : Upper (D 9) (R 9) [6,40,192,257,65,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b543 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 272, camps := [{ cop := 6, region := 436, targets := 1 },{ cop := 2, region := 48, targets := 256 },{ cop := 4, region := 388, targets := 32 }], pairs := [(1,0),(2,0),(2,5),(4,0),(4,8)], upper := (rows 7 42 196 265 112 160 65 400 272), lower := (rows 7 42 196 265 112 160 65 128 256), losses := [{ target := 0, region := (rows 0 10 84 8 84 253 64 213 341), good := (rows 438 42 500 426 500 160 500 160 256) }] }

theorem u544 : Upper (D 9) (R 9) [6,40,192,257,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 84, targets := 257 }], pairs := [(2,0),(2,8),(4,0),(4,8)], upper := (rows 7 42 196 265 112 160 80 385 257), lower := (rows 7 42 196 265 112 160 80 128 256), losses := [] }

theorem u545 : Upper (D 9) (R 9) [6,40,192,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b545 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 257 }], pairs := [(1,8),(3,7),(4,0),(4,7),(4,8)], upper := (rows 7 42 196 265 112 160 320 145 273), lower := (rows 7 42 196 265 112 160 320 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 18 32 329 0 257), good := (rows 351 122 68 329 112 32 320 0 320) },{ target := 8, region := (rows 1 10 4 8 20 173 64 129 0), good := (rows 183 42 244 171 112 160 64 160 0) }] }

theorem u546 : Upper (D 9) (R 9) [6,40,192,257,96,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b546 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 3, region := 114, targets := 128 },{ cop := 3, region := 98, targets := 256 }], pairs := [(1,7),(1,8),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 265 304 96 65 144 400), lower := (rows 7 42 196 265 304 96 65 128 256), losses := [] }

theorem u547 : Upper (D 9) (R 9) [6,40,192,257,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b547 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 196 265 304 96 80 129 385), lower := (rows 7 42 196 265 304 96 80 128 256), losses := [] }

theorem u548 : Upper (D 9) (R 9) [6,40,192,257,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b548 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 265 304 96 192 145 273), lower := (rows 7 42 196 265 304 96 192 128 256), losses := [] }

theorem u549 : Upper (D 9) (R 9) [6,40,192,257,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b549 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 3, region := 114, targets := 128 }], pairs := [(0,8),(1,7),(2,8),(4,7)], upper := (rows 7 42 196 265 336 48 65 160 416), lower := (rows 7 42 196 265 336 48 65 128 256), losses := [] }

theorem u550 : Upper (D 9) (R 9) [6,40,192,257,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b550 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 42 196 265 336 48 96 129 385), lower := (rows 7 42 196 265 336 48 96 128 256), losses := [] }

theorem u551 : Upper (D 9) (R 9) [6,40,192,257,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b551 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 265 336 48 192 161 289), lower := (rows 7 42 196 265 336 48 192 128 256), losses := [] }

theorem u552 : Upper (D 9) (R 9) [6,40,192,257,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b552 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 160 },{ cop := 6, region := 436, targets := 1 },{ cop := 4, region := 164, targets := 256 }], pairs := [(2,0),(2,8),(4,0),(4,5),(4,7)], upper := (rows 7 42 196 265 336 160 65 176 304), lower := (rows 7 42 196 265 336 160 65 128 256), losses := [] }

theorem u553 : Upper (D 9) (R 9) [6,40,192,257,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b553 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 7 42 196 265 336 160 80 161 289), lower := (rows 7 42 196 265 336 160 80 128 256), losses := [] }

theorem u554 : Upper (D 9) (R 9) [6,40,192,257,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b554 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 68, targets := 257 }], pairs := [(2,0),(2,8),(3,7),(4,0),(4,7)], upper := (rows 7 42 196 265 336 160 96 145 273), lower := (rows 7 42 196 265 336 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 164 8 24 164 231 128 256), good := (rows 102 126 228 344 336 228 100 228 256) },{ target := 7, region := (rows 1 2 4 9 19 32 98 0 265), good := (rows 351 378 68 281 336 96 96 0 256) }] }

theorem u555 : Upper (D 9) (R 9) [6,40,192,257,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b555 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 80, targets := 416 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(4,5),(4,7),(4,8)], upper := (rows 7 42 196 280 81 160 65 416 288), lower := (rows 7 42 196 280 81 160 65 128 256), losses := [] }

theorem u556 : Upper (D 9) (R 9) [6,40,192,272,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b556 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 396, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 1 }], pairs := [(1,6),(2,0),(2,5),(3,5),(3,6)], upper := (rows 7 42 196 280 81 160 96 385 257), lower := (rows 7 42 196 280 81 160 96 128 256), losses := [] }

theorem u557 : Upper (D 9) (R 9) [6,40,192,272,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b557 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 164, targets := 256 }], pairs := [(0,8),(1,6),(1,8),(2,8),(3,6)], upper := (rows 7 42 196 280 81 160 320 161 289), lower := (rows 7 42 196 280 81 160 320 128 256), losses := [{ target := 8, region := (rows 9 10 20 8 16 191 64 155 0), good := (rows 167 171 228 191 245 160 64 160 0) }] }

theorem u558 : Upper (D 9) (R 9) [6,40,192,272,65,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b558 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 48, targets := 257 }], pairs := [(0,5),(2,5),(3,5),(4,0),(4,8)], upper := (rows 7 42 196 280 112 160 65 385 257), lower := (rows 7 42 196 280 112 160 65 128 256), losses := [{ target := 5, region := (rows 3 2 87 24 16 0 67 195 323), good := (rows 455 463 452 284 476 128 453 128 256) }] }

theorem u559 : Upper (D 9) (R 9) [6,40,192,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b559 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 48, targets := 257 }], pairs := [(0,5),(2,5),(3,7),(4,0),(4,8)], upper := (rows 7 42 196 280 112 160 320 129 257), lower := (rows 7 42 196 280 112 160 320 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 18 32 329 0 257), good := (rows 351 122 68 344 112 32 320 0 320) }] }

theorem u560 : Upper (D 9) (R 9) [6,40,192,272,96,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b560 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 328 145 33 80 416 288), lower := (rows 7 42 196 328 145 33 80 128 256), losses := [] }

theorem u561 : Upper (D 9) (R 9) [6,40,192,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b561 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 4, region := 100, targets := 256 }], pairs := [(1,7),(2,8),(3,7),(4,5),(4,6)], upper := (rows 7 42 196 328 145 33 96 400 272), lower := (rows 7 42 196 328 145 33 96 128 256), losses := [] }

theorem u562 : Upper (D 9) (R 9) [6,40,192,320,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b562 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 7 42 196 328 145 33 320 176 304), lower := (rows 7 42 196 328 145 33 320 128 256), losses := [] }

theorem u563 : Upper (D 9) (R 9) [6,40,192,320,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b563 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 68, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,6)], upper := (rows 7 42 196 328 145 48 65 416 288), lower := (rows 7 42 196 328 145 48 65 128 256), losses := [] }

theorem u564 : Upper (D 9) (R 9) [6,40,192,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b564 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 100, targets := 257 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,0),(2,8),(3,7)], upper := (rows 7 42 196 328 145 48 96 385 257), lower := (rows 7 42 196 328 145 48 96 128 256), losses := [] }

theorem u565 : Upper (D 9) (R 9) [6,40,192,320,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b565 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 42 196 328 145 48 320 161 289), lower := (rows 7 42 196 328 145 48 320 128 256), losses := [] }

theorem u566 : Upper (D 9) (R 9) [6,40,192,320,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b566 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(2,0),(2,5),(3,0),(4,0),(4,6)], upper := (rows 7 42 196 328 176 33 65 400 272), lower := (rows 7 42 196 328 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 72 50 32 64 179 307), good := (rows 406 442 204 332 432 432 460 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 97 144 272), good := (rows 71 74 196 328 476 65 65 128 256) }] }

theorem u567 : Upper (D 9) (R 9) [6,40,192,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b567 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 328 176 33 80 385 257), lower := (rows 7 42 196 328 176 33 80 128 256), losses := [] }

theorem u568 : Upper (D 9) (R 9) [6,40,192,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b568 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 7 42 196 328 176 33 320 145 273), lower := (rows 7 42 196 328 176 33 320 128 256), losses := [] }

theorem u569 : Upper (D 9) (R 9) [6,40,192,320,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 7 42 196 328 273 33 80 160 416), lower := (rows 7 42 196 328 273 33 80 128 256), losses := [] }

theorem u570 : Upper (D 9) (R 9) [6,40,192,320,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b570 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 106, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 4, region := 228, targets := 256 }], pairs := [(1,7),(2,8),(3,7),(4,5),(4,6)], upper := (rows 7 42 196 328 273 33 96 144 400), lower := (rows 7 42 196 328 273 33 96 128 256), losses := [] }

theorem u571 : Upper (D 9) (R 9) [6,40,192,320,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b571 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 328 273 33 192 176 304), lower := (rows 7 42 196 328 273 33 192 128 256), losses := [] }

theorem u572 : Upper (D 9) (R 9) [6,40,192,320,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b572 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 4, region := 106, targets := 128 }], pairs := [(0,8),(1,7),(2,8),(3,7)], upper := (rows 7 42 196 328 273 48 65 160 416), lower := (rows 7 42 196 328 273 48 65 128 256), losses := [] }

theorem u573 : Upper (D 9) (R 9) [6,40,192,320,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b573 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 328 273 48 96 129 385), lower := (rows 7 42 196 328 273 48 96 128 256), losses := [] }

theorem u574 : Upper (D 9) (R 9) [6,40,192,320,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b574 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 328 273 48 192 161 289), lower := (rows 7 42 196 328 273 48 192 128 256), losses := [] }

theorem u575 : Upper (D 9) (R 9) [6,40,192,320,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b575 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 72, targets := 160 },{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 228, targets := 256 }], pairs := [(1,6),(2,8),(3,5),(3,7),(4,6)], upper := (rows 7 42 196 328 273 160 65 176 304), lower := (rows 7 42 196 328 273 160 65 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 81 255 0 221 349), good := (rows 439 426 436 442 433 160 433 160 256) }] }

theorem u576 : Upper (D 9) (R 9) [6,40,192,320,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b576 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 7 42 196 328 273 160 80 161 289), lower := (rows 7 42 196 328 273 160 80 128 256), losses := [] }

theorem u577 : Upper (D 9) (R 9) [6,40,192,320,257,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b577 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 68, targets := 257 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,0),(2,8),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 328 273 160 96 145 273), lower := (rows 7 42 196 328 273 160 96 128 256), losses := [] }

theorem u578 : Upper (D 9) (R 9) [6,40,192,320,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b578 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(2,0),(2,5),(3,0),(4,0),(4,6)], upper := (rows 7 42 196 328 304 33 65 144 400), lower := (rows 7 42 196 328 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 72 50 32 64 179 307), good := (rows 406 442 204 332 432 432 460 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 97 144 272), good := (rows 71 74 196 328 476 65 65 128 256) }] }

theorem u579 : Upper (D 9) (R 9) [6,40,192,320,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 328 304 33 80 129 385), lower := (rows 7 42 196 328 304 33 80 128 256), losses := [] }

theorem u580 : Upper (D 9) (R 9) [6,40,192,320,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b580 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 328 304 33 192 145 273), lower := (rows 7 42 196 328 304 33 192 128 256), losses := [] }

theorem u581 : Upper (D 9) (R 9) [6,40,192,320,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b581 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r582 : Route 9 := (fun mask => (mask,id))

def c582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u582 : Upper (D 9) (R 9) [6,40,192,320,288,128,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288,128,1] 13 (by decide) (choices 1) [1,16] r582 c582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25
  · exact u26

def b583 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 328 304 160 80 129 257), lower := (rows 7 42 196 328 304 160 80 128 256), losses := [] }

theorem u583 : Upper (D 9) (R 9) [6,40,192,320,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b583 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(1,6),(1,7),(1,8),(4,0),(4,6)], upper := (rows 7 42 196 328 400 33 65 176 304), lower := (rows 7 42 196 328 400 33 65 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 127 97 0 239 367), good := (rows 439 442 436 442 400 433 433 128 256) },{ target := 7, region := (rows 1 10 4 8 16 97 97 0 256), good := (rows 103 106 100 362 272 97 97 0 256) },{ target := 8, region := (rows 1 10 4 8 16 97 97 128 0), good := (rows 103 106 228 106 144 97 97 128 0) }] }

theorem u584 : Upper (D 9) (R 9) [6,40,192,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 7 42 196 328 400 33 80 161 289), lower := (rows 7 42 196 328 400 33 80 128 256), losses := [] }

theorem u585 : Upper (D 9) (R 9) [6,40,192,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b585 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r586 : Route 9 := (fun mask => (mask,id))

def c586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u586 : Upper (D 9) (R 9) [6,40,192,320,384,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,384,1,32] 13 (by decide) (choices 1) [1,16] r586 c586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27
  · exact u28

def b587 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,8),(1,6),(2,8),(4,6)], upper := (rows 7 42 196 328 400 48 65 161 289), lower := (rows 7 42 196 328 400 48 65 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 93 127 0 193 321), good := (rows 439 58 436 442 432 48 433 128 256) }] }

theorem u587 : Upper (D 9) (R 9) [6,40,192,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b587 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(1,0),(2,0),(3,0)], upper := (rows 7 42 196 328 400 48 96 129 257), lower := (rows 7 42 196 328 400 48 96 128 256), losses := [] }

theorem u588 : Upper (D 9) (R 9) [6,40,192,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b588 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 91, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 98 164 25 88 288 65 384 384), lower := (rows 7 98 164 25 88 288 65 128 256), losses := [] }

theorem u589 : Upper (D 9) (R 9) [6,96,160,17,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b589 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 98 164 25 88 288 192 385 257), lower := (rows 7 98 164 25 88 288 192 128 256), losses := [] }

theorem u590 : Upper (D 9) (R 9) [6,96,160,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b590 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 157, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 7 98 164 25 88 288 320 129 385), lower := (rows 7 98 164 25 88 288 320 128 256), losses := [] }

theorem u591 : Upper (D 9) (R 9) [6,96,160,17,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b591 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 98 164 25 208 288 65 392 264), lower := (rows 7 98 164 25 208 288 65 128 256), losses := [] }

theorem u592 : Upper (D 9) (R 9) [6,96,160,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b592 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 164 25 208 288 72 385 257), lower := (rows 7 98 164 25 208 288 72 128 256), losses := [] }

theorem u593 : Upper (D 9) (R 9) [6,96,160,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b593 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 157, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 7 98 164 25 208 288 320 137 265), lower := (rows 7 98 164 25 208 288 320 128 256), losses := [] }

theorem u594 : Upper (D 9) (R 9) [6,96,160,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b594 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 98 164 25 336 33 72 384 384), lower := (rows 7 98 164 25 336 33 72 128 256), losses := [] }

theorem u595 : Upper (D 9) (R 9) [6,96,160,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b595 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 264, camps := [{ cop := 6, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 98 164 25 336 33 192 392 264), lower := (rows 7 98 164 25 336 33 192 128 256), losses := [] }

theorem u596 : Upper (D 9) (R 9) [6,96,160,17,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b596 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 98 164 25 336 33 320 136 392), lower := (rows 7 98 164 25 336 33 320 128 256), losses := [] }

theorem u597 : Upper (D 9) (R 9) [6,96,160,17,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b597 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 164 73 152 288 65 400 272), lower := (rows 7 98 164 73 152 288 65 128 256), losses := [] }

theorem u598 : Upper (D 9) (R 9) [6,96,160,65,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b598 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 98 164 73 152 288 80 385 257), lower := (rows 7 98 164 73 152 288 80 128 256), losses := [] }

theorem u599 : Upper (D 9) (R 9) [6,96,160,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b599 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P09
