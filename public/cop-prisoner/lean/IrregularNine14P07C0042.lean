import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0002

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 292 137 208 40 66 145 273), lower := (rows 7 98 292 137 208 40 66 128 256), losses := [] }

theorem u2520 : Upper (D 7) (R 7) [6,96,288,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2520 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 292 137 208 40 80 131 259), lower := (rows 7 98 292 137 208 40 80 128 256), losses := [] }

theorem u2521 : Upper (D 7) (R 7) [6,96,288,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2521 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2522 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 292 138 208 33 65 152 280), lower := (rows 7 98 292 138 208 33 65 128 256), losses := [] }

theorem u2522 : Upper (D 7) (R 7) [6,96,288,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 98 292 138 208 33 72 145 273), lower := (rows 7 98 292 138 208 33 72 128 256), losses := [] }

theorem u2523 : Upper (D 7) (R 7) [6,96,288,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2523 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 292 138 208 33 80 137 265), lower := (rows 7 98 292 138 208 33 80 128 256), losses := [] }

theorem u2524 : Upper (D 7) (R 7) [6,96,288,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2524 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 388, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 98 388 25 146 33 72 224 352), lower := (rows 7 98 388 25 146 33 72 128 256), losses := [] }

theorem u2525 : Upper (D 7) (R 7) [6,96,384,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2525 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 388 25 146 33 96 200 328), lower := (rows 7 98 388 25 146 33 96 128 256), losses := [] }

theorem u2526 : Upper (D 7) (R 7) [6,96,384,17,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2527 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 388 25 146 40 96 193 321), lower := (rows 7 98 388 25 146 40 96 128 256), losses := [] }

theorem u2527 : Upper (D 7) (R 7) [6,96,384,17,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2527 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2528 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 454, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 7 98 388 25 152 33 66 224 352), lower := (rows 7 98 388 25 152 33 66 128 256), losses := [] }

theorem u2528 : Upper (D 7) (R 7) [6,96,384,17,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2529 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 388 25 152 34 96 193 321), lower := (rows 7 98 388 25 152 34 96 128 256), losses := [] }

theorem u2529 : Upper (D 7) (R 7) [6,96,384,17,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2530 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 7 98 388 25 176 33 66 200 328), lower := (rows 7 98 388 25 176 33 66 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 16 32 123 136 264), good := (rows 70 98 388 478 242 98 66 128 256) }] }

theorem u2530 : Upper (D 7) (R 7) [6,96,384,17,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 404, targets := 1 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 7 98 388 25 176 33 72 194 322), lower := (rows 7 98 388 25 176 33 72 128 256), losses := [] }

theorem u2531 : Upper (D 7) (R 7) [6,96,384,17,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2531 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2532 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 106, targets := 128 },{ cop := 1, region := 388, targets := 1 }], pairs := [(1,7),(2,0),(3,7)], upper := (rows 7 98 388 26 145 33 72 224 352), lower := (rows 7 98 388 26 145 33 72 128 256), losses := [] }

theorem u2532 : Upper (D 7) (R 7) [6,96,384,18,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2532 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 388 26 145 33 96 200 328), lower := (rows 7 98 388 26 145 33 96 128 256), losses := [] }

theorem u2533 : Upper (D 7) (R 7) [6,96,384,18,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 388 26 145 40 96 193 321), lower := (rows 7 98 388 26 145 40 96 128 256), losses := [] }

theorem u2534 : Upper (D 7) (R 7) [6,96,384,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2534 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 388 26 152 33 65 224 352), lower := (rows 7 98 388 26 152 33 65 128 256), losses := [] }

theorem u2535 : Upper (D 7) (R 7) [6,96,384,18,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 7 98 388 26 152 33 96 193 321), lower := (rows 7 98 388 26 152 33 96 128 256), losses := [] }

theorem u2536 : Upper (D 7) (R 7) [6,96,384,18,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 388 26 176 33 65 200 328), lower := (rows 7 98 388 26 176 33 65 128 256), losses := [] }

theorem u2537 : Upper (D 7) (R 7) [6,96,384,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 388 26 176 33 72 193 321), lower := (rows 7 98 388 26 176 33 72 128 256), losses := [] }

theorem u2538 : Upper (D 7) (R 7) [6,96,384,18,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2538 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 388 56 146 33 65 200 328), lower := (rows 7 98 388 56 146 33 65 128 256), losses := [] }

theorem u2539 : Upper (D 7) (R 7) [6,96,384,48,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 388 56 146 33 72 193 321), lower := (rows 7 98 388 56 146 33 72 128 256), losses := [] }

theorem u2540 : Upper (D 7) (R 7) [6,96,384,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2540 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 98 388 56 208 33 65 138 266), lower := (rows 7 98 388 56 208 33 65 128 256), losses := [] }

theorem u2541 : Upper (D 7) (R 7) [6,96,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,1)], upper := (rows 7 98 388 56 208 33 66 137 265), lower := (rows 7 98 388 56 208 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 47 11 18 33 64 161 289), good := (rows 445 508 388 444 208 429 92 128 256) }] }

theorem u2542 : Upper (D 7) (R 7) [6,96,384,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 388 56 208 33 72 131 259), lower := (rows 7 98 388 56 208 33 72 128 256), losses := [] }

theorem u2543 : Upper (D 7) (R 7) [6,96,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2543 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,5),(3,0),(3,1),(4,0)], upper := (rows 7 259 13 56 82 160 96 192 448), lower := (rows 7 259 13 56 82 160 96 128 256), losses := [{ target := 5, region := (rows 13 10 12 8 16 0 64 208 336), good := (rows 7 259 15 415 466 128 448 128 256) }] }

theorem u2544 : Upper (D 7) (R 7) [6,257,9,48,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2545 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(4,0)], upper := (rows 7 259 13 56 82 160 192 224 352), lower := (rows 7 259 13 56 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 28 24 16 224 0 128 256), good := (rows 7 259 13 61 63 160 160 160 256) }] }

theorem u2545 : Upper (D 7) (R 7) [6,257,9,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2546 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 259 13 104 50 160 80 192 448), lower := (rows 7 259 13 104 50 160 80 128 256), losses := [] }

theorem u2546 : Upper (D 7) (R 7) [6,257,9,96,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2546 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2547 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 259 13 104 50 160 192 208 336), lower := (rows 7 259 13 104 50 160 192 128 256), losses := [] }

theorem u2547 : Upper (D 7) (R 7) [6,257,9,96,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 259 13 104 146 48 192 224 352), lower := (rows 7 259 13 104 146 48 192 128 256), losses := [] }

theorem u2548 : Upper (D 7) (R 7) [6,257,9,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2548 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 259 13 104 146 96 192 176 304), lower := (rows 7 259 13 104 146 96 192 128 256), losses := [] }

theorem u2549 : Upper (D 7) (R 7) [6,257,9,96,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 144, targets := 3 },{ cop := 0, region := 104, targets := 128 }], pairs := [(2,0),(3,7),(4,0),(4,1)], upper := (rows 7 259 28 42 208 96 65 160 416), lower := (rows 7 259 28 42 208 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 112 112 64 252 380), good := (rows 390 258 444 446 496 496 496 128 256) }] }

theorem u2550 : Upper (D 7) (R 7) [6,257,24,34,192,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2551 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 387, targets := 96 }], pairs := [(0,5),(0,6),(1,5),(1,6)], upper := (rows 7 259 28 42 208 96 96 129 385), lower := (rows 7 259 28 42 208 96 96 128 256), losses := [] }

theorem u2551 : Upper (D 7) (R 7) [6,257,24,34,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2552 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 28 42 208 96 192 161 289), lower := (rows 7 259 28 42 208 96 192 128 256), losses := [] }

theorem u2552 : Upper (D 7) (R 7) [6,257,24,34,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 240, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 259 37 26 112 160 72 192 448), lower := (rows 7 259 37 26 112 160 72 128 256), losses := [] }

theorem u2553 : Upper (D 7) (R 7) [6,257,33,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2553 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 37 26 112 160 192 200 328), lower := (rows 7 259 37 26 112 160 192 128 256), losses := [] }

theorem u2554 : Upper (D 7) (R 7) [6,257,33,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2555 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 168, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 259 37 56 82 160 72 192 448), lower := (rows 7 259 37 56 82 160 72 128 256), losses := [] }

theorem u2555 : Upper (D 7) (R 7) [6,257,33,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2555 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2556 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(4,0)], upper := (rows 7 259 37 56 82 160 192 200 328), lower := (rows 7 259 37 56 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 28 24 16 224 0 128 256), good := (rows 7 259 37 61 63 160 160 160 256) }] }

theorem u2556 : Upper (D 7) (R 7) [6,257,33,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2557 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 37 74 112 160 72 144 400), lower := (rows 7 259 37 74 112 160 72 128 256), losses := [] }

theorem u2557 : Upper (D 7) (R 7) [6,257,33,66,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2557 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 259 37 74 112 160 80 136 392), lower := (rows 7 259 37 74 112 160 80 128 256), losses := [] }

theorem u2558 : Upper (D 7) (R 7) [6,257,33,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2558 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 37 74 112 160 192 152 280), lower := (rows 7 259 37 74 112 160 192 128 256), losses := [] }

theorem u2559 : Upper (D 7) (R 7) [6,257,33,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 259 37 74 152 160 80 224 352), lower := (rows 7 259 37 74 152 160 80 128 256), losses := [] }

theorem u2560 : Upper (D 7) (R 7) [6,257,33,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2560 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 2 },{ cop := 3, region := 144, targets := 32 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 259 37 74 152 160 96 208 336), lower := (rows 7 259 37 74 152 160 96 128 256), losses := [] }

theorem u2561 : Upper (D 7) (R 7) [6,257,33,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 37 74 208 160 72 176 304), lower := (rows 7 259 37 74 208 160 72 128 256), losses := [] }

theorem u2562 : Upper (D 7) (R 7) [6,257,33,66,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2562 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 37 74 208 160 80 168 296), lower := (rows 7 259 37 74 208 160 80 128 256), losses := [] }

theorem u2563 : Upper (D 7) (R 7) [6,257,33,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2563 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 2 },{ cop := 3, region := 144, targets := 32 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 259 37 74 208 160 96 152 280), lower := (rows 7 259 37 74 208 160 96 128 256), losses := [] }

theorem u2564 : Upper (D 7) (R 7) [6,257,33,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 152, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 37 88 176 96 66 136 392), lower := (rows 7 259 37 88 176 96 66 128 256), losses := [] }

theorem u2565 : Upper (D 7) (R 7) [6,257,33,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 37 88 176 96 72 130 386), lower := (rows 7 259 37 88 176 96 72 128 256), losses := [] }

theorem u2566 : Upper (D 7) (R 7) [6,257,33,80,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2566 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 37 88 176 96 192 138 266), lower := (rows 7 259 37 88 176 96 192 128 256), losses := [] }

theorem u2567 : Upper (D 7) (R 7) [6,257,33,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 37 104 208 160 66 152 280), lower := (rows 7 259 37 104 208 160 66 128 256), losses := [] }

theorem u2568 : Upper (D 7) (R 7) [6,257,33,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 259 37 104 208 160 72 146 274), lower := (rows 7 259 37 104 208 160 72 128 256), losses := [] }

theorem u2569 : Upper (D 7) (R 7) [6,257,33,96,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2569 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 259 37 104 208 160 80 138 266), lower := (rows 7 259 37 104 208 160 80 128 256), losses := [] }

theorem u2570 : Upper (D 7) (R 7) [6,257,33,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2570 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,5),(2,0),(2,1),(4,0)], upper := (rows 7 259 44 25 82 160 96 192 448), lower := (rows 7 259 44 25 82 160 96 128 256), losses := [{ target := 5, region := (rows 5 10 4 8 16 0 64 208 336), good := (rows 7 259 15 411 466 128 448 128 256) }] }

theorem u2571 : Upper (D 7) (R 7) [6,257,40,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,6),(2,0),(2,1),(4,0)], upper := (rows 7 259 44 25 82 160 192 224 352), lower := (rows 7 259 44 25 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 20 24 16 224 0 128 256), good := (rows 7 259 44 29 63 160 160 160 256) }] }

theorem u2572 : Upper (D 7) (R 7) [6,257,40,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5),(2,0),(2,1),(3,5)], upper := (rows 7 259 44 26 81 160 96 192 448), lower := (rows 7 259 44 26 81 160 96 128 256), losses := [] }

theorem u2573 : Upper (D 7) (R 7) [6,257,40,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2574 : Route 9 := (fun mask => (mask,id))

def c2574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2574 : Upper (D 7) (R 7) [6,257,40,18,65,128,128] 13 := by
  apply FastRouting.sound _ _ [6,257,40,18,65,128,128] 13 (by decide) (choices 1) [32,64] r2574 c2574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u166
  · exact u167

def b2575 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 259 44 73 50 160 80 192 448), lower := (rows 7 259 44 73 50 160 80 128 256), losses := [] }

theorem u2575 : Upper (D 7) (R 7) [6,257,40,65,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2575 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(2,6),(4,0)], upper := (rows 7 259 44 73 50 160 192 208 336), lower := (rows 7 259 44 73 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 255 155 283), good := (rows 502 498 492 508 498 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 240 240 144 272), good := (rows 5 257 108 109 496 224 224 224 256) },{ target := 6, region := (rows 1 2 12 8 16 224 0 128 256), good := (rows 7 259 44 45 50 160 160 160 256) }] }

theorem u2576 : Upper (D 7) (R 7) [6,257,40,65,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 259 44 73 82 160 80 160 416), lower := (rows 7 259 44 73 82 160 80 128 256), losses := [] }

theorem u2577 : Upper (D 7) (R 7) [6,257,40,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2577 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 402, targets := 32 },{ cop := 0, region := 240, targets := 1 }], pairs := [(1,5),(2,0),(4,0),(4,5)], upper := (rows 7 259 44 73 82 160 96 144 400), lower := (rows 7 259 44 73 82 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 255 155 283), good := (rows 502 498 492 508 498 224 96 224 256) }] }

theorem u2578 : Upper (D 7) (R 7) [6,257,40,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(2,6),(4,0)], upper := (rows 7 259 44 73 82 160 192 176 304), lower := (rows 7 259 44 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 255 155 283), good := (rows 502 498 492 508 498 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 240 240 144 272), good := (rows 5 257 108 109 496 224 224 224 256) },{ target := 6, region := (rows 1 2 12 8 16 240 0 144 272), good := (rows 7 259 44 45 434 160 160 160 256) }] }

theorem u2579 : Upper (D 7) (R 7) [6,257,40,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P07
