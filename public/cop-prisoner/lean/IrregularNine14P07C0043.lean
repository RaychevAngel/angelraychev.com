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

def b2580 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 73 112 160 66 144 400), lower := (rows 7 259 44 73 112 160 66 128 256), losses := [] }

theorem u2580 : Upper (D 7) (R 7) [6,257,40,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 259 44 73 112 160 80 130 386), lower := (rows 7 259 44 73 112 160 80 128 256), losses := [] }

theorem u2581 : Upper (D 7) (R 7) [6,257,40,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2581 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 44 73 112 160 192 146 274), lower := (rows 7 259 44 73 112 160 192 128 256), losses := [] }

theorem u2582 : Upper (D 7) (R 7) [6,257,40,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 44 73 146 160 80 224 352), lower := (rows 7 259 44 73 146 160 80 128 256), losses := [] }

theorem u2583 : Upper (D 7) (R 7) [6,257,40,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2583 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 402, targets := 32 },{ cop := 0, region := 240, targets := 1 }], pairs := [(1,5),(2,0),(4,0),(4,5)], upper := (rows 7 259 44 73 146 160 96 208 336), lower := (rows 7 259 44 73 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 255 155 283), good := (rows 502 498 492 508 498 224 96 224 256) }] }

theorem u2584 : Upper (D 7) (R 7) [6,257,40,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 73 208 160 66 176 304), lower := (rows 7 259 44 73 208 160 66 128 256), losses := [] }

theorem u2585 : Upper (D 7) (R 7) [6,257,40,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 44 73 208 160 80 162 290), lower := (rows 7 259 44 73 208 160 80 128 256), losses := [] }

theorem u2586 : Upper (D 7) (R 7) [6,257,40,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2586 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2587 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 32 },{ cop := 5, region := 80, targets := 3 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 7 259 44 73 208 160 96 146 274), lower := (rows 7 259 44 73 208 160 96 128 256), losses := [] }

theorem u2587 : Upper (D 7) (R 7) [6,257,40,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2588 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 259 44 74 81 160 80 160 416), lower := (rows 7 259 44 74 81 160 80 128 256), losses := [] }

theorem u2588 : Upper (D 7) (R 7) [6,257,40,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2588 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,5),(4,1)], upper := (rows 7 259 44 74 81 160 96 144 400), lower := (rows 7 259 44 74 81 160 96 128 256), losses := [] }

theorem u2589 : Upper (D 7) (R 7) [6,257,40,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(4,1)], upper := (rows 7 259 44 74 81 160 192 176 304), lower := (rows 7 259 44 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 240 240 144 272), good := (rows 6 258 108 110 496 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 19 255 255 155 283), good := (rows 501 497 492 508 497 224 224 224 256) }] }

theorem u2590 : Upper (D 7) (R 7) [6,257,40,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 74 112 160 65 144 400), lower := (rows 7 259 44 74 112 160 65 128 256), losses := [] }

theorem u2591 : Upper (D 7) (R 7) [6,257,40,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 259 44 74 112 160 80 129 385), lower := (rows 7 259 44 74 112 160 80 128 256), losses := [] }

theorem u2592 : Upper (D 7) (R 7) [6,257,40,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2592 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 44 74 112 160 192 145 273), lower := (rows 7 259 44 74 112 160 192 128 256), losses := [] }

theorem u2593 : Upper (D 7) (R 7) [6,257,40,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 259 44 74 145 160 80 224 352), lower := (rows 7 259 44 74 145 160 80 128 256), losses := [] }

theorem u2594 : Upper (D 7) (R 7) [6,257,40,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2594 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(2,1),(3,0),(4,1)], upper := (rows 7 259 44 74 145 160 96 208 336), lower := (rows 7 259 44 74 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 9 16 176 244 144 272), good := (rows 78 266 108 74 508 224 96 224 256) },{ target := 1, region := (rows 1 0 12 8 19 191 255 155 283), good := (rows 501 497 492 508 497 224 96 224 256) }] }

theorem u2595 : Upper (D 7) (R 7) [6,257,40,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 44 74 208 160 65 176 304), lower := (rows 7 259 44 74 208 160 65 128 256), losses := [] }

theorem u2596 : Upper (D 7) (R 7) [6,257,40,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 44 74 208 160 80 161 289), lower := (rows 7 259 44 74 208 160 80 128 256), losses := [] }

theorem u2597 : Upper (D 7) (R 7) [6,257,40,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2597 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 259 44 74 208 160 96 145 273), lower := (rows 7 259 44 74 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 176 176 244 128 256), good := (rows 78 266 124 74 240 240 112 240 256) },{ target := 1, region := (rows 1 0 12 8 187 187 255 131 259), good := (rows 501 497 124 508 240 240 112 240 256) }] }

theorem u2598 : Upper (D 7) (R 7) [6,257,40,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 44 200 81 34 80 160 416), lower := (rows 7 259 44 200 81 34 80 128 256), losses := [] }

theorem u2599 : Upper (D 7) (R 7) [6,257,40,192,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2599 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 3 },{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5),(3,0),(3,1),(3,5)], upper := (rows 7 259 44 200 81 34 96 144 400), lower := (rows 7 259 44 200 81 34 96 128 256), losses := [] }

theorem u2600 : Upper (D 7) (R 7) [6,257,40,192,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 259 44 200 81 34 192 176 304), lower := (rows 7 259 44 200 81 34 192 128 256), losses := [] }

theorem u2601 : Upper (D 7) (R 7) [6,257,40,192,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 259 44 200 81 48 66 160 416), lower := (rows 7 259 44 200 81 48 66 128 256), losses := [] }

theorem u2602 : Upper (D 7) (R 7) [6,257,40,192,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2602 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 387, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 259 44 200 81 48 96 130 386), lower := (rows 7 259 44 200 81 48 96 128 256), losses := [] }

theorem u2603 : Upper (D 7) (R 7) [6,257,40,192,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2603 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 259 44 200 81 48 192 162 290), lower := (rows 7 259 44 200 81 48 192 128 256), losses := [] }

theorem u2604 : Upper (D 7) (R 7) [6,257,40,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2604 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 259 44 200 82 33 80 160 416), lower := (rows 7 259 44 200 82 33 80 128 256), losses := [] }

theorem u2605 : Upper (D 7) (R 7) [6,257,40,192,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2605 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 136, targets := 35 },{ cop := 0, region := 112, targets := 128 }], pairs := [(3,0),(3,1),(3,5),(4,7)], upper := (rows 7 259 44 200 82 33 96 144 400), lower := (rows 7 259 44 200 82 33 96 128 256), losses := [] }

theorem u2606 : Upper (D 7) (R 7) [6,257,40,192,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 259 44 200 82 33 192 176 304), lower := (rows 7 259 44 200 82 33 192 128 256), losses := [] }

theorem u2607 : Upper (D 7) (R 7) [6,257,40,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 259 44 200 82 48 65 160 416), lower := (rows 7 259 44 200 82 48 65 128 256), losses := [] }

theorem u2608 : Upper (D 7) (R 7) [6,257,40,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2609 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 387, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 259 44 200 82 48 96 129 385), lower := (rows 7 259 44 200 82 48 96 128 256), losses := [] }

theorem u2609 : Upper (D 7) (R 7) [6,257,40,192,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2609 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 259 44 200 82 48 192 161 289), lower := (rows 7 259 44 200 82 48 192 128 256), losses := [] }

theorem u2610 : Upper (D 7) (R 7) [6,257,40,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2610 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 200 112 33 66 144 400), lower := (rows 7 259 44 200 112 33 66 128 256), losses := [] }

theorem u2611 : Upper (D 7) (R 7) [6,257,40,192,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 259 44 200 112 33 80 130 386), lower := (rows 7 259 44 200 112 33 80 128 256), losses := [] }

theorem u2612 : Upper (D 7) (R 7) [6,257,40,192,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2612 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 259 44 200 112 33 192 146 274), lower := (rows 7 259 44 200 112 33 192 128 256), losses := [] }

theorem u2613 : Upper (D 7) (R 7) [6,257,40,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 200 112 34 65 144 400), lower := (rows 7 259 44 200 112 34 65 128 256), losses := [] }

theorem u2614 : Upper (D 7) (R 7) [6,257,40,192,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 259 44 200 112 34 80 129 385), lower := (rows 7 259 44 200 112 34 80 128 256), losses := [] }

theorem u2615 : Upper (D 7) (R 7) [6,257,40,192,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2615 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 259 44 200 112 34 192 145 273), lower := (rows 7 259 44 200 112 34 192 128 256), losses := [] }

theorem u2616 : Upper (D 7) (R 7) [6,257,40,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 259 100 25 50 160 72 192 448), lower := (rows 7 259 100 25 50 160 72 128 256), losses := [] }

theorem u2617 : Upper (D 7) (R 7) [6,257,96,17,34,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2617 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 259 100 25 50 160 192 200 328), lower := (rows 7 259 100 25 50 160 192 128 256), losses := [] }

theorem u2618 : Upper (D 7) (R 7) [6,257,96,17,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2619 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 259, targets := 128 },{ cop := 3, region := 228, targets := 1 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 7 259 100 25 146 40 192 224 352), lower := (rows 7 259 100 25 146 40 192 128 256), losses := [] }

theorem u2619 : Upper (D 7) (R 7) [6,257,96,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2619 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 25 146 96 192 168 296), lower := (rows 7 259 100 25 146 96 192 128 256), losses := [] }

theorem u2620 : Upper (D 7) (R 7) [6,257,96,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 144, targets := 3 },{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 7 259 100 25 176 34 72 192 448), lower := (rows 7 259 100 25 176 34 72 128 256), losses := [] }

theorem u2621 : Upper (D 7) (R 7) [6,257,96,17,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2621 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2622 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 68, targets := 3 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(2,0),(2,1),(4,0)], upper := (rows 7 259 100 25 176 34 192 200 328), lower := (rows 7 259 100 25 176 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 8 24 35 216 136 264), good := (rows 38 290 100 508 244 34 192 192 256) }] }

theorem u2622 : Upper (D 7) (R 7) [6,257,96,17,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 259, targets := 128 },{ cop := 3, region := 228, targets := 1 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 7 259 100 26 145 40 192 224 352), lower := (rows 7 259 100 26 145 40 192 128 256), losses := [] }

theorem u2623 : Upper (D 7) (R 7) [6,257,96,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2623 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 26 145 96 192 168 296), lower := (rows 7 259 100 26 145 96 192 128 256), losses := [] }

theorem u2624 : Upper (D 7) (R 7) [6,257,96,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 41 82 160 72 144 400), lower := (rows 7 259 100 41 82 160 72 128 256), losses := [] }

theorem u2625 : Upper (D 7) (R 7) [6,257,96,33,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2625 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 259 100 41 82 160 80 136 392), lower := (rows 7 259 100 41 82 160 80 128 256), losses := [] }

theorem u2626 : Upper (D 7) (R 7) [6,257,96,33,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2626 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 259 100 41 82 160 192 152 280), lower := (rows 7 259 100 41 82 160 192 128 256), losses := [] }

theorem u2627 : Upper (D 7) (R 7) [6,257,96,33,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 4, region := 164, targets := 3 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 259 100 41 88 160 66 144 400), lower := (rows 7 259 100 41 88 160 66 128 256), losses := [] }

theorem u2628 : Upper (D 7) (R 7) [6,257,96,33,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 84, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 7 259 100 41 88 160 80 130 386), lower := (rows 7 259 100 41 88 160 80 128 256), losses := [] }

theorem u2629 : Upper (D 7) (R 7) [6,257,96,33,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2629 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 259 100 41 88 160 192 146 274), lower := (rows 7 259 100 41 88 160 192 128 256), losses := [] }

theorem u2630 : Upper (D 7) (R 7) [6,257,96,33,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 41 146 160 72 208 336), lower := (rows 7 259 100 41 146 160 72 128 256), losses := [] }

theorem u2631 : Upper (D 7) (R 7) [6,257,96,33,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2631 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 259 100 41 146 160 80 200 328), lower := (rows 7 259 100 41 146 160 80 128 256), losses := [] }

theorem u2632 : Upper (D 7) (R 7) [6,257,96,33,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2632 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(4,0),(4,5)], upper := (rows 7 259 100 41 152 160 66 208 336), lower := (rows 7 259 100 41 152 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 184 67 136 264), good := (rows 70 322 100 508 444 160 66 160 256) }] }

theorem u2633 : Upper (D 7) (R 7) [6,257,96,33,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 259 100 41 152 160 80 194 322), lower := (rows 7 259 100 41 152 160 80 128 256), losses := [] }

theorem u2634 : Upper (D 7) (R 7) [6,257,96,33,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2634 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 4, region := 164, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,7)], upper := (rows 7 259 100 42 88 160 65 144 400), lower := (rows 7 259 100 42 88 160 65 128 256), losses := [] }

theorem u2635 : Upper (D 7) (R 7) [6,257,96,34,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 42 88 160 80 129 385), lower := (rows 7 259 100 42 88 160 80 128 256), losses := [] }

theorem u2636 : Upper (D 7) (R 7) [6,257,96,34,72,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2636 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 259 100 42 88 160 192 145 273), lower := (rows 7 259 100 42 88 160 192 128 256), losses := [] }

theorem u2637 : Upper (D 7) (R 7) [6,257,96,34,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 259 100 42 145 48 72 192 448), lower := (rows 7 259 100 42 145 48 72 128 256), losses := [] }

theorem u2638 : Upper (D 7) (R 7) [6,257,96,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2638 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 259 100 42 145 48 192 200 328), lower := (rows 7 259 100 42 145 48 192 128 256), losses := [] }

theorem u2639 : Upper (D 7) (R 7) [6,257,96,34,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P07
