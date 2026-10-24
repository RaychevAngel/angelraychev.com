import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0002

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2580 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 132, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 11 35 196 280 22 96 65 164 292), lower := (rows 11 35 196 280 22 96 65 128 256), losses := [] }

theorem u2580 : Upper (D 6) (R 6) [10,33,192,272,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 },{ cop := 7, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 196 280 22 96 68 161 289), lower := (rows 11 35 196 280 22 96 68 128 256), losses := [] }

theorem u2581 : Upper (D 6) (R 6) [10,33,192,272,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 265, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 196 280 22 96 96 133 261), lower := (rows 11 35 196 280 22 96 96 128 256), losses := [] }

theorem u2582 : Upper (D 6) (R 6) [10,33,192,272,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 280 81 36 66 164 292), lower := (rows 11 35 196 280 81 36 66 128 256), losses := [] }

theorem u2583 : Upper (D 6) (R 6) [10,33,192,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 68, targets := 3 },{ cop := 7, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 196 280 81 36 68 162 290), lower := (rows 11 35 196 280 81 36 68 128 256), losses := [] }

theorem u2584 : Upper (D 6) (R 6) [10,33,192,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 1, region := 80, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 35 196 280 81 36 96 134 262), lower := (rows 11 35 196 280 81 36 96 128 256), losses := [] }

theorem u2585 : Upper (D 6) (R 6) [10,33,192,272,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2586 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 196 280 82 36 65 164 292), lower := (rows 11 35 196 280 82 36 65 128 256), losses := [] }

theorem u2586 : Upper (D 6) (R 6) [10,33,192,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2587 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 },{ cop := 7, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 35 196 280 82 36 68 161 289), lower := (rows 11 35 196 280 82 36 68 128 256), losses := [] }

theorem u2587 : Upper (D 6) (R 6) [10,33,192,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2588 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 196 280 82 36 96 133 261), lower := (rows 11 35 196 280 82 36 96 128 256), losses := [] }

theorem u2588 : Upper (D 6) (R 6) [10,33,192,272,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 35 196 328 21 36 66 176 304), lower := (rows 11 35 196 328 21 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 52 67 144 272), good := (rows 74 98 228 328 508 36 66 128 256) }] }

theorem u2589 : Upper (D 6) (R 6) [10,33,192,320,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2590 : Route 9 := (fun mask => (mask,id))

def c2590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2590 : Upper (D 6) (R 6) [10,33,192,320,5,4,16] 13 := by
  apply FastRouting.sound _ _ [10,33,192,320,5,4,16] 13 (by decide) (choices 1) [2,32] r2590 c2590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u168
  · exact u169

def b2591 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 35 196 328 21 36 96 146 274), lower := (rows 11 35 196 328 21 36 96 128 256), losses := [] }

theorem u2591 : Upper (D 6) (R 6) [10,33,192,320,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 48, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 196 328 22 36 65 176 304), lower := (rows 11 35 196 328 22 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 76 17 125 64 211 339), good := (rows 446 434 492 492 446 44 508 128 256) }] }

theorem u2592 : Upper (D 6) (R 6) [10,33,192,320,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1)], upper := (rows 11 35 196 328 22 36 80 161 289), lower := (rows 11 35 196 328 22 36 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 116 80 130 258), good := (rows 393 417 228 360 508 36 124 128 256) }] }

theorem u2593 : Upper (D 6) (R 6) [10,33,192,320,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2593 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 11 35 196 328 22 36 96 145 273), lower := (rows 11 35 196 328 22 36 96 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 32 98 144 272), good := (rows 75 99 192 328 475 96 96 128 256) }] }

theorem u2594 : Upper (D 6) (R 6) [10,33,192,320,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 388 13 84 96 66 176 304), lower := (rows 11 35 388 13 84 96 66 128 256), losses := [] }

theorem u2595 : Upper (D 6) (R 6) [10,33,384,5,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 388 13 84 96 80 162 290), lower := (rows 11 35 388 13 84 96 80 128 256), losses := [] }

theorem u2596 : Upper (D 6) (R 6) [10,33,384,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2596 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 35 388 13 84 96 96 146 274), lower := (rows 11 35 388 13 84 96 96 128 256), losses := [] }

theorem u2597 : Upper (D 6) (R 6) [10,33,384,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 388 73 84 36 66 176 304), lower := (rows 11 35 388 73 84 36 66 128 256), losses := [] }

theorem u2598 : Upper (D 6) (R 6) [10,33,384,65,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 388 73 84 36 80 162 290), lower := (rows 11 35 388 73 84 36 80 128 256), losses := [] }

theorem u2599 : Upper (D 6) (R 6) [10,33,384,65,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2599 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 388 73 84 36 96 146 274), lower := (rows 11 35 388 73 84 36 96 128 256), losses := [] }

theorem u2600 : Upper (D 6) (R 6) [10,33,384,65,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 11 38 69 140 49 288 66 208 336), lower := (rows 11 38 69 140 49 288 66 128 256), losses := [] }

theorem u2601 : Upper (D 6) (R 6) [10,36,65,132,33,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2601 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0)], upper := (rows 11 38 69 140 49 288 80 194 322), lower := (rows 11 38 69 140 49 288 80 128 256), losses := [] }

theorem u2602 : Upper (D 6) (R 6) [10,36,65,132,33,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2602 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 38 69 140 82 288 65 176 304), lower := (rows 11 38 69 140 82 288 65 128 256), losses := [] }

theorem u2603 : Upper (D 6) (R 6) [10,36,65,132,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2603 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 11 38 69 140 82 288 80 161 289), lower := (rows 11 38 69 140 82 288 80 128 256), losses := [] }

theorem u2604 : Upper (D 6) (R 6) [10,36,65,132,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2604 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 69 140 82 288 96 145 273), lower := (rows 11 38 69 140 82 288 96 128 256), losses := [] }

theorem u2605 : Upper (D 6) (R 6) [10,36,65,132,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2605 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 38 69 140 112 288 65 146 274), lower := (rows 11 38 69 140 112 288 65 128 256), losses := [] }

theorem u2606 : Upper (D 6) (R 6) [10,36,65,132,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2606 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 38 69 140 112 288 66 145 273), lower := (rows 11 38 69 140 112 288 66 128 256), losses := [] }

theorem u2607 : Upper (D 6) (R 6) [10,36,65,132,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2607 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 11 38 69 140 112 288 80 131 259), lower := (rows 11 38 69 140 112 288 80 128 256), losses := [] }

theorem u2608 : Upper (D 6) (R 6) [10,36,65,132,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2608 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2609 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 38 69 140 274 48 65 224 352), lower := (rows 11 38 69 140 274 48 65 128 256), losses := [] }

theorem u2609 : Upper (D 6) (R 6) [10,36,65,132,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2609 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 11 38 69 140 274 48 96 193 321), lower := (rows 11 38 69 140 274 48 96 128 256), losses := [] }

theorem u2610 : Upper (D 6) (R 6) [10,36,65,132,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2610 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 38 69 152 336 34 65 164 292), lower := (rows 11 38 69 152 336 34 65 128 256), losses := [] }

theorem u2611 : Upper (D 6) (R 6) [10,36,65,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 69 152 336 34 68 161 289), lower := (rows 11 38 69 152 336 34 68 128 256), losses := [] }

theorem u2612 : Upper (D 6) (R 6) [10,36,65,144,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 38 69 152 336 34 96 133 261), lower := (rows 11 38 69 152 336 34 96 128 256), losses := [] }

theorem u2613 : Upper (D 6) (R 6) [10,36,65,144,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 25 148 288 65 224 352), lower := (rows 11 38 70 25 148 288 65 128 256), losses := [] }

theorem u2614 : Upper (D 6) (R 6) [10,36,66,17,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2614 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 25 148 288 96 193 321), lower := (rows 11 38 70 25 148 288 96 128 256), losses := [] }

theorem u2615 : Upper (D 6) (R 6) [10,36,66,17,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2615 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 25 176 288 65 196 324), lower := (rows 11 38 70 25 176 288 65 128 256), losses := [] }

theorem u2616 : Upper (D 6) (R 6) [10,36,66,17,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2616 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 25 176 288 68 193 321), lower := (rows 11 38 70 25 176 288 68 128 256), losses := [] }

theorem u2617 : Upper (D 6) (R 6) [10,36,66,17,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2617 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2618 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 25 208 288 65 164 292), lower := (rows 11 38 70 25 208 288 65 128 256), losses := [] }

theorem u2618 : Upper (D 6) (R 6) [10,36,66,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2618 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2619 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 70 25 208 288 68 161 289), lower := (rows 11 38 70 25 208 288 68 128 256), losses := [] }

theorem u2619 : Upper (D 6) (R 6) [10,36,66,17,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2619 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 25 208 288 96 133 261), lower := (rows 11 38 70 25 208 288 96 128 256), losses := [] }

theorem u2620 : Upper (D 6) (R 6) [10,36,66,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2620 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 400, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 56 208 33 65 388 260), lower := (rows 11 38 70 56 208 33 65 128 256), losses := [] }

theorem u2621 : Upper (D 6) (R 6) [10,36,66,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2622 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 56 208 33 68 385 257), lower := (rows 11 38 70 56 208 33 68 128 256), losses := [] }

theorem u2622 : Upper (D 6) (R 6) [10,36,66,48,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 70 56 208 33 320 133 261), lower := (rows 11 38 70 56 208 33 320 128 256), losses := [] }

theorem u2623 : Upper (D 6) (R 6) [10,36,66,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2623 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 400, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 56 400 33 65 196 324), lower := (rows 11 38 70 56 400 33 65 128 256), losses := [] }

theorem u2624 : Upper (D 6) (R 6) [10,36,66,48,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 441, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 70 56 400 33 68 193 321), lower := (rows 11 38 70 56 400 33 68 128 256), losses := [] }

theorem u2625 : Upper (D 6) (R 6) [10,36,66,48,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 38 70 88 145 288 65 164 292), lower := (rows 11 38 70 88 145 288 65 128 256), losses := [] }

theorem u2626 : Upper (D 6) (R 6) [10,36,66,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2626 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 88 145 288 68 161 289), lower := (rows 11 38 70 88 145 288 68 128 256), losses := [] }

theorem u2627 : Upper (D 6) (R 6) [10,36,66,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2627 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 88 145 288 96 133 261), lower := (rows 11 38 70 88 145 288 96 128 256), losses := [] }

theorem u2628 : Upper (D 6) (R 6) [10,36,66,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2628 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1)], upper := (rows 11 38 70 88 148 288 65 161 289), lower := (rows 11 38 70 88 148 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 365 65 193 321), good := (rows 489 60 508 504 188 288 481 128 288) }] }

theorem u2629 : Upper (D 6) (R 6) [10,36,66,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2629 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 153, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 38 70 88 148 288 96 129 257), lower := (rows 11 38 70 88 148 288 96 128 256), losses := [] }

theorem u2630 : Upper (D 6) (R 6) [10,36,66,80,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2630 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 70 88 176 33 65 388 260), lower := (rows 11 38 70 88 176 33 65 128 256), losses := [] }

theorem u2631 : Upper (D 6) (R 6) [10,36,66,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 432, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 88 176 33 68 385 257), lower := (rows 11 38 70 88 176 33 68 128 256), losses := [] }

theorem u2632 : Upper (D 6) (R 6) [10,36,66,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 38 70 88 176 33 320 133 261), lower := (rows 11 38 70 88 176 33 320 128 256), losses := [{ target := 5, region := (rows 1 2 7 24 16 0 371 161 289), good := (rows 463 454 70 88 472 453 320 128 320) }] }

theorem u2633 : Upper (D 6) (R 6) [10,36,66,80,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2633 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r2634 : Route 9 := (fun mask => (mask,id))

def c2634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2634 : Upper (D 6) (R 6) [10,36,66,80,160,256,1] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,160,256,1] 13 (by decide) (choices 1) [1,4] r2634 c2634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u170
  · exact u171

def b2635 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 432, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 70 88 176 288 68 129 257), lower := (rows 11 38 70 88 176 288 68 128 256), losses := [] }

theorem u2635 : Upper (D 6) (R 6) [10,36,66,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2635 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 70 88 400 33 65 164 292), lower := (rows 11 38 70 88 400 33 65 128 256), losses := [] }

theorem u2636 : Upper (D 6) (R 6) [10,36,66,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 70 88 400 33 68 161 289), lower := (rows 11 38 70 88 400 33 68 128 256), losses := [] }

theorem u2637 : Upper (D 6) (R 6) [10,36,66,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 88 400 33 96 133 261), lower := (rows 11 38 70 88 400 33 96 128 256), losses := [] }

theorem u2638 : Upper (D 6) (R 6) [10,36,66,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 70 152 81 288 65 164 292), lower := (rows 11 38 70 152 81 288 65 128 256), losses := [] }

theorem u2639 : Upper (D 6) (R 6) [10,36,66,144,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2639 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P06
