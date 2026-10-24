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

def b2640 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 42 145 160 72 208 336), lower := (rows 7 259 100 42 145 160 72 128 256), losses := [] }

theorem u2640 : Upper (D 7) (R 7) [6,257,96,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2640 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 259 100 42 145 160 80 200 328), lower := (rows 7 259 100 42 145 160 80 128 256), losses := [] }

theorem u2641 : Upper (D 7) (R 7) [6,257,96,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2641 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(2,0),(2,7),(3,0)], upper := (rows 7 259 100 42 152 160 65 208 336), lower := (rows 7 259 100 42 152 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 11 81 245 64 196 324), good := (rows 446 314 500 42 184 160 508 160 256) }] }

theorem u2642 : Upper (D 7) (R 7) [6,257,96,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 259 100 42 152 160 80 193 321), lower := (rows 7 259 100 42 152 160 80 128 256), losses := [] }

theorem u2643 : Upper (D 7) (R 7) [6,257,96,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2643 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 69, targets := 128 },{ cop := 4, region := 36, targets := 3 }], pairs := [(0,7),(2,0),(2,1),(2,7)], upper := (rows 7 259 100 42 208 160 65 152 280), lower := (rows 7 259 100 42 208 160 65 128 256), losses := [] }

theorem u2644 : Upper (D 7) (R 7) [6,257,96,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 42 208 160 72 145 273), lower := (rows 7 259 100 42 208 160 72 128 256), losses := [] }

theorem u2645 : Upper (D 7) (R 7) [6,257,96,34,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2645 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 42 208 160 80 137 265), lower := (rows 7 259 100 42 208 160 80 128 256), losses := [] }

theorem u2646 : Upper (D 7) (R 7) [6,257,96,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2646 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2647 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 100 56 208 33 66 136 392), lower := (rows 7 259 100 56 208 33 66 128 256), losses := [] }

theorem u2647 : Upper (D 7) (R 7) [6,257,96,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2648 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 56 208 33 72 130 386), lower := (rows 7 259 100 56 208 33 72 128 256), losses := [] }

theorem u2648 : Upper (D 7) (R 7) [6,257,96,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2648 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 100 56 208 33 192 138 266), lower := (rows 7 259 100 56 208 33 192 128 256), losses := [] }

theorem u2649 : Upper (D 7) (R 7) [6,257,96,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 100 56 208 34 65 136 392), lower := (rows 7 259 100 56 208 34 65 128 256), losses := [] }

theorem u2650 : Upper (D 7) (R 7) [6,257,96,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 259 100 56 208 34 72 129 385), lower := (rows 7 259 100 56 208 34 72 128 256), losses := [] }

theorem u2651 : Upper (D 7) (R 7) [6,257,96,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2651 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 100 56 208 34 192 137 265), lower := (rows 7 259 100 56 208 34 192 128 256), losses := [] }

theorem u2652 : Upper (D 7) (R 7) [6,257,96,48,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 259, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 259 100 137 146 40 80 224 352), lower := (rows 7 259 100 137 146 40 80 128 256), losses := [] }

theorem u2653 : Upper (D 7) (R 7) [6,257,96,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2653 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 100 137 146 40 96 208 336), lower := (rows 7 259 100 137 146 40 96 128 256), losses := [] }

theorem u2654 : Upper (D 7) (R 7) [6,257,96,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2654 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 100 137 146 48 96 200 328), lower := (rows 7 259 100 137 146 48 96 128 256), losses := [] }

theorem u2655 : Upper (D 7) (R 7) [6,257,96,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2655 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 152, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 100 168 208 33 66 152 280), lower := (rows 7 259 100 168 208 33 66 128 256), losses := [] }

theorem u2656 : Upper (D 7) (R 7) [6,257,96,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 168 208 33 72 146 274), lower := (rows 7 259 100 168 208 33 72 128 256), losses := [] }

theorem u2657 : Upper (D 7) (R 7) [6,257,96,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2657 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 168 208 33 80 138 266), lower := (rows 7 259 100 168 208 33 80 128 256), losses := [] }

theorem u2658 : Upper (D 7) (R 7) [6,257,96,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2658 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 168 208 34 72 145 273), lower := (rows 7 259 100 168 208 34 72 128 256), losses := [] }

theorem u2659 : Upper (D 7) (R 7) [6,257,96,160,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2659 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 259 100 168 208 34 80 137 265), lower := (rows 7 259 100 168 208 34 80 128 256), losses := [] }

theorem u2660 : Upper (D 7) (R 7) [6,257,96,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2660 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 450, targets := 32 },{ cop := 6, region := 176, targets := 2 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 7 266 21 41 112 160 66 192 448), lower := (rows 7 266 21 41 112 160 66 128 256), losses := [] }

theorem u2661 : Upper (D 7) (R 7) [6,264,17,33,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 21 41 112 160 192 194 322), lower := (rows 7 266 21 41 112 160 192 128 256), losses := [] }

theorem u2662 : Upper (D 7) (R 7) [6,264,17,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 266 21 42 112 160 65 192 448), lower := (rows 7 266 21 42 112 160 65 128 256), losses := [] }

theorem u2663 : Upper (D 7) (R 7) [6,264,17,34,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 21 42 112 160 192 193 321), lower := (rows 7 266 21 42 112 160 192 128 256), losses := [] }

theorem u2664 : Upper (D 7) (R 7) [6,264,17,34,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 21 42 208 96 65 160 416), lower := (rows 7 266 21 42 208 96 65 128 256), losses := [] }

theorem u2665 : Upper (D 7) (R 7) [6,264,17,34,192,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 266 21 42 208 96 96 129 385), lower := (rows 7 266 21 42 208 96 96 128 256), losses := [] }

theorem u2666 : Upper (D 7) (R 7) [6,264,17,34,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 21 42 208 96 192 161 289), lower := (rows 7 266 21 42 208 96 192 128 256), losses := [] }

theorem u2667 : Upper (D 7) (R 7) [6,264,17,34,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 104, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,0)], upper := (rows 7 266 21 104 176 34 65 192 448), lower := (rows 7 266 21 104 176 34 65 128 256), losses := [] }

theorem u2668 : Upper (D 7) (R 7) [6,264,17,96,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r2669 : Route 9 := (fun mask => (mask,id))

def c2669 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2669 : Upper (D 7) (R 7) [6,264,17,96,160,2,128] 13 := by
  apply FastRouting.sound _ _ [6,264,17,96,160,2,128] 13 (by decide) (choices 1) [1,64] r2669 c2669
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u168
  · exact u169

def b2670 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(1,5),(2,1),(4,0)], upper := (rows 7 266 37 25 82 160 96 192 448), lower := (rows 7 266 37 25 82 160 96 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 16 0 64 208 336), good := (rows 7 266 5 411 466 128 448 128 256) }] }

theorem u2670 : Upper (D 7) (R 7) [6,264,33,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,6),(1,0),(2,1),(4,0)], upper := (rows 7 266 37 25 82 160 192 224 352), lower := (rows 7 266 37 25 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 20 24 16 224 0 128 256), good := (rows 7 266 37 29 63 160 160 160 256) }] }

theorem u2671 : Upper (D 7) (R 7) [6,264,33,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 450, targets := 32 },{ cop := 6, region := 176, targets := 2 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 7 266 37 25 112 160 66 192 448), lower := (rows 7 266 37 25 112 160 66 128 256), losses := [] }

theorem u2672 : Upper (D 7) (R 7) [6,264,33,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 25 112 160 192 194 322), lower := (rows 7 266 37 25 112 160 192 128 256), losses := [] }

theorem u2673 : Upper (D 7) (R 7) [6,264,33,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 37 26 112 160 65 192 448), lower := (rows 7 266 37 26 112 160 65 128 256), losses := [] }

theorem u2674 : Upper (D 7) (R 7) [6,264,33,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 26 112 160 192 193 321), lower := (rows 7 266 37 26 112 160 192 128 256), losses := [] }

theorem u2675 : Upper (D 7) (R 7) [6,264,33,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2676 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 37 56 82 160 65 192 448), lower := (rows 7 266 37 56 82 160 65 128 256), losses := [] }

theorem u2676 : Upper (D 7) (R 7) [6,264,33,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2677 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,0),(3,1),(4,5)], upper := (rows 7 266 37 56 82 160 192 193 321), lower := (rows 7 266 37 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 6 266 100 120 122 224 224 224 256) },{ target := 1, region := (rows 1 0 5 24 16 229 229 133 261), good := (rows 485 264 485 120 120 224 224 224 256) }] }

theorem u2677 : Upper (D 7) (R 7) [6,264,33,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 266 37 73 112 160 66 144 400), lower := (rows 7 266 37 73 112 160 66 128 256), losses := [] }

theorem u2678 : Upper (D 7) (R 7) [6,264,33,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 266 37 73 112 160 80 130 386), lower := (rows 7 266 37 73 112 160 80 128 256), losses := [] }

theorem u2679 : Upper (D 7) (R 7) [6,264,33,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2679 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 73 112 160 192 146 274), lower := (rows 7 266 37 73 112 160 192 128 256), losses := [] }

theorem u2680 : Upper (D 7) (R 7) [6,264,33,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 7 266 37 73 208 48 66 160 416), lower := (rows 7 266 37 73 208 48 66 128 256), losses := [] }

theorem u2681 : Upper (D 7) (R 7) [6,264,33,65,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2681 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 72, targets := 130 },{ cop := 3, region := 386, targets := 1 }], pairs := [(1,0),(3,1),(3,7)], upper := (rows 7 266 37 73 208 48 96 130 386), lower := (rows 7 266 37 73 208 48 96 128 256), losses := [] }

theorem u2682 : Upper (D 7) (R 7) [6,264,33,65,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2682 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 266 37 73 208 48 192 162 290), lower := (rows 7 266 37 73 208 48 192 128 256), losses := [] }

theorem u2683 : Upper (D 7) (R 7) [6,264,33,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2683 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 266 37 73 208 160 66 176 304), lower := (rows 7 266 37 73 208 160 66 128 256), losses := [] }

theorem u2684 : Upper (D 7) (R 7) [6,264,33,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2685 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 266 37 73 208 160 80 162 290), lower := (rows 7 266 37 73 208 160 80 128 256), losses := [] }

theorem u2685 : Upper (D 7) (R 7) [6,264,33,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2685 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 72, targets := 130 },{ cop := 3, region := 402, targets := 1 }], pairs := [(1,0),(3,1),(3,7),(4,0)], upper := (rows 7 266 37 73 208 160 96 146 274), lower := (rows 7 266 37 73 208 160 96 128 256), losses := [] }

theorem u2686 : Upper (D 7) (R 7) [6,264,33,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 37 74 112 160 65 144 400), lower := (rows 7 266 37 74 112 160 65 128 256), losses := [] }

theorem u2687 : Upper (D 7) (R 7) [6,264,33,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2688 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 266 37 74 112 160 80 129 385), lower := (rows 7 266 37 74 112 160 80 128 256), losses := [] }

theorem u2688 : Upper (D 7) (R 7) [6,264,33,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2688 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 37 74 112 160 192 145 273), lower := (rows 7 266 37 74 112 160 192 128 256), losses := [] }

theorem u2689 : Upper (D 7) (R 7) [6,264,33,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2690 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 266 37 74 208 48 65 160 416), lower := (rows 7 266 37 74 208 48 65 128 256), losses := [] }

theorem u2690 : Upper (D 7) (R 7) [6,264,33,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2690 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2691 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 7, region := 112, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 266 37 74 208 48 96 129 385), lower := (rows 7 266 37 74 208 48 96 128 256), losses := [] }

theorem u2691 : Upper (D 7) (R 7) [6,264,33,66,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2691 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 266 37 74 208 48 192 161 289), lower := (rows 7 266 37 74 208 48 192 128 256), losses := [] }

theorem u2692 : Upper (D 7) (R 7) [6,264,33,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2692 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 37 74 208 160 65 176 304), lower := (rows 7 266 37 74 208 160 65 128 256), losses := [] }

theorem u2693 : Upper (D 7) (R 7) [6,264,33,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 266 37 74 208 160 80 161 289), lower := (rows 7 266 37 74 208 160 80 128 256), losses := [] }

theorem u2694 : Upper (D 7) (R 7) [6,264,33,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2694 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 5, region := 80, targets := 1 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 266 37 74 208 160 96 145 273), lower := (rows 7 266 37 74 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 176 176 244 128 256), good := (rows 78 266 124 74 240 240 112 240 256) }] }

theorem u2695 : Upper (D 7) (R 7) [6,264,33,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2696 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 7 266 37 88 146 160 65 224 352), lower := (rows 7 266 37 88 146 160 65 128 256), losses := [] }

theorem u2696 : Upper (D 7) (R 7) [6,264,33,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2697 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 7 266 37 88 146 160 96 193 321), lower := (rows 7 266 37 88 146 160 96 128 256), losses := [] }

theorem u2697 : Upper (D 7) (R 7) [6,264,33,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 37 88 176 96 65 130 386), lower := (rows 7 266 37 88 176 96 65 128 256), losses := [] }

theorem u2698 : Upper (D 7) (R 7) [6,264,33,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 144, targets := 66 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 7 266 37 88 176 96 66 129 385), lower := (rows 7 266 37 88 176 96 66 128 256), losses := [] }

theorem u2699 : Upper (D 7) (R 7) [6,264,33,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P07
