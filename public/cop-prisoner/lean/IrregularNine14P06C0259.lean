import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0061

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15540 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 296 21 34 68 196 324), lower := (rows 11 131 52 296 21 34 64 128 256), losses := [] }

theorem u15540 : Upper (D 6) (R 6) [10,129,48,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15541 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 131 52 296 21 36 66 194 322), lower := (rows 11 131 52 296 21 36 64 128 256), losses := [] }

theorem u15541 : Upper (D 6) (R 6) [10,129,48,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15542 : Route 9 := (fun mask => (mask,id))

def c15542 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15542 : Upper (D 6) (R 6) [10,129,48,288,5,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,5,64] 13 (by decide) (choices 1) [2,4] r15542 c15542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3680
  · exact u3681

def b15543 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 296 22 33 68 196 324), lower := (rows 11 131 52 296 22 33 64 128 256), losses := [] }

theorem u15543 : Upper (D 6) (R 6) [10,129,48,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15544 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 52 296 22 36 65 193 321), lower := (rows 11 131 52 296 22 36 64 128 256), losses := [] }

theorem u15544 : Upper (D 6) (R 6) [10,129,48,288,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15545 : Route 9 := (fun mask => (mask,id))

def c15545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15545 : Upper (D 6) (R 6) [10,129,48,288,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,6,64] 13 (by decide) (choices 1) [1,4] r15545 c15545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3682
  · exact u3683

def b15546 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 296 81 34 68 196 324), lower := (rows 11 131 52 296 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 16 35 84 148 276), good := (rows 42 162 508 296 508 34 64 128 256) }] }

theorem u15546 : Upper (D 6) (R 6) [10,129,48,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15547 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 296 81 36 70 198 326), lower := (rows 11 131 52 296 81 36 64 128 256), losses := [] }

theorem u15547 : Upper (D 6) (R 6) [10,129,48,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15548 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 296 81 96 70 134 262), lower := (rows 11 131 52 296 81 96 64 128 256), losses := [] }

theorem u15548 : Upper (D 6) (R 6) [10,129,48,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15549 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 52 296 82 33 68 196 324), lower := (rows 11 131 52 296 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 17 32 108 172 300), good := (rows 474 146 508 492 82 508 64 128 256) }] }

theorem u15549 : Upper (D 6) (R 6) [10,129,48,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15550 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 296 82 36 69 197 325), lower := (rows 11 131 52 296 82 36 64 128 256), losses := [] }

theorem u15550 : Upper (D 6) (R 6) [10,129,48,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15551 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 52 296 82 96 69 133 261), lower := (rows 11 131 52 296 82 96 64 128 256), losses := [] }

theorem u15551 : Upper (D 6) (R 6) [10,129,48,288,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15552 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 52 296 84 33 70 198 326), lower := (rows 11 131 52 296 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 49 32 65 129 257), good := (rows 478 466 60 316 84 508 64 128 256) }] }

theorem u15552 : Upper (D 6) (R 6) [10,129,48,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15553 : Route 9 := (fun mask => (mask,id))

def c15553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15553 : Upper (D 6) (R 6) [10,129,48,288,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,288,68,2] 13 (by decide) (choices 1) [1,4] r15553 c15553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3684
  · exact u3685

def b15554 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 52 296 84 36 67 195 323), lower := (rows 11 131 52 296 84 36 64 128 256), losses := [] }

theorem u15554 : Upper (D 6) (R 6) [10,129,48,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15555 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 296 84 96 71 135 263), lower := (rows 11 131 52 296 84 96 64 128 256), losses := [] }

theorem u15555 : Upper (D 6) (R 6) [10,129,48,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15556 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 328 21 34 100 228 356), lower := (rows 11 131 52 328 21 34 64 128 256), losses := [] }

theorem u15556 : Upper (D 6) (R 6) [10,129,48,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15557 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 131 52 328 21 36 98 226 354), lower := (rows 11 131 52 328 21 36 64 128 256), losses := [] }

theorem u15557 : Upper (D 6) (R 6) [10,129,48,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15558 : PairBound 9 := { available := 38, camps := [], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 131 52 328 21 96 102 166 294), lower := (rows 11 131 52 328 21 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 19 104 64 128 256), good := (rows 61 149 52 360 21 96 96 128 256) },{ target := 6, region := (rows 1 18 4 8 16 32 0 132 260), good := (rows 11 131 438 264 407 32 0 128 256) }] }

theorem u15558 : Upper (D 6) (R 6) [10,129,48,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15559 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 131 52 328 22 33 100 228 356), lower := (rows 11 131 52 328 22 33 64 128 256), losses := [] }

theorem u15559 : Upper (D 6) (R 6) [10,129,48,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15560 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 52 328 22 36 97 225 353), lower := (rows 11 131 52 328 22 36 64 128 256), losses := [] }

theorem u15560 : Upper (D 6) (R 6) [10,129,48,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15561 : Route 9 := (fun mask => (mask,id))

def c15561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15561 : Upper (D 6) (R 6) [10,129,48,320,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,6,64] 13 (by decide) (choices 1) [1,4,32] r15561 c15561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3686
  · exact u3687
  · exact u3688

def b15562 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 131 52 328 81 34 100 164 292), lower := (rows 11 131 52 328 81 34 64 128 256), losses := [] }

theorem u15562 : Upper (D 6) (R 6) [10,129,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15563 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 131 52 328 81 36 102 166 294), lower := (rows 11 131 52 328 81 36 64 128 256), losses := [] }

theorem u15563 : Upper (D 6) (R 6) [10,129,48,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15564 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 131 52 328 82 33 100 164 292), lower := (rows 11 131 52 328 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 35 84 148 276), good := (rows 41 161 508 328 508 33 64 128 256) }] }

theorem u15564 : Upper (D 6) (R 6) [10,129,48,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15565 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 52 328 82 36 101 165 293), lower := (rows 11 131 52 328 82 36 64 128 256), losses := [] }

theorem u15565 : Upper (D 6) (R 6) [10,129,48,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15566 : Route 9 := (fun mask => (mask,id))

def c15566 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15566 : Upper (D 6) (R 6) [10,129,48,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,68,1] 13 (by decide) (choices 1) [2,4,32] r15566 c15566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3689
  · exact u3690
  · exact u3691

def r15567 : Route 9 := (fun mask => (mask,id))

def c15567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15567 : Upper (D 6) (R 6) [10,129,48,320,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,48,320,68,2] 13 (by decide) (choices 1) [1,4,32] r15567 c15567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3692
  · exact u3693
  · exact u3694

def b15568 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 52 328 84 36 99 163 291), lower := (rows 11 131 52 328 84 36 64 128 256), losses := [] }

theorem u15568 : Upper (D 6) (R 6) [10,129,48,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15569 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 13 276 34 112 240 368), lower := (rows 11 131 100 13 276 34 64 128 256), losses := [] }

theorem u15569 : Upper (D 6) (R 6) [10,129,96,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15570 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 100 13 276 48 98 226 354), lower := (rows 11 131 100 13 276 48 64 128 256), losses := [] }

theorem u15570 : Upper (D 6) (R 6) [10,129,96,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15570 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15571 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 13 276 96 114 178 306), lower := (rows 11 131 100 13 276 96 64 128 256), losses := [] }

theorem u15571 : Upper (D 6) (R 6) [10,129,96,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15572 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 13 304 34 84 212 340), lower := (rows 11 131 100 13 304 34 64 128 256), losses := [] }

theorem u15572 : Upper (D 6) (R 6) [10,129,96,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15573 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 13 304 36 82 210 338), lower := (rows 11 131 100 13 304 36 64 128 256), losses := [] }

theorem u15573 : Upper (D 6) (R 6) [10,129,96,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15574 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 100 13 304 48 70 198 326), lower := (rows 11 131 100 13 304 48 64 128 256), losses := [] }

theorem u15574 : Upper (D 6) (R 6) [10,129,96,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15574 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15575 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 13 304 96 86 150 278), lower := (rows 11 131 100 13 304 96 64 128 256), losses := [] }

theorem u15575 : Upper (D 6) (R 6) [10,129,96,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15576 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 25 276 34 100 228 356), lower := (rows 11 131 100 25 276 34 64 128 256), losses := [] }

theorem u15576 : Upper (D 6) (R 6) [10,129,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15577 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 25 276 36 98 226 354), lower := (rows 11 131 100 25 276 36 64 128 256), losses := [] }

theorem u15577 : Upper (D 6) (R 6) [10,129,96,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15578 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 25 276 96 102 166 294), lower := (rows 11 131 100 25 276 96 64 128 256), losses := [] }

theorem u15578 : Upper (D 6) (R 6) [10,129,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15579 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 25 304 34 68 196 324), lower := (rows 11 131 100 25 304 34 64 128 256), losses := [] }

theorem u15579 : Upper (D 6) (R 6) [10,129,96,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15580 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 25 304 36 70 198 326), lower := (rows 11 131 100 25 304 36 64 128 256), losses := [] }

theorem u15580 : Upper (D 6) (R 6) [10,129,96,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15581 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 25 304 96 70 134 262), lower := (rows 11 131 100 25 304 96 64 128 256), losses := [] }

theorem u15581 : Upper (D 6) (R 6) [10,129,96,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15582 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 28 273 34 100 228 356), lower := (rows 11 131 100 28 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 494 486 484 476 508 486 64 128 256) }] }

theorem u15582 : Upper (D 6) (R 6) [10,129,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15583 : PairBound 9 := { available := 98, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 100 28 273 36 98 226 354), lower := (rows 11 131 100 28 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 87 24 16 127 67 131 259), good := (rows 494 486 100 60 508 36 100 128 256) }] }

theorem u15583 : Upper (D 6) (R 6) [10,129,96,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15584 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 28 273 96 102 166 294), lower := (rows 11 131 100 28 273 96 64 128 256), losses := [] }

theorem u15584 : Upper (D 6) (R 6) [10,129,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15585 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 28 274 33 100 228 356), lower := (rows 11 131 100 28 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 55 24 16 35 119 183 311), good := (rows 493 485 484 476 508 485 64 128 256) }] }

theorem u15585 : Upper (D 6) (R 6) [10,129,96,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15586 : PairBound 9 := { available := 97, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 131 100 28 274 36 97 225 353), lower := (rows 11 131 100 28 274 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 87 24 16 127 67 131 259), good := (rows 493 485 100 60 508 36 100 128 256) }] }

theorem u15586 : Upper (D 6) (R 6) [10,129,96,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15587 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 28 274 96 101 165 293), lower := (rows 11 131 100 28 274 96 64 128 256), losses := [] }

theorem u15587 : Upper (D 6) (R 6) [10,129,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15588 : Route 9 := (fun mask => (mask,id))

def c15588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15588 : Upper (D 6) (R 6) [10,129,96,20,288,1] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20,288,1] 13 (by decide) (choices 1) [2,4] r15588 c15588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3695
  · exact u3696

def r15589 : Route 9 := (fun mask => (mask,id))

def c15589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15589 : Upper (D 6) (R 6) [10,129,96,20,288,2] 13 := by
  apply FastRouting.sound _ _ [10,129,96,20,288,2] 13 (by decide) (choices 1) [1,4] r15589 c15589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3697
  · exact u3698

def b15590 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 100 28 304 36 67 195 323), lower := (rows 11 131 100 28 304 36 64 128 256), losses := [] }

theorem u15590 : Upper (D 6) (R 6) [10,129,96,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15591 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 28 304 96 71 135 263), lower := (rows 11 131 100 28 304 96 64 128 256), losses := [] }

theorem u15591 : Upper (D 6) (R 6) [10,129,96,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15592 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 100 41 276 34 84 212 340), lower := (rows 11 131 100 41 276 34 64 128 256), losses := [] }

theorem u15592 : Upper (D 6) (R 6) [10,129,96,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15593 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 41 276 36 82 210 338), lower := (rows 11 131 100 41 276 36 64 128 256), losses := [] }

theorem u15593 : Upper (D 6) (R 6) [10,129,96,33,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15594 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 131 100 41 276 48 70 198 326), lower := (rows 11 131 100 41 276 48 64 128 256), losses := [] }

theorem u15594 : Upper (D 6) (R 6) [10,129,96,33,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15594 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15595 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 131 100 41 276 96 86 150 278), lower := (rows 11 131 100 41 276 96 64 128 256), losses := [] }

theorem u15595 : Upper (D 6) (R 6) [10,129,96,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15596 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 131 100 41 336 34 84 148 276), lower := (rows 11 131 100 41 336 34 64 128 256), losses := [] }

theorem u15596 : Upper (D 6) (R 6) [10,129,96,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15597 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 372, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 100 41 336 36 86 150 278), lower := (rows 11 131 100 41 336 36 64 128 256), losses := [] }

theorem u15597 : Upper (D 6) (R 6) [10,129,96,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15598 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 100 41 336 48 70 134 262), lower := (rows 11 131 100 41 336 48 64 128 256), losses := [] }

theorem u15598 : Upper (D 6) (R 6) [10,129,96,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15598 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15599 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 131 100 56 22 33 324 452 324), lower := (rows 11 131 100 56 22 33 64 128 256), losses := [] }

theorem u15599 : Upper (D 6) (R 6) [10,129,96,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15599
end Delivery.IrregularNine14.P06
