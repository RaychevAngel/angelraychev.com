import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0014

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11580 : Route 9 := (fun mask => (mask,id))

def c11580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11580 : Upper (D 7) (R 7) [96,384,3,48,192,2,1] 13 := by
  apply FastRouting.sound _ _ [96,384,3,48,192,2,1] 13 (by decide) (choices 1) [4,8] r11580 c11580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u855
  · exact u856

def b11581 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 97 386 7 56 208 34 68 137 265), lower := (rows 97 386 7 56 208 34 68 128 256), losses := [] }

theorem u11581 : Upper (D 7) (R 7) [96,384,3,48,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11581 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11582 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 386 7 56 208 34 72 133 261), lower := (rows 97 386 7 56 208 34 72 128 256), losses := [] }

theorem u11582 : Upper (D 7) (R 7) [96,384,3,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11582 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11583 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 386 7 56 208 36 65 138 266), lower := (rows 97 386 7 56 208 36 65 128 256), losses := [] }

theorem u11583 : Upper (D 7) (R 7) [96,384,3,48,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11583 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11584 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 1, region := 80, targets := 1 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 97 386 7 56 208 36 66 137 265), lower := (rows 97 386 7 56 208 36 66 128 256), losses := [] }

theorem u11584 : Upper (D 7) (R 7) [96,384,3,48,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11584 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11585 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 386 7 56 208 36 72 131 259), lower := (rows 97 386 7 56 208 36 72 128 256), losses := [] }

theorem u11585 : Upper (D 7) (R 7) [96,384,3,48,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11585 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11586 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 97 386 13 14 145 34 80 224 352), lower := (rows 97 386 13 14 145 34 80 128 256), losses := [] }

theorem u11586 : Upper (D 7) (R 7) [96,384,9,6,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11586 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11587 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 13 14 145 34 96 208 336), lower := (rows 97 386 13 14 145 34 96 128 256), losses := [] }

theorem u11587 : Upper (D 7) (R 7) [96,384,9,6,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11588 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 386 13 14 145 48 96 194 322), lower := (rows 97 386 13 14 145 48 96 128 256), losses := [] }

theorem u11588 : Upper (D 7) (R 7) [96,384,9,6,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11588 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11589 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 65, targets := 130 },{ cop := 0, region := 386, targets := 1 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 386 13 26 52 160 65 194 322), lower := (rows 97 386 13 26 52 160 65 128 256), losses := [] }

theorem u11589 : Upper (D 7) (R 7) [96,384,9,18,36,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11590 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 386, targets := 32 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,1)], upper := (rows 97 386 13 26 52 160 66 193 321), lower := (rows 97 386 13 26 52 160 66 128 256), losses := [{ target := 1, region := (rows 65 0 4 8 20 231 64 193 321), good := (rows 481 416 445 56 52 160 481 160 256) },{ target := 5, region := (rows 1 23 4 24 16 0 95 133 261), good := (rows 451 450 463 90 478 128 66 128 256) }] }

theorem u11590 : Upper (D 7) (R 7) [96,384,9,18,36,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11591 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 386 13 26 145 34 68 224 352), lower := (rows 97 386 13 26 145 34 68 128 256), losses := [] }

theorem u11591 : Upper (D 7) (R 7) [96,384,9,18,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11591 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11592 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 13 26 145 34 96 196 324), lower := (rows 97 386 13 26 145 34 96 128 256), losses := [] }

theorem u11592 : Upper (D 7) (R 7) [96,384,9,18,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11593 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 42 208 36 65 146 274), lower := (rows 97 386 13 42 208 36 65 128 256), losses := [] }

theorem u11593 : Upper (D 7) (R 7) [96,384,9,34,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11593 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11594 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 386 13 42 208 36 66 145 273), lower := (rows 97 386 13 42 208 36 66 128 256), losses := [] }

theorem u11594 : Upper (D 7) (R 7) [96,384,9,34,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11594 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11595 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 386 13 42 208 36 80 131 259), lower := (rows 97 386 13 42 208 36 80 128 256), losses := [] }

theorem u11595 : Upper (D 7) (R 7) [96,384,9,34,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11595 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11596 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 386 13 56 145 34 66 196 324), lower := (rows 97 386 13 56 145 34 66 128 256), losses := [] }

theorem u11596 : Upper (D 7) (R 7) [96,384,9,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11597 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 56 145 34 68 194 322), lower := (rows 97 386 13 56 145 34 68 128 256), losses := [] }

theorem u11597 : Upper (D 7) (R 7) [96,384,9,48,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11597 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11598 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 13 56 208 34 65 134 262), lower := (rows 97 386 13 56 208 34 65 128 256), losses := [] }

theorem u11598 : Upper (D 7) (R 7) [96,384,9,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11599 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 1, region := 120, targets := 1 }], pairs := [(2,1),(3,0),(3,1),(4,1)], upper := (rows 97 386 13 56 208 34 66 133 261), lower := (rows 97 386 13 56 208 34 66 128 256), losses := [] }

theorem u11599 : Upper (D 7) (R 7) [96,384,9,48,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11600 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 56 208 34 68 131 259), lower := (rows 97 386 13 56 208 34 68 128 256), losses := [] }

theorem u11600 : Upper (D 7) (R 7) [96,384,9,48,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11600 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11601 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 386, targets := 1 },{ cop := 1, region := 97, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 97 386 13 152 22 33 66 224 352), lower := (rows 97 386 13 152 22 33 66 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 119 161 289), good := (rows 482 450 478 216 94 482 66 128 256) }] }

theorem u11601 : Upper (D 7) (R 7) [96,384,9,144,6,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11602 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 13 152 22 34 96 193 321), lower := (rows 97 386 13 152 22 34 96 128 256), losses := [] }

theorem u11602 : Upper (D 7) (R 7) [96,384,9,144,6,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11603 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 13 168 82 36 65 146 274), lower := (rows 97 386 13 168 82 36 65 128 256), losses := [] }

theorem u11603 : Upper (D 7) (R 7) [96,384,9,160,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11603 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11604 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 97 386 13 168 82 36 66 145 273), lower := (rows 97 386 13 168 82 36 66 128 256), losses := [] }

theorem u11604 : Upper (D 7) (R 7) [96,384,9,160,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11604 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11605 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 386 13 168 82 36 80 131 259), lower := (rows 97 386 13 168 82 36 80 128 256), losses := [] }

theorem u11605 : Upper (D 7) (R 7) [96,384,9,160,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11605 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11606 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 0, region := 386, targets := 1 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(4,1)], upper := (rows 97 386 14 28 145 33 66 224 352), lower := (rows 97 386 14 28 145 33 66 128 256), losses := [] }

theorem u11606 : Upper (D 7) (R 7) [96,384,10,20,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11607 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 386 14 28 145 34 96 193 321), lower := (rows 97 386 14 28 145 34 96 128 256), losses := [] }

theorem u11607 : Upper (D 7) (R 7) [96,384,10,20,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11608 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 65, targets := 130 },{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(0,1),(0,7),(1,5),(1,6)], upper := (rows 97 386 14 56 84 160 65 131 259), lower := (rows 97 386 14 56 84 160 65 128 256), losses := [] }

theorem u11608 : Upper (D 7) (R 7) [96,384,10,48,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11609 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 124, targets := 1 },{ cop := 2, region := 80, targets := 32 }], pairs := [(2,0),(3,0),(4,0),(4,5)], upper := (rows 97 386 14 56 84 160 66 129 257), lower := (rows 97 386 14 56 84 160 66 128 256), losses := [] }

theorem u11609 : Upper (D 7) (R 7) [96,384,10,48,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11610 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,1)], upper := (rows 97 386 14 56 145 34 65 196 324), lower := (rows 97 386 14 56 145 34 65 128 256), losses := [{ target := 1, region := (rows 41 0 4 8 20 32 125 132 260), good := (rows 97 384 477 121 209 97 65 128 256) },{ target := 5, region := (rows 1 14 12 8 16 0 81 136 264), good := (rows 65 386 398 478 209 2 65 128 256) }] }

theorem u11610 : Upper (D 7) (R 7) [96,384,10,48,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11611 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 97 386 14 56 145 34 68 193 321), lower := (rows 97 386 14 56 145 34 68 128 256), losses := [] }

theorem u11611 : Upper (D 7) (R 7) [96,384,10,48,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11611 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11612 : Route 9 := (fun mask => (mask,id))

def c11612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11612 : Upper (D 7) (R 7) [96,384,10,48,192,2,1] 13 := by
  apply FastRouting.sound _ _ [96,384,10,48,192,2,1] 13 (by decide) (choices 1) [1,4] r11612 c11612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u857
  · exact u858

def b11613 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 124, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 97 386 14 56 208 34 68 129 257), lower := (rows 97 386 14 56 208 34 68 128 256), losses := [] }

theorem u11613 : Upper (D 7) (R 7) [96,384,10,48,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11613 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11614 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 14 152 50 33 65 196 324), lower := (rows 97 386 14 152 50 33 65 128 256), losses := [] }

theorem u11614 : Upper (D 7) (R 7) [96,384,10,144,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11615 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 113, targets := 128 },{ cop := 0, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(4,7)], upper := (rows 97 386 14 152 50 33 68 193 321), lower := (rows 97 386 14 152 50 33 68 128 256), losses := [] }

theorem u11615 : Upper (D 7) (R 7) [96,384,10,144,34,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11615 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11616 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 14 168 82 33 65 148 276), lower := (rows 97 386 14 168 82 33 65 128 256), losses := [] }

theorem u11616 : Upper (D 7) (R 7) [96,384,10,160,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11617 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 97 386 14 168 82 33 68 145 273), lower := (rows 97 386 14 168 82 33 68 128 256), losses := [] }

theorem u11617 : Upper (D 7) (R 7) [96,384,10,160,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11617 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11618 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 14 168 82 33 80 133 261), lower := (rows 97 386 14 168 82 33 80 128 256), losses := [] }

theorem u11618 : Upper (D 7) (R 7) [96,384,10,160,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11618 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11619 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 14 168 84 33 65 146 274), lower := (rows 97 386 14 168 84 33 65 128 256), losses := [] }

theorem u11619 : Upper (D 7) (R 7) [96,384,10,160,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11620 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,7)], upper := (rows 97 386 14 168 84 33 66 145 273), lower := (rows 97 386 14 168 84 33 66 128 256), losses := [] }

theorem u11620 : Upper (D 7) (R 7) [96,384,10,160,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11621 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 386 14 168 84 33 80 131 259), lower := (rows 97 386 14 168 84 33 80 128 256), losses := [] }

theorem u11621 : Upper (D 7) (R 7) [96,384,10,160,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11621 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11622 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 28 42 208 33 65 134 262), lower := (rows 97 386 28 42 208 33 65 128 256), losses := [] }

theorem u11622 : Upper (D 7) (R 7) [96,384,24,34,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11623 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 386 28 42 208 33 66 133 261), lower := (rows 97 386 28 42 208 33 66 128 256), losses := [] }

theorem u11623 : Upper (D 7) (R 7) [96,384,24,34,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11624 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 386 28 42 208 33 68 131 259), lower := (rows 97 386 28 42 208 33 68 128 256), losses := [] }

theorem u11624 : Upper (D 7) (R 7) [96,384,24,34,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11624 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11625 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 386 28 44 145 34 65 194 322), lower := (rows 97 386 28 44 145 34 65 128 256), losses := [] }

theorem u11625 : Upper (D 7) (R 7) [96,384,24,36,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11626 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 97 386 28 44 145 34 66 193 321), lower := (rows 97 386 28 44 145 34 66 128 256), losses := [] }

theorem u11626 : Upper (D 7) (R 7) [96,384,24,36,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11627 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 386 38 74 145 33 68 152 280), lower := (rows 97 386 38 74 145 33 68 128 256), losses := [] }

theorem u11627 : Upper (D 7) (R 7) [96,384,34,66,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11627 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11628 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 74 145 33 72 148 276), lower := (rows 97 386 38 74 145 33 72 128 256), losses := [] }

theorem u11628 : Upper (D 7) (R 7) [96,384,34,66,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11628 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11629 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 386 38 74 145 33 80 140 268), lower := (rows 97 386 38 74 145 33 80 128 256), losses := [] }

theorem u11629 : Upper (D 7) (R 7) [96,384,34,66,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11629 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11630 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 97 386 38 74 145 36 80 137 265), lower := (rows 97 386 38 74 145 36 80 128 256), losses := [] }

theorem u11630 : Upper (D 7) (R 7) [96,384,34,66,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11630 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11631 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 386 38 74 145 40 80 133 261), lower := (rows 97 386 38 74 145 40 80 128 256), losses := [] }

theorem u11631 : Upper (D 7) (R 7) [96,384,34,66,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11631 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11632 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 386 38 74 148 33 65 152 280), lower := (rows 97 386 38 74 148 33 65 128 256), losses := [] }

theorem u11632 : Upper (D 7) (R 7) [96,384,34,66,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11633 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 74 148 33 72 145 273), lower := (rows 97 386 38 74 148 33 72 128 256), losses := [] }

theorem u11633 : Upper (D 7) (R 7) [96,384,34,66,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11633 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11634 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 32 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,5),(3,5)], upper := (rows 97 386 38 74 148 33 80 137 265), lower := (rows 97 386 38 74 148 33 80 128 256), losses := [] }

theorem u11634 : Upper (D 7) (R 7) [96,384,34,66,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11634 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11635 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 109, targets := 128 },{ cop := 2, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 97 386 38 76 145 33 66 152 280), lower := (rows 97 386 38 76 145 33 66 128 256), losses := [] }

theorem u11635 : Upper (D 7) (R 7) [96,384,34,68,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11636 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 73, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 386 38 76 145 33 72 146 274), lower := (rows 97 386 38 76 145 33 72 128 256), losses := [] }

theorem u11636 : Upper (D 7) (R 7) [96,384,34,68,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11636 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11637 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 386 38 76 145 33 80 138 266), lower := (rows 97 386 38 76 145 33 80 128 256), losses := [] }

theorem u11637 : Upper (D 7) (R 7) [96,384,34,68,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11637 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11638 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 386 38 76 145 48 65 138 266), lower := (rows 97 386 38 76 145 48 65 128 256), losses := [] }

theorem u11638 : Upper (D 7) (R 7) [96,384,34,68,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11639 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 72, targets := 33 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(3,0),(3,5)], upper := (rows 97 386 38 76 145 48 66 137 265), lower := (rows 97 386 38 76 145 48 66 128 256), losses := [] }

theorem u11639 : Upper (D 7) (R 7) [96,384,34,68,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11639
end Delivery.IrregularNine14.P07
