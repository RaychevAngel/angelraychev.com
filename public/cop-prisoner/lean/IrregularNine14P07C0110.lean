import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 44 200 148 33 66 145 273), lower := (rows 35 322 44 200 148 33 66 128 256), losses := [] }

theorem u6600 : Upper (D 7) (R 7) [34,320,40,192,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 44 200 148 33 80 131 259), lower := (rows 35 322 44 200 148 33 80 128 256), losses := [] }

theorem u6601 : Upper (D 7) (R 7) [34,320,40,192,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6601 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6602 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 322 69 137 146 40 68 176 304), lower := (rows 35 322 69 137 146 40 68 128 256), losses := [] }

theorem u6602 : Upper (D 7) (R 7) [34,320,65,129,130,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6602 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6603 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 168, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 35 322 69 137 146 40 80 164 292), lower := (rows 35 322 69 137 146 40 80 128 256), losses := [] }

theorem u6603 : Upper (D 7) (R 7) [34,320,65,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6603 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 69 137 146 40 96 148 276), lower := (rows 35 322 69 137 146 40 96 128 256), losses := [] }

theorem u6604 : Upper (D 7) (R 7) [34,320,65,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6604 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 184, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 322 69 137 148 40 66 176 304), lower := (rows 35 322 69 137 148 40 66 128 256), losses := [] }

theorem u6605 : Upper (D 7) (R 7) [34,320,65,129,132,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6605 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 169, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 322 69 137 148 40 80 162 290), lower := (rows 35 322 69 137 148 40 80 128 256), losses := [] }

theorem u6606 : Upper (D 7) (R 7) [34,320,65,129,132,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6606 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6607 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 69 137 148 40 96 146 274), lower := (rows 35 322 69 137 148 40 96 128 256), losses := [] }

theorem u6607 : Upper (D 7) (R 7) [34,320,65,129,132,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6607 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6608 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 184, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 322 69 137 148 48 66 168 296), lower := (rows 35 322 69 137 148 48 66 128 256), losses := [] }

theorem u6608 : Upper (D 7) (R 7) [34,320,65,129,132,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6609 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 35 322 69 137 148 48 72 162 290), lower := (rows 35 322 69 137 148 48 72 128 256), losses := [] }

theorem u6609 : Upper (D 7) (R 7) [34,320,65,129,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6609 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6610 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 69 137 148 48 96 138 266), lower := (rows 35 322 69 137 148 48 96 128 256), losses := [] }

theorem u6610 : Upper (D 7) (R 7) [34,320,65,129,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6610 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 176, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 35 322 69 138 148 33 72 176 304), lower := (rows 35 322 69 138 148 33 72 128 256), losses := [] }

theorem u6611 : Upper (D 7) (R 7) [34,320,65,130,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6611 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 322 69 138 148 33 80 168 296), lower := (rows 35 322 69 138 148 33 80 128 256), losses := [] }

theorem u6612 : Upper (D 7) (R 7) [34,320,65,130,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6612 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6613 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 322 69 138 148 33 96 152 280), lower := (rows 35 322 69 138 148 33 96 128 256), losses := [] }

theorem u6613 : Upper (D 7) (R 7) [34,320,65,130,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6614 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 322 69 138 148 48 65 168 296), lower := (rows 35 322 69 138 148 48 65 128 256), losses := [] }

theorem u6614 : Upper (D 7) (R 7) [34,320,65,130,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 176, targets := 66 }], pairs := [(4,1),(4,6)], upper := (rows 35 322 69 138 148 48 72 161 289), lower := (rows 35 322 69 138 148 48 72 128 256), losses := [] }

theorem u6615 : Upper (D 7) (R 7) [34,320,65,130,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6615 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 322 69 138 148 48 96 137 265), lower := (rows 35 322 69 138 148 48 96 128 256), losses := [] }

theorem u6616 : Upper (D 7) (R 7) [34,320,65,130,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6616 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 322 76 137 146 33 68 176 304), lower := (rows 35 322 76 137 146 33 68 128 256), losses := [] }

theorem u6617 : Upper (D 7) (R 7) [34,320,72,129,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6617 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 76 137 146 33 80 164 292), lower := (rows 35 322 76 137 146 33 80 128 256), losses := [] }

theorem u6618 : Upper (D 7) (R 7) [34,320,72,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6618 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 76 137 146 33 96 148 276), lower := (rows 35 322 76 137 146 33 96 128 256), losses := [] }

theorem u6619 : Upper (D 7) (R 7) [34,320,72,129,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6620 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 35 322 76 137 146 36 65 176 304), lower := (rows 35 322 76 137 146 36 65 128 256), losses := [] }

theorem u6620 : Upper (D 7) (R 7) [34,320,72,129,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6620 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6621 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 322 76 137 146 36 80 161 289), lower := (rows 35 322 76 137 146 36 80 128 256), losses := [] }

theorem u6621 : Upper (D 7) (R 7) [34,320,72,129,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6621 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6622 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 35 322 76 137 146 36 96 145 273), lower := (rows 35 322 76 137 146 36 96 128 256), losses := [] }

theorem u6622 : Upper (D 7) (R 7) [34,320,72,129,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6622 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6623 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 76 137 148 33 66 176 304), lower := (rows 35 322 76 137 148 33 66 128 256), losses := [] }

theorem u6623 : Upper (D 7) (R 7) [34,320,72,129,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6624 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 322 76 137 148 33 80 162 290), lower := (rows 35 322 76 137 148 33 80 128 256), losses := [] }

theorem u6624 : Upper (D 7) (R 7) [34,320,72,129,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6624 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6625 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 76 137 148 33 96 146 274), lower := (rows 35 322 76 137 148 33 96 128 256), losses := [] }

theorem u6625 : Upper (D 7) (R 7) [34,320,72,129,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6626 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 322 76 138 145 33 68 176 304), lower := (rows 35 322 76 138 145 33 68 128 256), losses := [] }

theorem u6626 : Upper (D 7) (R 7) [34,320,72,130,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6626 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6627 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 76 138 145 33 80 164 292), lower := (rows 35 322 76 138 145 33 80 128 256), losses := [] }

theorem u6627 : Upper (D 7) (R 7) [34,320,72,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6627 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6628 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 35 322 76 138 145 33 96 148 276), lower := (rows 35 322 76 138 145 33 96 128 256), losses := [] }

theorem u6628 : Upper (D 7) (R 7) [34,320,72,130,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6629 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 322 76 138 145 48 65 164 292), lower := (rows 35 322 76 138 145 48 65 128 256), losses := [{ target := 0, region := (rows 0 66 70 73 16 48 64 129 257), good := (rows 430 334 78 142 440 48 462 128 256) }] }

theorem u6629 : Upper (D 7) (R 7) [34,320,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6630 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 322 76 138 145 48 68 161 289), lower := (rows 35 322 76 138 145 48 68 128 256), losses := [] }

theorem u6630 : Upper (D 7) (R 7) [34,320,72,130,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6630 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6631 : Route 9 := (fun mask => (mask,id))

def c6631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6631 : Upper (D 7) (R 7) [34,320,72,130,129,16,32] 13 := by
  apply FastRouting.sound _ _ [34,320,72,130,129,16,32] 13 (by decide) (choices 1) [1,4] r6631 c6631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u490
  · exact u491

def b6632 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6)], upper := (rows 35 322 76 138 176 33 65 148 276), lower := (rows 35 322 76 138 176 33 65 128 256), losses := [] }

theorem u6632 : Upper (D 7) (R 7) [34,320,72,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6633 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 322 76 138 176 33 68 145 273), lower := (rows 35 322 76 138 176 33 68 128 256), losses := [] }

theorem u6633 : Upper (D 7) (R 7) [34,320,72,130,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6633 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6634 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 76 138 176 33 80 133 261), lower := (rows 35 322 76 138 176 33 80 128 256), losses := [] }

theorem u6634 : Upper (D 7) (R 7) [34,320,72,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6634 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6635 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 76 168 146 33 65 148 276), lower := (rows 35 322 76 168 146 33 65 128 256), losses := [] }

theorem u6635 : Upper (D 7) (R 7) [34,320,72,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 322 76 168 146 33 68 145 273), lower := (rows 35 322 76 168 146 33 68 128 256), losses := [] }

theorem u6636 : Upper (D 7) (R 7) [34,320,72,160,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6636 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6637 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 76 168 146 33 80 133 261), lower := (rows 35 322 76 168 146 33 80 128 256), losses := [] }

theorem u6637 : Upper (D 7) (R 7) [34,320,72,160,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6637 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6638 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 76 168 148 33 65 146 274), lower := (rows 35 322 76 168 148 33 65 128 256), losses := [] }

theorem u6638 : Upper (D 7) (R 7) [34,320,72,160,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6639 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 8, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 35 322 76 168 148 33 66 145 273), lower := (rows 35 322 76 168 148 33 66 128 256), losses := [] }

theorem u6639 : Upper (D 7) (R 7) [34,320,72,160,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6640 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 322 76 168 148 33 80 131 259), lower := (rows 35 322 76 168 148 33 80 128 256), losses := [] }

theorem u6640 : Upper (D 7) (R 7) [34,320,72,160,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6640 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6641 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 100 137 146 40 65 148 276), lower := (rows 35 322 100 137 146 40 65 128 256), losses := [] }

theorem u6641 : Upper (D 7) (R 7) [34,320,96,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6641 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6642 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 322 100 137 146 40 68 145 273), lower := (rows 35 322 100 137 146 40 68 128 256), losses := [] }

theorem u6642 : Upper (D 7) (R 7) [34,320,96,129,130,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6642 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6643 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 259, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 322 100 137 146 40 80 133 261), lower := (rows 35 322 100 137 146 40 80 128 256), losses := [] }

theorem u6643 : Upper (D 7) (R 7) [34,320,96,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6643 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6644 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 35 322 100 137 148 33 66 152 280), lower := (rows 35 322 100 137 148 33 66 128 256), losses := [] }

theorem u6644 : Upper (D 7) (R 7) [34,320,96,129,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6645 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 100 137 148 33 72 146 274), lower := (rows 35 322 100 137 148 33 72 128 256), losses := [] }

theorem u6645 : Upper (D 7) (R 7) [34,320,96,129,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6645 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6646 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 322 100 137 148 33 80 138 266), lower := (rows 35 322 100 137 148 33 80 128 256), losses := [] }

theorem u6646 : Upper (D 7) (R 7) [34,320,96,129,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6646 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 100 137 148 40 65 146 274), lower := (rows 35 322 100 137 148 40 65 128 256), losses := [] }

theorem u6647 : Upper (D 7) (R 7) [34,320,96,129,132,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6647 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6648 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 100 137 148 40 66 145 273), lower := (rows 35 322 100 137 148 40 66 128 256), losses := [] }

theorem u6648 : Upper (D 7) (R 7) [34,320,96,129,132,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6648 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6649 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 322 100 137 148 40 80 131 259), lower := (rows 35 322 100 137 148 40 80 128 256), losses := [] }

theorem u6649 : Upper (D 7) (R 7) [34,320,96,129,132,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6649 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6650 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 322 100 138 148 33 65 152 280), lower := (rows 35 322 100 138 148 33 65 128 256), losses := [] }

theorem u6650 : Upper (D 7) (R 7) [34,320,96,130,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6651 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7)], upper := (rows 35 322 100 138 148 33 72 145 273), lower := (rows 35 322 100 138 148 33 72 128 256), losses := [] }

theorem u6651 : Upper (D 7) (R 7) [34,320,96,130,132,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6651 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6652 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 322 100 138 148 33 80 137 265), lower := (rows 35 322 100 138 148 33 80 128 256), losses := [] }

theorem u6652 : Upper (D 7) (R 7) [34,320,96,130,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6652 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6653 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 42 21 74 146 288 65 192 448), lower := (rows 37 42 21 74 146 288 65 128 256), losses := [] }

theorem u6653 : Upper (D 7) (R 7) [36,40,17,66,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6653 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6654 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 33 },{ cop := 4, region := 357, targets := 2 }], pairs := [(0,1),(3,0),(3,5)], upper := (rows 37 42 21 74 146 288 192 193 321), lower := (rows 37 42 21 74 146 288 192 128 256), losses := [] }

theorem u6654 : Upper (D 7) (R 7) [36,40,17,66,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6654 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6655 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 42 21 74 208 288 65 130 386), lower := (rows 37 42 21 74 208 288 65 128 256), losses := [] }

theorem u6655 : Upper (D 7) (R 7) [36,40,17,66,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6655 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6656 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 293, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 42 21 74 208 288 66 129 385), lower := (rows 37 42 21 74 208 288 66 128 256), losses := [] }

theorem u6656 : Upper (D 7) (R 7) [36,40,17,66,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6656 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6657 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 21 74 208 288 192 131 259), lower := (rows 37 42 21 74 208 288 192 128 256), losses := [] }

theorem u6657 : Upper (D 7) (R 7) [36,40,17,66,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6657 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6658 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 74, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 37 42 21 74 274 160 65 192 448), lower := (rows 37 42 21 74 274 160 65 128 256), losses := [] }

theorem u6658 : Upper (D 7) (R 7) [36,40,17,66,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6659 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 21 74 274 160 192 193 321), lower := (rows 37 42 21 74 274 160 192 128 256), losses := [] }

theorem u6659 : Upper (D 7) (R 7) [36,40,17,66,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P07
