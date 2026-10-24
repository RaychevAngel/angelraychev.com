import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0121

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23580 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 13 88 33 114 178 306), lower := (rows 35 134 324 13 88 33 64 128 256), losses := [] }

theorem u23580 : Upper (D 6) (R 6) [34,132,320,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23581 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 13 88 34 113 177 305), lower := (rows 35 134 324 13 88 34 64 128 256), losses := [] }

theorem u23581 : Upper (D 6) (R 6) [34,132,320,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23582 : PairBound 9 := { available := 35, camps := [], pairs := [(0,6),(4,2)], upper := (rows 35 134 324 13 88 48 99 163 291), lower := (rows 35 134 324 13 88 48 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 24 56 65 129 257), good := (rows 483 130 320 505 120 48 64 128 256) },{ target := 6, region := (rows 17 10 4 8 16 48 0 145 273), good := (rows 419 134 260 399 443 433 0 128 256) }] }

theorem u23582 : Upper (D 6) (R 6) [34,132,320,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23582 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23583 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 13 112 33 90 154 282), lower := (rows 35 134 324 13 112 33 64 128 256), losses := [] }

theorem u23583 : Upper (D 6) (R 6) [34,132,320,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23584 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 13 112 34 89 153 281), lower := (rows 35 134 324 13 112 34 64 128 256), losses := [] }

theorem u23584 : Upper (D 6) (R 6) [34,132,320,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23585 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 13 112 40 83 147 275), lower := (rows 35 134 324 13 112 40 64 128 256), losses := [] }

theorem u23585 : Upper (D 6) (R 6) [34,132,320,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23585 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23586 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 324 13 112 48 75 139 267), lower := (rows 35 134 324 13 112 48 64 128 256), losses := [] }

theorem u23586 : Upper (D 6) (R 6) [34,132,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23587 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 324 25 28 33 98 226 354), lower := (rows 35 134 324 25 28 33 64 128 256), losses := [] }

theorem u23587 : Upper (D 6) (R 6) [34,132,320,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23588 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 25 28 34 97 225 353), lower := (rows 35 134 324 25 28 34 64 128 256), losses := [] }

theorem u23588 : Upper (D 6) (R 6) [34,132,320,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23589 : Route 9 := (fun mask => (mask,id))

def c23589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23589 : Upper (D 6) (R 6) [34,132,320,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,132,320,17,12,64] 13 (by decide) (choices 1) [1,2,32] r23589 c23589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7273
  · exact u7274
  · exact u7275

def b23590 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 324 25 52 33 74 202 330), lower := (rows 35 134 324 25 52 33 64 128 256), losses := [] }

theorem u23590 : Upper (D 6) (R 6) [34,132,320,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23591 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 25 52 34 73 201 329), lower := (rows 35 134 324 25 52 34 64 128 256), losses := [] }

theorem u23591 : Upper (D 6) (R 6) [34,132,320,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23592 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 25 52 40 67 195 323), lower := (rows 35 134 324 25 52 40 64 128 256), losses := [] }

theorem u23592 : Upper (D 6) (R 6) [34,132,320,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23592 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23593 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 324 25 52 96 75 139 267), lower := (rows 35 134 324 25 52 96 64 128 256), losses := [] }

theorem u23593 : Upper (D 6) (R 6) [34,132,320,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23594 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 324 25 82 33 108 172 300), lower := (rows 35 134 324 25 82 33 64 128 256), losses := [] }

theorem u23594 : Upper (D 6) (R 6) [34,132,320,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23595 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 324 25 82 36 105 169 297), lower := (rows 35 134 324 25 82 36 64 128 256), losses := [] }

theorem u23595 : Upper (D 6) (R 6) [34,132,320,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23596 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 324 25 82 40 101 165 293), lower := (rows 35 134 324 25 82 40 64 128 256), losses := [] }

theorem u23596 : Upper (D 6) (R 6) [34,132,320,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23596 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23597 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,0),(2,0)], upper := (rows 35 134 324 25 88 33 102 166 294), lower := (rows 35 134 324 25 88 33 64 128 256), losses := [] }

theorem u23597 : Upper (D 6) (R 6) [34,132,320,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23598 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 25 88 34 101 165 293), lower := (rows 35 134 324 25 88 34 64 128 256), losses := [] }

theorem u23598 : Upper (D 6) (R 6) [34,132,320,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23599 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 324 25 88 36 99 163 291), lower := (rows 35 134 324 25 88 36 64 128 256), losses := [] }

theorem u23599 : Upper (D 6) (R 6) [34,132,320,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23600 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 324 25 112 33 78 142 270), lower := (rows 35 134 324 25 112 33 64 128 256), losses := [] }

theorem u23600 : Upper (D 6) (R 6) [34,132,320,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23601 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 25 112 34 77 141 269), lower := (rows 35 134 324 25 112 34 64 128 256), losses := [] }

theorem u23601 : Upper (D 6) (R 6) [34,132,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23602 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 324 25 112 36 75 139 267), lower := (rows 35 134 324 25 112 36 64 128 256), losses := [] }

theorem u23602 : Upper (D 6) (R 6) [34,132,320,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23603 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 324 25 112 40 71 135 263), lower := (rows 35 134 324 25 112 40 64 128 256), losses := [] }

theorem u23603 : Upper (D 6) (R 6) [34,132,320,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23603 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23604 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 324 26 52 33 73 201 329), lower := (rows 35 134 324 26 52 33 64 128 256), losses := [] }

theorem u23604 : Upper (D 6) (R 6) [34,132,320,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23605 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 324 26 52 40 65 193 321), lower := (rows 35 134 324 26 52 40 64 128 256), losses := [] }

theorem u23605 : Upper (D 6) (R 6) [34,132,320,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23605 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23606 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 324 26 52 96 73 137 265), lower := (rows 35 134 324 26 52 96 64 128 256), losses := [] }

theorem u23606 : Upper (D 6) (R 6) [34,132,320,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23607 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 324 26 81 33 108 172 300), lower := (rows 35 134 324 26 81 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 132 324 508 113 33 64 128 256) }] }

theorem u23607 : Upper (D 6) (R 6) [34,132,320,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23608 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 324 26 81 36 105 169 297), lower := (rows 35 134 324 26 81 36 64 128 256), losses := [] }

theorem u23608 : Upper (D 6) (R 6) [34,132,320,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23609 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 324 26 81 40 101 165 293), lower := (rows 35 134 324 26 81 40 64 128 256), losses := [] }

theorem u23609 : Upper (D 6) (R 6) [34,132,320,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23609 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23610 : Route 9 := (fun mask => (mask,id))

def c23610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23610 : Upper (D 6) (R 6) [34,132,320,18,96,1] 13 := by
  apply FastRouting.sound _ _ [34,132,320,18,96,1] 13 (by decide) (choices 1) [1,4,8] r23610 c23610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7276
  · exact u7277
  · exact u7278

def b23611 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 324 26 112 36 73 137 265), lower := (rows 35 134 324 26 112 36 64 128 256), losses := [] }

theorem u23611 : Upper (D 6) (R 6) [34,132,320,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23612 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 324 26 112 40 69 133 261), lower := (rows 35 134 324 26 112 40 64 128 256), losses := [] }

theorem u23612 : Upper (D 6) (R 6) [34,132,320,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23612 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23613 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 324 28 81 33 106 170 298), lower := (rows 35 134 324 28 81 33 64 128 256), losses := [] }

theorem u23613 : Upper (D 6) (R 6) [34,132,320,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23614 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 28 81 34 105 169 297), lower := (rows 35 134 324 28 81 34 64 128 256), losses := [] }

theorem u23614 : Upper (D 6) (R 6) [34,132,320,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23615 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 324 28 81 40 99 163 291), lower := (rows 35 134 324 28 81 40 64 128 256), losses := [] }

theorem u23615 : Upper (D 6) (R 6) [34,132,320,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23615 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23616 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 324 28 82 33 105 169 297), lower := (rows 35 134 324 28 82 33 64 128 256), losses := [] }

theorem u23616 : Upper (D 6) (R 6) [34,132,320,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23617 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 324 28 82 40 97 161 289), lower := (rows 35 134 324 28 82 40 64 128 256), losses := [] }

theorem u23617 : Upper (D 6) (R 6) [34,132,320,20,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23617 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23618 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 324 28 112 33 75 139 267), lower := (rows 35 134 324 28 112 33 64 128 256), losses := [] }

theorem u23618 : Upper (D 6) (R 6) [34,132,320,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23619 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 28 112 34 73 137 265), lower := (rows 35 134 324 28 112 34 64 128 256), losses := [] }

theorem u23619 : Upper (D 6) (R 6) [34,132,320,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23620 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 324 28 112 40 67 131 259), lower := (rows 35 134 324 28 112 40 64 128 256), losses := [] }

theorem u23620 : Upper (D 6) (R 6) [34,132,320,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23620 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23621 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 44 81 33 90 154 282), lower := (rows 35 134 324 44 81 33 64 128 256), losses := [] }

theorem u23621 : Upper (D 6) (R 6) [34,132,320,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23622 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 44 81 34 89 153 281), lower := (rows 35 134 324 44 81 34 64 128 256), losses := [] }

theorem u23622 : Upper (D 6) (R 6) [34,132,320,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23623 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 324 44 81 40 83 147 275), lower := (rows 35 134 324 44 81 40 64 128 256), losses := [] }

theorem u23623 : Upper (D 6) (R 6) [34,132,320,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23623 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23624 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 324 44 81 48 75 139 267), lower := (rows 35 134 324 44 81 48 64 128 256), losses := [] }

theorem u23624 : Upper (D 6) (R 6) [34,132,320,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23624 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23625 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 44 82 33 89 153 281), lower := (rows 35 134 324 44 82 33 64 128 256), losses := [] }

theorem u23625 : Upper (D 6) (R 6) [34,132,320,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23626 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 324 44 82 40 81 145 273), lower := (rows 35 134 324 44 82 40 64 128 256), losses := [] }

theorem u23626 : Upper (D 6) (R 6) [34,132,320,36,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23626 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23627 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 324 44 82 48 73 137 265), lower := (rows 35 134 324 44 82 48 64 128 256), losses := [] }

theorem u23627 : Upper (D 6) (R 6) [34,132,320,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23627 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23628 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 324 44 88 33 83 147 275), lower := (rows 35 134 324 44 88 33 64 128 256), losses := [] }

theorem u23628 : Upper (D 6) (R 6) [34,132,320,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23629 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 44 88 34 81 145 273), lower := (rows 35 134 324 44 88 34 64 128 256), losses := [] }

theorem u23629 : Upper (D 6) (R 6) [34,132,320,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23630 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 324 44 88 48 67 131 259), lower := (rows 35 134 324 44 88 48 64 128 256), losses := [] }

theorem u23630 : Upper (D 6) (R 6) [34,132,320,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23630 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23631 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 324 56 81 33 78 142 270), lower := (rows 35 134 324 56 81 33 64 128 256), losses := [] }

theorem u23631 : Upper (D 6) (R 6) [34,132,320,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23632 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 324 56 81 34 77 141 269), lower := (rows 35 134 324 56 81 34 64 128 256), losses := [] }

theorem u23632 : Upper (D 6) (R 6) [34,132,320,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23633 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 324 56 81 36 75 139 267), lower := (rows 35 134 324 56 81 36 64 128 256), losses := [] }

theorem u23633 : Upper (D 6) (R 6) [34,132,320,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23634 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 324 56 81 40 71 135 263), lower := (rows 35 134 324 56 81 40 64 128 256), losses := [] }

theorem u23634 : Upper (D 6) (R 6) [34,132,320,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23634 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23635 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 324 56 82 33 77 141 269), lower := (rows 35 134 324 56 82 33 64 128 256), losses := [] }

theorem u23635 : Upper (D 6) (R 6) [34,132,320,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23636 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 324 56 82 36 73 137 265), lower := (rows 35 134 324 56 82 36 64 128 256), losses := [] }

theorem u23636 : Upper (D 6) (R 6) [34,132,320,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23637 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 324 56 82 40 69 133 261), lower := (rows 35 134 324 56 82 40 64 128 256), losses := [] }

theorem u23637 : Upper (D 6) (R 6) [34,132,320,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23637 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23638 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 52 13 82 33 324 452 324), lower := (rows 35 138 52 13 82 33 64 128 256), losses := [] }

theorem u23638 : Upper (D 6) (R 6) [34,136,48,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23639 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 52 13 82 36 321 449 321), lower := (rows 35 138 52 13 82 36 64 128 256), losses := [] }

theorem u23639 : Upper (D 6) (R 6) [34,136,48,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23639
end Delivery.IrregularNine14.P06
