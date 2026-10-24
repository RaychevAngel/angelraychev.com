import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0105
import IrregularNine14P06C0106

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21600 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,2),(2,6)], upper := (rows 35 74 388 25 84 36 99 163 291), lower := (rows 35 74 388 25 84 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 74 384 475 80 32 64 128 256) }] }

theorem u21600 : Upper (D 6) (R 6) [34,72,384,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21601 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 388 26 21 33 100 228 356), lower := (rows 35 74 388 26 21 33 64 128 256), losses := [] }

theorem u21601 : Upper (D 6) (R 6) [34,72,384,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21602 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 35 74 388 26 21 36 97 225 353), lower := (rows 35 74 388 26 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 65 129 257), good := (rows 483 74 384 26 475 32 64 128 256) }] }

theorem u21602 : Upper (D 6) (R 6) [34,72,384,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21603 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 26 21 96 101 165 293), lower := (rows 35 74 388 26 21 96 64 128 256), losses := [] }

theorem u21603 : Upper (D 6) (R 6) [34,72,384,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21604 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 388 44 21 33 82 210 338), lower := (rows 35 74 388 44 21 33 64 128 256), losses := [] }

theorem u21604 : Upper (D 6) (R 6) [34,72,384,36,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21605 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 44 21 34 81 209 337), lower := (rows 35 74 388 44 21 34 64 128 256), losses := [] }

theorem u21605 : Upper (D 6) (R 6) [34,72,384,36,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21606 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 74 388 44 21 48 67 195 323), lower := (rows 35 74 388 44 21 48 64 128 256), losses := [] }

theorem u21606 : Upper (D 6) (R 6) [34,72,384,36,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21606 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21607 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 44 21 96 83 147 275), lower := (rows 35 74 388 44 21 96 64 128 256), losses := [] }

theorem u21607 : Upper (D 6) (R 6) [34,72,384,36,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21608 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 388 44 81 33 86 150 278), lower := (rows 35 74 388 44 81 33 64 128 256), losses := [] }

theorem u21608 : Upper (D 6) (R 6) [34,72,384,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21609 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 44 81 34 85 149 277), lower := (rows 35 74 388 44 81 34 64 128 256), losses := [] }

theorem u21609 : Upper (D 6) (R 6) [34,72,384,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21610 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 388 44 81 36 83 147 275), lower := (rows 35 74 388 44 81 36 64 128 256), losses := [] }

theorem u21610 : Upper (D 6) (R 6) [34,72,384,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21611 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 388 44 81 48 71 135 263), lower := (rows 35 74 388 44 81 48 64 128 256), losses := [] }

theorem u21611 : Upper (D 6) (R 6) [34,72,384,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21611 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21612 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 388 44 84 33 83 147 275), lower := (rows 35 74 388 44 84 33 64 128 256), losses := [] }

theorem u21612 : Upper (D 6) (R 6) [34,72,384,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21613 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 44 84 34 81 145 273), lower := (rows 35 74 388 44 84 34 64 128 256), losses := [] }

theorem u21613 : Upper (D 6) (R 6) [34,72,384,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21614 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 388 44 84 48 67 131 259), lower := (rows 35 74 388 44 84 48 64 128 256), losses := [] }

theorem u21614 : Upper (D 6) (R 6) [34,72,384,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21614 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21615 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 388 56 21 33 70 198 326), lower := (rows 35 74 388 56 21 33 64 128 256), losses := [] }

theorem u21615 : Upper (D 6) (R 6) [34,72,384,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21616 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 56 21 34 69 197 325), lower := (rows 35 74 388 56 21 34 64 128 256), losses := [] }

theorem u21616 : Upper (D 6) (R 6) [34,72,384,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21617 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 388 56 21 36 67 195 323), lower := (rows 35 74 388 56 21 36 64 128 256), losses := [] }

theorem u21617 : Upper (D 6) (R 6) [34,72,384,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21618 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 56 21 96 71 135 263), lower := (rows 35 74 388 56 21 96 64 128 256), losses := [] }

theorem u21618 : Upper (D 6) (R 6) [34,72,384,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21619 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 131 44 25 82 36 324 452 324), lower := (rows 35 131 44 25 82 36 64 128 256), losses := [] }

theorem u21619 : Upper (D 6) (R 6) [34,129,40,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21620 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 25 82 96 324 388 260), lower := (rows 35 131 44 25 82 96 64 128 256), losses := [] }

theorem u21620 : Upper (D 6) (R 6) [34,129,40,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21621 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 25 82 288 68 196 324), lower := (rows 35 131 44 25 82 288 64 128 256), losses := [] }

theorem u21621 : Upper (D 6) (R 6) [34,129,40,17,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21621 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21622 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 25 84 34 324 452 324), lower := (rows 35 131 44 25 84 34 64 128 256), losses := [] }

theorem u21622 : Upper (D 6) (R 6) [34,129,40,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21623 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 25 84 36 322 450 322), lower := (rows 35 131 44 25 84 36 64 128 256), losses := [] }

theorem u21623 : Upper (D 6) (R 6) [34,129,40,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21624 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 25 84 96 326 390 262), lower := (rows 35 131 44 25 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 60 116 96 96 128 256) }] }

theorem u21624 : Upper (D 6) (R 6) [34,129,40,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21625 : Route 9 := (fun mask => (mask,id))

def c21625 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21625 : Upper (D 6) (R 6) [34,129,40,17,68,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,68,256] 13 (by decide) (choices 1) [2,4] r21625 c21625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6347
  · exact u6348

def b21626 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 131 44 25 274 36 68 196 324), lower := (rows 35 131 44 25 274 36 64 128 256), losses := [] }

theorem u21626 : Upper (D 6) (R 6) [34,129,40,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21627 : Route 9 := (fun mask => (mask,id))

def c21627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21627 : Upper (D 6) (R 6) [34,129,40,17,258,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,258,64] 13 (by decide) (choices 1) [4] r21627 c21627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u6349

def b21628 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 25 276 34 68 196 324), lower := (rows 35 131 44 25 276 34 64 128 256), losses := [] }

theorem u21628 : Upper (D 6) (R 6) [34,129,40,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21629 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 25 276 36 66 194 322), lower := (rows 35 131 44 25 276 36 64 128 256), losses := [] }

theorem u21629 : Upper (D 6) (R 6) [34,129,40,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21630 : Route 9 := (fun mask => (mask,id))

def c21630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21630 : Upper (D 6) (R 6) [34,129,40,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,260,64] 13 (by decide) (choices 1) [2,4] r21630 c21630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6350
  · exact u6351

def b21631 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 25 336 34 68 196 324), lower := (rows 35 131 44 25 336 34 64 128 256), losses := [] }

theorem u21631 : Upper (D 6) (R 6) [34,129,40,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21632 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 25 336 36 70 198 326), lower := (rows 35 131 44 25 336 36 64 128 256), losses := [] }

theorem u21632 : Upper (D 6) (R 6) [34,129,40,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21633 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 25 336 96 70 134 262), lower := (rows 35 131 44 25 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 60 368 96 96 128 256) }] }

theorem u21633 : Upper (D 6) (R 6) [34,129,40,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21634 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 26 81 36 324 452 324), lower := (rows 35 131 44 26 81 36 64 128 256), losses := [] }

theorem u21634 : Upper (D 6) (R 6) [34,129,40,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21635 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 26 81 96 324 388 260), lower := (rows 35 131 44 26 81 96 64 128 256), losses := [] }

theorem u21635 : Upper (D 6) (R 6) [34,129,40,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21636 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 26 81 288 68 196 324), lower := (rows 35 131 44 26 81 288 64 128 256), losses := [] }

theorem u21636 : Upper (D 6) (R 6) [34,129,40,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21636 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21637 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 26 84 33 324 452 324), lower := (rows 35 131 44 26 84 33 64 128 256), losses := [] }

theorem u21637 : Upper (D 6) (R 6) [34,129,40,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21638 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 44 26 84 36 321 449 321), lower := (rows 35 131 44 26 84 36 64 128 256), losses := [] }

theorem u21638 : Upper (D 6) (R 6) [34,129,40,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21639 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 26 84 96 325 389 261), lower := (rows 35 131 44 26 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 62 116 96 96 128 256) }] }

theorem u21639 : Upper (D 6) (R 6) [34,129,40,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21640 : Route 9 := (fun mask => (mask,id))

def c21640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21640 : Upper (D 6) (R 6) [34,129,40,18,68,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,68,256] 13 (by decide) (choices 1) [1,4] r21640 c21640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6352
  · exact u6353

def b21641 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 26 273 36 68 196 324), lower := (rows 35 131 44 26 273 36 64 128 256), losses := [] }

theorem u21641 : Upper (D 6) (R 6) [34,129,40,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21642 : Route 9 := (fun mask => (mask,id))

def c21642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21642 : Upper (D 6) (R 6) [34,129,40,18,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,257,64] 13 (by decide) (choices 1) [4] r21642 c21642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u6354

def b21643 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 26 276 33 68 196 324), lower := (rows 35 131 44 26 276 33 64 128 256), losses := [] }

theorem u21643 : Upper (D 6) (R 6) [34,129,40,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21644 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 44 26 276 36 65 193 321), lower := (rows 35 131 44 26 276 36 64 128 256), losses := [] }

theorem u21644 : Upper (D 6) (R 6) [34,129,40,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21645 : Route 9 := (fun mask => (mask,id))

def c21645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21645 : Upper (D 6) (R 6) [34,129,40,18,260,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,260,64] 13 (by decide) (choices 1) [1,4] r21645 c21645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6355
  · exact u6356

def b21646 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 26 336 33 68 196 324), lower := (rows 35 131 44 26 336 33 64 128 256), losses := [] }

theorem u21646 : Upper (D 6) (R 6) [34,129,40,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21647 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 26 336 36 69 197 325), lower := (rows 35 131 44 26 336 36 64 128 256), losses := [] }

theorem u21647 : Upper (D 6) (R 6) [34,129,40,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21648 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 26 336 96 69 133 261), lower := (rows 35 131 44 26 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 130 44 62 368 96 96 128 256) }] }

theorem u21648 : Upper (D 6) (R 6) [34,129,40,18,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21649 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 81 34 324 452 324), lower := (rows 35 131 44 28 81 34 64 128 256), losses := [] }

theorem u21649 : Upper (D 6) (R 6) [34,129,40,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21650 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 28 81 36 322 450 322), lower := (rows 35 131 44 28 81 36 64 128 256), losses := [] }

theorem u21650 : Upper (D 6) (R 6) [34,129,40,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21651 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 81 96 326 390 262), lower := (rows 35 131 44 28 81 96 64 128 256), losses := [] }

theorem u21651 : Upper (D 6) (R 6) [34,129,40,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21652 : Route 9 := (fun mask => (mask,id))

def c21652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21652 : Upper (D 6) (R 6) [34,129,40,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,65,256] 13 (by decide) (choices 1) [2,4] r21652 c21652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6357
  · exact u6358

def b21653 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 82 33 324 452 324), lower := (rows 35 131 44 28 82 33 64 128 256), losses := [] }

theorem u21653 : Upper (D 6) (R 6) [34,129,40,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21654 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 28 82 36 321 449 321), lower := (rows 35 131 44 28 82 36 64 128 256), losses := [] }

theorem u21654 : Upper (D 6) (R 6) [34,129,40,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21655 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 28 82 96 325 389 261), lower := (rows 35 131 44 28 82 96 64 128 256), losses := [] }

theorem u21655 : Upper (D 6) (R 6) [34,129,40,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21656 : Route 9 := (fun mask => (mask,id))

def c21656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21656 : Upper (D 6) (R 6) [34,129,40,20,66,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,66,256] 13 (by decide) (choices 1) [1,4] r21656 c21656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6359
  · exact u6360

def b21657 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 28 273 34 68 196 324), lower := (rows 35 131 44 28 273 34 64 128 256), losses := [] }

theorem u21657 : Upper (D 6) (R 6) [34,129,40,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21658 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 28 273 36 66 194 322), lower := (rows 35 131 44 28 273 36 64 128 256), losses := [] }

theorem u21658 : Upper (D 6) (R 6) [34,129,40,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21659 : Route 9 := (fun mask => (mask,id))

def c21659 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21659 : Upper (D 6) (R 6) [34,129,40,20,257,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,20,257,64] 13 (by decide) (choices 1) [2,4] r21659 c21659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6361
  · exact u6362

#print axioms u21659
end Delivery.IrregularNine14.P06
