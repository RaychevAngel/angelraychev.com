import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 3, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 266 81 36 68 176 304), lower := (rows 35 131 76 266 81 36 68 128 256), losses := [] }

theorem u6600 : Upper (D 6) (R 6) [34,129,72,258,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 76 266 81 36 80 164 292), lower := (rows 35 131 76 266 81 36 80 128 256), losses := [] }

theorem u6601 : Upper (D 6) (R 6) [34,129,72,258,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6601 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6602 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 76 266 81 36 96 148 276), lower := (rows 35 131 76 266 81 36 96 128 256), losses := [] }

theorem u6602 : Upper (D 6) (R 6) [34,129,72,258,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6603 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 76 266 112 36 65 148 276), lower := (rows 35 131 76 266 112 36 65 128 256), losses := [] }

theorem u6603 : Upper (D 6) (R 6) [34,129,72,258,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 266 112 36 68 145 273), lower := (rows 35 131 76 266 112 36 68 128 256), losses := [] }

theorem u6604 : Upper (D 6) (R 6) [34,129,72,258,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 76 266 112 36 80 133 261), lower := (rows 35 131 76 266 112 36 80 128 256), losses := [] }

theorem u6605 : Upper (D 6) (R 6) [34,129,72,258,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6605 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 268 21 96 66 176 304), lower := (rows 35 131 76 268 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 144 272), good := (rows 98 226 108 300 508 96 98 128 256) }] }

theorem u6606 : Upper (D 6) (R 6) [34,129,72,260,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6607 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 268 21 96 80 162 290), lower := (rows 35 131 76 268 21 96 80 128 256), losses := [] }

theorem u6607 : Upper (D 6) (R 6) [34,129,72,260,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6607 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6608 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 131 76 268 21 96 96 146 274), lower := (rows 35 131 76 268 21 96 96 128 256), losses := [] }

theorem u6608 : Upper (D 6) (R 6) [34,129,72,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6609 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 268 22 96 65 176 304), lower := (rows 35 131 76 268 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 125 17 100 64 209 337), good := (rows 446 410 492 300 446 492 508 128 256) }] }

theorem u6609 : Upper (D 6) (R 6) [34,129,72,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6610 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 268 22 96 80 161 289), lower := (rows 35 131 76 268 22 96 80 128 256), losses := [] }

theorem u6610 : Upper (D 6) (R 6) [34,129,72,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6610 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 268 22 96 96 145 273), lower := (rows 35 131 76 268 22 96 96 128 256), losses := [] }

theorem u6611 : Upper (D 6) (R 6) [34,129,72,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 280 21 96 66 164 292), lower := (rows 35 131 76 280 21 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 119 67 156 284), good := (rows 98 226 492 444 508 96 98 128 256) }] }

theorem u6612 : Upper (D 6) (R 6) [34,129,72,272,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6613 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 21 96 68 162 290), lower := (rows 35 131 76 280 21 96 68 128 256), losses := [] }

theorem u6613 : Upper (D 6) (R 6) [34,129,72,272,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6614 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 131 76 280 21 96 96 134 262), lower := (rows 35 131 76 280 21 96 96 128 256), losses := [] }

theorem u6614 : Upper (D 6) (R 6) [34,129,72,272,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 36, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 280 22 96 65 164 292), lower := (rows 35 131 76 280 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 91 17 100 64 245 373), good := (rows 446 410 492 408 446 492 508 128 256) }] }

theorem u6615 : Upper (D 6) (R 6) [34,129,72,272,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 22 96 68 161 289), lower := (rows 35 131 76 280 22 96 68 128 256), losses := [] }

theorem u6616 : Upper (D 6) (R 6) [34,129,72,272,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 76 280 22 96 96 133 261), lower := (rows 35 131 76 280 22 96 96 128 256), losses := [] }

theorem u6617 : Upper (D 6) (R 6) [34,129,72,272,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 280 81 36 66 164 292), lower := (rows 35 131 76 280 81 36 66 128 256), losses := [] }

theorem u6618 : Upper (D 6) (R 6) [34,129,72,272,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 81 36 68 162 290), lower := (rows 35 131 76 280 81 36 68 128 256), losses := [] }

theorem u6619 : Upper (D 6) (R 6) [34,129,72,272,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6620 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 76 280 81 36 96 134 262), lower := (rows 35 131 76 280 81 36 96 128 256), losses := [] }

theorem u6620 : Upper (D 6) (R 6) [34,129,72,272,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6621 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 280 82 36 65 164 292), lower := (rows 35 131 76 280 82 36 65 128 256), losses := [] }

theorem u6621 : Upper (D 6) (R 6) [34,129,72,272,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6622 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 76 280 82 36 68 161 289), lower := (rows 35 131 76 280 82 36 68 128 256), losses := [] }

theorem u6622 : Upper (D 6) (R 6) [34,129,72,272,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6623 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 76 280 82 36 96 133 261), lower := (rows 35 131 76 280 82 36 96 128 256), losses := [] }

theorem u6623 : Upper (D 6) (R 6) [34,129,72,272,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6624 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 194, targets := 36 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 76 296 21 36 66 208 336), lower := (rows 35 131 76 296 21 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 52 67 144 272), good := (rows 98 194 108 296 508 36 66 128 256) }] }

theorem u6624 : Upper (D 6) (R 6) [34,129,72,288,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6625 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 131 76 296 21 36 80 194 322), lower := (rows 35 131 76 296 21 36 80 128 256), losses := [] }

theorem u6625 : Upper (D 6) (R 6) [34,129,72,288,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6625 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6626 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 4, region := 130, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 76 296 21 96 66 148 276), lower := (rows 35 131 76 296 21 96 66 128 256), losses := [] }

theorem u6626 : Upper (D 6) (R 6) [34,129,72,288,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6627 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 21 96 68 146 274), lower := (rows 35 131 76 296 21 96 68 128 256), losses := [] }

theorem u6627 : Upper (D 6) (R 6) [34,129,72,288,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6628 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 130, targets := 32 },{ cop := 4, region := 130, targets := 64 }], pairs := [(1,5),(1,6)], upper := (rows 35 131 76 296 21 96 80 134 262), lower := (rows 35 131 76 296 21 96 80 128 256), losses := [] }

theorem u6628 : Upper (D 6) (R 6) [34,129,72,288,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6628 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6629 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 131 76 296 22 36 65 208 336), lower := (rows 35 131 76 296 22 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 52 67 144 272), good := (rows 97 193 108 296 508 36 65 128 256) }] }

theorem u6629 : Upper (D 6) (R 6) [34,129,72,288,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6630 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 76 296 22 36 80 193 321), lower := (rows 35 131 76 296 22 36 80 128 256), losses := [{ target := 2, region := (rows 41 38 0 40 16 32 80 132 260), good := (rows 43 131 459 299 466 427 80 128 256) }] }

theorem u6630 : Upper (D 6) (R 6) [34,129,72,288,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6630 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6631 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 76 296 22 96 65 148 276), lower := (rows 35 131 76 296 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 125 17 100 64 209 337), good := (rows 446 410 492 300 446 492 508 128 256) }] }

theorem u6631 : Upper (D 6) (R 6) [34,129,72,288,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6632 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 22 96 68 145 273), lower := (rows 35 131 76 296 22 96 68 128 256), losses := [] }

theorem u6632 : Upper (D 6) (R 6) [34,129,72,288,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6633 : Route 9 := (fun mask => (mask,id))

def c6633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6633 : Upper (D 6) (R 6) [34,129,72,288,6,64,16] 13 := by
  apply FastRouting.sound _ _ [34,129,72,288,6,64,16] 13 (by decide) (choices 1) [1,4] r6633 c6633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u497
  · exact u498

def b6634 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 81 36 66 148 276), lower := (rows 35 131 76 296 81 36 66 128 256), losses := [] }

theorem u6634 : Upper (D 6) (R 6) [34,129,72,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6635 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 81 36 68 146 274), lower := (rows 35 131 76 296 81 36 68 128 256), losses := [] }

theorem u6635 : Upper (D 6) (R 6) [34,129,72,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 76 296 81 36 80 134 262), lower := (rows 35 131 76 296 81 36 80 128 256), losses := [] }

theorem u6636 : Upper (D 6) (R 6) [34,129,72,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6636 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6637 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 82 36 65 148 276), lower := (rows 35 131 76 296 82 36 65 128 256), losses := [] }

theorem u6637 : Upper (D 6) (R 6) [34,129,72,288,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6638 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 296 82 36 68 145 273), lower := (rows 35 131 76 296 82 36 68 128 256), losses := [] }

theorem u6638 : Upper (D 6) (R 6) [34,129,72,288,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6639 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 35 131 76 296 82 36 80 133 261), lower := (rows 35 131 76 296 82 36 80 128 256), losses := [] }

theorem u6639 : Upper (D 6) (R 6) [34,129,72,288,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6639 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6640 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 100 14 81 288 68 152 280), lower := (rows 35 131 100 14 81 288 68 128 256), losses := [] }

theorem u6640 : Upper (D 6) (R 6) [34,129,96,6,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6640 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6641 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 100 14 81 288 72 148 276), lower := (rows 35 131 100 14 81 288 72 128 256), losses := [] }

theorem u6641 : Upper (D 6) (R 6) [34,129,96,6,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6641 [(5,8),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6642 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6)], upper := (rows 35 131 100 14 81 288 80 140 268), lower := (rows 35 131 100 14 81 288 80 128 256), losses := [] }

theorem u6642 : Upper (D 6) (R 6) [34,129,96,6,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6642 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6643 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 14 88 288 65 148 276), lower := (rows 35 131 100 14 88 288 65 128 256), losses := [] }

theorem u6643 : Upper (D 6) (R 6) [34,129,96,6,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6643 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6644 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 100 14 88 288 68 145 273), lower := (rows 35 131 100 14 88 288 68 128 256), losses := [] }

theorem u6644 : Upper (D 6) (R 6) [34,129,96,6,72,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6644 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6645 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 131 100 14 88 288 80 133 261), lower := (rows 35 131 100 14 88 288 80 128 256), losses := [] }

theorem u6645 : Upper (D 6) (R 6) [34,129,96,6,72,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6645 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6646 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 276 48 65 200 328), lower := (rows 35 131 100 14 276 48 65 128 256), losses := [{ target := 1, region := (rows 1 0 13 8 24 56 67 136 264), good := (rows 101 197 100 508 308 48 69 128 256) }] }

theorem u6646 : Upper (D 6) (R 6) [34,129,96,6,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6646 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 35 131 100 14 276 48 72 193 321), lower := (rows 35 131 100 14 276 48 72 128 256), losses := [] }

theorem u6647 : Upper (D 6) (R 6) [34,129,96,6,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6647 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6648 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 25 82 36 68 392 264), lower := (rows 35 131 100 25 82 36 68 128 256), losses := [] }

theorem u6648 : Upper (D 6) (R 6) [34,129,96,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6649 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 100 25 82 36 72 388 260), lower := (rows 35 131 100 25 82 36 72 128 256), losses := [] }

theorem u6649 : Upper (D 6) (R 6) [34,129,96,17,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6649 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6650 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 25 82 36 320 140 268), lower := (rows 35 131 100 25 82 36 320 128 256), losses := [] }

theorem u6650 : Upper (D 6) (R 6) [34,129,96,17,66,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6650 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6651 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 25 274 36 68 200 328), lower := (rows 35 131 100 25 274 36 68 128 256), losses := [] }

theorem u6651 : Upper (D 6) (R 6) [34,129,96,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6652 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 25 274 36 72 196 324), lower := (rows 35 131 100 25 274 36 72 128 256), losses := [] }

theorem u6652 : Upper (D 6) (R 6) [34,129,96,17,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6652 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6653 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 100 25 336 36 66 140 268), lower := (rows 35 131 100 25 336 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 95 8 24 127 67 136 264), good := (rows 102 230 100 508 372 36 102 128 256) }] }

theorem u6653 : Upper (D 6) (R 6) [34,129,96,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6654 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 25 336 36 68 138 266), lower := (rows 35 131 100 25 336 36 68 128 256), losses := [] }

theorem u6654 : Upper (D 6) (R 6) [34,129,96,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6655 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 25 336 36 72 134 262), lower := (rows 35 131 100 25 336 36 72 128 256), losses := [] }

theorem u6655 : Upper (D 6) (R 6) [34,129,96,17,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6655 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6656 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 394, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 35 131 100 26 81 36 68 392 264), lower := (rows 35 131 100 26 81 36 68 128 256), losses := [] }

theorem u6656 : Upper (D 6) (R 6) [34,129,96,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6657 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 100 26 81 36 72 388 260), lower := (rows 35 131 100 26 81 36 72 128 256), losses := [] }

theorem u6657 : Upper (D 6) (R 6) [34,129,96,18,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6657 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6658 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 26 81 36 320 140 268), lower := (rows 35 131 100 26 81 36 320 128 256), losses := [] }

theorem u6658 : Upper (D 6) (R 6) [34,129,96,18,65,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6658 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6659 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 131 100 26 273 36 68 200 328), lower := (rows 35 131 100 26 273 36 68 128 256), losses := [] }

theorem u6659 : Upper (D 6) (R 6) [34,129,96,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P06
