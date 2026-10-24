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

def b23640 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 13 82 96 325 389 261), lower := (rows 35 138 52 13 82 96 64 128 256), losses := [] }

theorem u23640 : Upper (D 6) (R 6) [34,136,48,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23641 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 52 13 82 288 69 197 325), lower := (rows 35 138 52 13 82 288 64 128 256), losses := [] }

theorem u23641 : Upper (D 6) (R 6) [34,136,48,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23641 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23642 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 52 13 274 33 68 196 324), lower := (rows 35 138 52 13 274 33 64 128 256), losses := [] }

theorem u23642 : Upper (D 6) (R 6) [34,136,48,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23643 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 52 13 274 36 65 193 321), lower := (rows 35 138 52 13 274 36 64 128 256), losses := [] }

theorem u23643 : Upper (D 6) (R 6) [34,136,48,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23644 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 35 138 52 13 274 96 69 197 325), lower := (rows 35 138 52 13 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 106 72 136 264), good := (rows 33 488 52 493 308 96 96 128 256) }] }

theorem u23644 : Upper (D 6) (R 6) [34,136,48,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23645 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 52 13 336 33 70 198 326), lower := (rows 35 138 52 13 336 33 64 128 256), losses := [] }

theorem u23645 : Upper (D 6) (R 6) [34,136,48,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23646 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 13 336 34 69 197 325), lower := (rows 35 138 52 13 336 34 64 128 256), losses := [] }

theorem u23646 : Upper (D 6) (R 6) [34,136,48,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23647 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 52 13 336 36 67 195 323), lower := (rows 35 138 52 13 336 36 64 128 256), losses := [] }

theorem u23647 : Upper (D 6) (R 6) [34,136,48,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23648 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 13 336 96 71 135 263), lower := (rows 35 138 52 13 336 96 64 128 256), losses := [] }

theorem u23648 : Upper (D 6) (R 6) [34,136,48,5,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23649 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 14 81 33 324 452 324), lower := (rows 35 138 52 14 81 33 64 128 256), losses := [] }

theorem u23649 : Upper (D 6) (R 6) [34,136,48,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23650 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 52 14 81 36 321 449 321), lower := (rows 35 138 52 14 81 36 64 128 256), losses := [] }

theorem u23650 : Upper (D 6) (R 6) [34,136,48,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23651 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 14 81 96 325 389 261), lower := (rows 35 138 52 14 81 96 64 128 256), losses := [] }

theorem u23651 : Upper (D 6) (R 6) [34,136,48,6,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23652 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 52 14 81 288 69 197 325), lower := (rows 35 138 52 14 81 288 64 128 256), losses := [] }

theorem u23652 : Upper (D 6) (R 6) [34,136,48,6,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23652 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23653 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 14 273 33 68 196 324), lower := (rows 35 138 52 14 273 33 64 128 256), losses := [] }

theorem u23653 : Upper (D 6) (R 6) [34,136,48,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23654 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 52 14 273 36 65 193 321), lower := (rows 35 138 52 14 273 36 64 128 256), losses := [] }

theorem u23654 : Upper (D 6) (R 6) [34,136,48,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23655 : Route 9 := (fun mask => (mask,id))

def c23655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23655 : Upper (D 6) (R 6) [34,136,48,6,257,64] 13 := by
  apply FastRouting.sound _ _ [34,136,48,6,257,64] 13 (by decide) (choices 1) [1,4] r23655 c23655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7279
  · exact u7280

def b23656 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 14 336 33 69 197 325), lower := (rows 35 138 52 14 336 33 64 128 256), losses := [] }

theorem u23656 : Upper (D 6) (R 6) [34,136,48,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23657 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 14 336 36 65 193 321), lower := (rows 35 138 52 14 336 36 64 128 256), losses := [] }

theorem u23657 : Upper (D 6) (R 6) [34,136,48,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23658 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 52 14 336 96 69 133 261), lower := (rows 35 138 52 14 336 96 64 128 256), losses := [] }

theorem u23658 : Upper (D 6) (R 6) [34,136,48,6,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23659 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 73 82 33 324 388 260), lower := (rows 35 138 52 73 82 33 64 128 256), losses := [] }

theorem u23659 : Upper (D 6) (R 6) [34,136,48,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23660 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 52 73 82 36 325 389 261), lower := (rows 35 138 52 73 82 36 64 128 256), losses := [] }

theorem u23660 : Upper (D 6) (R 6) [34,136,48,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23661 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 138 52 73 82 288 69 133 261), lower := (rows 35 138 52 73 82 288 64 128 256), losses := [] }

theorem u23661 : Upper (D 6) (R 6) [34,136,48,65,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23661 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23662 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 73 84 33 326 390 262), lower := (rows 35 138 52 73 84 33 64 128 256), losses := [] }

theorem u23662 : Upper (D 6) (R 6) [34,136,48,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23663 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 73 84 34 325 389 261), lower := (rows 35 138 52 73 84 34 64 128 256), losses := [] }

theorem u23663 : Upper (D 6) (R 6) [34,136,48,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23664 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 52 73 84 36 323 387 259), lower := (rows 35 138 52 73 84 36 64 128 256), losses := [] }

theorem u23664 : Upper (D 6) (R 6) [34,136,48,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23665 : Route 9 := (fun mask => (mask,id))

def c23665 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23665 : Upper (D 6) (R 6) [34,136,48,65,68,256] 13 := by
  apply FastRouting.sound _ _ [34,136,48,65,68,256] 13 (by decide) (choices 1) [1,2,4] r23665 c23665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7281
  · exact u7282
  · exact u7283

def b23666 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 73 273 34 68 196 324), lower := (rows 35 138 52 73 273 34 64 128 256), losses := [] }

theorem u23666 : Upper (D 6) (R 6) [34,136,48,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23667 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 73 273 36 70 198 326), lower := (rows 35 138 52 73 273 36 64 128 256), losses := [] }

theorem u23667 : Upper (D 6) (R 6) [34,136,48,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23668 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 73 273 96 70 134 262), lower := (rows 35 138 52 73 273 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 48 105 273 96 96 128 256) }] }

theorem u23668 : Upper (D 6) (R 6) [34,136,48,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23669 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 73 274 33 68 196 324), lower := (rows 35 138 52 73 274 33 64 128 256), losses := [] }

theorem u23669 : Upper (D 6) (R 6) [34,136,48,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23670 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 138 52 73 274 36 69 197 325), lower := (rows 35 138 52 73 274 36 64 128 256), losses := [] }

theorem u23670 : Upper (D 6) (R 6) [34,136,48,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23671 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 73 274 96 69 133 261), lower := (rows 35 138 52 73 274 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 48 105 275 96 96 128 256) }] }

theorem u23671 : Upper (D 6) (R 6) [34,136,48,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23672 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 73 276 33 70 198 326), lower := (rows 35 138 52 73 276 33 64 128 256), losses := [] }

theorem u23672 : Upper (D 6) (R 6) [34,136,48,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23673 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 73 276 34 69 197 325), lower := (rows 35 138 52 73 276 34 64 128 256), losses := [] }

theorem u23673 : Upper (D 6) (R 6) [34,136,48,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23674 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 73 276 36 67 195 323), lower := (rows 35 138 52 73 276 36 64 128 256), losses := [] }

theorem u23674 : Upper (D 6) (R 6) [34,136,48,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23675 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 73 276 96 71 135 263), lower := (rows 35 138 52 73 276 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 48 105 272 96 96 128 256) }] }

theorem u23675 : Upper (D 6) (R 6) [34,136,48,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23676 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 52 73 336 33 70 134 262), lower := (rows 35 138 52 73 336 33 64 128 256), losses := [] }

theorem u23676 : Upper (D 6) (R 6) [34,136,48,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23677 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 73 336 34 69 133 261), lower := (rows 35 138 52 73 336 34 64 128 256), losses := [] }

theorem u23677 : Upper (D 6) (R 6) [34,136,48,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23678 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 73 336 36 71 135 263), lower := (rows 35 138 52 73 336 36 64 128 256), losses := [] }

theorem u23678 : Upper (D 6) (R 6) [34,136,48,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23679 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 74 84 33 325 389 261), lower := (rows 35 138 52 74 84 33 64 128 256), losses := [] }

theorem u23679 : Upper (D 6) (R 6) [34,136,48,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23680 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 52 74 84 36 321 385 257), lower := (rows 35 138 52 74 84 36 64 128 256), losses := [] }

theorem u23680 : Upper (D 6) (R 6) [34,136,48,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23681 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 52 74 84 288 69 133 261), lower := (rows 35 138 52 74 84 288 64 128 256), losses := [] }

theorem u23681 : Upper (D 6) (R 6) [34,136,48,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23681 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23682 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 74 273 33 68 196 324), lower := (rows 35 138 52 74 273 33 64 128 256), losses := [] }

theorem u23682 : Upper (D 6) (R 6) [34,136,48,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23683 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 52 74 273 36 69 197 325), lower := (rows 35 138 52 74 273 36 64 128 256), losses := [] }

theorem u23683 : Upper (D 6) (R 6) [34,136,48,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23684 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 2 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 74 273 96 69 133 261), lower := (rows 35 138 52 74 273 96 64 128 256), losses := [] }

theorem u23684 : Upper (D 6) (R 6) [34,136,48,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23685 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 74 276 33 69 197 325), lower := (rows 35 138 52 74 276 33 64 128 256), losses := [] }

theorem u23685 : Upper (D 6) (R 6) [34,136,48,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23686 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 74 276 36 65 193 321), lower := (rows 35 138 52 74 276 36 64 128 256), losses := [] }

theorem u23686 : Upper (D 6) (R 6) [34,136,48,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23687 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 2 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 52 74 276 96 69 133 261), lower := (rows 35 138 52 74 276 96 64 128 256), losses := [] }

theorem u23687 : Upper (D 6) (R 6) [34,136,48,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23688 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 52 74 336 33 69 133 261), lower := (rows 35 138 52 74 336 33 64 128 256), losses := [] }

theorem u23688 : Upper (D 6) (R 6) [34,136,48,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23689 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 74 336 36 69 133 261), lower := (rows 35 138 52 74 336 36 64 128 256), losses := [] }

theorem u23689 : Upper (D 6) (R 6) [34,136,48,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23690 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 76 81 33 326 390 262), lower := (rows 35 138 52 76 81 33 64 128 256), losses := [] }

theorem u23690 : Upper (D 6) (R 6) [34,136,48,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23691 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 76 81 34 325 389 261), lower := (rows 35 138 52 76 81 34 64 128 256), losses := [] }

theorem u23691 : Upper (D 6) (R 6) [34,136,48,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23692 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 52 76 81 36 323 387 259), lower := (rows 35 138 52 76 81 36 64 128 256), losses := [] }

theorem u23692 : Upper (D 6) (R 6) [34,136,48,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23693 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 52 76 81 288 71 135 263), lower := (rows 35 138 52 76 81 288 64 128 256), losses := [] }

theorem u23693 : Upper (D 6) (R 6) [34,136,48,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23693 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23694 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 52 76 273 33 70 198 326), lower := (rows 35 138 52 76 273 33 64 128 256), losses := [] }

theorem u23694 : Upper (D 6) (R 6) [34,136,48,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23695 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 52 76 273 34 69 197 325), lower := (rows 35 138 52 76 273 34 64 128 256), losses := [] }

theorem u23695 : Upper (D 6) (R 6) [34,136,48,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23696 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 52 76 273 36 67 195 323), lower := (rows 35 138 52 76 273 36 64 128 256), losses := [] }

theorem u23696 : Upper (D 6) (R 6) [34,136,48,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23697 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 52 76 273 96 71 135 263), lower := (rows 35 138 52 76 273 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 48 104 273 96 96 128 256) }] }

theorem u23697 : Upper (D 6) (R 6) [34,136,48,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23698 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 138 52 76 274 33 69 197 325), lower := (rows 35 138 52 76 274 33 64 128 256), losses := [] }

theorem u23698 : Upper (D 6) (R 6) [34,136,48,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23699 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 52 76 274 36 65 193 321), lower := (rows 35 138 52 76 274 36 64 128 256), losses := [] }

theorem u23699 : Upper (D 6) (R 6) [34,136,48,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23699 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23699
end Delivery.IrregularNine14.P06
