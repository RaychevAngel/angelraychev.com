import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0351
import IrregularNine14P06C0352
import IrregularNine14P06C0353

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36600 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 133 266 49 116 84 212 340), lower := (rows 35 74 133 266 49 32 64 128 256), losses := [] }

theorem u36600 : Upper (D 6) (R 6) [34,72,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36601 : Route 9 := (fun mask => (mask,id))

def c36601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36601 : Upper (D 6) (R 6) [34,72,129,258,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258,36] 13 (by decide) (choices 1) [1,4,16,64] r36601 c36601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21101
  · exact u21102
  · exact u21103
  · exact u21104

def b36602 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 74 133 266 81 52 116 180 308), lower := (rows 35 74 133 266 81 32 64 128 256), losses := [] }

theorem u36602 : Upper (D 6) (R 6) [34,72,129,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36603 : Route 9 := (fun mask => (mask,id))

def c36603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36603 : Upper (D 6) (R 6) [34,72,129,258,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258,68] 13 (by decide) (choices 1) [1,4,16] r36603 c36603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21105
  · exact u21106
  · exact u21107

def r36604 : Route 9 := (fun mask => (mask,id))

def c36604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36604 : Upper (D 6) (R 6) [34,72,129,258,96] 13 := by
  apply FastRouting.sound _ _ [34,72,129,258,96] 13 (by decide) (choices 1) [1,4,16] r36604 c36604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21108
  · exact u21109
  · exact u21110

def b36605 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 133 268 19 116 116 244 372), lower := (rows 35 74 133 268 19 32 64 128 256), losses := [] }

theorem u36605 : Upper (D 6) (R 6) [34,72,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36606 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 133 268 21 114 114 242 370), lower := (rows 35 74 133 268 21 32 64 128 256), losses := [] }

theorem u36606 : Upper (D 6) (R 6) [34,72,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36607 : Route 9 := (fun mask => (mask,id))

def c36607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36607 : Upper (D 6) (R 6) [34,72,129,260,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,6] 13 (by decide) (choices 1) [1,16,64] r36607 c36607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21111
  · exact u21112
  · exact u21113

def b36608 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 133 268 49 118 86 214 342), lower := (rows 35 74 133 268 49 32 64 128 256), losses := [] }

theorem u36608 : Upper (D 6) (R 6) [34,72,129,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36609 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 133 268 50 117 85 213 341), lower := (rows 35 74 133 268 50 32 64 128 256), losses := [] }

theorem u36609 : Upper (D 6) (R 6) [34,72,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36610 : Route 9 := (fun mask => (mask,id))

def c36610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36610 : Upper (D 6) (R 6) [34,72,129,260,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,36] 13 (by decide) (choices 1) [1,2,16,64] r36610 c36610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21114
  · exact u21115
  · exact u21116
  · exact u21117

def r36611 : Route 9 := (fun mask => (mask,id))

def c36611 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36611 : Upper (D 6) (R 6) [34,72,129,260,65] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,65] 13 (by decide) (choices 1) [2,4,16] r36611 c36611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21118
  · exact u21119
  · exact u21120

def b36612 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 268 82 53 117 181 309), lower := (rows 35 74 133 268 82 32 64 128 256), losses := [] }

theorem u36612 : Upper (D 6) (R 6) [34,72,129,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36613 : Route 9 := (fun mask => (mask,id))

def c36613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36613 : Upper (D 6) (R 6) [34,72,129,260,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,68] 13 (by decide) (choices 1) [1,2,16] r36613 c36613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21121
  · exact u21122
  · exact u21123

def r36614 : Route 9 := (fun mask => (mask,id))

def c36614 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36614 : Upper (D 6) (R 6) [34,72,129,260,96] 13 := by
  apply FastRouting.sound _ _ [34,72,129,260,96] 13 (by decide) (choices 1) [1,2,4,16] r36614 c36614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21124
  · exact u21125
  · exact u21126
  · exact u21127

def b36615 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 133 280 19 100 100 228 356), lower := (rows 35 74 133 280 19 32 64 128 256), losses := [] }

theorem u36615 : Upper (D 6) (R 6) [34,72,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36616 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 133 280 21 102 102 230 358), lower := (rows 35 74 133 280 21 32 64 128 256), losses := [] }

theorem u36616 : Upper (D 6) (R 6) [34,72,129,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36617 : Route 9 := (fun mask => (mask,id))

def c36617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36617 : Upper (D 6) (R 6) [34,72,129,272,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,272,6] 13 (by decide) (choices 1) [1,4,64] r36617 c36617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21128
  · exact u21129
  · exact u21130

def b36618 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 133 280 49 102 70 198 326), lower := (rows 35 74 133 280 49 32 64 128 256), losses := [] }

theorem u36618 : Upper (D 6) (R 6) [34,72,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36619 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 133 280 50 101 69 197 325), lower := (rows 35 74 133 280 50 32 64 128 256), losses := [] }

theorem u36619 : Upper (D 6) (R 6) [34,72,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36620 : Route 9 := (fun mask => (mask,id))

def c36620 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36620 : Upper (D 6) (R 6) [34,72,129,272,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,272,36] 13 (by decide) (choices 1) [1,2,4,64] r36620 c36620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21131
  · exact u21132
  · exact u21133
  · exact u21134

def b36621 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 133 280 81 38 102 166 294), lower := (rows 35 74 133 280 81 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 23 24 16 35 0 131 259), good := (rows 423 431 421 284 445 32 0 128 256) }] }

theorem u36621 : Upper (D 6) (R 6) [34,72,129,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36622 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 280 82 37 101 165 293), lower := (rows 35 74 133 280 82 32 64 128 256), losses := [] }

theorem u36622 : Upper (D 6) (R 6) [34,72,129,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36623 : Route 9 := (fun mask => (mask,id))

def c36623 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36623 : Upper (D 6) (R 6) [34,72,129,272,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,272,68] 13 (by decide) (choices 1) [1,2,4] r36623 c36623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21135
  · exact u21136
  · exact u21137

def b36624 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 133 280 112 39 71 135 263), lower := (rows 35 74 133 280 112 32 64 128 256), losses := [] }

theorem u36624 : Upper (D 6) (R 6) [34,72,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36625 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 133 296 19 116 84 212 340), lower := (rows 35 74 133 296 19 32 64 128 256), losses := [] }

theorem u36625 : Upper (D 6) (R 6) [34,72,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36626 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 133 296 21 118 86 214 342), lower := (rows 35 74 133 296 21 32 64 128 256), losses := [] }

theorem u36626 : Upper (D 6) (R 6) [34,72,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36627 : Route 9 := (fun mask => (mask,id))

def c36627 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36627 : Upper (D 6) (R 6) [34,72,129,288,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288,6] 13 (by decide) (choices 1) [1,4,16,64] r36627 c36627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21138
  · exact u21139
  · exact u21140
  · exact u21141

def r36628 : Route 9 := (fun mask => (mask,id))

def c36628 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36628 : Upper (D 6) (R 6) [34,72,129,288,65] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288,65] 13 (by decide) (choices 1) [2,4,16] r36628 c36628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21142
  · exact u21143
  · exact u21144

def b36629 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 296 82 53 85 149 277), lower := (rows 35 74 133 296 82 32 64 128 256), losses := [] }

theorem u36629 : Upper (D 6) (R 6) [34,72,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36630 : Route 9 := (fun mask => (mask,id))

def c36630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36630 : Upper (D 6) (R 6) [34,72,129,288,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,288,68] 13 (by decide) (choices 1) [1,2,4,16] r36630 c36630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21145
  · exact u21146
  · exact u21147
  · exact u21148

def b36631 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 35 74 134 13 21 368 368 496 368), lower := (rows 35 74 134 13 21 32 64 128 256), losses := [] }

theorem u36631 : Upper (D 6) (R 6) [34,72,130,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36632 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 134 13 49 372 340 468 340), lower := (rows 35 74 134 13 49 32 64 128 256), losses := [] }

theorem u36632 : Upper (D 6) (R 6) [34,72,130,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36633 : Route 9 := (fun mask => (mask,id))

def c36633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u36633 : Upper (D 6) (R 6) [34,72,130,5,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,36] 13 (by decide) (choices 1) [1,16,64,256] r36633 c36633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21149
  · exact u21150
  · exact u21151
  · exact u21152

def r36634 : Route 9 := (fun mask => (mask,id))

def c36634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36634 : Upper (D 6) (R 6) [34,72,130,5,65] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,65] 13 (by decide) (choices 1) [4,16,256] r36634 c36634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21153
  · exact u21154
  · exact u21155

def r36635 : Route 9 := (fun mask => (mask,id))

def c36635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36635 : Upper (D 6) (R 6) [34,72,130,5,68] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,68] 13 (by decide) (choices 1) [1,16,256] r36635 c36635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21156
  · exact u21157
  · exact u21158

def r36636 : Route 9 := (fun mask => (mask,id))

def c36636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36636 : Upper (D 6) (R 6) [34,72,130,5,96] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,96] 13 (by decide) (choices 1) [1,4,16,256] r36636 c36636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21159
  · exact u21160
  · exact u21161
  · exact u21162

def r36637 : Route 9 := (fun mask => (mask,id))

def c36637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36637 : Upper (D 6) (R 6) [34,72,130,5,257] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,257] 13 (by decide) (choices 1) [4,16,64] r36637 c36637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21163
  · exact u21164
  · exact u21165

def r36638 : Route 9 := (fun mask => (mask,id))

def c36638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36638 : Upper (D 6) (R 6) [34,72,130,5,260] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,260] 13 (by decide) (choices 1) [1,16,64] r36638 c36638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21166
  · exact u21167
  · exact u21168

def r36639 : Route 9 := (fun mask => (mask,id))

def c36639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36639 : Upper (D 6) (R 6) [34,72,130,5,288] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,288] 13 (by decide) (choices 1) [1,4,16,64] r36639 c36639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21169
  · exact u21170
  · exact u21171
  · exact u21172

def r36640 : Route 9 := (fun mask => (mask,id))

def c36640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36640 : Upper (D 6) (R 6) [34,72,130,5,320] 13 := by
  apply FastRouting.sound _ _ [34,72,130,5,320] 13 (by decide) (choices 1) [1,4,16] r36640 c36640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21173
  · exact u21174
  · exact u21175

def b36641 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 134 25 21 356 356 484 356), lower := (rows 35 74 134 25 21 32 64 128 256), losses := [] }

theorem u36641 : Upper (D 6) (R 6) [34,72,130,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36642 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 74 134 25 49 356 324 452 324), lower := (rows 35 74 134 25 49 32 64 128 256), losses := [] }

theorem u36642 : Upper (D 6) (R 6) [34,72,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36643 : Route 9 := (fun mask => (mask,id))

def c36643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36643 : Upper (D 6) (R 6) [34,72,130,17,36] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17,36] 13 (by decide) (choices 1) [1,4,64,256] r36643 c36643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21176
  · exact u21177
  · exact u21178
  · exact u21179

def b36644 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 10, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 134 25 81 292 356 420 292), lower := (rows 35 74 134 25 81 32 64 128 256), losses := [] }

theorem u36644 : Upper (D 6) (R 6) [34,72,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36645 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 134 25 84 293 357 421 293), lower := (rows 35 74 134 25 84 32 64 128 256), losses := [{ target := 6, region := (rows 7 2 7 24 16 63 0 159 287), good := (rows 423 431 423 445 445 32 0 128 256) }] }

theorem u36645 : Upper (D 6) (R 6) [34,72,130,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36646 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 134 25 112 293 325 389 261), lower := (rows 35 74 134 25 112 32 64 128 256), losses := [] }

theorem u36646 : Upper (D 6) (R 6) [34,72,130,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36647 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 74 134 25 273 100 100 228 356), lower := (rows 35 74 134 25 273 32 64 128 256), losses := [] }

theorem u36647 : Upper (D 6) (R 6) [34,72,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36648 : Route 9 := (fun mask => (mask,id))

def c36648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36648 : Upper (D 6) (R 6) [34,72,130,17,260] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17,260] 13 (by decide) (choices 1) [1,4,64] r36648 c36648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21180
  · exact u21181
  · exact u21182

def r36649 : Route 9 := (fun mask => (mask,id))

def c36649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36649 : Upper (D 6) (R 6) [34,72,130,17,288] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17,288] 13 (by decide) (choices 1) [1,4,64] r36649 c36649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21183
  · exact u21184
  · exact u21185

def r36650 : Route 9 := (fun mask => (mask,id))

def c36650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36650 : Upper (D 6) (R 6) [34,72,130,17,320] 13 := by
  apply FastRouting.sound _ _ [34,72,130,17,320] 13 (by decide) (choices 1) [1,4] r36650 c36650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21186
  · exact u21187

def b36651 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 74 134 28 21 353 353 481 353), lower := (rows 35 74 134 28 21 32 64 128 256), losses := [] }

theorem u36651 : Upper (D 6) (R 6) [34,72,130,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36652 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 134 28 49 357 325 453 325), lower := (rows 35 74 134 28 49 32 64 128 256), losses := [] }

theorem u36652 : Upper (D 6) (R 6) [34,72,130,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36653 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 134 28 52 353 321 449 321), lower := (rows 35 74 134 28 52 32 64 128 256), losses := [] }

theorem u36653 : Upper (D 6) (R 6) [34,72,130,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36654 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 74 134 28 81 293 357 421 293), lower := (rows 35 74 134 28 81 32 64 128 256), losses := [{ target := 6, region := (rows 7 2 7 24 16 63 0 159 287), good := (rows 423 431 423 445 445 32 0 128 256) }] }

theorem u36654 : Upper (D 6) (R 6) [34,72,130,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36655 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 134 28 84 289 353 417 289), lower := (rows 35 74 134 28 84 32 64 128 256), losses := [] }

theorem u36655 : Upper (D 6) (R 6) [34,72,130,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36656 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 134 28 112 293 325 389 261), lower := (rows 35 74 134 28 112 32 64 128 256), losses := [] }

theorem u36656 : Upper (D 6) (R 6) [34,72,130,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36657 : Route 9 := (fun mask => (mask,id))

def c36657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36657 : Upper (D 6) (R 6) [34,72,130,20,257] 13 := by
  apply FastRouting.sound _ _ [34,72,130,20,257] 13 (by decide) (choices 1) [1,4,64] r36657 c36657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21188
  · exact u21189
  · exact u21190

def b36658 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 134 28 276 97 97 225 353), lower := (rows 35 74 134 28 276 32 64 128 256), losses := [] }

theorem u36658 : Upper (D 6) (R 6) [34,72,130,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36659 : Route 9 := (fun mask => (mask,id))

def c36659 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36659 : Upper (D 6) (R 6) [34,72,130,20,288] 13 := by
  apply FastRouting.sound _ _ [34,72,130,20,288] 13 (by decide) (choices 1) [1,4,64] r36659 c36659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21191
  · exact u21192
  · exact u21193

#print axioms u36659
end Delivery.IrregularNine14.P06
