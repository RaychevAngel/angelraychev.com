import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0434
import IrregularNine14P06C0435
import IrregularNine14P06C0436

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39600 : Route 9 := (fun mask => (mask,id))

def c39600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39600 : Upper (D 6) (R 6) [40,96,144,5,260] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,260] 13 (by decide) (choices 1) [1,2,64] r39600 c39600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26093
  · exact u26094
  · exact u26095

def r39601 : Route 9 := (fun mask => (mask,id))

def c39601 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39601 : Upper (D 6) (R 6) [40,96,144,5,320] 13 := by
  apply FastRouting.sound _ _ [40,96,144,5,320] 13 (by decide) (choices 1) [1,2,4] r39601 c39601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26096
  · exact u26097
  · exact u26098

def b39602 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 3, region := 353, targets := 2 }], pairs := [(0,1),(2,5),(3,5)], upper := (rows 41 98 148 14 19 357 325 453 325), lower := (rows 41 98 148 14 19 32 64 128 256), losses := [] }

theorem u39602 : Upper (D 6) (R 6) [40,96,144,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39603 : Route 9 := (fun mask => (mask,id))

def c39603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39603 : Upper (D 6) (R 6) [40,96,144,6,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,5] 13 (by decide) (choices 1) [1,2,64,256] r39603 c39603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26099
  · exact u26100
  · exact u26101
  · exact u26102

def b39604 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 41 98 148 14 22 353 321 449 321), lower := (rows 41 98 148 14 22 32 64 128 256), losses := [] }

theorem u39604 : Upper (D 6) (R 6) [40,96,144,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39605 : Route 9 := (fun mask => (mask,id))

def c39605 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39605 : Upper (D 6) (R 6) [40,96,144,6,65] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,65] 13 (by decide) (choices 1) [1,2,4,256] r39605 c39605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26103
  · exact u26104
  · exact u26105
  · exact u26106

def b39606 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 148 14 82 293 325 389 261), lower := (rows 41 98 148 14 82 32 64 128 256), losses := [] }

theorem u39606 : Upper (D 6) (R 6) [40,96,144,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39607 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 355, targets := 4 },{ cop := 3, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 41 98 148 14 84 291 323 387 259), lower := (rows 41 98 148 14 84 32 64 128 256), losses := [] }

theorem u39607 : Upper (D 6) (R 6) [40,96,144,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39608 : Route 9 := (fun mask => (mask,id))

def c39608 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39608 : Upper (D 6) (R 6) [40,96,144,6,257] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,257] 13 (by decide) (choices 1) [1,2,4,64] r39608 c39608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26107
  · exact u26108
  · exact u26109
  · exact u26110

def r39609 : Route 9 := (fun mask => (mask,id))

def c39609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39609 : Upper (D 6) (R 6) [40,96,144,6,258] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,258] 13 (by decide) (choices 1) [1,4,64] r39609 c39609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26111
  · exact u26112
  · exact u26113

def r39610 : Route 9 := (fun mask => (mask,id))

def c39610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39610 : Upper (D 6) (R 6) [40,96,144,6,260] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,260] 13 (by decide) (choices 1) [1,2,64] r39610 c39610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26114
  · exact u26115
  · exact u26116

def r39611 : Route 9 := (fun mask => (mask,id))

def c39611 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39611 : Upper (D 6) (R 6) [40,96,144,6,320] 13 := by
  apply FastRouting.sound _ _ [40,96,144,6,320] 13 (by decide) (choices 1) [1,2,4] r39611 c39611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26117
  · exact u26118
  · exact u26119

def b39612 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 148 76 19 295 327 391 263), lower := (rows 41 98 148 76 19 32 64 128 256), losses := [] }

theorem u39612 : Upper (D 6) (R 6) [40,96,144,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39613 : Route 9 := (fun mask => (mask,id))

def c39613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39613 : Upper (D 6) (R 6) [40,96,144,68,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68,5] 13 (by decide) (choices 1) [1,2,256] r39613 c39613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26120
  · exact u26121
  · exact u26122

def r39614 : Route 9 := (fun mask => (mask,id))

def c39614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39614 : Upper (D 6) (R 6) [40,96,144,68,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68,6] 13 (by decide) (choices 1) [1,2,256] r39614 c39614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26123
  · exact u26124
  · exact u26125

def r39615 : Route 9 := (fun mask => (mask,id))

def c39615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39615 : Upper (D 6) (R 6) [40,96,144,68,257] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68,257] 13 (by decide) (choices 1) [1,2,4] r39615 c39615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26126
  · exact u26127
  · exact u26128

def r39616 : Route 9 := (fun mask => (mask,id))

def c39616 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39616 : Upper (D 6) (R 6) [40,96,144,68,258] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68,258] 13 (by decide) (choices 1) [1,2,4] r39616 c39616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26129
  · exact u26130
  · exact u26131

def r39617 : Route 9 := (fun mask => (mask,id))

def c39617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39617 : Upper (D 6) (R 6) [40,96,144,68,260] 13 := by
  apply FastRouting.sound _ _ [40,96,144,68,260] 13 (by decide) (choices 1) [1,2] r39617 c39617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26132
  · exact u26133

def b39618 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 148 265 19 102 70 198 326), lower := (rows 41 98 148 265 19 32 64 128 256), losses := [] }

theorem u39618 : Upper (D 6) (R 6) [40,96,144,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39619 : Route 9 := (fun mask => (mask,id))

def c39619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39619 : Upper (D 6) (R 6) [40,96,144,257,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,5] 13 (by decide) (choices 1) [2,4,64] r39619 c39619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26134
  · exact u26135
  · exact u26136

def r39620 : Route 9 := (fun mask => (mask,id))

def c39620 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39620 : Upper (D 6) (R 6) [40,96,144,257,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,6] 13 (by decide) (choices 1) [1,2,4,64] r39620 c39620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26137
  · exact u26138
  · exact u26139
  · exact u26140

def r39621 : Route 9 := (fun mask => (mask,id))

def c39621 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39621 : Upper (D 6) (R 6) [40,96,144,257,65] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,65] 13 (by decide) (choices 1) [2,4] r39621 c39621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26141
  · exact u26142

def b39622 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 148 265 82 39 71 135 263), lower := (rows 41 98 148 265 82 32 64 128 256), losses := [] }

theorem u39622 : Upper (D 6) (R 6) [40,96,144,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39623 : Route 9 := (fun mask => (mask,id))

def c39623 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39623 : Upper (D 6) (R 6) [40,96,144,257,68] 13 := by
  apply FastRouting.sound _ _ [40,96,144,257,68] 13 (by decide) (choices 1) [1,2,4] r39623 c39623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26143
  · exact u26144
  · exact u26145

def b39624 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(3,5)], upper := (rows 41 98 148 266 19 101 69 197 325), lower := (rows 41 98 148 266 19 32 64 128 256), losses := [] }

theorem u39624 : Upper (D 6) (R 6) [40,96,144,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39625 : Route 9 := (fun mask => (mask,id))

def c39625 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39625 : Upper (D 6) (R 6) [40,96,144,258,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258,5] 13 (by decide) (choices 1) [1,2,4,64] r39625 c39625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26146
  · exact u26147
  · exact u26148
  · exact u26149

def r39626 : Route 9 := (fun mask => (mask,id))

def c39626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39626 : Upper (D 6) (R 6) [40,96,144,258,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258,6] 13 (by decide) (choices 1) [1,4,64] r39626 c39626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26150
  · exact u26151
  · exact u26152

def r39627 : Route 9 := (fun mask => (mask,id))

def c39627 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39627 : Upper (D 6) (R 6) [40,96,144,258,65] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258,65] 13 (by decide) (choices 1) [1,2,4] r39627 c39627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26153
  · exact u26154
  · exact u26155

def b39628 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 148 266 82 37 69 133 261), lower := (rows 41 98 148 266 82 32 64 128 256), losses := [] }

theorem u39628 : Upper (D 6) (R 6) [40,96,144,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39629 : Route 9 := (fun mask => (mask,id))

def c39629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39629 : Upper (D 6) (R 6) [40,96,144,258,68] 13 := by
  apply FastRouting.sound _ _ [40,96,144,258,68] 13 (by decide) (choices 1) [1,2,4] r39629 c39629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26156
  · exact u26157
  · exact u26158

def r39630 : Route 9 := (fun mask => (mask,id))

def c39630 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39630 : Upper (D 6) (R 6) [40,96,144,260,3] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260,3] 13 (by decide) (choices 1) [1,2,4,64] r39630 c39630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26159
  · exact u26160
  · exact u26161
  · exact u26162

def r39631 : Route 9 := (fun mask => (mask,id))

def c39631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39631 : Upper (D 6) (R 6) [40,96,144,260,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260,5] 13 (by decide) (choices 1) [1,2,64] r39631 c39631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26163
  · exact u26164
  · exact u26165

def r39632 : Route 9 := (fun mask => (mask,id))

def c39632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39632 : Upper (D 6) (R 6) [40,96,144,260,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260,6] 13 (by decide) (choices 1) [1,2,64] r39632 c39632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26166
  · exact u26167
  · exact u26168

def r39633 : Route 9 := (fun mask => (mask,id))

def c39633 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39633 : Upper (D 6) (R 6) [40,96,144,260,65] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260,65] 13 (by decide) (choices 1) [1,2,4] r39633 c39633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26169
  · exact u26170
  · exact u26171

def b39634 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 98 148 268 82 39 71 135 263), lower := (rows 41 98 148 268 82 32 64 128 256), losses := [] }

theorem u39634 : Upper (D 6) (R 6) [40,96,144,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39635 : Route 9 := (fun mask => (mask,id))

def c39635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39635 : Upper (D 6) (R 6) [40,96,144,260,68] 13 := by
  apply FastRouting.sound _ _ [40,96,144,260,68] 13 (by decide) (choices 1) [1,2] r39635 c39635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26172
  · exact u26173

def b39636 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 41 98 148 328 19 39 71 135 263), lower := (rows 41 98 148 328 19 32 64 128 256), losses := [] }

theorem u39636 : Upper (D 6) (R 6) [40,96,144,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39637 : Route 9 := (fun mask => (mask,id))

def c39637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39637 : Upper (D 6) (R 6) [40,96,144,320,5] 13 := by
  apply FastRouting.sound _ _ [40,96,144,320,5] 13 (by decide) (choices 1) [1,2,4] r39637 c39637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26174
  · exact u26175
  · exact u26176

def r39638 : Route 9 := (fun mask => (mask,id))

def c39638 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39638 : Upper (D 6) (R 6) [40,96,144,320,6] 13 := by
  apply FastRouting.sound _ _ [40,96,144,320,6] 13 (by decide) (choices 1) [1,2,4] r39638 c39638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26177
  · exact u26178
  · exact u26179

def b39639 : PairBound 9 := { available := 278, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 41 98 196 13 19 310 342 406 278), lower := (rows 41 98 196 13 19 32 64 128 256), losses := [] }

theorem u39639 : Upper (D 6) (R 6) [40,96,192,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39640 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 41 98 196 13 21 306 338 402 274), lower := (rows 41 98 196 13 21 32 64 128 256), losses := [] }

theorem u39640 : Upper (D 6) (R 6) [40,96,192,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39641 : Route 9 := (fun mask => (mask,id))

def c39641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39641 : Upper (D 6) (R 6) [40,96,192,5,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5,6] 13 (by decide) (choices 1) [1,2,16,256] r39641 c39641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26180
  · exact u26181
  · exact u26182
  · exact u26183

def r39642 : Route 9 := (fun mask => (mask,id))

def c39642 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39642 : Upper (D 6) (R 6) [40,96,192,5,257] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5,257] 13 (by decide) (choices 1) [2,4,16] r39642 c39642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26184
  · exact u26185
  · exact u26186

def r39643 : Route 9 := (fun mask => (mask,id))

def c39643 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39643 : Upper (D 6) (R 6) [40,96,192,5,258] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5,258] 13 (by decide) (choices 1) [1,2,4,16] r39643 c39643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26187
  · exact u26188
  · exact u26189
  · exact u26190

def r39644 : Route 9 := (fun mask => (mask,id))

def c39644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39644 : Upper (D 6) (R 6) [40,96,192,5,260] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5,260] 13 (by decide) (choices 1) [1,2,16] r39644 c39644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26191
  · exact u26192
  · exact u26193

def b39645 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 305, targets := 64 },{ cop := 4, region := 452, targets := 32 }], pairs := [(0,6),(2,5),(4,6)], upper := (rows 41 98 196 14 19 309 341 405 277), lower := (rows 41 98 196 14 19 32 64 128 256), losses := [] }

theorem u39645 : Upper (D 6) (R 6) [40,96,192,6,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39646 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 305, targets := 64 },{ cop := 4, region := 354, targets := 4 }], pairs := [(0,6),(1,2),(4,6)], upper := (rows 41 98 196 14 21 307 339 403 275), lower := (rows 41 98 196 14 21 32 64 128 256), losses := [] }

theorem u39646 : Upper (D 6) (R 6) [40,96,192,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39647 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 16, targets := 33 },{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,0),(4,5)], upper := (rows 41 98 196 14 22 305 337 401 273), lower := (rows 41 98 196 14 22 32 64 128 256), losses := [] }

theorem u39647 : Upper (D 6) (R 6) [40,96,192,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39648 : Route 9 := (fun mask => (mask,id))

def c39648 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39648 : Upper (D 6) (R 6) [40,96,192,6,257] 13 := by
  apply FastRouting.sound _ _ [40,96,192,6,257] 13 (by decide) (choices 1) [1,2,4,16] r39648 c39648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26194
  · exact u26195
  · exact u26196
  · exact u26197

def r39649 : Route 9 := (fun mask => (mask,id))

def c39649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39649 : Upper (D 6) (R 6) [40,96,192,6,258] 13 := by
  apply FastRouting.sound _ _ [40,96,192,6,258] 13 (by decide) (choices 1) [1,4,16] r39649 c39649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26198
  · exact u26199
  · exact u26200

def r39650 : Route 9 := (fun mask => (mask,id))

def c39650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39650 : Upper (D 6) (R 6) [40,96,192,6,260] 13 := by
  apply FastRouting.sound _ _ [40,96,192,6,260] 13 (by decide) (choices 1) [1,2,16] r39650 c39650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26201
  · exact u26202
  · exact u26203

def b39651 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 25 19 294 326 390 262), lower := (rows 41 98 196 25 19 32 64 128 256), losses := [] }

theorem u39651 : Upper (D 6) (R 6) [40,96,192,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b39652 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 196 25 21 294 326 390 262), lower := (rows 41 98 196 25 21 32 64 128 256), losses := [] }

theorem u39652 : Upper (D 6) (R 6) [40,96,192,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39653 : Route 9 := (fun mask => (mask,id))

def c39653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39653 : Upper (D 6) (R 6) [40,96,192,17,6] 13 := by
  apply FastRouting.sound _ _ [40,96,192,17,6] 13 (by decide) (choices 1) [1,2,4,256] r39653 c39653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26204
  · exact u26205
  · exact u26206
  · exact u26207

def b39654 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 41 98 196 25 273 38 70 134 262), lower := (rows 41 98 196 25 273 32 64 128 256), losses := [] }

theorem u39654 : Upper (D 6) (R 6) [40,96,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39655 : Route 9 := (fun mask => (mask,id))

def c39655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39655 : Upper (D 6) (R 6) [40,96,192,17,258] 13 := by
  apply FastRouting.sound _ _ [40,96,192,17,258] 13 (by decide) (choices 1) [1,2,4] r39655 c39655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26208
  · exact u26209
  · exact u26210

def r39656 : Route 9 := (fun mask => (mask,id))

def c39656 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39656 : Upper (D 6) (R 6) [40,96,192,17,260] 13 := by
  apply FastRouting.sound _ _ [40,96,192,17,260] 13 (by decide) (choices 1) [1,2,4] r39656 c39656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26211
  · exact u26212
  · exact u26213

def b39657 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 26 19 293 325 389 261), lower := (rows 41 98 196 26 19 32 64 128 256), losses := [] }

theorem u39657 : Upper (D 6) (R 6) [40,96,192,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r39658 : Route 9 := (fun mask => (mask,id))

def c39658 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39658 : Upper (D 6) (R 6) [40,96,192,18,5] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18,5] 13 (by decide) (choices 1) [1,2,4,256] r39658 c39658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26214
  · exact u26215
  · exact u26216
  · exact u26217

def b39659 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 98 196 26 22 293 325 389 261), lower := (rows 41 98 196 26 22 32 64 128 256), losses := [] }

theorem u39659 : Upper (D 6) (R 6) [40,96,192,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b39659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u39659
end Delivery.IrregularNine14.P06
