import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0562
import IrregularNine14P07C0564
import IrregularNine14P07C0565
import IrregularNine14P07C0566
import IrregularNine14P07C0567
import IrregularNine14P07C0568
import IrregularNine14P07C0569
import IrregularNine14P07C0570
import IrregularNine14P07C0571
import IrregularNine14P07C0572
import IrregularNine14P07C0573

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42060_3 : Upper (D 7) (R 7) [34,65,160,384,3] 13 :=
  permutation_upper _ _ _ [34,65,3,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33756

theorem m42060_5 : Upper (D 7) (R 7) [34,65,160,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33868

theorem m42060_6 : Upper (D 7) (R 7) [34,65,160,384,6] 13 :=
  permutation_upper _ _ _ [34,65,9,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33877

theorem m42060_9 : Upper (D 7) (R 7) [34,65,160,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33916

theorem m42060_10 : Upper (D 7) (R 7) [34,65,160,384,10] 13 :=
  permutation_upper _ _ _ [34,65,9,384,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33917

theorem m42060_12 : Upper (D 7) (R 7) [34,65,160,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33964

theorem m42060_65 : Upper (D 7) (R 7) [34,65,160,384,65] 13 :=
  permutation_upper _ _ _ [34,65,34,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34026

theorem m42060_66 : Upper (D 7) (R 7) [34,65,160,384,66] 13 :=
  permutation_upper _ _ _ [34,65,33,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33995

theorem m42060_68 : Upper (D 7) (R 7) [34,65,160,384,68] 13 :=
  permutation_upper _ _ _ [34,65,40,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34073

theorem m42060_72 : Upper (D 7) (R 7) [34,65,160,384,72] 13 :=
  permutation_upper _ _ _ [34,65,40,384,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34093

def r42060 : Route 9 := (fun mask => (mask,id))

def c42060 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42060 : Upper (D 7) (R 7) [34,65,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,160,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42060 c42060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42060_3
  · exact m42060_5
  · exact m42060_6
  · exact m42060_9
  · exact m42060_10
  · exact m42060_12
  · exact m42060_65
  · exact m42060_66
  · exact m42060_68
  · exact m42060_72

def b42061 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 70 13 11 496 496 496 496 496), lower := (rows 35 70 13 11 16 32 64 128 256), losses := [] }

theorem u42061 : Upper (D 7) (R 7) [34,68,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42062 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 70 13 25 498 482 482 482 482), lower := (rows 35 70 13 25 16 32 64 128 256), losses := [] }

theorem u42062 : Upper (D 7) (R 7) [34,68,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42063 : Route 9 := (fun mask => (mask,id))

def c42063 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42063 : Upper (D 7) (R 7) [34,68,9,18] 13 := by
  apply FastRouting.sound _ _ [34,68,9,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42063 c42063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34145
  · exact u34146
  · exact u34147
  · exact u34148
  · exact u34149
  · exact u34150
  · exact u34151
  · exact u34152
  · exact u34153
  · exact u34154

def b42064 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 70 13 41 466 498 466 466 466), lower := (rows 35 70 13 41 16 32 64 128 256), losses := [] }

theorem u42064 : Upper (D 7) (R 7) [34,68,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42065 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 13 42 465 497 465 465 465), lower := (rows 35 70 13 42 16 32 64 128 256), losses := [] }

theorem u42065 : Upper (D 7) (R 7) [34,68,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42066 : Route 9 := (fun mask => (mask,id))

def c42066 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42066 : Upper (D 7) (R 7) [34,68,9,48] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42066 c42066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34155
  · exact u34156
  · exact u34157
  · exact u34158
  · exact u34159
  · exact u34160
  · exact u34161
  · exact u34162
  · exact u34163
  · exact u34164

def b42067 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 6, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 13 73 434 434 498 434 434), lower := (rows 35 70 13 73 16 32 64 128 256), losses := [] }

theorem u42067 : Upper (D 7) (R 7) [34,68,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42068 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 13 74 433 433 497 433 433), lower := (rows 35 70 13 74 16 32 64 128 256), losses := [] }

theorem u42068 : Upper (D 7) (R 7) [34,68,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42069 : Route 9 := (fun mask => (mask,id))

def c42069 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42069 : Upper (D 7) (R 7) [34,68,9,80] 13 := by
  apply FastRouting.sound _ _ [34,68,9,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42069 c42069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34165
  · exact u34166
  · exact u34167
  · exact u34168
  · exact u34169
  · exact u34170
  · exact u34171
  · exact u34172
  · exact u34173
  · exact u34174

def b42070 : PairBound 9 := { available := 403, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 70 13 104 403 435 467 403 403), lower := (rows 35 70 13 104 16 32 64 128 256), losses := [] }

theorem u42070 : Upper (D 7) (R 7) [34,68,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42071 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 70 13 137 498 498 498 498 498), lower := (rows 35 70 13 137 16 32 64 128 256), losses := [] }

theorem u42071 : Upper (D 7) (R 7) [34,68,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42072 : Route 9 := (fun mask => (mask,id))

def c42072 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42072 : Upper (D 7) (R 7) [34,68,9,130] 13 := by
  apply FastRouting.sound _ _ [34,68,9,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42072 c42072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34175
  · exact u34176
  · exact u34177
  · exact u34178
  · exact u34179
  · exact u34180
  · exact u34181
  · exact u34182
  · exact u34183
  · exact u34184

def r42073 : Route 9 := (fun mask => (mask,id))

def c42073 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42073 : Upper (D 7) (R 7) [34,68,9,144] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42073 c42073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34185
  · exact u34186
  · exact u34187
  · exact u34188
  · exact u34189
  · exact u34190
  · exact u34191
  · exact u34192
  · exact u34193
  · exact u34194
  · exact u34195
  · exact u34196
  · exact u34197
  · exact u34198
  · exact u34199

def r42074 : Route 9 := (fun mask => (mask,id))

def c42074 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42074 : Upper (D 7) (R 7) [34,68,9,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42074 c42074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34200
  · exact u34201
  · exact u34202
  · exact u34203
  · exact u34204
  · exact u34205
  · exact u34206
  · exact u34207
  · exact u34208
  · exact u34209

def r42075 : Route 9 := (fun mask => (mask,id))

def c42075 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42075 : Upper (D 7) (R 7) [34,68,9,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42075 c42075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34210
  · exact u34211
  · exact u34212
  · exact u34213
  · exact u34214
  · exact u34215
  · exact u34216
  · exact u34217
  · exact u34218
  · exact u34219

def b42076 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 70 13 265 242 242 242 242 498), lower := (rows 35 70 13 265 16 32 64 128 256), losses := [] }

theorem u42076 : Upper (D 7) (R 7) [34,68,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42077 : Route 9 := (fun mask => (mask,id))

def c42077 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42077 : Upper (D 7) (R 7) [34,68,9,258] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42077 c42077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34220
  · exact u34221
  · exact u34222
  · exact u34223
  · exact u34224
  · exact u34225

def r42078 : Route 9 := (fun mask => (mask,id))

def c42078 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42078 : Upper (D 7) (R 7) [34,68,9,272] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42078 c42078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34226
  · exact u34227
  · exact u34228
  · exact u34229
  · exact u34230
  · exact u34231
  · exact u34232
  · exact u34233
  · exact u34234
  · exact u34235

def r42079 : Route 9 := (fun mask => (mask,id))

def c42079 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42079 : Upper (D 7) (R 7) [34,68,9,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42079 c42079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34236
  · exact u34237
  · exact u34238
  · exact u34239
  · exact u34240
  · exact u34241

def r42080 : Route 9 := (fun mask => (mask,id))

def c42080 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42080 : Upper (D 7) (R 7) [34,68,9,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42080 c42080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34242
  · exact u34243
  · exact u34244
  · exact u34245
  · exact u34246
  · exact u34247

def r42081 : Route 9 := (fun mask => (mask,id))

def c42081 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42081 : Upper (D 7) (R 7) [34,68,9,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42081 c42081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34248
  · exact u34249
  · exact u34250
  · exact u34251
  · exact u34252
  · exact u34253
  · exact u34254
  · exact u34255
  · exact u34256
  · exact u34257

def r42082 : Route 9 := (fun mask => (mask,id))

def c42082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42082 : Upper (D 7) (R 7) [34,68,10,17] 13 := by
  apply FastRouting.sound _ _ [34,68,10,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42082 c42082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34258
  · exact u34259
  · exact u34260
  · exact u34261
  · exact u34262
  · exact u34263
  · exact u34264
  · exact u34265
  · exact u34266
  · exact u34267

def b42083 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 14 41 465 497 465 465 465), lower := (rows 35 70 14 41 16 32 64 128 256), losses := [] }

theorem u42083 : Upper (D 7) (R 7) [34,68,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42084 : Route 9 := (fun mask => (mask,id))

def c42084 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42084 : Upper (D 7) (R 7) [34,68,10,48] 13 := by
  apply FastRouting.sound _ _ [34,68,10,48] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42084 c42084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34268
  · exact u34269
  · exact u34270
  · exact u34271
  · exact u34272
  · exact u34273

def b42085 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(2,0)], upper := (rows 35 70 14 73 433 433 497 433 433), lower := (rows 35 70 14 73 16 32 64 128 256), losses := [] }

theorem u42085 : Upper (D 7) (R 7) [34,68,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42086 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 6, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(2,0)], upper := (rows 35 70 14 88 433 417 481 417 417), lower := (rows 35 70 14 88 16 32 64 128 256), losses := [] }

theorem u42086 : Upper (D 7) (R 7) [34,68,10,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42087 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 14 104 401 433 465 401 401), lower := (rows 35 70 14 104 16 32 64 128 256), losses := [] }

theorem u42087 : Upper (D 7) (R 7) [34,68,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42088 : Route 9 := (fun mask => (mask,id))

def c42088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42088 : Upper (D 7) (R 7) [34,68,10,129] 13 := by
  apply FastRouting.sound _ _ [34,68,10,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42088 c42088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34274
  · exact u34275
  · exact u34276
  · exact u34277
  · exact u34278
  · exact u34279
  · exact u34280
  · exact u34281
  · exact u34282
  · exact u34283

def r42089 : Route 9 := (fun mask => (mask,id))

def c42089 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42089 : Upper (D 7) (R 7) [34,68,10,144] 13 := by
  apply FastRouting.sound _ _ [34,68,10,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42089 c42089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34284
  · exact u34285
  · exact u34286
  · exact u34287
  · exact u34288
  · exact u34289
  · exact u34290
  · exact u34291
  · exact u34292
  · exact u34293

def r42090 : Route 9 := (fun mask => (mask,id))

def c42090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42090 : Upper (D 7) (R 7) [34,68,10,160] 13 := by
  apply FastRouting.sound _ _ [34,68,10,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42090 c42090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34294
  · exact u34295
  · exact u34296
  · exact u34297
  · exact u34298
  · exact u34299

def b42091 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(2,0)], upper := (rows 35 70 14 200 433 433 497 433 433), lower := (rows 35 70 14 200 16 32 64 128 256), losses := [] }

theorem u42091 : Upper (D 7) (R 7) [34,68,10,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42092 : Route 9 := (fun mask => (mask,id))

def c42092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42092 : Upper (D 7) (R 7) [34,68,10,257] 13 := by
  apply FastRouting.sound _ _ [34,68,10,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42092 c42092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34300
  · exact u34301
  · exact u34302
  · exact u34303
  · exact u34304
  · exact u34305

def r42093 : Route 9 := (fun mask => (mask,id))

def c42093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42093 : Upper (D 7) (R 7) [34,68,10,272] 13 := by
  apply FastRouting.sound _ _ [34,68,10,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42093 c42093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34306
  · exact u34307
  · exact u34308
  · exact u34309
  · exact u34310
  · exact u34311

def r42094 : Route 9 := (fun mask => (mask,id))

def c42094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42094 : Upper (D 7) (R 7) [34,68,10,288] 13 := by
  apply FastRouting.sound _ _ [34,68,10,288] 13 (by decide) (choices 2) [65,129,192] r42094 c42094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34312
  · exact u34313
  · exact u34314

def b42095 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(2,0)], upper := (rows 35 70 14 328 177 177 241 177 433), lower := (rows 35 70 14 328 16 32 64 128 256), losses := [] }

theorem u42095 : Upper (D 7) (R 7) [34,68,10,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42096 : Route 9 := (fun mask => (mask,id))

def c42096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42096 : Upper (D 7) (R 7) [34,68,10,384] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42096 c42096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34315
  · exact u34316
  · exact u34317
  · exact u34318
  · exact u34319
  · exact u34320

def b42097 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 497 481 481 481 481), lower := (rows 35 70 28 11 16 32 64 128 256), losses := [] }

theorem u42097 : Upper (D 7) (R 7) [34,68,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42098 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 28 41 467 483 451 451 451), lower := (rows 35 70 28 41 16 32 64 128 256), losses := [] }

theorem u42098 : Upper (D 7) (R 7) [34,68,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42099 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 28 42 465 481 449 449 449), lower := (rows 35 70 28 42 16 32 64 128 256), losses := [] }

theorem u42099 : Upper (D 7) (R 7) [34,68,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42100_3 : Upper (D 7) (R 7) [34,68,24,65,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34321

theorem m42100_33 : Upper (D 7) (R 7) [34,68,24,65,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34330

theorem m42100_34 : Upper (D 7) (R 7) [34,68,24,65,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34338

def r42100 : Route 9 := (fun mask => (mask,id))

def c42100 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42100 : Upper (D 7) (R 7) [34,68,24,65] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42100 c42100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42100_3
  · exact m42100_33
  · exact m42100_34
  · exact u34344
  · exact u34345
  · exact u34346
  · exact u34347
  · exact u34348
  · exact u34349
  · exact u34350

def b42101 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 433 417 481 417 417), lower := (rows 35 70 28 74 16 32 64 128 256), losses := [] }

theorem u42101 : Upper (D 7) (R 7) [34,68,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42102_3 : Upper (D 7) (R 7) [34,68,24,96,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34322

def r42102 : Route 9 := (fun mask => (mask,id))

def c42102 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42102 : Upper (D 7) (R 7) [34,68,24,96] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42102 c42102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42102_3
  · exact u34356
  · exact u34357
  · exact u34358
  · exact u34359
  · exact u34360

theorem m42103_3 : Upper (D 7) (R 7) [34,68,24,129,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34323

theorem m42103_33 : Upper (D 7) (R 7) [34,68,24,129,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34331

theorem m42103_34 : Upper (D 7) (R 7) [34,68,24,129,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34339

theorem m42103_65 : Upper (D 7) (R 7) [34,68,24,129,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34344

theorem m42103_66 : Upper (D 7) (R 7) [34,68,24,129,66] 13 :=
  permutation_upper _ _ _ [34,68,24,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34351

theorem m42103_96 : Upper (D 7) (R 7) [34,68,24,129,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34356

def r42103 : Route 9 := (fun mask => (mask,id))

def c42103 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42103 : Upper (D 7) (R 7) [34,68,24,129] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42103 c42103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42103_3
  · exact m42103_33
  · exact m42103_34
  · exact m42103_65
  · exact m42103_66
  · exact m42103_96
  · exact u34361
  · exact u34362
  · exact u34363
  · exact u34364
  · exact u34365
  · exact u34366
  · exact u34367
  · exact u34368
  · exact u34369

theorem m42104_33 : Upper (D 7) (R 7) [34,68,24,130,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34332

theorem m42104_65 : Upper (D 7) (R 7) [34,68,24,130,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34345

theorem m42104_96 : Upper (D 7) (R 7) [34,68,24,130,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34357

theorem m42104_129 : Upper (D 7) (R 7) [34,68,24,130,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34362

def r42104 : Route 9 := (fun mask => (mask,id))

def c42104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42104 : Upper (D 7) (R 7) [34,68,24,130] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42104 c42104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42104_33
  · exact m42104_65
  · exact m42104_96
  · exact m42104_129
  · exact u34370
  · exact u34371
  · exact u34372
  · exact u34373
  · exact u34374
  · exact u34375

theorem m42105_3 : Upper (D 7) (R 7) [34,68,24,160,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34324

theorem m42105_65 : Upper (D 7) (R 7) [34,68,24,160,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34346

theorem m42105_66 : Upper (D 7) (R 7) [34,68,24,160,66] 13 :=
  permutation_upper _ _ _ [34,68,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34352

theorem m42105_129 : Upper (D 7) (R 7) [34,68,24,160,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34363

theorem m42105_130 : Upper (D 7) (R 7) [34,68,24,160,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34370

def r42105 : Route 9 := (fun mask => (mask,id))

def c42105 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42105 : Upper (D 7) (R 7) [34,68,24,160] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42105 c42105
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42105_3
  · exact m42105_65
  · exact m42105_66
  · exact m42105_129
  · exact m42105_130
  · exact u34376
  · exact u34377
  · exact u34378
  · exact u34379
  · exact u34380

theorem m42106_3 : Upper (D 7) (R 7) [34,68,24,192,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34325

theorem m42106_33 : Upper (D 7) (R 7) [34,68,24,192,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34333

theorem m42106_34 : Upper (D 7) (R 7) [34,68,24,192,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34340

theorem m42106_129 : Upper (D 7) (R 7) [34,68,24,192,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34364

theorem m42106_130 : Upper (D 7) (R 7) [34,68,24,192,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34371

theorem m42106_160 : Upper (D 7) (R 7) [34,68,24,192,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34376

def r42106 : Route 9 := (fun mask => (mask,id))

def c42106 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42106 : Upper (D 7) (R 7) [34,68,24,192] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42106 c42106
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42106_3
  · exact m42106_33
  · exact m42106_34
  · exact m42106_129
  · exact m42106_130
  · exact m42106_160
  · exact u34381
  · exact u34382
  · exact u34383
  · exact u34384

theorem m42107_3 : Upper (D 7) (R 7) [34,68,24,257,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34326

theorem m42107_33 : Upper (D 7) (R 7) [34,68,24,257,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34334

theorem m42107_34 : Upper (D 7) (R 7) [34,68,24,257,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34341

theorem m42107_65 : Upper (D 7) (R 7) [34,68,24,257,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34347

theorem m42107_66 : Upper (D 7) (R 7) [34,68,24,257,66] 13 :=
  permutation_upper _ _ _ [34,68,24,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34353

theorem m42107_96 : Upper (D 7) (R 7) [34,68,24,257,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34358

theorem m42107_129 : Upper (D 7) (R 7) [34,68,24,257,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34365

theorem m42107_130 : Upper (D 7) (R 7) [34,68,24,257,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34372

theorem m42107_160 : Upper (D 7) (R 7) [34,68,24,257,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34377

theorem m42107_192 : Upper (D 7) (R 7) [34,68,24,257,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34381

def r42107 : Route 9 := (fun mask => (mask,id))

def c42107 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42107 : Upper (D 7) (R 7) [34,68,24,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42107 c42107
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42107_3
  · exact m42107_33
  · exact m42107_34
  · exact m42107_65
  · exact m42107_66
  · exact m42107_96
  · exact m42107_129
  · exact m42107_130
  · exact m42107_160
  · exact m42107_192

theorem m42108_33 : Upper (D 7) (R 7) [34,68,24,258,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34335

theorem m42108_65 : Upper (D 7) (R 7) [34,68,24,258,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34348

theorem m42108_96 : Upper (D 7) (R 7) [34,68,24,258,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34359

theorem m42108_129 : Upper (D 7) (R 7) [34,68,24,258,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34366

theorem m42108_160 : Upper (D 7) (R 7) [34,68,24,258,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34378

theorem m42108_192 : Upper (D 7) (R 7) [34,68,24,258,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34382

def r42108 : Route 9 := (fun mask => (mask,id))

def c42108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42108 : Upper (D 7) (R 7) [34,68,24,258] 13 := by
  apply FastRouting.sound _ _ [34,68,24,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42108 c42108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42108_33
  · exact m42108_65
  · exact m42108_96
  · exact m42108_129
  · exact m42108_160
  · exact m42108_192

theorem m42109_3 : Upper (D 7) (R 7) [34,68,24,288,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34327

theorem m42109_65 : Upper (D 7) (R 7) [34,68,24,288,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34349

theorem m42109_66 : Upper (D 7) (R 7) [34,68,24,288,66] 13 :=
  permutation_upper _ _ _ [34,68,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34354

theorem m42109_129 : Upper (D 7) (R 7) [34,68,24,288,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34367

theorem m42109_130 : Upper (D 7) (R 7) [34,68,24,288,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34373

theorem m42109_192 : Upper (D 7) (R 7) [34,68,24,288,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34383

def r42109 : Route 9 := (fun mask => (mask,id))

def c42109 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42109 : Upper (D 7) (R 7) [34,68,24,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42109 c42109
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42109_3
  · exact m42109_65
  · exact m42109_66
  · exact m42109_129
  · exact m42109_130
  · exact m42109_192

theorem m42110_3 : Upper (D 7) (R 7) [34,68,24,320,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34328

theorem m42110_33 : Upper (D 7) (R 7) [34,68,24,320,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34336

theorem m42110_34 : Upper (D 7) (R 7) [34,68,24,320,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34342

theorem m42110_129 : Upper (D 7) (R 7) [34,68,24,320,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34368

theorem m42110_130 : Upper (D 7) (R 7) [34,68,24,320,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34374

theorem m42110_160 : Upper (D 7) (R 7) [34,68,24,320,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34379

def r42110 : Route 9 := (fun mask => (mask,id))

def c42110 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42110 : Upper (D 7) (R 7) [34,68,24,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r42110 c42110
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42110_3
  · exact m42110_33
  · exact m42110_34
  · exact m42110_129
  · exact m42110_130
  · exact m42110_160

theorem m42111_3 : Upper (D 7) (R 7) [34,68,24,384,3] 13 :=
  permutation_upper _ _ _ [34,68,24,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34329

theorem m42111_33 : Upper (D 7) (R 7) [34,68,24,384,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34337

theorem m42111_34 : Upper (D 7) (R 7) [34,68,24,384,34] 13 :=
  permutation_upper _ _ _ [34,68,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34343

theorem m42111_65 : Upper (D 7) (R 7) [34,68,24,384,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34350

theorem m42111_66 : Upper (D 7) (R 7) [34,68,24,384,66] 13 :=
  permutation_upper _ _ _ [34,68,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34355

theorem m42111_96 : Upper (D 7) (R 7) [34,68,24,384,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34360

theorem m42111_129 : Upper (D 7) (R 7) [34,68,24,384,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34369

theorem m42111_130 : Upper (D 7) (R 7) [34,68,24,384,130] 13 :=
  permutation_upper _ _ _ [34,68,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34375

theorem m42111_160 : Upper (D 7) (R 7) [34,68,24,384,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34380

theorem m42111_192 : Upper (D 7) (R 7) [34,68,24,384,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34384

def r42111 : Route 9 := (fun mask => (mask,id))

def c42111 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42111 : Upper (D 7) (R 7) [34,68,24,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42111 c42111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42111_3
  · exact m42111_33
  · exact m42111_34
  · exact m42111_65
  · exact m42111_66
  · exact m42111_96
  · exact m42111_129
  · exact m42111_130
  · exact m42111_160
  · exact m42111_192

def b42112 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 70 44 11 465 497 465 465 465), lower := (rows 35 70 44 11 16 32 64 128 256), losses := [] }

theorem u42112 : Upper (D 7) (R 7) [34,68,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42113 : Route 9 := (fun mask => (mask,id))

def c42113 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42113 : Upper (D 7) (R 7) [34,68,40,17] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42113 c42113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34385
  · exact u34386
  · exact u34387
  · exact u34388
  · exact u34389
  · exact u34390
  · exact u34391
  · exact u34392
  · exact u34393
  · exact u34394

def r42114 : Route 9 := (fun mask => (mask,id))

def c42114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42114 : Upper (D 7) (R 7) [34,68,40,18] 13 := by
  apply FastRouting.sound _ _ [34,68,40,18] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42114 c42114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34395
  · exact u34396
  · exact u34397
  · exact u34398
  · exact u34399
  · exact u34400

def b42115 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 73 403 435 467 403 403), lower := (rows 35 70 44 73 16 32 64 128 256), losses := [] }

theorem u42115 : Upper (D 7) (R 7) [34,68,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42116 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 44 74 401 433 465 401 401), lower := (rows 35 70 44 74 16 32 64 128 256), losses := [] }

theorem u42116 : Upper (D 7) (R 7) [34,68,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42117 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 88 403 419 451 387 387), lower := (rows 35 70 44 88 16 32 64 128 256), losses := [] }

theorem u42117 : Upper (D 7) (R 7) [34,68,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42118 : Route 9 := (fun mask => (mask,id))

def c42118 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42118 : Upper (D 7) (R 7) [34,68,40,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42118 c42118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34401
  · exact u34402
  · exact u34403
  · exact u34404
  · exact u34405
  · exact u34406
  · exact u34407
  · exact u34408
  · exact u34409
  · exact u34410

def r42119 : Route 9 := (fun mask => (mask,id))

def c42119 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42119 : Upper (D 7) (R 7) [34,68,40,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,130] 13 (by decide) (choices 2) [65,129,192,257,320,384] r42119 c42119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34411
  · exact u34412
  · exact u34413
  · exact u34414
  · exact u34415
  · exact u34416

#print axioms u42119
end Delivery.IrregularNine14.P07
