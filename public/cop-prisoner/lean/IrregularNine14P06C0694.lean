import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0534
import IrregularNine14P06C0535
import IrregularNine14P06C0536
import IrregularNine14P06C0537
import IrregularNine14P06C0538

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41640 : Route 9 := (fun mask => (mask,id))

def c41640 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41640 : Upper (D 6) (R 6) [10,48,160,68] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41640 c41640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32083
  · exact u32084
  · exact u32085
  · exact u32086
  · exact u32087
  · exact u32088
  · exact u32089
  · exact u32090
  · exact u32091
  · exact u32092

def r41641 : Route 9 := (fun mask => (mask,id))

def c41641 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41641 : Upper (D 6) (R 6) [10,48,160,257] 13 := by
  apply FastRouting.sound _ _ [10,48,160,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41641 c41641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32093
  · exact u32094
  · exact u32095
  · exact u32096
  · exact u32097
  · exact u32098

def b41642 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 164 266 85 101 69 197 325), lower := (rows 11 50 164 266 16 32 64 128 256), losses := [] }

theorem u41642 : Upper (D 6) (R 6) [10,48,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41643 : Route 9 := (fun mask => (mask,id))

def c41643 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41643 : Upper (D 6) (R 6) [10,48,160,260] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41643 c41643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32099
  · exact u32100
  · exact u32101
  · exact u32102
  · exact u32103
  · exact u32104

def r41644 : Route 9 := (fun mask => (mask,id))

def c41644 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41644 : Upper (D 6) (R 6) [10,48,160,320] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41644 c41644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32105
  · exact u32106
  · exact u32107
  · exact u32108
  · exact u32109
  · exact u32110

def b41645 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 196 11 373 357 357 485 357), lower := (rows 11 50 196 11 16 32 64 128 256), losses := [] }

theorem u41645 : Upper (D 6) (R 6) [10,48,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41646 : Route 9 := (fun mask => (mask,id))

def c41646 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41646 : Upper (D 6) (R 6) [10,48,192,5] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r41646 c41646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32111
  · exact u32112
  · exact u32113
  · exact u32114
  · exact u32115
  · exact u32116
  · exact u32117
  · exact u32118
  · exact u32119
  · exact u32120
  · exact u32121
  · exact u32122
  · exact u32123
  · exact u32124
  · exact u32125

def b41647 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 196 14 373 357 357 485 357), lower := (rows 11 50 196 14 16 32 64 128 256), losses := [] }

theorem u41647 : Upper (D 6) (R 6) [10,48,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41648 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 196 41 343 359 327 455 327), lower := (rows 11 50 196 41 16 32 64 128 256), losses := [] }

theorem u41648 : Upper (D 6) (R 6) [10,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41649 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 196 42 341 357 325 453 325), lower := (rows 11 50 196 42 16 32 64 128 256), losses := [] }

theorem u41649 : Upper (D 6) (R 6) [10,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41650 : Route 9 := (fun mask => (mask,id))

def c41650 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41650 : Upper (D 6) (R 6) [10,48,192,36] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41650 c41650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32126
  · exact u32127
  · exact u32128
  · exact u32129
  · exact u32130
  · exact u32131
  · exact u32132
  · exact u32133
  · exact u32134
  · exact u32135

def r41651 : Route 9 := (fun mask => (mask,id))

def c41651 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41651 : Upper (D 6) (R 6) [10,48,192,65] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r41651 c41651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32136
  · exact u32137
  · exact u32138
  · exact u32139
  · exact u32140
  · exact u32141
  · exact u32142
  · exact u32143
  · exact u32144
  · exact u32145

def b41652 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 196 74 309 293 357 421 293), lower := (rows 11 50 196 74 16 32 64 128 256), losses := [] }

theorem u41652 : Upper (D 6) (R 6) [10,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41653 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 196 76 311 295 359 423 295), lower := (rows 11 50 196 76 16 32 64 128 256), losses := [] }

theorem u41653 : Upper (D 6) (R 6) [10,48,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41654 : Route 9 := (fun mask => (mask,id))

def c41654 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41654 : Upper (D 6) (R 6) [10,48,192,96] 13 := by
  apply FastRouting.sound _ _ [10,48,192,96] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41654 c41654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32146
  · exact u32147
  · exact u32148
  · exact u32149
  · exact u32150
  · exact u32151

def r41655 : Route 9 := (fun mask => (mask,id))

def c41655 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41655 : Upper (D 6) (R 6) [10,48,192,257] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41655 c41655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32152
  · exact u32153
  · exact u32154
  · exact u32155
  · exact u32156
  · exact u32157
  · exact u32158
  · exact u32159
  · exact u32160
  · exact u32161

def b41656 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 196 266 117 101 101 229 357), lower := (rows 11 50 196 266 16 32 64 128 256), losses := [] }

theorem u41656 : Upper (D 6) (R 6) [10,48,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41657 : Route 9 := (fun mask => (mask,id))

def c41657 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41657 : Upper (D 6) (R 6) [10,48,192,260] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41657 c41657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32162
  · exact u32163
  · exact u32164
  · exact u32165
  · exact u32166
  · exact u32167
  · exact u32168
  · exact u32169
  · exact u32170
  · exact u32171

def r41658 : Route 9 := (fun mask => (mask,id))

def c41658 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41658 : Upper (D 6) (R 6) [10,48,192,288] 13 := by
  apply FastRouting.sound _ _ [10,48,192,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41658 c41658
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32172
  · exact u32173
  · exact u32174
  · exact u32175
  · exact u32176
  · exact u32177

def r41659 : Route 9 := (fun mask => (mask,id))

def c41659 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41659 : Upper (D 6) (R 6) [10,48,192,320] 13 := by
  apply FastRouting.sound _ _ [10,48,192,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r41659 c41659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32178
  · exact u32179
  · exact u32180
  · exact u32181
  · exact u32182
  · exact u32183

def b41660 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 388 11 117 101 101 229 357), lower := (rows 11 50 388 11 16 32 64 128 256), losses := [] }

theorem u41660 : Upper (D 6) (R 6) [10,48,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41661 : Route 9 := (fun mask => (mask,id))

def c41661 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41661 : Upper (D 6) (R 6) [10,48,384,5] 13 := by
  apply FastRouting.sound _ _ [10,48,384,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41661 c41661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32184
  · exact u32185
  · exact u32186
  · exact u32187
  · exact u32188
  · exact u32189
  · exact u32190
  · exact u32191
  · exact u32192
  · exact u32193

def b41662 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 388 14 117 101 101 229 357), lower := (rows 11 50 388 14 16 32 64 128 256), losses := [] }

theorem u41662 : Upper (D 6) (R 6) [10,48,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41663 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 388 41 87 103 71 199 327), lower := (rows 11 50 388 41 16 32 64 128 256), losses := [] }

theorem u41663 : Upper (D 6) (R 6) [10,48,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41664 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 388 42 85 101 69 197 325), lower := (rows 11 50 388 42 16 32 64 128 256), losses := [] }

theorem u41664 : Upper (D 6) (R 6) [10,48,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41665 : Route 9 := (fun mask => (mask,id))

def c41665 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41665 : Upper (D 6) (R 6) [10,48,384,36] 13 := by
  apply FastRouting.sound _ _ [10,48,384,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41665 c41665
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32194
  · exact u32195
  · exact u32196
  · exact u32197
  · exact u32198
  · exact u32199

def r41666 : Route 9 := (fun mask => (mask,id))

def c41666 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41666 : Upper (D 6) (R 6) [10,48,384,65] 13 := by
  apply FastRouting.sound _ _ [10,48,384,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41666 c41666
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32200
  · exact u32201
  · exact u32202
  · exact u32203
  · exact u32204
  · exact u32205
  · exact u32206
  · exact u32207
  · exact u32208
  · exact u32209

def b41667 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 50 388 74 117 101 101 229 357), lower := (rows 11 50 388 74 16 32 64 128 256), losses := [] }

theorem u41667 : Upper (D 6) (R 6) [10,48,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41668 : Route 9 := (fun mask => (mask,id))

def c41668 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41668 : Upper (D 6) (R 6) [10,48,384,68] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r41668 c41668
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32210
  · exact u32211
  · exact u32212
  · exact u32213
  · exact u32214
  · exact u32215
  · exact u32216
  · exact u32217
  · exact u32218
  · exact u32219

def r41669 : Route 9 := (fun mask => (mask,id))

def c41669 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41669 : Upper (D 6) (R 6) [10,48,384,96] 13 := by
  apply FastRouting.sound _ _ [10,48,384,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41669 c41669
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32220
  · exact u32221
  · exact u32222
  · exact u32223
  · exact u32224
  · exact u32225

def b41670 : PairBound 9 := { available := 485, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 22 13 501 485 485 485 485), lower := (rows 11 98 22 13 16 32 64 128 256), losses := [] }

theorem u41670 : Upper (D 6) (R 6) [10,96,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41671 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 22 41 469 485 453 453 453), lower := (rows 11 98 22 41 16 32 64 128 256), losses := [] }

theorem u41671 : Upper (D 6) (R 6) [10,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41672_5 : Upper (D 6) (R 6) [10,96,18,36,5] 13 :=
  permutation_upper _ _ _ [10,96,18,5,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32226

theorem m41672_68 : Upper (D 6) (R 6) [10,96,18,36,68] 13 :=
  permutation_upper _ _ _ [10,96,18,33,65] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32231

def r41672 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41672 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41672 : Upper (D 6) (R 6) [10,96,18,36] 13 := by
  apply FastRouting.sound _ _ [10,96,18,36] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r41672 c41672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41672_5
  · exact u32236
  · exact m41672_68
  · exact u32237
  · exact u32238
  · exact u32239
  · exact u32240

def b41673 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 22 104 405 421 453 389 389), lower := (rows 11 98 22 104 16 32 64 128 256), losses := [] }

theorem u41673 : Upper (D 6) (R 6) [10,96,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m41674_5 : Upper (D 6) (R 6) [10,96,18,129,5] 13 :=
  permutation_upper _ _ _ [10,96,18,5,132] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32228

theorem m41674_33 : Upper (D 6) (R 6) [10,96,18,129,33] 13 :=
  permutation_upper _ _ _ [10,96,18,36,132] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32238

theorem m41674_36 : Upper (D 6) (R 6) [10,96,18,129,36] 13 :=
  permutation_upper _ _ _ [10,96,18,33,132] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32233

theorem m41674_96 : Upper (D 6) (R 6) [10,96,18,129,96] 13 :=
  permutation_upper _ _ _ [10,96,18,96,132] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32242

def r41674 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41674 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41674 : Upper (D 6) (R 6) [10,96,18,129] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41674 c41674
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41674_5
  · exact m41674_33
  · exact m41674_36
  · exact m41674_96
  · exact u32244
  · exact u32245
  · exact u32246

theorem m41675_5 : Upper (D 6) (R 6) [10,96,18,132,5] 13 :=
  permutation_upper _ _ _ [10,96,18,5,129] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32227

theorem m41675_33 : Upper (D 6) (R 6) [10,96,18,132,33] 13 :=
  permutation_upper _ _ _ [10,96,18,36,129] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32237

theorem m41675_36 : Upper (D 6) (R 6) [10,96,18,132,36] 13 :=
  permutation_upper _ _ _ [10,96,18,33,129] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32232

theorem m41675_96 : Upper (D 6) (R 6) [10,96,18,132,96] 13 :=
  permutation_upper _ _ _ [10,96,18,96,129] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32241

theorem m41675_260 : Upper (D 6) (R 6) [10,96,18,132,260] 13 :=
  permutation_upper _ _ _ [10,96,18,129,257] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32244

def r41675 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41675 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41675 : Upper (D 6) (R 6) [10,96,18,132] 13 := by
  apply FastRouting.sound _ _ [10,96,18,132] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41675 c41675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41675_5
  · exact m41675_33
  · exact m41675_36
  · exact m41675_96
  · exact u32247
  · exact m41675_260
  · exact u32248

theorem m41676_5 : Upper (D 6) (R 6) [10,96,18,160,5] 13 :=
  permutation_upper _ _ _ [10,96,18,5,160] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32229

theorem m41676_65 : Upper (D 6) (R 6) [10,96,18,160,65] 13 :=
  permutation_upper _ _ _ [10,96,18,36,192] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32239

theorem m41676_68 : Upper (D 6) (R 6) [10,96,18,160,68] 13 :=
  permutation_upper _ _ _ [10,96,18,33,192] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32234

theorem m41676_257 : Upper (D 6) (R 6) [10,96,18,160,257] 13 :=
  permutation_upper _ _ _ [10,96,18,132,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32248

theorem m41676_260 : Upper (D 6) (R 6) [10,96,18,160,260] 13 :=
  permutation_upper _ _ _ [10,96,18,129,288] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32246

def r41676 : Route 9 := (fun mask => (mask,id))

def c41676 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41676 : Upper (D 6) (R 6) [10,96,18,160] 13 := by
  apply FastRouting.sound _ _ [10,96,18,160] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41676 c41676
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41676_5
  · exact m41676_65
  · exact m41676_68
  · exact m41676_257
  · exact m41676_260
  · exact u32249

theorem m41677_5 : Upper (D 6) (R 6) [10,96,18,384,5] 13 :=
  permutation_upper _ _ _ [10,96,18,5,384] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32230

theorem m41677_33 : Upper (D 6) (R 6) [10,96,18,384,33] 13 :=
  permutation_upper _ _ _ [10,96,18,36,384] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32240

theorem m41677_36 : Upper (D 6) (R 6) [10,96,18,384,36] 13 :=
  permutation_upper _ _ _ [10,96,18,33,384] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32235

theorem m41677_96 : Upper (D 6) (R 6) [10,96,18,384,96] 13 :=
  permutation_upper _ _ _ [10,96,18,96,384] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32243

def r41677 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41677 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41677 : Upper (D 6) (R 6) [10,96,18,384] 13 := by
  apply FastRouting.sound _ _ [10,96,18,384] 13 (by decide) (choices 2) [5,33,36,96] r41677 c41677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41677_5
  · exact m41677_33
  · exact m41677_36
  · exact m41677_96

def b41678 : PairBound 9 := { available := 468, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 11 468 500 468 468 468), lower := (rows 11 98 37 11 16 32 64 128 256), losses := [] }

theorem u41678 : Upper (D 6) (R 6) [10,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41679 : PairBound 9 := { available := 470, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 13 470 502 470 470 470), lower := (rows 11 98 37 13 16 32 64 128 256), losses := [] }

theorem u41679 : Upper (D 6) (R 6) [10,96,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41680 : PairBound 9 := { available := 469, camps := [{ cop := 1, region := 13, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 14 469 501 469 469 469), lower := (rows 11 98 37 14 16 32 64 128 256), losses := [] }

theorem u41680 : Upper (D 6) (R 6) [10,96,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41681 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41681 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41681 : Upper (D 6) (R 6) [10,96,33,17] 13 := by
  apply FastRouting.sound _ _ [10,96,33,17] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r41681 c41681
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32250
  · exact u32251
  · exact u32252
  · exact u32253
  · exact u32254
  · exact u32255
  · exact u32256

def b41682 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 37 26 469 485 453 453 453), lower := (rows 11 98 37 26 16 32 64 128 256), losses := [] }

theorem u41682 : Upper (D 6) (R 6) [10,96,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41683 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41683 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41683 : Upper (D 6) (R 6) [10,96,33,20] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41683 c41683
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32257
  · exact u32258
  · exact u32259
  · exact u32260
  · exact u32261
  · exact u32262
  · exact u32263
  · exact u32264
  · exact u32265
  · exact u32266
  · exact u32267

def b41684 : PairBound 9 := { available := 406, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 73 406 438 470 406 406), lower := (rows 11 98 37 73 16 32 64 128 256), losses := [] }

theorem u41684 : Upper (D 6) (R 6) [10,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41685 : PairBound 9 := { available := 405, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 74 405 437 469 405 405), lower := (rows 11 98 37 74 16 32 64 128 256), losses := [] }

theorem u41685 : Upper (D 6) (R 6) [10,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41686 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41686 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41686 : Upper (D 6) (R 6) [10,96,33,68] 13 := by
  apply FastRouting.sound _ _ [10,96,33,68] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41686 c41686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32268
  · exact u32269
  · exact u32270
  · exact u32271
  · exact u32272
  · exact u32273
  · exact u32274

def r41687 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41687 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41687 : Upper (D 6) (R 6) [10,96,33,80] 13 := by
  apply FastRouting.sound _ _ [10,96,33,80] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41687 c41687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32275
  · exact u32276
  · exact u32277
  · exact u32278
  · exact u32279
  · exact u32280
  · exact u32281

def r41688 : Route 9 := (fun mask => (mask,id))

def c41688 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41688 : Upper (D 6) (R 6) [10,96,33,129] 13 := by
  apply FastRouting.sound _ _ [10,96,33,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r41688 c41688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32282
  · exact u32283
  · exact u32284
  · exact u32285
  · exact u32286
  · exact u32287

def b41689 : PairBound 9 := { available := 341, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 37 138 341 373 341 469 341), lower := (rows 11 98 37 138 16 32 64 128 256), losses := [] }

theorem u41689 : Upper (D 6) (R 6) [10,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41690 : Route 9 := (fun mask => (mask,id))

def c41690 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41690 : Upper (D 6) (R 6) [10,96,33,132] 13 := by
  apply FastRouting.sound _ _ [10,96,33,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41690 c41690
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32288
  · exact u32289
  · exact u32290
  · exact u32291
  · exact u32292
  · exact u32293
  · exact u32294
  · exact u32295
  · exact u32296
  · exact u32297

def r41691 : Route 9 := (fun mask => (mask,id))

def c41691 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41691 : Upper (D 6) (R 6) [10,96,33,144] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41691 c41691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32298
  · exact u32299
  · exact u32300
  · exact u32301
  · exact u32302
  · exact u32303
  · exact u32304
  · exact u32305
  · exact u32306
  · exact u32307

def r41692 : Route 9 := (fun mask => (mask,id))

def c41692 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41692 : Upper (D 6) (R 6) [10,96,33,192] 13 := by
  apply FastRouting.sound _ _ [10,96,33,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41692 c41692
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32308
  · exact u32309
  · exact u32310
  · exact u32311
  · exact u32312
  · exact u32313

def r41693 : Route 9 := (fun mask => (mask,id))

def c41693 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41693 : Upper (D 6) (R 6) [10,96,33,384] 13 := by
  apply FastRouting.sound _ _ [10,96,33,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41693 c41693
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32314
  · exact u32315
  · exact u32316
  · exact u32317
  · exact u32318
  · exact u32319

def b41694 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 52 11 469 485 453 453 453), lower := (rows 11 98 52 11 16 32 64 128 256), losses := [] }

theorem u41694 : Upper (D 6) (R 6) [10,96,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41695 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41695 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41695 : Upper (D 6) (R 6) [10,96,48,5] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r41695 c41695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32320
  · exact u32321
  · exact u32322
  · exact u32323
  · exact u32324
  · exact u32325
  · exact u32326
  · exact u32327
  · exact u32328
  · exact u32329
  · exact u32330

def b41696 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 98 52 14 469 485 453 453 453), lower := (rows 11 98 52 14 16 32 64 128 256), losses := [] }

theorem u41696 : Upper (D 6) (R 6) [10,96,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41697 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 52 73 407 423 455 391 391), lower := (rows 11 98 52 73 16 32 64 128 256), losses := [] }

theorem u41697 : Upper (D 6) (R 6) [10,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41698 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 52 74 405 421 453 389 389), lower := (rows 11 98 52 74 16 32 64 128 256), losses := [] }

theorem u41698 : Upper (D 6) (R 6) [10,96,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41699 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c41699 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41699 : Upper (D 6) (R 6) [10,96,48,68] 13 := by
  apply FastRouting.sound _ _ [10,96,48,68] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r41699 c41699
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32331
  · exact u32332
  · exact u32333
  · exact u32334
  · exact u32335
  · exact u32336
  · exact u32337

#print axioms u41699
end Delivery.IrregularNine14.P06
