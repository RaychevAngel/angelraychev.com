import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0568
import IrregularNine14P06C0569
import IrregularNine14P06C0570
import IrregularNine14P06C0571
import IrregularNine14P06C0572

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42120 : Route 9 := (fun mask => (mask,id))

def c42120 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42120 : Upper (D 6) (R 6) [10,160,80,260] 13 := by
  apply FastRouting.sound _ _ [10,160,80,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42120 c42120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34106
  · exact u34107
  · exact u34108
  · exact u34109
  · exact u34110
  · exact u34111
  · exact u34112
  · exact u34113
  · exact u34114
  · exact u34115

def r42121 : Route 9 := (fun mask => (mask,id))

def c42121 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42121 : Upper (D 6) (R 6) [10,160,80,288] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42121 c42121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34116
  · exact u34117
  · exact u34118
  · exact u34119
  · exact u34120
  · exact u34121

def r42122 : Route 9 := (fun mask => (mask,id))

def c42122 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42122 : Upper (D 6) (R 6) [10,160,80,320] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320] 13 (by decide) (choices 2) [3,5,6,33,34,36] r42122 c42122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34122
  · exact u34123
  · exact u34124
  · exact u34125
  · exact u34126
  · exact u34127

def b42123 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 11 341 373 341 469 341), lower := (rows 11 162 100 11 16 32 64 128 256), losses := [] }

theorem u42123 : Upper (D 6) (R 6) [10,160,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42124 : Route 9 := (fun mask => (mask,id))

def c42124 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42124 : Upper (D 6) (R 6) [10,160,96,5] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42124 c42124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34128
  · exact u34129
  · exact u34130
  · exact u34131
  · exact u34132
  · exact u34133
  · exact u34134
  · exact u34135
  · exact u34136
  · exact u34137

def b42125 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 100 14 341 373 341 469 341), lower := (rows 11 162 100 14 16 32 64 128 256), losses := [] }

theorem u42125 : Upper (D 6) (R 6) [10,160,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42126 : Route 9 := (fun mask => (mask,id))

def c42126 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42126 : Upper (D 6) (R 6) [10,160,96,17] 13 := by
  apply FastRouting.sound _ _ [10,160,96,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42126 c42126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34138
  · exact u34139
  · exact u34140
  · exact u34141
  · exact u34142
  · exact u34143
  · exact u34144
  · exact u34145
  · exact u34146
  · exact u34147

def b42127 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 26 341 357 325 453 325), lower := (rows 11 162 100 26 16 32 64 128 256), losses := [] }

theorem u42127 : Upper (D 6) (R 6) [10,160,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42128 : Route 9 := (fun mask => (mask,id))

def c42128 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42128 : Upper (D 6) (R 6) [10,160,96,20] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42128 c42128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34148
  · exact u34149
  · exact u34150
  · exact u34151
  · exact u34152
  · exact u34153
  · exact u34154
  · exact u34155
  · exact u34156
  · exact u34157

def r42129 : Route 9 := (fun mask => (mask,id))

def c42129 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42129 : Upper (D 6) (R 6) [10,160,96,65] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42129 c42129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34158
  · exact u34159
  · exact u34160
  · exact u34161
  · exact u34162
  · exact u34163

def b42130 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 74 277 309 341 405 277), lower := (rows 11 162 100 74 16 32 64 128 256), losses := [] }

theorem u42130 : Upper (D 6) (R 6) [10,160,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42131 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 100 76 279 311 343 407 279), lower := (rows 11 162 100 76 16 32 64 128 256), losses := [] }

theorem u42131 : Upper (D 6) (R 6) [10,160,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42132 : Route 9 := (fun mask => (mask,id))

def c42132 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42132 : Upper (D 6) (R 6) [10,160,96,80] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42132 c42132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34164
  · exact u34165
  · exact u34166
  · exact u34167
  · exact u34168
  · exact u34169

def r42133 : Route 9 := (fun mask => (mask,id))

def c42133 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42133 : Upper (D 6) (R 6) [10,160,96,257] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42133 c42133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34170
  · exact u34171
  · exact u34172
  · exact u34173
  · exact u34174
  · exact u34175

def b42134 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 100 266 85 117 85 213 341), lower := (rows 11 162 100 266 16 32 64 128 256), losses := [] }

theorem u42134 : Upper (D 6) (R 6) [10,160,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42135 : Route 9 := (fun mask => (mask,id))

def c42135 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42135 : Upper (D 6) (R 6) [10,160,96,260] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42135 c42135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34176
  · exact u34177
  · exact u34178
  · exact u34179
  · exact u34180
  · exact u34181

def r42136 : Route 9 := (fun mask => (mask,id))

def c42136 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42136 : Upper (D 6) (R 6) [10,160,96,272] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42136 c42136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34182
  · exact u34183
  · exact u34184
  · exact u34185
  · exact u34186
  · exact u34187

def r42137 : Route 9 := (fun mask => (mask,id))

def c42137 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42137 : Upper (D 6) (R 6) [10,160,96,320] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320] 13 (by decide) (choices 2) [3,5,6] r42137 c42137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34188
  · exact u34189
  · exact u34190

def b42138 : PairBound 9 := { available := 116, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 11 116 116 116 244 372), lower := (rows 11 162 261 11 16 32 64 128 256), losses := [] }

theorem u42138 : Upper (D 6) (R 6) [10,160,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42139 : PairBound 9 := { available := 118, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 162 261 13 118 118 118 246 374), lower := (rows 11 162 261 13 16 32 64 128 256), losses := [] }

theorem u42139 : Upper (D 6) (R 6) [10,160,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42140 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 14 117 117 117 245 373), lower := (rows 11 162 261 14 16 32 64 128 256), losses := [] }

theorem u42140 : Upper (D 6) (R 6) [10,160,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42141 : Route 9 := (fun mask => (mask,id))

def c42141 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42141 : Upper (D 6) (R 6) [10,160,257,17] 13 := by
  apply FastRouting.sound _ _ [10,160,257,17] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42141 c42141
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34191
  · exact u34192
  · exact u34193
  · exact u34194
  · exact u34195
  · exact u34196

def b42142 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 26 117 101 101 229 357), lower := (rows 11 162 261 26 16 32 64 128 256), losses := [] }

theorem u42142 : Upper (D 6) (R 6) [10,160,257,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42143 : Route 9 := (fun mask => (mask,id))

def c42143 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42143 : Upper (D 6) (R 6) [10,160,257,20] 13 := by
  apply FastRouting.sound _ _ [10,160,257,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42143 c42143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34197
  · exact u34198
  · exact u34199
  · exact u34200
  · exact u34201
  · exact u34202
  · exact u34203
  · exact u34204
  · exact u34205
  · exact u34206

def b42144 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 261 41 86 118 86 214 342), lower := (rows 11 162 261 41 16 32 64 128 256), losses := [] }

theorem u42144 : Upper (D 6) (R 6) [10,160,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42145 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 261 42 85 117 85 213 341), lower := (rows 11 162 261 42 16 32 64 128 256), losses := [] }

theorem u42145 : Upper (D 6) (R 6) [10,160,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42146 : Route 9 := (fun mask => (mask,id))

def c42146 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42146 : Upper (D 6) (R 6) [10,160,257,36] 13 := by
  apply FastRouting.sound _ _ [10,160,257,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42146 c42146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34207
  · exact u34208
  · exact u34209
  · exact u34210
  · exact u34211
  · exact u34212

def r42147 : Route 9 := (fun mask => (mask,id))

def c42147 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42147 : Upper (D 6) (R 6) [10,160,257,48] 13 := by
  apply FastRouting.sound _ _ [10,160,257,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42147 c42147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34213
  · exact u34214
  · exact u34215
  · exact u34216
  · exact u34217
  · exact u34218

def r42148 : Route 9 := (fun mask => (mask,id))

def c42148 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42148 : Upper (D 6) (R 6) [10,160,257,65] 13 := by
  apply FastRouting.sound _ _ [10,160,257,65] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42148 c42148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34219
  · exact u34220
  · exact u34221
  · exact u34222
  · exact u34223
  · exact u34224

def b42149 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 261 74 117 117 117 245 373), lower := (rows 11 162 261 74 16 32 64 128 256), losses := [] }

theorem u42149 : Upper (D 6) (R 6) [10,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42150 : Route 9 := (fun mask => (mask,id))

def c42150 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42150 : Upper (D 6) (R 6) [10,160,257,68] 13 := by
  apply FastRouting.sound _ _ [10,160,257,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42150 c42150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34225
  · exact u34226
  · exact u34227
  · exact u34228
  · exact u34229
  · exact u34230
  · exact u34231
  · exact u34232
  · exact u34233
  · exact u34234

def r42151 : Route 9 := (fun mask => (mask,id))

def c42151 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42151 : Upper (D 6) (R 6) [10,160,257,80] 13 := by
  apply FastRouting.sound _ _ [10,160,257,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42151 c42151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34235
  · exact u34236
  · exact u34237
  · exact u34238
  · exact u34239
  · exact u34240
  · exact u34241
  · exact u34242
  · exact u34243
  · exact u34244

def r42152 : Route 9 := (fun mask => (mask,id))

def c42152 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42152 : Upper (D 6) (R 6) [10,160,257,96] 13 := by
  apply FastRouting.sound _ _ [10,160,257,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42152 c42152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34245
  · exact u34246
  · exact u34247
  · exact u34248
  · exact u34249
  · exact u34250

def b42153 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 262 13 117 117 117 245 373), lower := (rows 11 162 262 13 16 32 64 128 256), losses := [] }

theorem u42153 : Upper (D 6) (R 6) [10,160,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42154 : Route 9 := (fun mask => (mask,id))

def c42154 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42154 : Upper (D 6) (R 6) [10,160,258,17] 13 := by
  apply FastRouting.sound _ _ [10,160,258,17] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42154 c42154
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34251
  · exact u34252
  · exact u34253
  · exact u34254
  · exact u34255
  · exact u34256

def r42155 : Route 9 := (fun mask => (mask,id))

def c42155 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42155 : Upper (D 6) (R 6) [10,160,258,20] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42155 c42155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34257
  · exact u34258
  · exact u34259
  · exact u34260
  · exact u34261
  · exact u34262

def b42156 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 262 41 85 117 85 213 341), lower := (rows 11 162 262 41 16 32 64 128 256), losses := [] }

theorem u42156 : Upper (D 6) (R 6) [10,160,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42157 : Route 9 := (fun mask => (mask,id))

def c42157 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42157 : Upper (D 6) (R 6) [10,160,258,36] 13 := by
  apply FastRouting.sound _ _ [10,160,258,36] 13 (by decide) (choices 2) [5,65,68] r42157 c42157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34263
  · exact u34264
  · exact u34265

def r42158 : Route 9 := (fun mask => (mask,id))

def c42158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42158 : Upper (D 6) (R 6) [10,160,258,48] 13 := by
  apply FastRouting.sound _ _ [10,160,258,48] 13 (by decide) (choices 2) [5,65,68] r42158 c42158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34266
  · exact u34267
  · exact u34268

def r42159 : Route 9 := (fun mask => (mask,id))

def c42159 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42159 : Upper (D 6) (R 6) [10,160,258,65] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42159 c42159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34269
  · exact u34270
  · exact u34271
  · exact u34272
  · exact u34273
  · exact u34274

def r42160 : Route 9 := (fun mask => (mask,id))

def c42160 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42160 : Upper (D 6) (R 6) [10,160,258,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42160 c42160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34275
  · exact u34276
  · exact u34277
  · exact u34278
  · exact u34279
  · exact u34280

def r42161 : Route 9 := (fun mask => (mask,id))

def c42161 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42161 : Upper (D 6) (R 6) [10,160,258,80] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42161 c42161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34281
  · exact u34282
  · exact u34283
  · exact u34284
  · exact u34285
  · exact u34286

def r42162 : Route 9 := (fun mask => (mask,id))

def c42162 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42162 : Upper (D 6) (R 6) [10,160,258,96] 13 := by
  apply FastRouting.sound _ _ [10,160,258,96] 13 (by decide) (choices 2) [5,65,68] r42162 c42162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34287
  · exact u34288
  · exact u34289

def b42163 : PairBound 9 := { available := 101, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 276 11 117 101 101 229 357), lower := (rows 11 162 276 11 16 32 64 128 256), losses := [] }

theorem u42163 : Upper (D 6) (R 6) [10,160,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42164 : Route 9 := (fun mask => (mask,id))

def c42164 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42164 : Upper (D 6) (R 6) [10,160,272,5] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42164 c42164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34290
  · exact u34291
  · exact u34292
  · exact u34293
  · exact u34294
  · exact u34295
  · exact u34296
  · exact u34297
  · exact u34298
  · exact u34299

def b42165 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 276 14 117 101 101 229 357), lower := (rows 11 162 276 14 16 32 64 128 256), losses := [] }

theorem u42165 : Upper (D 6) (R 6) [10,160,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42166 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 276 41 87 103 71 199 327), lower := (rows 11 162 276 41 16 32 64 128 256), losses := [] }

theorem u42166 : Upper (D 6) (R 6) [10,160,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42167 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 276 42 85 101 69 197 325), lower := (rows 11 162 276 42 16 32 64 128 256), losses := [] }

theorem u42167 : Upper (D 6) (R 6) [10,160,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42168 : Route 9 := (fun mask => (mask,id))

def c42168 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42168 : Upper (D 6) (R 6) [10,160,272,36] 13 := by
  apply FastRouting.sound _ _ [10,160,272,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42168 c42168
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

def r42169 : Route 9 := (fun mask => (mask,id))

def c42169 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42169 : Upper (D 6) (R 6) [10,160,272,65] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42169 c42169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34306
  · exact u34307
  · exact u34308
  · exact u34309
  · exact u34310
  · exact u34311
  · exact u34312
  · exact u34313
  · exact u34314
  · exact u34315

def b42170 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 276 74 117 101 101 229 357), lower := (rows 11 162 276 74 16 32 64 128 256), losses := [] }

theorem u42170 : Upper (D 6) (R 6) [10,160,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42171 : Route 9 := (fun mask => (mask,id))

def c42171 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42171 : Upper (D 6) (R 6) [10,160,272,68] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42171 c42171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34316
  · exact u34317
  · exact u34318
  · exact u34319
  · exact u34320
  · exact u34321
  · exact u34322
  · exact u34323
  · exact u34324
  · exact u34325

def r42172 : Route 9 := (fun mask => (mask,id))

def c42172 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42172 : Upper (D 6) (R 6) [10,160,272,96] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42172 c42172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34326
  · exact u34327
  · exact u34328
  · exact u34329
  · exact u34330
  · exact u34331

def b42173 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 292 11 85 117 85 213 341), lower := (rows 11 162 292 11 16 32 64 128 256), losses := [] }

theorem u42173 : Upper (D 6) (R 6) [10,160,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42174 : Route 9 := (fun mask => (mask,id))

def c42174 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42174 : Upper (D 6) (R 6) [10,160,288,5] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42174 c42174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34332
  · exact u34333
  · exact u34334
  · exact u34335
  · exact u34336
  · exact u34337

def b42175 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 292 14 85 117 85 213 341), lower := (rows 11 162 292 14 16 32 64 128 256), losses := [] }

theorem u42175 : Upper (D 6) (R 6) [10,160,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42176 : Route 9 := (fun mask => (mask,id))

def c42176 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42176 : Upper (D 6) (R 6) [10,160,288,17] 13 := by
  apply FastRouting.sound _ _ [10,160,288,17] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42176 c42176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34338
  · exact u34339
  · exact u34340
  · exact u34341
  · exact u34342
  · exact u34343

def b42177 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 292 26 85 101 69 197 325), lower := (rows 11 162 292 26 16 32 64 128 256), losses := [] }

theorem u42177 : Upper (D 6) (R 6) [10,160,288,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42178 : Route 9 := (fun mask => (mask,id))

def c42178 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42178 : Upper (D 6) (R 6) [10,160,288,20] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42178 c42178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34344
  · exact u34345
  · exact u34346
  · exact u34347
  · exact u34348
  · exact u34349

def r42179 : Route 9 := (fun mask => (mask,id))

def c42179 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42179 : Upper (D 6) (R 6) [10,160,288,65] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42179 c42179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34350
  · exact u34351
  · exact u34352
  · exact u34353
  · exact u34354
  · exact u34355

#print axioms u42179
end Delivery.IrregularNine14.P06
