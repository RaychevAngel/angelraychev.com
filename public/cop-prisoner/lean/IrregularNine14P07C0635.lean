import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0419
import IrregularNine14P07C0420
import IrregularNine14P07C0421

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38100 : Route 9 := (fun mask => (mask,id))

def c38100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38100 : Upper (D 7) (R 7) [36,192,65,18,160] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,160] 13 (by decide) (choices 1) [1,2,8,256] r38100 c38100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25156
  · exact u25157
  · exact u25158
  · exact u25159

def r38101 : Route 9 := (fun mask => (mask,id))

def c38101 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38101 : Upper (D 7) (R 7) [36,192,65,18,257] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,257] 13 (by decide) (choices 1) [2,8,128] r38101 c38101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25160
  · exact u25161
  · exact u25162

def b38102 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 69 26 274 169 233 169 425), lower := (rows 37 194 69 26 274 32 64 128 256), losses := [] }

theorem u38102 : Upper (D 7) (R 7) [36,192,65,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38103 : Route 9 := (fun mask => (mask,id))

def c38103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38103 : Upper (D 7) (R 7) [36,192,65,18,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,264] 13 (by decide) (choices 1) [1,2,128] r38103 c38103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25163
  · exact u25164
  · exact u25165

def r38104 : Route 9 := (fun mask => (mask,id))

def c38104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38104 : Upper (D 7) (R 7) [36,192,65,18,288] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,288] 13 (by decide) (choices 1) [1,2,8,128] r38104 c38104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25166
  · exact u25167
  · exact u25168
  · exact u25169

def r38105 : Route 9 := (fun mask => (mask,id))

def c38105 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38105 : Upper (D 7) (R 7) [36,192,65,18,384] 13 := by
  apply FastRouting.sound _ _ [36,192,65,18,384] 13 (by decide) (choices 1) [1,2,8] r38105 c38105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25170
  · exact u25171
  · exact u25172

def b38106 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 69 41 152 306 338 402 274), lower := (rows 37 194 69 41 152 32 64 128 256), losses := [] }

theorem u38106 : Upper (D 7) (R 7) [36,192,65,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38107 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 69 41 274 186 218 154 410), lower := (rows 37 194 69 41 274 32 64 128 256), losses := [] }

theorem u38107 : Upper (D 7) (R 7) [36,192,65,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38108 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 69 41 280 178 210 146 402), lower := (rows 37 194 69 41 280 32 64 128 256), losses := [] }

theorem u38108 : Upper (D 7) (R 7) [36,192,65,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38109 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 194 69 41 400 58 90 154 282), lower := (rows 37 194 69 41 400 32 64 128 256), losses := [] }

theorem u38109 : Upper (D 7) (R 7) [36,192,65,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38110 : Route 9 := (fun mask => (mask,id))

def c38110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38110 : Upper (D 7) (R 7) [36,192,65,34,129] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,129] 13 (by decide) (choices 1) [2,8,16,256] r38110 c38110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25173
  · exact u25174
  · exact u25175
  · exact u25176

def b38111 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 69 42 146 313 345 409 281), lower := (rows 37 194 69 42 146 32 64 128 256), losses := [] }

theorem u38111 : Upper (D 7) (R 7) [36,192,65,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38112 : Route 9 := (fun mask => (mask,id))

def c38112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38112 : Upper (D 7) (R 7) [36,192,65,34,136] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,136] 13 (by decide) (choices 1) [1,2,16,256] r38112 c38112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25177
  · exact u25178
  · exact u25179
  · exact u25180

def r38113 : Route 9 := (fun mask => (mask,id))

def c38113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38113 : Upper (D 7) (R 7) [36,192,65,34,257] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,257] 13 (by decide) (choices 1) [2,8,16,128] r38113 c38113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25181
  · exact u25182
  · exact u25183
  · exact u25184

def r38114 : Route 9 := (fun mask => (mask,id))

def c38114 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38114 : Upper (D 7) (R 7) [36,192,65,34,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,258] 13 (by decide) (choices 1) [1,8,16,128] r38114 c38114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25185
  · exact u25186
  · exact u25187
  · exact u25188

def r38115 : Route 9 := (fun mask => (mask,id))

def c38115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38115 : Upper (D 7) (R 7) [36,192,65,34,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,264] 13 (by decide) (choices 1) [1,2,16,128] r38115 c38115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25189
  · exact u25190
  · exact u25191
  · exact u25192

def r38116 : Route 9 := (fun mask => (mask,id))

def c38116 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38116 : Upper (D 7) (R 7) [36,192,65,34,384] 13 := by
  apply FastRouting.sound _ _ [36,192,65,34,384] 13 (by decide) (choices 1) [1,2,8,16] r38116 c38116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25193
  · exact u25194
  · exact u25195
  · exact u25196

def r38117 : Route 9 := (fun mask => (mask,id))

def c38117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38117 : Upper (D 7) (R 7) [36,192,65,48,129] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,129] 13 (by decide) (choices 1) [2,8,256] r38117 c38117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25197
  · exact u25198
  · exact u25199

def b38118 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 69 56 146 299 331 395 267), lower := (rows 37 194 69 56 146 32 64 128 256), losses := [] }

theorem u38118 : Upper (D 7) (R 7) [36,192,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38119 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(2,7)], upper := (rows 37 194 69 56 152 291 323 387 259), lower := (rows 37 194 69 56 152 32 64 128 256), losses := [] }

theorem u38119 : Upper (D 7) (R 7) [36,192,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38120 : Route 9 := (fun mask => (mask,id))

def c38120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38120 : Upper (D 7) (R 7) [36,192,65,48,257] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,257] 13 (by decide) (choices 1) [2,8,128] r38120 c38120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25200
  · exact u25201
  · exact u25202

def r38121 : Route 9 := (fun mask => (mask,id))

def c38121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38121 : Upper (D 7) (R 7) [36,192,65,48,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,258] 13 (by decide) (choices 1) [1,2,8,128] r38121 c38121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25203
  · exact u25204
  · exact u25205
  · exact u25206

def r38122 : Route 9 := (fun mask => (mask,id))

def c38122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38122 : Upper (D 7) (R 7) [36,192,65,48,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,264] 13 (by decide) (choices 1) [1,2,128] r38122 c38122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25207
  · exact u25208
  · exact u25209

def r38123 : Route 9 := (fun mask => (mask,id))

def c38123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38123 : Upper (D 7) (R 7) [36,192,65,48,384] 13 := by
  apply FastRouting.sound _ _ [36,192,65,48,384] 13 (by decide) (choices 1) [1,2,8] r38123 c38123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25210
  · exact u25211
  · exact u25212

def r38124 : Route 9 := (fun mask => (mask,id))

def c38124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38124 : Upper (D 7) (R 7) [36,192,65,129,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129,258] 13 (by decide) (choices 1) [2,8,16] r38124 c38124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25213
  · exact u25214
  · exact u25215

def r38125 : Route 9 := (fun mask => (mask,id))

def c38125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38125 : Upper (D 7) (R 7) [36,192,65,129,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129,264] 13 (by decide) (choices 1) [2,16] r38125 c38125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25216
  · exact u25217

def r38126 : Route 9 := (fun mask => (mask,id))

def c38126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38126 : Upper (D 7) (R 7) [36,192,65,129,288] 13 := by
  apply FastRouting.sound _ _ [36,192,65,129,288] 13 (by decide) (choices 1) [2,8,16] r38126 c38126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25218
  · exact u25219
  · exact u25220

def b38127 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 69 138 273 58 122 186 314), lower := (rows 37 194 69 138 273 32 64 128 256), losses := [] }

theorem u38127 : Upper (D 7) (R 7) [36,192,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38128 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 69 138 274 57 121 185 313), lower := (rows 37 194 69 138 274 32 64 128 256), losses := [] }

theorem u38128 : Upper (D 7) (R 7) [36,192,65,130,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38129 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 69 138 280 51 115 179 307), lower := (rows 37 194 69 138 280 32 64 128 256), losses := [] }

theorem u38129 : Upper (D 7) (R 7) [36,192,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38130 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 37 194 69 138 304 59 91 155 283), lower := (rows 37 194 69 138 304 32 64 128 256), losses := [] }

theorem u38130 : Upper (D 7) (R 7) [36,192,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38131 : Route 9 := (fun mask => (mask,id))

def c38131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38131 : Upper (D 7) (R 7) [36,192,65,144,257] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,257] 13 (by decide) (choices 1) [2,8] r38131 c38131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25221
  · exact u25222

def r38132 : Route 9 := (fun mask => (mask,id))

def c38132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38132 : Upper (D 7) (R 7) [36,192,65,144,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,258] 13 (by decide) (choices 1) [1,2,8] r38132 c38132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25223
  · exact u25224
  · exact u25225

def r38133 : Route 9 := (fun mask => (mask,id))

def c38133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38133 : Upper (D 7) (R 7) [36,192,65,144,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,264] 13 (by decide) (choices 1) [1,2] r38133 c38133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25226
  · exact u25227

def r38134 : Route 9 := (fun mask => (mask,id))

def c38134 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38134 : Upper (D 7) (R 7) [36,192,65,144,288] 13 := by
  apply FastRouting.sound _ _ [36,192,65,144,288] 13 (by decide) (choices 1) [1,2,8] r38134 c38134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25228
  · exact u25229
  · exact u25230

def r38135 : Route 9 := (fun mask => (mask,id))

def c38135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38135 : Upper (D 7) (R 7) [36,192,65,160,257] 13 := by
  apply FastRouting.sound _ _ [36,192,65,160,257] 13 (by decide) (choices 1) [2,8,16] r38135 c38135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25231
  · exact u25232
  · exact u25233

def r38136 : Route 9 := (fun mask => (mask,id))

def c38136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38136 : Upper (D 7) (R 7) [36,192,65,160,258] 13 := by
  apply FastRouting.sound _ _ [36,192,65,160,258] 13 (by decide) (choices 1) [1,2,8,16] r38136 c38136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25234
  · exact u25235
  · exact u25236
  · exact u25237

def r38137 : Route 9 := (fun mask => (mask,id))

def c38137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38137 : Upper (D 7) (R 7) [36,192,65,160,264] 13 := by
  apply FastRouting.sound _ _ [36,192,65,160,264] 13 (by decide) (choices 1) [1,2,16] r38137 c38137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25238
  · exact u25239
  · exact u25240

def b38138 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 16, targets := 160 },{ cop := 4, region := 8, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 37 194 76 11 19 432 496 432 432), lower := (rows 37 194 76 11 19 32 64 128 256), losses := [] }

theorem u38138 : Upper (D 7) (R 7) [36,192,72,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38139 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 11 49 434 466 402 402), lower := (rows 37 194 76 11 49 32 64 128 256), losses := [] }

theorem u38139 : Upper (D 7) (R 7) [36,192,72,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38140 : Route 9 := (fun mask => (mask,id))

def c38140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u38140 : Upper (D 7) (R 7) [36,192,72,3,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,34] 13 (by decide) (choices 1) [1,16,128,256] r38140 c38140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25241
  · exact u25242
  · exact u25243
  · exact u25244

def r38141 : Route 9 := (fun mask => (mask,id))

def c38141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38141 : Upper (D 7) (R 7) [36,192,72,3,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,129] 13 (by decide) (choices 1) [2,16,256] r38141 c38141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25245
  · exact u25246
  · exact u25247

def b38142 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 11 146 305 369 433 305), lower := (rows 37 194 76 11 146 32 64 128 256), losses := [] }

theorem u38142 : Upper (D 7) (R 7) [36,192,72,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38143 : Route 9 := (fun mask => (mask,id))

def c38143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38143 : Upper (D 7) (R 7) [36,192,72,3,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,160] 13 (by decide) (choices 1) [1,2,16,256] r38143 c38143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25248
  · exact u25249
  · exact u25250
  · exact u25251

def r38144 : Route 9 := (fun mask => (mask,id))

def c38144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38144 : Upper (D 7) (R 7) [36,192,72,3,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,257] 13 (by decide) (choices 1) [2,16,128] r38144 c38144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25252
  · exact u25253
  · exact u25254

def r38145 : Route 9 := (fun mask => (mask,id))

def c38145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38145 : Upper (D 7) (R 7) [36,192,72,3,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,258] 13 (by decide) (choices 1) [1,16,128] r38145 c38145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25255
  · exact u25256
  · exact u25257

def r38146 : Route 9 := (fun mask => (mask,id))

def c38146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38146 : Upper (D 7) (R 7) [36,192,72,3,288] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,288] 13 (by decide) (choices 1) [1,2,16,128] r38146 c38146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25258
  · exact u25259
  · exact u25260
  · exact u25261

def r38147 : Route 9 := (fun mask => (mask,id))

def c38147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38147 : Upper (D 7) (R 7) [36,192,72,3,384] 13 := by
  apply FastRouting.sound _ _ [36,192,72,3,384] 13 (by decide) (choices 1) [1,2,16] r38147 c38147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25262
  · exact u25263
  · exact u25264

def b38148 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 76 25 19 418 482 418 418), lower := (rows 37 194 76 25 19 32 64 128 256), losses := [] }

theorem u38148 : Upper (D 7) (R 7) [36,192,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38149 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 194 76 25 49 418 450 386 386), lower := (rows 37 194 76 25 49 32 64 128 256), losses := [] }

theorem u38149 : Upper (D 7) (R 7) [36,192,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38150 : Route 9 := (fun mask => (mask,id))

def c38150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u38150 : Upper (D 7) (R 7) [36,192,72,17,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,34] 13 (by decide) (choices 1) [1,2,128,256] r38150 c38150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25265
  · exact u25266
  · exact u25267
  · exact u25268

def b38151 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 25 145 290 354 418 290), lower := (rows 37 194 76 25 145 32 64 128 256), losses := [] }

theorem u38151 : Upper (D 7) (R 7) [36,192,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38152 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 25 146 291 355 419 291), lower := (rows 37 194 76 25 146 32 64 128 256), losses := [] }

theorem u38152 : Upper (D 7) (R 7) [36,192,72,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38153 : Route 9 := (fun mask => (mask,id))

def c38153 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38153 : Upper (D 7) (R 7) [36,192,72,17,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,160] 13 (by decide) (choices 1) [1,2,256] r38153 c38153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25269
  · exact u25270
  · exact u25271

def b38154 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 25 273 162 226 162 418), lower := (rows 37 194 76 25 273 32 64 128 256), losses := [] }

theorem u38154 : Upper (D 7) (R 7) [36,192,72,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38155 : Route 9 := (fun mask => (mask,id))

def c38155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38155 : Upper (D 7) (R 7) [36,192,72,17,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,258] 13 (by decide) (choices 1) [1,2,128] r38155 c38155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25272
  · exact u25273
  · exact u25274

def r38156 : Route 9 := (fun mask => (mask,id))

def c38156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38156 : Upper (D 7) (R 7) [36,192,72,17,288] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,288] 13 (by decide) (choices 1) [1,2,128] r38156 c38156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25275
  · exact u25276
  · exact u25277

def r38157 : Route 9 := (fun mask => (mask,id))

def c38157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38157 : Upper (D 7) (R 7) [36,192,72,17,384] 13 := by
  apply FastRouting.sound _ _ [36,192,72,17,384] 13 (by decide) (choices 1) [1,2] r38157 c38157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25278
  · exact u25279

def b38158 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 161 },{ cop := 3, region := 485, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 37 194 76 26 19 417 481 417 417), lower := (rows 37 194 76 26 19 32 64 128 256), losses := [] }

theorem u38158 : Upper (D 7) (R 7) [36,192,72,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38159 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 26 49 419 451 387 387), lower := (rows 37 194 76 26 49 32 64 128 256), losses := [] }

theorem u38159 : Upper (D 7) (R 7) [36,192,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38159
end Delivery.IrregularNine14.P07
