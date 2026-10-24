import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0085
import IrregularNine14P05C0086
import IrregularNine14P05C0087
import IrregularNine14P05C0088

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8700 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 168 317 301 365 429 301), lower := (rows 7 19 70 168 16 32 64 128 256), losses := [] }

theorem u8700 : Upper (D 5) (R 5) [6,17,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8701 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 392 61 45 109 173 301), lower := (rows 7 19 70 392 16 32 64 128 256), losses := [] }

theorem u8701 : Upper (D 5) (R 5) [6,17,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8701
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8702 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 76 14 441 425 489 425 425), lower := (rows 7 19 76 14 16 32 64 128 256), losses := [] }

theorem u8702 : Upper (D 5) (R 5) [6,17,72,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8703 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8703 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8703 : Upper (D 5) (R 5) [6,17,72,33] 13 := by
  apply FastRouting.sound _ _ [6,17,72,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8703 c8703
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5105
  · exact u5106
  · exact u5107
  · exact u5108
  · exact u5109
  · exact u5110
  · exact u5111
  · exact u5112
  · exact u5113
  · exact u5114
  · exact u5115

def r8704 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8704 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8704 : Upper (D 5) (R 5) [6,17,72,34] 13 := by
  apply FastRouting.sound _ _ [6,17,72,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8704 c8704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5116
  · exact u5117
  · exact u5118
  · exact u5119
  · exact u5120
  · exact u5121
  · exact u5122
  · exact u5123
  · exact u5124
  · exact u5125
  · exact u5126

def r8705 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8705 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8705 : Upper (D 5) (R 5) [6,17,72,36] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8705 c8705
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5127
  · exact u5128
  · exact u5129
  · exact u5130
  · exact u5131
  · exact u5132
  · exact u5133
  · exact u5134
  · exact u5135
  · exact u5136
  · exact u5137

def r8706 : Route 9 := (fun mask => (mask,id))

def c8706 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8706 : Upper (D 5) (R 5) [6,17,72,129] 13 := by
  apply FastRouting.sound _ _ [6,17,72,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8706 c8706
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5138
  · exact u5139
  · exact u5140
  · exact u5141
  · exact u5142
  · exact u5143
  · exact u5144
  · exact u5145
  · exact u5146
  · exact u5147

def r8707 : Route 9 := (fun mask => (mask,id))

def c8707 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8707 : Upper (D 5) (R 5) [6,17,72,130] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8707 c8707
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5148
  · exact u5149
  · exact u5150
  · exact u5151
  · exact u5152
  · exact u5153
  · exact u5154
  · exact u5155
  · exact u5156
  · exact u5157

def r8708 : Route 9 := (fun mask => (mask,id))

def c8708 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8708 : Upper (D 5) (R 5) [6,17,72,132] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8708 c8708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5158
  · exact u5159
  · exact u5160
  · exact u5161
  · exact u5162
  · exact u5163
  · exact u5164
  · exact u5165
  · exact u5166
  · exact u5167

def r8709 : Route 9 := (fun mask => (mask,id))

def c8709 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8709 : Upper (D 5) (R 5) [6,17,72,160] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8709 c8709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5168
  · exact u5169
  · exact u5170
  · exact u5171
  · exact u5172
  · exact u5173
  · exact u5174
  · exact u5175
  · exact u5176
  · exact u5177
  · exact u5178
  · exact u5179
  · exact u5180
  · exact u5181
  · exact u5182

def r8710 : Route 9 := (fun mask => (mask,id))

def c8710 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8710 : Upper (D 5) (R 5) [6,17,72,384] 13 := by
  apply FastRouting.sound _ _ [6,17,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8710 c8710
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5183
  · exact u5184
  · exact u5185
  · exact u5186
  · exact u5187
  · exact u5188
  · exact u5189
  · exact u5190
  · exact u5191
  · exact u5192

def b8711 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 100 14 441 425 489 425 425), lower := (rows 7 19 100 14 16 32 64 128 256), losses := [] }

theorem u8711 : Upper (D 5) (R 5) [6,17,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8711
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8712 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8712 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8712 : Upper (D 5) (R 5) [6,17,96,33] 13 := by
  apply FastRouting.sound _ _ [6,17,96,33] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r8712 c8712
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5193
  · exact u5194
  · exact u5195
  · exact u5196
  · exact u5197
  · exact u5198
  · exact u5199

def r8713 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8713 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8713 : Upper (D 5) (R 5) [6,17,96,34] 13 := by
  apply FastRouting.sound _ _ [6,17,96,34] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r8713 c8713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5200
  · exact u5201
  · exact u5202
  · exact u5203
  · exact u5204
  · exact u5205
  · exact u5206

def b8714 : PairBound 9 := { available := 395, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 100 44 411 427 459 395 395), lower := (rows 7 19 100 44 16 32 64 128 256), losses := [] }

theorem u8714 : Upper (D 5) (R 5) [6,17,96,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8715 : Route 9 := (fun mask => (mask,id))

def c8715 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8715 : Upper (D 5) (R 5) [6,17,96,129] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8715 c8715
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5207
  · exact u5208
  · exact u5209
  · exact u5210
  · exact u5211
  · exact u5212
  · exact u5213
  · exact u5214
  · exact u5215
  · exact u5216

def r8716 : Route 9 := (fun mask => (mask,id))

def c8716 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8716 : Upper (D 5) (R 5) [6,17,96,130] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8716 c8716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5217
  · exact u5218
  · exact u5219
  · exact u5220
  · exact u5221
  · exact u5222
  · exact u5223
  · exact u5224
  · exact u5225
  · exact u5226

def r8717 : Route 9 := (fun mask => (mask,id))

def c8717 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8717 : Upper (D 5) (R 5) [6,17,96,132] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8717 c8717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5227
  · exact u5228
  · exact u5229
  · exact u5230
  · exact u5231
  · exact u5232
  · exact u5233
  · exact u5234
  · exact u5235
  · exact u5236

def r8718 : Route 9 := (fun mask => (mask,id))

def c8718 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8718 : Upper (D 5) (R 5) [6,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,17,96,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8718 c8718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5237
  · exact u5238
  · exact u5239
  · exact u5240
  · exact u5241
  · exact u5242
  · exact u5243
  · exact u5244
  · exact u5245
  · exact u5246

def r8719 : Route 9 := (fun mask => (mask,id))

def c8719 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8719 : Upper (D 5) (R 5) [6,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,17,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8719 c8719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5247
  · exact u5248
  · exact u5249
  · exact u5250
  · exact u5251
  · exact u5252
  · exact u5253
  · exact u5254
  · exact u5255
  · exact u5256

def b8720 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 196 14 313 297 361 425 297), lower := (rows 7 19 196 14 16 32 64 128 256), losses := [] }

theorem u8720 : Upper (D 5) (R 5) [6,17,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8721 : Route 9 := (fun mask => (mask,id))

def c8721 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8721 : Upper (D 5) (R 5) [6,17,192,33] 13 := by
  apply FastRouting.sound _ _ [6,17,192,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8721 c8721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5257
  · exact u5258
  · exact u5259
  · exact u5260
  · exact u5261
  · exact u5262
  · exact u5263
  · exact u5264
  · exact u5265
  · exact u5266

def r8722 : Route 9 := (fun mask => (mask,id))

def c8722 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8722 : Upper (D 5) (R 5) [6,17,192,34] 13 := by
  apply FastRouting.sound _ _ [6,17,192,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8722 c8722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5267
  · exact u5268
  · exact u5269
  · exact u5270
  · exact u5271
  · exact u5272
  · exact u5273
  · exact u5274
  · exact u5275
  · exact u5276

def r8723 : Route 9 := (fun mask => (mask,id))

def c8723 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8723 : Upper (D 5) (R 5) [6,17,192,36] 13 := by
  apply FastRouting.sound _ _ [6,17,192,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8723 c8723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5277
  · exact u5278
  · exact u5279
  · exact u5280
  · exact u5281
  · exact u5282
  · exact u5283
  · exact u5284
  · exact u5285
  · exact u5286

def r8724 : Route 9 := (fun mask => (mask,id))

def c8724 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8724 : Upper (D 5) (R 5) [6,17,192,257] 13 := by
  apply FastRouting.sound _ _ [6,17,192,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r8724 c8724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5287
  · exact u5288
  · exact u5289
  · exact u5290
  · exact u5291
  · exact u5292

def r8725 : Route 9 := (fun mask => (mask,id))

def c8725 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8725 : Upper (D 5) (R 5) [6,17,192,258] 13 := by
  apply FastRouting.sound _ _ [6,17,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r8725 c8725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5293
  · exact u5294
  · exact u5295
  · exact u5296
  · exact u5297
  · exact u5298

def r8726 : Route 9 := (fun mask => (mask,id))

def c8726 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8726 : Upper (D 5) (R 5) [6,17,192,260] 13 := by
  apply FastRouting.sound _ _ [6,17,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r8726 c8726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5299
  · exact u5300
  · exact u5301
  · exact u5302
  · exact u5303
  · exact u5304

def r8727 : Route 9 := (fun mask => (mask,id))

def c8727 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8727 : Upper (D 5) (R 5) [6,17,192,288] 13 := by
  apply FastRouting.sound _ _ [6,17,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8727 c8727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5305
  · exact u5306
  · exact u5307
  · exact u5308
  · exact u5309
  · exact u5310
  · exact u5311
  · exact u5312
  · exact u5313
  · exact u5314

def b8728 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 42 473 489 457 457 457), lower := (rows 7 22 37 42 16 32 64 128 256), losses := [] }

theorem u8728 : Upper (D 5) (R 5) [6,20,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8729 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 73 442 426 490 426 426), lower := (rows 7 22 37 73 16 32 64 128 256), losses := [] }

theorem u8729 : Upper (D 5) (R 5) [6,20,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8729
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8730 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 74 441 425 489 425 425), lower := (rows 7 22 37 74 16 32 64 128 256), losses := [] }

theorem u8730 : Upper (D 5) (R 5) [6,20,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8731 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 104 411 427 459 395 395), lower := (rows 7 22 37 104 16 32 64 128 256), losses := [] }

theorem u8731 : Upper (D 5) (R 5) [6,20,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8732 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 200 315 299 363 427 299), lower := (rows 7 22 37 200 16 32 64 128 256), losses := [] }

theorem u8732 : Upper (D 5) (R 5) [6,20,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8732
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8733 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 38 41 473 489 457 457 457), lower := (rows 7 22 38 41 16 32 64 128 256), losses := [] }

theorem u8733 : Upper (D 5) (R 5) [6,20,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8734 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 38 73 441 425 489 425 425), lower := (rows 7 22 38 73 16 32 64 128 256), losses := [] }

theorem u8734 : Upper (D 5) (R 5) [6,20,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8735 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 38 104 409 425 457 393 393), lower := (rows 7 22 38 104 16 32 64 128 256), losses := [] }

theorem u8735 : Upper (D 5) (R 5) [6,20,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8736 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 38 200 313 297 361 425 297), lower := (rows 7 22 38 200 16 32 64 128 256), losses := [] }

theorem u8736 : Upper (D 5) (R 5) [6,20,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8737 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 44 73 443 427 491 427 427), lower := (rows 7 22 44 73 16 32 64 128 256), losses := [] }

theorem u8737 : Upper (D 5) (R 5) [6,20,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8738 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 44 74 441 425 489 425 425), lower := (rows 7 22 44 74 16 32 64 128 256), losses := [] }

theorem u8738 : Upper (D 5) (R 5) [6,20,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8739 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 44 200 315 299 363 427 299), lower := (rows 7 22 44 200 16 32 64 128 256), losses := [] }

theorem u8739 : Upper (D 5) (R 5) [6,20,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8740 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 41 442 426 490 426 426), lower := (rows 7 22 69 41 16 32 64 128 256), losses := [] }

theorem u8740 : Upper (D 5) (R 5) [6,20,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8741 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 42 441 425 489 425 425), lower := (rows 7 22 69 42 16 32 64 128 256), losses := [] }

theorem u8741 : Upper (D 5) (R 5) [6,20,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8742 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 137 314 298 362 426 298), lower := (rows 7 22 69 137 16 32 64 128 256), losses := [] }

theorem u8742 : Upper (D 5) (R 5) [6,20,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 138 313 297 361 425 297), lower := (rows 7 22 69 138 16 32 64 128 256), losses := [] }

theorem u8743 : Upper (D 5) (R 5) [6,20,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8744 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 168 315 299 363 427 299), lower := (rows 7 22 69 168 16 32 64 128 256), losses := [] }

theorem u8744 : Upper (D 5) (R 5) [6,20,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8745 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 392 59 43 107 171 299), lower := (rows 7 22 69 392 16 32 64 128 256), losses := [] }

theorem u8745 : Upper (D 5) (R 5) [6,20,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 70 41 441 425 489 425 425), lower := (rows 7 22 70 41 16 32 64 128 256), losses := [] }

theorem u8746 : Upper (D 5) (R 5) [6,20,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 70 137 313 297 361 425 297), lower := (rows 7 22 70 137 16 32 64 128 256), losses := [] }

theorem u8747 : Upper (D 5) (R 5) [6,20,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8748 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 70 168 313 297 361 425 297), lower := (rows 7 22 70 168 16 32 64 128 256), losses := [] }

theorem u8748 : Upper (D 5) (R 5) [6,20,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8749 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 70 392 57 41 105 169 297), lower := (rows 7 22 70 392 16 32 64 128 256), losses := [] }

theorem u8749 : Upper (D 5) (R 5) [6,20,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 41 443 427 491 427 427), lower := (rows 7 22 76 41 16 32 64 128 256), losses := [] }

theorem u8750 : Upper (D 5) (R 5) [6,20,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8751 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 42 441 425 489 425 425), lower := (rows 7 22 76 42 16 32 64 128 256), losses := [] }

theorem u8751 : Upper (D 5) (R 5) [6,20,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8752 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 137 315 299 363 427 299), lower := (rows 7 22 76 137 16 32 64 128 256), losses := [] }

theorem u8752 : Upper (D 5) (R 5) [6,20,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 138 313 297 361 425 297), lower := (rows 7 22 76 138 16 32 64 128 256), losses := [] }

theorem u8753 : Upper (D 5) (R 5) [6,20,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 168 315 299 363 427 299), lower := (rows 7 22 76 168 16 32 64 128 256), losses := [] }

theorem u8754 : Upper (D 5) (R 5) [6,20,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 392 59 43 107 171 299), lower := (rows 7 22 76 392 16 32 64 128 256), losses := [] }

theorem u8755 : Upper (D 5) (R 5) [6,20,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 41 411 427 459 395 395), lower := (rows 7 22 100 41 16 32 64 128 256), losses := [] }

theorem u8756 : Upper (D 5) (R 5) [6,20,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8756
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 42 409 425 457 393 393), lower := (rows 7 22 100 42 16 32 64 128 256), losses := [] }

theorem u8757 : Upper (D 5) (R 5) [6,20,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 137 315 299 363 427 299), lower := (rows 7 22 100 137 16 32 64 128 256), losses := [] }

theorem u8758 : Upper (D 5) (R 5) [6,20,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8759 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 138 313 297 361 425 297), lower := (rows 7 22 100 138 16 32 64 128 256), losses := [] }

theorem u8759 : Upper (D 5) (R 5) [6,20,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8759
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8759
end Delivery.IrregularNine14.P05
