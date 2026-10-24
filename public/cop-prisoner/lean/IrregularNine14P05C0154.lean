import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0118
import IrregularNine14P05C0119
import IrregularNine14P05C0120
import IrregularNine14P05C0121
import IrregularNine14P05C0122
import IrregularNine14P05C0123
import IrregularNine14P05C0124

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9240 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 44 76 411 427 459 395 395), lower := (rows 19 38 44 76 16 32 64 128 256), losses := [] }

theorem u9240 : Upper (D 5) (R 5) [18,36,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9241 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 44 200 287 303 335 399 271), lower := (rows 19 38 44 200 16 32 64 128 256), losses := [] }

theorem u9241 : Upper (D 5) (R 5) [18,36,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9242 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9242 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9242 : Upper (D 5) (R 5) [18,36,65,33] 13 := by
  apply FastRouting.sound _ _ [18,36,65,33] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r9242 c9242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7092
  · exact u7093
  · exact u7094
  · exact u7095
  · exact u7096
  · exact u7097
  · exact u7098

def b9243 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 38 69 42 413 429 461 397 397), lower := (rows 19 38 69 42 16 32 64 128 256), losses := [] }

theorem u9243 : Upper (D 5) (R 5) [18,36,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9244 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 8, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 69 44 411 427 459 395 395), lower := (rows 19 38 69 44 16 32 64 128 256), losses := [] }

theorem u9244 : Upper (D 5) (R 5) [18,36,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9245 : Route 9 := (fun mask => (mask,id))

def c9245 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9245 : Upper (D 5) (R 5) [18,36,65,129] 13 := by
  apply FastRouting.sound _ _ [18,36,65,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9245 c9245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7099
  · exact u7100
  · exact u7101
  · exact u7102
  · exact u7103
  · exact u7104
  · exact u7105
  · exact u7106
  · exact u7107
  · exact u7108

def r9246 : Route 9 := (fun mask => (mask,id))

def c9246 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9246 : Upper (D 5) (R 5) [18,36,65,130] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9246 c9246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7109
  · exact u7110
  · exact u7111
  · exact u7112
  · exact u7113
  · exact u7114
  · exact u7115
  · exact u7116
  · exact u7117
  · exact u7118

def r9247 : Route 9 := (fun mask => (mask,id))

def c9247 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9247 : Upper (D 5) (R 5) [18,36,65,132] 13 := by
  apply FastRouting.sound _ _ [18,36,65,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9247 c9247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7119
  · exact u7120
  · exact u7121
  · exact u7122
  · exact u7123
  · exact u7124
  · exact u7125
  · exact u7126
  · exact u7127
  · exact u7128

def r9248 : Route 9 := (fun mask => (mask,id))

def c9248 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9248 : Upper (D 5) (R 5) [18,36,65,160] 13 := by
  apply FastRouting.sound _ _ [18,36,65,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9248 c9248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7129
  · exact u7130
  · exact u7131
  · exact u7132
  · exact u7133
  · exact u7134
  · exact u7135
  · exact u7136
  · exact u7137
  · exact u7138

def r9249 : Route 9 := (fun mask => (mask,id))

def c9249 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9249 : Upper (D 5) (R 5) [18,36,65,384] 13 := by
  apply FastRouting.sound _ _ [18,36,65,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9249 c9249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7139
  · exact u7140
  · exact u7141
  · exact u7142
  · exact u7143
  · exact u7144
  · exact u7145
  · exact u7146
  · exact u7147
  · exact u7148

def r9250 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9250 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9250 : Upper (D 5) (R 5) [18,36,66,33] 13 := by
  apply FastRouting.sound _ _ [18,36,66,33] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r9250 c9250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7149
  · exact u7150
  · exact u7151
  · exact u7152
  · exact u7153
  · exact u7154
  · exact u7155

def b9251 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 8, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 70 44 409 425 457 393 393), lower := (rows 19 38 70 44 16 32 64 128 256), losses := [] }

theorem u9251 : Upper (D 5) (R 5) [18,36,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9252 : Route 9 := (fun mask => (mask,id))

def c9252 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9252 : Upper (D 5) (R 5) [18,36,66,129] 13 := by
  apply FastRouting.sound _ _ [18,36,66,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9252 c9252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7156
  · exact u7157
  · exact u7158
  · exact u7159
  · exact u7160
  · exact u7161
  · exact u7162
  · exact u7163
  · exact u7164
  · exact u7165

def r9253 : Route 9 := (fun mask => (mask,id))

def c9253 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9253 : Upper (D 5) (R 5) [18,36,66,132] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132] 13 (by decide) (choices 2) [9,33,40,257,264,288] r9253 c9253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7166
  · exact u7167
  · exact u7168
  · exact u7169
  · exact u7170
  · exact u7171

def r9254 : Route 9 := (fun mask => (mask,id))

def c9254 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9254 : Upper (D 5) (R 5) [18,36,66,160] 13 := by
  apply FastRouting.sound _ _ [18,36,66,160] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9254 c9254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7172
  · exact u7173
  · exact u7174
  · exact u7175
  · exact u7176
  · exact u7177

def r9255 : Route 9 := (fun mask => (mask,id))

def c9255 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9255 : Upper (D 5) (R 5) [18,36,66,384] 13 := by
  apply FastRouting.sound _ _ [18,36,66,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9255 c9255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7178
  · exact u7179
  · exact u7180
  · exact u7181
  · exact u7182
  · exact u7183

def r9256 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9256 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9256 : Upper (D 5) (R 5) [18,36,72,33] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r9256 c9256
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7184
  · exact u7185
  · exact u7186
  · exact u7187
  · exact u7188
  · exact u7189
  · exact u7190
  · exact u7191
  · exact u7192
  · exact u7193
  · exact u7194

def b9257 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 38 76 42 413 429 461 397 397), lower := (rows 19 38 76 42 16 32 64 128 256), losses := [] }

theorem u9257 : Upper (D 5) (R 5) [18,36,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9258 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 8, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 76 44 411 427 459 395 395), lower := (rows 19 38 76 44 16 32 64 128 256), losses := [] }

theorem u9258 : Upper (D 5) (R 5) [18,36,72,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9259 : Route 9 := (fun mask => (mask,id))

def c9259 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9259 : Upper (D 5) (R 5) [18,36,72,129] 13 := by
  apply FastRouting.sound _ _ [18,36,72,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9259 c9259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7195
  · exact u7196
  · exact u7197
  · exact u7198
  · exact u7199
  · exact u7200
  · exact u7201
  · exact u7202
  · exact u7203
  · exact u7204
  · exact u7205
  · exact u7206
  · exact u7207
  · exact u7208
  · exact u7209

def r9260 : Route 9 := (fun mask => (mask,id))

def c9260 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9260 : Upper (D 5) (R 5) [18,36,72,130] 13 := by
  apply FastRouting.sound _ _ [18,36,72,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9260 c9260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7210
  · exact u7211
  · exact u7212
  · exact u7213
  · exact u7214
  · exact u7215
  · exact u7216
  · exact u7217
  · exact u7218
  · exact u7219

def r9261 : Route 9 := (fun mask => (mask,id))

def c9261 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9261 : Upper (D 5) (R 5) [18,36,72,132] 13 := by
  apply FastRouting.sound _ _ [18,36,72,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9261 c9261
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7220
  · exact u7221
  · exact u7222
  · exact u7223
  · exact u7224
  · exact u7225
  · exact u7226
  · exact u7227
  · exact u7228
  · exact u7229

def r9262 : Route 9 := (fun mask => (mask,id))

def c9262 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9262 : Upper (D 5) (R 5) [18,36,72,160] 13 := by
  apply FastRouting.sound _ _ [18,36,72,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9262 c9262
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7230
  · exact u7231
  · exact u7232
  · exact u7233
  · exact u7234
  · exact u7235
  · exact u7236
  · exact u7237
  · exact u7238
  · exact u7239

def r9263 : Route 9 := (fun mask => (mask,id))

def c9263 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9263 : Upper (D 5) (R 5) [18,36,72,384] 13 := by
  apply FastRouting.sound _ _ [18,36,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9263 c9263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7240
  · exact u7241
  · exact u7242
  · exact u7243
  · exact u7244
  · exact u7245
  · exact u7246
  · exact u7247
  · exact u7248
  · exact u7249

def b9264 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 100 137 287 303 335 399 271), lower := (rows 19 38 100 137 16 32 64 128 256), losses := [] }

theorem u9264 : Upper (D 5) (R 5) [18,36,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9264
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9265 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 100 140 283 299 331 395 267), lower := (rows 19 38 100 140 16 32 64 128 256), losses := [] }

theorem u9265 : Upper (D 5) (R 5) [18,36,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9265
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9266 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 100 392 31 47 79 143 271), lower := (rows 19 38 100 392 16 32 64 128 256), losses := [] }

theorem u9266 : Upper (D 5) (R 5) [18,36,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9266
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9267 : Route 9 := (fun mask => (mask,id))

def c9267 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9267 : Upper (D 5) (R 5) [18,36,192,33] 13 := by
  apply FastRouting.sound _ _ [18,36,192,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9267 c9267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7250
  · exact u7251
  · exact u7252
  · exact u7253
  · exact u7254
  · exact u7255
  · exact u7256
  · exact u7257
  · exact u7258
  · exact u7259

def b9268 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 19 38 196 42 285 301 333 397 269), lower := (rows 19 38 196 42 16 32 64 128 256), losses := [] }

theorem u9268 : Upper (D 5) (R 5) [18,36,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9268
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9269 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 8, targets := 1 },{ cop := 1, region := 8, targets := 2 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 196 44 283 299 331 395 267), lower := (rows 19 38 196 44 16 32 64 128 256), losses := [] }

theorem u9269 : Upper (D 5) (R 5) [18,36,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9269
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9270 : Route 9 := (fun mask => (mask,id))

def c9270 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9270 : Upper (D 5) (R 5) [18,36,192,257] 13 := by
  apply FastRouting.sound _ _ [18,36,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9270 c9270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7260
  · exact u7261
  · exact u7262
  · exact u7263
  · exact u7264
  · exact u7265
  · exact u7266
  · exact u7267
  · exact u7268
  · exact u7269

def r9271 : Route 9 := (fun mask => (mask,id))

def c9271 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9271 : Upper (D 5) (R 5) [18,36,192,258] 13 := by
  apply FastRouting.sound _ _ [18,36,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9271 c9271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7270
  · exact u7271
  · exact u7272
  · exact u7273
  · exact u7274
  · exact u7275

def r9272 : Route 9 := (fun mask => (mask,id))

def c9272 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9272 : Upper (D 5) (R 5) [18,36,192,260] 13 := by
  apply FastRouting.sound _ _ [18,36,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9272 c9272
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7276
  · exact u7277
  · exact u7278
  · exact u7279
  · exact u7280
  · exact u7281

def r9273 : Route 9 := (fun mask => (mask,id))

def c9273 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9273 : Upper (D 5) (R 5) [18,36,192,288] 13 := by
  apply FastRouting.sound _ _ [18,36,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9273 c9273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7282
  · exact u7283
  · exact u7284
  · exact u7285
  · exact u7286
  · exact u7287

def r9274 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9274 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9274 : Upper (D 5) (R 5) [18,65,33,34] 13 := by
  apply FastRouting.sound _ _ [18,65,33,34] 13 (by decide) (choices 2) [12,132,136,384] r9274 c9274
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7288
  · exact u7289
  · exact u7290
  · exact u7291

def b9275 : PairBound 9 := { available := 398, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 37 44 414 430 462 398 398), lower := (rows 19 67 37 44 16 32 64 128 256), losses := [] }

theorem u9275 : Upper (D 5) (R 5) [18,65,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9275
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9276 : Route 9 := (fun mask => (mask,id))

def c9276 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9276 : Upper (D 5) (R 5) [18,65,33,130] 13 := by
  apply FastRouting.sound _ _ [18,65,33,130] 13 (by decide) (choices 2) [12,36,40,260,264,288] r9276 c9276
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7292
  · exact u7293
  · exact u7294
  · exact u7295
  · exact u7296
  · exact u7297

def r9277 : Route 9 := (fun mask => (mask,id))

def c9277 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9277 : Upper (D 5) (R 5) [18,65,33,132] 13 := by
  apply FastRouting.sound _ _ [18,65,33,132] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9277 c9277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7298
  · exact u7299
  · exact u7300
  · exact u7301
  · exact u7302
  · exact u7303
  · exact u7304
  · exact u7305
  · exact u7306
  · exact u7307

def r9278 : Route 9 := (fun mask => (mask,id))

def c9278 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9278 : Upper (D 5) (R 5) [18,65,33,160] 13 := by
  apply FastRouting.sound _ _ [18,65,33,160] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9278 c9278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7308
  · exact u7309
  · exact u7310
  · exact u7311
  · exact u7312
  · exact u7313

def r9279 : Route 9 := (fun mask => (mask,id))

def c9279 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9279 : Upper (D 5) (R 5) [18,65,33,384] 13 := by
  apply FastRouting.sound _ _ [18,65,33,384] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9279 c9279
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7314
  · exact u7315
  · exact u7316
  · exact u7317
  · exact u7318
  · exact u7319

def b9280 : PairBound 9 := { available := 397, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 38 44 413 429 461 397 397), lower := (rows 19 67 38 44 16 32 64 128 256), losses := [] }

theorem u9280 : Upper (D 5) (R 5) [18,65,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9280
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9281 : Route 9 := (fun mask => (mask,id))

def c9281 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9281 : Upper (D 5) (R 5) [18,65,34,129] 13 := by
  apply FastRouting.sound _ _ [18,65,34,129] 13 (by decide) (choices 2) [12,36,40,260,264,288] r9281 c9281
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7320
  · exact u7321
  · exact u7322
  · exact u7323
  · exact u7324
  · exact u7325

def r9282 : Route 9 := (fun mask => (mask,id))

def c9282 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9282 : Upper (D 5) (R 5) [18,65,34,132] 13 := by
  apply FastRouting.sound _ _ [18,65,34,132] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9282 c9282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7326
  · exact u7327
  · exact u7328
  · exact u7329
  · exact u7330
  · exact u7331
  · exact u7332
  · exact u7333
  · exact u7334
  · exact u7335

def r9283 : Route 9 := (fun mask => (mask,id))

def c9283 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9283 : Upper (D 5) (R 5) [18,65,34,160] 13 := by
  apply FastRouting.sound _ _ [18,65,34,160] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9283 c9283
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7336
  · exact u7337
  · exact u7338
  · exact u7339
  · exact u7340
  · exact u7341

def r9284 : Route 9 := (fun mask => (mask,id))

def c9284 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9284 : Upper (D 5) (R 5) [18,65,34,384] 13 := by
  apply FastRouting.sound _ _ [18,65,34,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9284 c9284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7342
  · exact u7343
  · exact u7344
  · exact u7345
  · exact u7346
  · exact u7347

def b9285 : PairBound 9 := { available := 399, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 44 415 431 463 399 399), lower := (rows 19 67 44 44 16 32 64 128 256), losses := [] }

theorem u9285 : Upper (D 5) (R 5) [18,65,40,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9285
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9286 : Route 9 := (fun mask => (mask,id))

def c9286 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9286 : Upper (D 5) (R 5) [18,65,40,129] 13 := by
  apply FastRouting.sound _ _ [18,65,40,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9286 c9286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7348
  · exact u7349
  · exact u7350
  · exact u7351
  · exact u7352
  · exact u7353
  · exact u7354
  · exact u7355
  · exact u7356
  · exact u7357

def r9287 : Route 9 := (fun mask => (mask,id))

def c9287 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9287 : Upper (D 5) (R 5) [18,65,40,130] 13 := by
  apply FastRouting.sound _ _ [18,65,40,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9287 c9287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7358
  · exact u7359
  · exact u7360
  · exact u7361
  · exact u7362
  · exact u7363
  · exact u7364
  · exact u7365
  · exact u7366
  · exact u7367

def r9288 : Route 9 := (fun mask => (mask,id))

def c9288 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9288 : Upper (D 5) (R 5) [18,65,40,132] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9288 c9288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7368
  · exact u7369
  · exact u7370
  · exact u7371
  · exact u7372
  · exact u7373
  · exact u7374
  · exact u7375
  · exact u7376
  · exact u7377
  · exact u7378
  · exact u7379
  · exact u7380
  · exact u7381
  · exact u7382

def b9289 : PairBound 9 := { available := 271, camps := [{ cop := 2, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 67 44 168 287 303 335 399 271), lower := (rows 19 67 44 168 16 32 64 128 256), losses := [] }

theorem u9289 : Upper (D 5) (R 5) [18,65,40,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9289
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9290 : Route 9 := (fun mask => (mask,id))

def c9290 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9290 : Upper (D 5) (R 5) [18,65,40,384] 13 := by
  apply FastRouting.sound _ _ [18,65,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9290 c9290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7383
  · exact u7384
  · exact u7385
  · exact u7386
  · exact u7387
  · exact u7388
  · exact u7389
  · exact u7390
  · exact u7391
  · exact u7392

def r9291 : Route 9 := (fun mask => (mask,id))

def c9291 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9291 : Upper (D 5) (R 5) [18,65,129,258] 13 := by
  apply FastRouting.sound _ _ [18,65,129,258] 13 (by decide) (choices 2) [12,36,40] r9291 c9291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7393
  · exact u7394
  · exact u7395

def r9292 : Route 9 := (fun mask => (mask,id))

def c9292 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9292 : Upper (D 5) (R 5) [18,65,129,260] 13 := by
  apply FastRouting.sound _ _ [18,65,129,260] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9292 c9292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7396
  · exact u7397
  · exact u7398
  · exact u7399
  · exact u7400
  · exact u7401

def r9293 : Route 9 := (fun mask => (mask,id))

def c9293 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9293 : Upper (D 5) (R 5) [18,65,129,288] 13 := by
  apply FastRouting.sound _ _ [18,65,129,288] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9293 c9293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7402
  · exact u7403
  · exact u7404
  · exact u7405
  · exact u7406
  · exact u7407

def r9294 : Route 9 := (fun mask => (mask,id))

def c9294 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9294 : Upper (D 5) (R 5) [18,65,130,260] 13 := by
  apply FastRouting.sound _ _ [18,65,130,260] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9294 c9294
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7408
  · exact u7409
  · exact u7410
  · exact u7411
  · exact u7412
  · exact u7413

def r9295 : Route 9 := (fun mask => (mask,id))

def c9295 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9295 : Upper (D 5) (R 5) [18,65,130,288] 13 := by
  apply FastRouting.sound _ _ [18,65,130,288] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9295 c9295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7414
  · exact u7415
  · exact u7416
  · exact u7417
  · exact u7418
  · exact u7419

theorem m9296_9 : Upper (D 5) (R 5) [18,65,136,260,9] 13 :=
  permutation_upper _ _ _ [18,65,136,260,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7421

theorem m9296_10 : Upper (D 5) (R 5) [18,65,136,260,10] 13 :=
  permutation_upper _ _ _ [18,65,136,260,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7422

theorem m9296_40 : Upper (D 5) (R 5) [18,65,136,260,40] 13 :=
  permutation_upper _ _ _ [18,65,136,260,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7426

def r9296 : Route 9 := (fun mask => (mask,id))

def c9296 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9296 : Upper (D 5) (R 5) [18,65,136,260] 13 := by
  apply FastRouting.sound _ _ [18,65,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9296 c9296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7420
  · exact u7421
  · exact u7422
  · exact m9296_9
  · exact m9296_10
  · exact u7423
  · exact u7424
  · exact u7425
  · exact u7426
  · exact m9296_40

def r9297 : Route 9 := (fun mask => (mask,id))

def c9297 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9297 : Upper (D 5) (R 5) [18,65,136,288] 13 := by
  apply FastRouting.sound _ _ [18,65,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9297 c9297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7427
  · exact u7428
  · exact u7429
  · exact u7430
  · exact u7431
  · exact u7432
  · exact u7433
  · exact u7434
  · exact u7435
  · exact u7436

theorem m9298_9 : Upper (D 5) (R 5) [18,65,160,288,9] 13 :=
  permutation_upper _ _ _ [18,65,160,288,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7438

theorem m9298_10 : Upper (D 5) (R 5) [18,65,160,288,10] 13 :=
  permutation_upper _ _ _ [18,65,160,288,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7439

def r9298 : Route 9 := (fun mask => (mask,id))

def c9298 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9298 : Upper (D 5) (R 5) [18,65,160,288] 13 := by
  apply FastRouting.sound _ _ [18,65,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9298 c9298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7437
  · exact u7438
  · exact u7439
  · exact m9298_9
  · exact m9298_10
  · exact u7440

def b9299 : PairBound 9 := { available := 398, camps := [{ cop := 2, region := 8, targets := 2 },{ cop := 2, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 37 41 414 430 462 398 398), lower := (rows 19 70 37 41 16 32 64 128 256), losses := [] }

theorem u9299 : Upper (D 5) (R 5) [18,68,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9299
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u9299
end Delivery.IrregularNine14.P05
