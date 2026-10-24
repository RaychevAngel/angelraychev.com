import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0119
import IrregularNine14P01C0120
import IrregularNine14P01C0121
import IrregularNine14P01C0122
import IrregularNine14P01C0123
import IrregularNine14P01C0124

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9120 : Route 9 := (fun mask => (mask,id))

def c9120 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9120 : Upper (D 1) (R 1) [52,272,66] 13 := by
  apply FastRouting.sound _ _ [52,272,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9120 c9120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7189
  · exact u7190
  · exact u7191
  · exact u7192
  · exact u7193
  · exact u7194
  · exact u7195
  · exact u7196
  · exact u7197
  · exact u7198

def r9121 : Route 9 := (fun mask => (mask,id))

def c9121 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9121 : Upper (D 1) (R 1) [52,272,72] 13 := by
  apply FastRouting.sound _ _ [52,272,72] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9121 c9121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b9122 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 100 203 219 235 203 203 459), lower := (rows 53 274 100 8 16 32 64 128 256), losses := [] }

theorem u9122 : Upper (D 1) (R 1) [52,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9123 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9123 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9123 : Upper (D 1) (R 1) [52,272,192] 13 := by
  apply FastRouting.sound _ _ [52,272,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9123 c9123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7209
  · exact u7210
  · exact u7211
  · exact u7212
  · exact u7213
  · exact u7214
  · exact u7215

def r9124 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9124 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9124 : Upper (D 1) (R 1) [52,320,3] 13 := by
  apply FastRouting.sound _ _ [52,320,3] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9124 c9124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7216
  · exact u7217
  · exact u7218
  · exact u7219
  · exact u7220
  · exact u7221
  · exact u7222

def r9125 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9125 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9125 : Upper (D 1) (R 1) [52,320,9] 13 := by
  apply FastRouting.sound _ _ [52,320,9] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9125 c9125
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7223
  · exact u7224
  · exact u7225
  · exact u7226
  · exact u7227
  · exact u7228
  · exact u7229

def r9126 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9126 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9126 : Upper (D 1) (R 1) [52,320,10] 13 := by
  apply FastRouting.sound _ _ [52,320,10] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9126 c9126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u7240

def b9127 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 21 234 250 234 234 234 490), lower := (rows 53 322 21 8 16 32 64 128 256), losses := [] }

theorem u9127 : Upper (D 1) (R 1) [52,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9128 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 22 235 251 235 235 235 491), lower := (rows 53 322 22 8 16 32 64 128 256), losses := [] }

theorem u9128 : Upper (D 1) (R 1) [52,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9129 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 28 235 243 227 227 227 483), lower := (rows 53 322 28 8 16 32 64 128 256), losses := [] }

theorem u9129 : Upper (D 1) (R 1) [52,320,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9130 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 322 52 203 219 235 203 203 459), lower := (rows 53 322 52 8 16 32 64 128 256), losses := [] }

theorem u9130 : Upper (D 1) (R 1) [52,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9131 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 53 322 69 186 186 186 250 186 442), lower := (rows 53 322 69 8 16 32 64 128 256), losses := [] }

theorem u9131 : Upper (D 1) (R 1) [52,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9132 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 322 70 187 187 187 251 187 443), lower := (rows 53 322 70 8 16 32 64 128 256), losses := [] }

theorem u9132 : Upper (D 1) (R 1) [52,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9133 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9133 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9133 : Upper (D 1) (R 1) [52,320,72] 13 := by
  apply FastRouting.sound _ _ [52,320,72] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9133 c9133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7241
  · exact u7242
  · exact u7243
  · exact u7244
  · exact u7245
  · exact u7246
  · exact u7247

def b9134 : PairBound 9 := { available := 171, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 84 171 187 171 235 171 427), lower := (rows 53 322 84 8 16 32 64 128 256), losses := [] }

theorem u9134 : Upper (D 1) (R 1) [52,320,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9135 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9135 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9135 : Upper (D 1) (R 1) [52,320,129] 13 := by
  apply FastRouting.sound _ _ [52,320,129] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9135 c9135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7248
  · exact u7249
  · exact u7250
  · exact u7251
  · exact u7252
  · exact u7253
  · exact u7254

def r9136 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9136 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9136 : Upper (D 1) (R 1) [52,320,130] 13 := by
  apply FastRouting.sound _ _ [52,320,130] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9136 c9136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7255
  · exact u7256
  · exact u7257
  · exact u7258
  · exact u7259
  · exact u7260
  · exact u7261
  · exact u7262
  · exact u7263
  · exact u7264
  · exact u7265

def r9137 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9137 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9137 : Upper (D 1) (R 1) [52,320,136] 13 := by
  apply FastRouting.sound _ _ [52,320,136] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9137 c9137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7266
  · exact u7267
  · exact u7268
  · exact u7269
  · exact u7270
  · exact u7271
  · exact u7272
  · exact u7273
  · exact u7274
  · exact u7275
  · exact u7276

def b9138 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 322 148 235 251 235 235 235 491), lower := (rows 53 322 148 8 16 32 64 128 256), losses := [] }

theorem u9138 : Upper (D 1) (R 1) [52,320,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9139 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9139 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9139 : Upper (D 1) (R 1) [52,320,192] 13 := by
  apply FastRouting.sound _ _ [52,320,192] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9139 c9139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7277
  · exact u7278
  · exact u7279
  · exact u7280
  · exact u7281
  · exact u7282
  · exact u7283

def r9140 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9140 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9140 : Upper (D 1) (R 1) [112,5,10] 13 := by
  apply FastRouting.sound _ _ [112,5,10] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r9140 c9140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7284
  · exact u7285
  · exact u7286
  · exact u7287
  · exact u7288
  · exact u7289
  · exact u7290

def b9141 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 490 506 490 490 490 490), lower := (rows 113 7 22 8 16 32 64 128 256), losses := [] }

theorem u9141 : Upper (D 1) (R 1) [112,5,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9142 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 490 498 482 482 482 482), lower := (rows 113 7 28 8 16 32 64 128 256), losses := [] }

theorem u9142 : Upper (D 1) (R 1) [112,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9143 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 458 474 490 458 458 458), lower := (rows 113 7 52 8 16 32 64 128 256), losses := [] }

theorem u9143 : Upper (D 1) (R 1) [112,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9144 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9144 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9144 : Upper (D 1) (R 1) [112,5,130] 13 := by
  apply FastRouting.sound _ _ [112,5,130] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r9144 c9144
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7291
  · exact u7292
  · exact u7293
  · exact u7294
  · exact u7295
  · exact u7296
  · exact u7297

def r9145 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9145 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9145 : Upper (D 1) (R 1) [112,5,136] 13 := by
  apply FastRouting.sound _ _ [112,5,136] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r9145 c9145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7298
  · exact u7299
  · exact u7300
  · exact u7301
  · exact u7302
  · exact u7303
  · exact u7304

def b9146 : PairBound 9 := { available := 490, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 490 506 490 490 490 490), lower := (rows 113 7 148 8 16 32 64 128 256), losses := [] }

theorem u9146 : Upper (D 1) (R 1) [112,5,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9147 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9147 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9147 : Upper (D 1) (R 1) [112,5,258] 13 := by
  apply FastRouting.sound _ _ [112,5,258] 13 (by decide) (choices 2) [18,48,130,144] r9147 c9147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7305
  · exact u7306
  · exact u7307
  · exact u7308

def r9148 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9148 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9148 : Upper (D 1) (R 1) [112,5,264] 13 := by
  apply FastRouting.sound _ _ [112,5,264] 13 (by decide) (choices 2) [18,48,130,144] r9148 c9148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7309
  · exact u7310
  · exact u7311
  · exact u7312

def b9149 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 276 234 250 234 234 234 490), lower := (rows 113 7 276 8 16 32 64 128 256), losses := [] }

theorem u9149 : Upper (D 1) (R 1) [112,5,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9150 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9150 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9150 : Upper (D 1) (R 1) [112,5,384] 13 := by
  apply FastRouting.sound _ _ [112,5,384] 13 (by decide) (choices 2) [18,48,130,144] r9150 c9150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7313
  · exact u7314
  · exact u7315
  · exact u7316

def r9151 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9151 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9151 : Upper (D 1) (R 1) [112,12,3] 13 := by
  apply FastRouting.sound _ _ [112,12,3] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r9151 c9151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7317
  · exact u7318
  · exact u7319
  · exact u7320
  · exact u7321
  · exact u7322
  · exact u7323

def b9152 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 21 490 498 482 482 482 482), lower := (rows 113 14 21 8 16 32 64 128 256), losses := [] }

theorem u9152 : Upper (D 1) (R 1) [112,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9152
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9153_3 : Upper (D 1) (R 1) [112,12,18,3] 13 :=
  permutation_upper _ _ _ [112,12,3,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7317

theorem m9153_33 : Upper (D 1) (R 1) [112,12,18,33] 13 :=
  permutation_upper _ _ _ [112,12,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7324

def r9153 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9153 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9153 : Upper (D 1) (R 1) [112,12,18] 13 := by
  apply FastRouting.sound _ _ [112,12,18] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9153 c9153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9153_3
  · exact m9153_33
  · exact u7330
  · exact u7331
  · exact u7332
  · exact u7333
  · exact u7334
  · exact u7335
  · exact u7336
  · exact u7337
  · exact u7338

def b9154 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 52 459 467 483 451 451 451), lower := (rows 113 14 52 8 16 32 64 128 256), losses := [] }

theorem u9154 : Upper (D 1) (R 1) [112,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9154
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9155_18 : Upper (D 1) (R 1) [112,12,129,18] 13 :=
  permutation_upper _ _ _ [112,12,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7332

theorem m9155_48 : Upper (D 1) (R 1) [112,12,129,48] 13 :=
  permutation_upper _ _ _ [112,12,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7339

def r9155 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9155 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9155 : Upper (D 1) (R 1) [112,12,129] 13 := by
  apply FastRouting.sound _ _ [112,12,129] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r9155 c9155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9155_18
  · exact m9155_48
  · exact u7346
  · exact u7347
  · exact u7348
  · exact u7349
  · exact u7350

theorem m9156_3 : Upper (D 1) (R 1) [112,12,130,3] 13 :=
  permutation_upper _ _ _ [112,12,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7319

theorem m9156_17 : Upper (D 1) (R 1) [112,12,130,17] 13 :=
  permutation_upper _ _ _ [112,12,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7325

theorem m9156_18 : Upper (D 1) (R 1) [112,12,130,18] 13 :=
  permutation_upper _ _ _ [112,12,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7333

theorem m9156_48 : Upper (D 1) (R 1) [112,12,130,48] 13 :=
  permutation_upper _ _ _ [112,12,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7340

theorem m9156_129 : Upper (D 1) (R 1) [112,12,130,129] 13 :=
  permutation_upper _ _ _ [112,12,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7346

def r9156 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9156 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9156 : Upper (D 1) (R 1) [112,12,130] 13 := by
  apply FastRouting.sound _ _ [112,12,130] 13 (by decide) (choices 2) [3,17,18,48,129,130,144,257,258,272,384] r9156 c9156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9156_3
  · exact m9156_17
  · exact m9156_18
  · exact m9156_48
  · exact m9156_129
  · exact u7351
  · exact u7352
  · exact u7353
  · exact u7354
  · exact u7355
  · exact u7356

theorem m9157_3 : Upper (D 1) (R 1) [112,12,144,3] 13 :=
  permutation_upper _ _ _ [112,12,3,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7320

theorem m9157_33 : Upper (D 1) (R 1) [112,12,144,33] 13 :=
  permutation_upper _ _ _ [112,12,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7326

theorem m9157_34 : Upper (D 1) (R 1) [112,12,144,34] 13 :=
  permutation_upper _ _ _ [112,12,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7334

theorem m9157_96 : Upper (D 1) (R 1) [112,12,144,96] 13 :=
  permutation_upper _ _ _ [112,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7341

theorem m9157_129 : Upper (D 1) (R 1) [112,12,144,129] 13 :=
  permutation_upper _ _ _ [112,12,129,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7347

theorem m9157_130 : Upper (D 1) (R 1) [112,12,144,130] 13 :=
  permutation_upper _ _ _ [112,12,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7352

def r9157 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9157 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9157 : Upper (D 1) (R 1) [112,12,144] 13 := by
  apply FastRouting.sound _ _ [112,12,144] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9157 c9157
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9157_3
  · exact m9157_33
  · exact m9157_34
  · exact m9157_96
  · exact m9157_129
  · exact m9157_130
  · exact u7357
  · exact u7358
  · exact u7359
  · exact u7360
  · exact u7361

theorem m9158_18 : Upper (D 1) (R 1) [112,12,257,18] 13 :=
  permutation_upper _ _ _ [112,12,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7335

theorem m9158_48 : Upper (D 1) (R 1) [112,12,257,48] 13 :=
  permutation_upper _ _ _ [112,12,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7342

theorem m9158_130 : Upper (D 1) (R 1) [112,12,257,130] 13 :=
  permutation_upper _ _ _ [112,12,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7353

theorem m9158_144 : Upper (D 1) (R 1) [112,12,257,144] 13 :=
  permutation_upper _ _ _ [112,12,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7358

def r9158 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9158 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9158 : Upper (D 1) (R 1) [112,12,257] 13 := by
  apply FastRouting.sound _ _ [112,12,257] 13 (by decide) (choices 2) [18,48,130,144] r9158 c9158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9158_18
  · exact m9158_48
  · exact m9158_130
  · exact m9158_144

theorem m9159_3 : Upper (D 1) (R 1) [112,12,258,3] 13 :=
  permutation_upper _ _ _ [112,12,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7321

theorem m9159_17 : Upper (D 1) (R 1) [112,12,258,17] 13 :=
  permutation_upper _ _ _ [112,12,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7327

theorem m9159_18 : Upper (D 1) (R 1) [112,12,258,18] 13 :=
  permutation_upper _ _ _ [112,12,18,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7336

theorem m9159_48 : Upper (D 1) (R 1) [112,12,258,48] 13 :=
  permutation_upper _ _ _ [112,12,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7343

theorem m9159_129 : Upper (D 1) (R 1) [112,12,258,129] 13 :=
  permutation_upper _ _ _ [112,12,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7348

theorem m9159_130 : Upper (D 1) (R 1) [112,12,258,130] 13 :=
  permutation_upper _ _ _ [112,12,130,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7354

theorem m9159_144 : Upper (D 1) (R 1) [112,12,258,144] 13 :=
  permutation_upper _ _ _ [112,12,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7359

def r9159 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9159 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9159 : Upper (D 1) (R 1) [112,12,258] 13 := by
  apply FastRouting.sound _ _ [112,12,258] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9159 c9159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9159_3
  · exact m9159_17
  · exact m9159_18
  · exact m9159_48
  · exact m9159_129
  · exact m9159_130
  · exact m9159_144

theorem m9160_3 : Upper (D 1) (R 1) [112,12,272,3] 13 :=
  permutation_upper _ _ _ [112,12,3,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7322

theorem m9160_33 : Upper (D 1) (R 1) [112,12,272,33] 13 :=
  permutation_upper _ _ _ [112,12,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7328

theorem m9160_34 : Upper (D 1) (R 1) [112,12,272,34] 13 :=
  permutation_upper _ _ _ [112,12,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7337

theorem m9160_96 : Upper (D 1) (R 1) [112,12,272,96] 13 :=
  permutation_upper _ _ _ [112,12,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7344

theorem m9160_129 : Upper (D 1) (R 1) [112,12,272,129] 13 :=
  permutation_upper _ _ _ [112,12,129,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7349

theorem m9160_130 : Upper (D 1) (R 1) [112,12,272,130] 13 :=
  permutation_upper _ _ _ [112,12,130,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7355

theorem m9160_160 : Upper (D 1) (R 1) [112,12,272,160] 13 :=
  permutation_upper _ _ _ [112,12,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7360

def r9160 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9160 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9160 : Upper (D 1) (R 1) [112,12,272] 13 := by
  apply FastRouting.sound _ _ [112,12,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r9160 c9160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9160_3
  · exact m9160_33
  · exact m9160_34
  · exact m9160_96
  · exact m9160_129
  · exact m9160_130
  · exact m9160_160

theorem m9161_3 : Upper (D 1) (R 1) [112,12,384,3] 13 :=
  permutation_upper _ _ _ [112,12,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7323

theorem m9161_17 : Upper (D 1) (R 1) [112,12,384,17] 13 :=
  permutation_upper _ _ _ [112,12,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7329

theorem m9161_18 : Upper (D 1) (R 1) [112,12,384,18] 13 :=
  permutation_upper _ _ _ [112,12,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7338

theorem m9161_48 : Upper (D 1) (R 1) [112,12,384,48] 13 :=
  permutation_upper _ _ _ [112,12,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7345

theorem m9161_129 : Upper (D 1) (R 1) [112,12,384,129] 13 :=
  permutation_upper _ _ _ [112,12,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7350

theorem m9161_130 : Upper (D 1) (R 1) [112,12,384,130] 13 :=
  permutation_upper _ _ _ [112,12,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7356

theorem m9161_144 : Upper (D 1) (R 1) [112,12,384,144] 13 :=
  permutation_upper _ _ _ [112,12,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7361

def r9161 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9161 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9161 : Upper (D 1) (R 1) [112,12,384] 13 := by
  apply FastRouting.sound _ _ [112,12,384] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9161 c9161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9161_3
  · exact m9161_17
  · exact m9161_18
  · exact m9161_48
  · exact m9161_129
  · exact m9161_130
  · exact m9161_144

def b9162 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 7 490 506 490 490 490 490), lower := (rows 113 22 7 8 16 32 64 128 256), losses := [] }

theorem u9162 : Upper (D 1) (R 1) [112,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9163 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 13 490 498 482 482 482 482), lower := (rows 113 22 13 8 16 32 64 128 256), losses := [] }

theorem u9163 : Upper (D 1) (R 1) [112,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9164 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9164 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9164 : Upper (D 1) (R 1) [112,20,10] 13 := by
  apply FastRouting.sound _ _ [112,20,10] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9164 c9164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7362
  · exact u7363
  · exact u7364
  · exact u7365
  · exact u7366
  · exact u7367
  · exact u7368
  · exact u7369
  · exact u7370
  · exact u7371
  · exact u7372

def b9165 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 37 458 474 490 458 458 458), lower := (rows 113 22 37 8 16 32 64 128 256), losses := [] }

theorem u9165 : Upper (D 1) (R 1) [112,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9166 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 38 459 475 491 459 459 459), lower := (rows 113 22 38 8 16 32 64 128 256), losses := [] }

theorem u9166 : Upper (D 1) (R 1) [112,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9167 : Route 9 := (fun mask => (mask,id))

def c9167 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9167 : Upper (D 1) (R 1) [112,20,40] 13 := by
  apply FastRouting.sound _ _ [112,20,40] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9167 c9167
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

def b9168 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 100 395 411 427 459 395 395), lower := (rows 113 22 100 8 16 32 64 128 256), losses := [] }

theorem u9168 : Upper (D 1) (R 1) [112,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9169 : PairBound 9 := { available := 490, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 133 490 506 490 490 490 490), lower := (rows 113 22 133 8 16 32 64 128 256), losses := [] }

theorem u9169 : Upper (D 1) (R 1) [112,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9170 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9170 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9170 : Upper (D 1) (R 1) [112,20,130] 13 := by
  apply FastRouting.sound _ _ [112,20,130] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9170 c9170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact u7393

def r9171 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9171 : Upper (D 1) (R 1) [112,20,136] 13 := by
  apply FastRouting.sound _ _ [112,20,136] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9171 c9171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7394
  · exact u7395
  · exact u7396
  · exact u7397
  · exact u7398
  · exact u7399
  · exact u7400
  · exact u7401
  · exact u7402
  · exact u7403
  · exact u7404

def r9172 : Route 9 := (fun mask => (mask,id))

def c9172 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 6 => 2 | 18 => 4 | 34 => 5 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9172 : Upper (D 1) (R 1) [112,20,160] 13 := by
  apply FastRouting.sound _ _ [112,20,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9172 c9172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7405
  · exact u7406
  · exact u7407
  · exact u7408
  · exact u7409
  · exact u7410
  · exact u7411
  · exact u7412
  · exact u7413
  · exact u7414

def b9173 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 261 234 250 234 234 234 490), lower := (rows 113 22 261 8 16 32 64 128 256), losses := [] }

theorem u9173 : Upper (D 1) (R 1) [112,20,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9174 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9174 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9174 : Upper (D 1) (R 1) [112,20,258] 13 := by
  apply FastRouting.sound _ _ [112,20,258] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r9174 c9174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7415
  · exact u7416
  · exact u7417
  · exact u7418
  · exact u7419
  · exact u7420
  · exact u7421

def r9175 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9175 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9175 : Upper (D 1) (R 1) [112,20,264] 13 := by
  apply FastRouting.sound _ _ [112,20,264] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r9175 c9175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7422
  · exact u7423
  · exact u7424
  · exact u7425
  · exact u7426
  · exact u7427
  · exact u7428

def r9176 : Route 9 := (fun mask => (mask,id))

def c9176 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9176 : Upper (D 1) (R 1) [112,20,288] 13 := by
  apply FastRouting.sound _ _ [112,20,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r9176 c9176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7429
  · exact u7430
  · exact u7431
  · exact u7432
  · exact u7433
  · exact u7434

def r9177 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9177 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9177 : Upper (D 1) (R 1) [112,20,384] 13 := by
  apply FastRouting.sound _ _ [112,20,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r9177 c9177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7435
  · exact u7436
  · exact u7437
  · exact u7438
  · exact u7439
  · exact u7440
  · exact u7441

def r9178 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9178 : Nat → Fin 9 := (fun _ => 0)

theorem u9178 : Upper (D 1) (R 1) [112,129,10] 13 := by
  apply FastRouting.sound _ _ [112,129,10] 13 (by decide) (choices 2) [6,18,20,48,130,132,144,258,260,272,384] r9178 c9178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7442
  · exact u7443
  · exact u7444
  · exact u7445
  · exact u7446
  · exact u7447
  · exact u7448
  · exact u7449
  · exact u7450
  · exact u7451
  · exact u7452

def b9179 : PairBound 9 := { available := 494, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 494 510 494 494 494 494), lower := (rows 113 131 22 8 16 32 64 128 256), losses := [] }

theorem u9179 : Upper (D 1) (R 1) [112,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9179
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u9179
end Delivery.IrregularNine14.P01
