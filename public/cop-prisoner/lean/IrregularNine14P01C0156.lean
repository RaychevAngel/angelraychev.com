import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0135
import IrregularNine14P01C0136
import IrregularNine14P01C0137
import IrregularNine14P01C0138
import IrregularNine14P01C0139

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9360 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 11 52 234 242 226 226 226 482), lower := (rows 277 11 52 8 16 32 64 128 256), losses := [] }

theorem u9360 : Upper (D 1) (R 1) [276,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9361 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9361 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9361 : Upper (D 1) (R 1) [276,9,96] 13 := by
  apply FastRouting.sound _ _ [276,9,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9361 c9361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8131
  · exact u8132
  · exact u8133
  · exact u8134
  · exact u8135
  · exact u8136
  · exact u8137

def b9362 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 277 26 7 234 242 226 226 226 482), lower := (rows 277 26 7 8 16 32 64 128 256), losses := [] }

theorem u9362 : Upper (D 1) (R 1) [276,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9363 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 277 26 37 234 242 226 226 226 482), lower := (rows 277 26 37 8 16 32 64 128 256), losses := [] }

theorem u9363 : Upper (D 1) (R 1) [276,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9364 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9364 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9364 : Upper (D 1) (R 1) [276,24,34] 13 := by
  apply FastRouting.sound _ _ [276,24,34] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9364 c9364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8138
  · exact u8139
  · exact u8140
  · exact u8141
  · exact u8142
  · exact u8143
  · exact u8144

def r9365 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9365 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9365 : Upper (D 1) (R 1) [276,24,96] 13 := by
  apply FastRouting.sound _ _ [276,24,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r9365 c9365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8145
  · exact u8146
  · exact u8147
  · exact u8148
  · exact u8149
  · exact u8150
  · exact u8151

def r9366 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9366 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9366 : Upper (D 1) (R 1) [276,33,10] 13 := by
  apply FastRouting.sound _ _ [276,33,10] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9366 c9366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8152
  · exact u8153
  · exact u8154
  · exact u8155
  · exact u8156
  · exact u8157
  · exact u8158

def b9367 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 22 234 250 234 234 234 490), lower := (rows 277 35 22 8 16 32 64 128 256), losses := [] }

theorem u9367 : Upper (D 1) (R 1) [276,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9368 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 28 234 242 226 226 226 482), lower := (rows 277 35 28 8 16 32 64 128 256), losses := [] }

theorem u9368 : Upper (D 1) (R 1) [276,33,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9369 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 35 38 218 218 250 218 218 474), lower := (rows 277 35 38 8 16 32 64 128 256), losses := [] }

theorem u9369 : Upper (D 1) (R 1) [276,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9370 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 277 35 44 218 210 242 210 210 466), lower := (rows 277 35 44 8 16 32 64 128 256), losses := [] }

theorem u9370 : Upper (D 1) (R 1) [276,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9371 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 52 202 218 234 202 202 458), lower := (rows 277 35 52 8 16 32 64 128 256), losses := [] }

theorem u9371 : Upper (D 1) (R 1) [276,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9372 : Route 9 := (fun mask => (mask,id))

def c9372 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9372 : Upper (D 1) (R 1) [276,33,66] 13 := by
  apply FastRouting.sound _ _ [276,33,66] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r9372 c9372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8159
  · exact u8160
  · exact u8161
  · exact u8162
  · exact u8163
  · exact u8164
  · exact u8165
  · exact u8166
  · exact u8167
  · exact u8168

def r9373 : Route 9 := (fun mask => (mask,id))

def c9373 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9373 : Upper (D 1) (R 1) [276,33,72] 13 := by
  apply FastRouting.sound _ _ [276,33,72] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r9373 c9373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8169
  · exact u8170
  · exact u8171
  · exact u8172
  · exact u8173
  · exact u8174
  · exact u8175
  · exact u8176
  · exact u8177
  · exact u8178

def b9374 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 35 84 234 250 234 234 234 490), lower := (rows 277 35 84 8 16 32 64 128 256), losses := [] }

theorem u9374 : Upper (D 1) (R 1) [276,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9375 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 277 35 100 218 218 250 218 218 474), lower := (rows 277 35 100 8 16 32 64 128 256), losses := [] }

theorem u9375 : Upper (D 1) (R 1) [276,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9376 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9376 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9376 : Upper (D 1) (R 1) [276,33,192] 13 := by
  apply FastRouting.sound _ _ [276,33,192] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9376 c9376
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8179
  · exact u8180
  · exact u8181
  · exact u8182
  · exact u8183
  · exact u8184
  · exact u8185

def r9377 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9377 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9377 : Upper (D 1) (R 1) [276,40,3] 13 := by
  apply FastRouting.sound _ _ [276,40,3] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9377 c9377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8186
  · exact u8187
  · exact u8188
  · exact u8189
  · exact u8190
  · exact u8191
  · exact u8192

def b9378 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 42 21 234 242 226 226 226 482), lower := (rows 277 42 21 8 16 32 64 128 256), losses := [] }

theorem u9378 : Upper (D 1) (R 1) [276,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9379 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 22 235 243 227 227 227 483), lower := (rows 277 42 22 8 16 32 64 128 256), losses := [] }

theorem u9379 : Upper (D 1) (R 1) [276,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9379
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9380 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 277 42 37 218 210 242 210 210 466), lower := (rows 277 42 37 8 16 32 64 128 256), losses := [] }

theorem u9380 : Upper (D 1) (R 1) [276,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9381 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 42 38 219 211 243 211 211 467), lower := (rows 277 42 38 8 16 32 64 128 256), losses := [] }

theorem u9381 : Upper (D 1) (R 1) [276,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9382 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 52 203 211 227 195 195 451), lower := (rows 277 42 52 8 16 32 64 128 256), losses := [] }

theorem u9382 : Upper (D 1) (R 1) [276,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9383 : Route 9 := (fun mask => (mask,id))

def c9383 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9383 : Upper (D 1) (R 1) [276,40,65] 13 := by
  apply FastRouting.sound _ _ [276,40,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r9383 c9383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8193
  · exact u8194
  · exact u8195
  · exact u8196
  · exact u8197
  · exact u8198
  · exact u8199
  · exact u8200
  · exact u8201
  · exact u8202

def r9384 : Route 9 := (fun mask => (mask,id))

def c9384 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9384 : Upper (D 1) (R 1) [276,40,66] 13 := by
  apply FastRouting.sound _ _ [276,40,66] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r9384 c9384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8203
  · exact u8204
  · exact u8205
  · exact u8206
  · exact u8207
  · exact u8208
  · exact u8209
  · exact u8210
  · exact u8211
  · exact u8212
  · exact u8213
  · exact u8214
  · exact u8215
  · exact u8216
  · exact u8217

def b9385 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 84 235 243 227 227 227 483), lower := (rows 277 42 84 8 16 32 64 128 256), losses := [] }

theorem u9385 : Upper (D 1) (R 1) [276,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9386 : Route 9 := (fun mask => (mask,id))

def c9386 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9386 : Upper (D 1) (R 1) [276,40,96] 13 := by
  apply FastRouting.sound _ _ [276,40,96] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r9386 c9386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8218
  · exact u8219
  · exact u8220
  · exact u8221
  · exact u8222
  · exact u8223
  · exact u8224
  · exact u8225
  · exact u8226
  · exact u8227

def r9387 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9387 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9387 : Upper (D 1) (R 1) [276,40,192] 13 := by
  apply FastRouting.sound _ _ [276,40,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r9387 c9387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8228
  · exact u8229
  · exact u8230
  · exact u8231
  · exact u8232
  · exact u8233
  · exact u8234
  · exact u8235
  · exact u8236
  · exact u8237
  · exact u8238

def b9388 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 7 234 250 234 234 234 490), lower := (rows 277 50 7 8 16 32 64 128 256), losses := [] }

theorem u9388 : Upper (D 1) (R 1) [276,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9389 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 13 234 242 226 226 226 482), lower := (rows 277 50 13 8 16 32 64 128 256), losses := [] }

theorem u9389 : Upper (D 1) (R 1) [276,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9390 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9390 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9390 : Upper (D 1) (R 1) [276,48,10] 13 := by
  apply FastRouting.sound _ _ [276,48,10] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9390 c9390
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8239
  · exact u8240
  · exact u8241
  · exact u8242
  · exact u8243
  · exact u8244
  · exact u8245

def b9391 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 37 202 218 234 202 202 458), lower := (rows 277 50 37 8 16 32 64 128 256), losses := [] }

theorem u9391 : Upper (D 1) (R 1) [276,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9392 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 50 38 203 219 235 203 203 459), lower := (rows 277 50 38 8 16 32 64 128 256), losses := [] }

theorem u9392 : Upper (D 1) (R 1) [276,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9393 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9393 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9393 : Upper (D 1) (R 1) [276,48,40] 13 := by
  apply FastRouting.sound _ _ [276,48,40] 13 (by decide) (choices 2) [3,65,66,192] r9393 c9393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8246
  · exact u8247
  · exact u8248
  · exact u8249

def b9394 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 277 50 69 234 250 234 234 234 490), lower := (rows 277 50 69 8 16 32 64 128 256), losses := [] }

theorem u9394 : Upper (D 1) (R 1) [276,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9395 : Route 9 := (fun mask => (mask,id))

def c9395 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9395 : Upper (D 1) (R 1) [276,48,66] 13 := by
  apply FastRouting.sound _ _ [276,48,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9395 c9395
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8250
  · exact u8251
  · exact u8252
  · exact u8253
  · exact u8254
  · exact u8255
  · exact u8256
  · exact u8257
  · exact u8258
  · exact u8259

def r9396 : Route 9 := (fun mask => (mask,id))

def c9396 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9396 : Upper (D 1) (R 1) [276,48,72] 13 := by
  apply FastRouting.sound _ _ [276,48,72] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9396 c9396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8260
  · exact u8261
  · exact u8262
  · exact u8263
  · exact u8264
  · exact u8265
  · exact u8266
  · exact u8267
  · exact u8268
  · exact u8269

def r9397 : Route 9 := (fun mask => (mask,id))

def c9397 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9397 : Upper (D 1) (R 1) [276,48,96] 13 := by
  apply FastRouting.sound _ _ [276,48,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r9397 c9397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8270
  · exact u8271
  · exact u8272
  · exact u8273
  · exact u8274
  · exact u8275

def r9398 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9398 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9398 : Upper (D 1) (R 1) [276,48,192] 13 := by
  apply FastRouting.sound _ _ [276,48,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9398 c9398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8276
  · exact u8277
  · exact u8278
  · exact u8279
  · exact u8280
  · exact u8281
  · exact u8282

def r9399 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9399 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9399 : Upper (D 1) (R 1) [276,96,3] 13 := by
  apply FastRouting.sound _ _ [276,96,3] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9399 c9399
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8283
  · exact u8284
  · exact u8285
  · exact u8286
  · exact u8287
  · exact u8288
  · exact u8289

def r9400 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9400 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9400 : Upper (D 1) (R 1) [276,96,9] 13 := by
  apply FastRouting.sound _ _ [276,96,9] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9400 c9400
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8290
  · exact u8291
  · exact u8292
  · exact u8293
  · exact u8294
  · exact u8295
  · exact u8296

def r9401 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9401 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9401 : Upper (D 1) (R 1) [276,96,10] 13 := by
  apply FastRouting.sound _ _ [276,96,10] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r9401 c9401
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8297
  · exact u8298
  · exact u8299
  · exact u8300
  · exact u8301
  · exact u8302
  · exact u8303
  · exact u8304
  · exact u8305
  · exact u8306
  · exact u8307

def b9402 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 21 234 250 234 234 234 490), lower := (rows 277 98 21 8 16 32 64 128 256), losses := [] }

theorem u9402 : Upper (D 1) (R 1) [276,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9403 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 22 235 251 235 235 235 491), lower := (rows 277 98 22 8 16 32 64 128 256), losses := [] }

theorem u9403 : Upper (D 1) (R 1) [276,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9404 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 28 235 243 227 227 227 483), lower := (rows 277 98 28 8 16 32 64 128 256), losses := [] }

theorem u9404 : Upper (D 1) (R 1) [276,96,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9405 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 277 98 37 218 218 250 218 218 474), lower := (rows 277 98 37 8 16 32 64 128 256), losses := [] }

theorem u9405 : Upper (D 1) (R 1) [276,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9406 : PairBound 9 := { available := 219, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 38 219 219 251 219 219 475), lower := (rows 277 98 38 8 16 32 64 128 256), losses := [] }

theorem u9406 : Upper (D 1) (R 1) [276,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9407 : Route 9 := (fun mask => (mask,id))

def c9407 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9407 : Upper (D 1) (R 1) [276,96,40] 13 := by
  apply FastRouting.sound _ _ [276,96,40] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r9407 c9407
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8308
  · exact u8309
  · exact u8310
  · exact u8311
  · exact u8312
  · exact u8313
  · exact u8314
  · exact u8315
  · exact u8316
  · exact u8317

def b9408 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 52 203 219 235 203 203 459), lower := (rows 277 98 52 8 16 32 64 128 256), losses := [] }

theorem u9408 : Upper (D 1) (R 1) [276,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9409 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 100 155 155 187 219 155 411), lower := (rows 277 98 100 8 16 32 64 128 256), losses := [] }

theorem u9409 : Upper (D 1) (R 1) [276,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9410 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9410 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9410 : Upper (D 1) (R 1) [276,96,129] 13 := by
  apply FastRouting.sound _ _ [276,96,129] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9410 c9410
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8318
  · exact u8319
  · exact u8320
  · exact u8321
  · exact u8322
  · exact u8323
  · exact u8324

def r9411 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9411 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9411 : Upper (D 1) (R 1) [276,96,130] 13 := by
  apply FastRouting.sound _ _ [276,96,130] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r9411 c9411
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8325
  · exact u8326
  · exact u8327
  · exact u8328
  · exact u8329
  · exact u8330
  · exact u8331
  · exact u8332
  · exact u8333
  · exact u8334
  · exact u8335

def r9412 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9412 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9412 : Upper (D 1) (R 1) [276,96,136] 13 := by
  apply FastRouting.sound _ _ [276,96,136] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r9412 c9412
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8336
  · exact u8337
  · exact u8338
  · exact u8339
  · exact u8340
  · exact u8341
  · exact u8342
  · exact u8343
  · exact u8344
  · exact u8345
  · exact u8346

def b9413 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 148 235 251 235 235 235 491), lower := (rows 277 98 148 8 16 32 64 128 256), losses := [] }

theorem u9413 : Upper (D 1) (R 1) [276,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9414 : Route 9 := (fun mask => (mask,id))

def c9414 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9414 : Upper (D 1) (R 1) [276,96,160] 13 := by
  apply FastRouting.sound _ _ [276,96,160] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r9414 c9414
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8347
  · exact u8348
  · exact u8349
  · exact u8350
  · exact u8351
  · exact u8352
  · exact u8353
  · exact u8354
  · exact u8355
  · exact u8356

def r9415 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9415 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9415 : Upper (D 1) (R 1) [304,5,10] 13 := by
  apply FastRouting.sound _ _ [304,5,10] 13 (by decide) (choices 2) [18,48,66,80,192] r9415 c9415
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u8357
  · exact u8358
  · exact u8359
  · exact u8360
  · exact u8361

def b9416 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 22 234 250 234 234 234 490), lower := (rows 305 7 22 8 16 32 64 128 256), losses := [] }

theorem u9416 : Upper (D 1) (R 1) [304,5,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9417 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 28 234 242 226 226 226 482), lower := (rows 305 7 28 8 16 32 64 128 256), losses := [] }

theorem u9417 : Upper (D 1) (R 1) [304,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9418 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 52 202 218 234 202 202 458), lower := (rows 305 7 52 8 16 32 64 128 256), losses := [] }

theorem u9418 : Upper (D 1) (R 1) [304,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9419 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9419 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9419 : Upper (D 1) (R 1) [304,5,66] 13 := by
  apply FastRouting.sound _ _ [304,5,66] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9419 c9419
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8362
  · exact u8363
  · exact u8364
  · exact u8365
  · exact u8366
  · exact u8367
  · exact u8368

#print axioms u9419
end Delivery.IrregularNine14.P01
