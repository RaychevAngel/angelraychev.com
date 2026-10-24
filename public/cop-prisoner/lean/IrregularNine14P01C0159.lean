import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0151
import IrregularNine14P01C0152
import IrregularNine14P01C0153
import IrregularNine14P01C0154
import IrregularNine14P01C0155
import IrregularNine14P01C0156
import IrregularNine14P01C0157
import IrregularNine14P01C0158

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9540 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9540 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9540 : Upper (D 1) (R 1) [52,264] 13 := by
  apply FastRouting.sound _ _ [52,264] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9540 c9540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9105
  · exact u9106
  · exact u9107
  · exact u9108
  · exact u9109
  · exact u9110
  · exact u9111
  · exact u9112

def r9541 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9541 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9541 : Upper (D 1) (R 1) [52,272] 13 := by
  apply FastRouting.sound _ _ [52,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r9541 c9541
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9113
  · exact u9114
  · exact u9115
  · exact u9116
  · exact u9117
  · exact u9118
  · exact u9119
  · exact u9120
  · exact u9121
  · exact u9122
  · exact u9123

def r9542 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9542 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9542 : Upper (D 1) (R 1) [52,320] 13 := by
  apply FastRouting.sound _ _ [52,320] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192] r9542 c9542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9124
  · exact u9125
  · exact u9126
  · exact u9127
  · exact u9128
  · exact u9129
  · exact u9130
  · exact u9131
  · exact u9132
  · exact u9133
  · exact u9134
  · exact u9135
  · exact u9136
  · exact u9137
  · exact u9138
  · exact u9139

def r9543 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9543 : Nat → Fin 9 := (fun _ => 0)

theorem u9543 : Upper (D 1) (R 1) [112,5] 13 := by
  apply FastRouting.sound _ _ [112,5] 13 (by decide) (choices 2) [10,18,24,48,130,136,144,258,264,272,384] r9543 c9543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9140
  · exact u9141
  · exact u9142
  · exact u9143
  · exact u9144
  · exact u9145
  · exact u9146
  · exact u9147
  · exact u9148
  · exact u9149
  · exact u9150

def r9544 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9544 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9544 : Upper (D 1) (R 1) [112,12] 13 := by
  apply FastRouting.sound _ _ [112,12] 13 (by decide) (choices 2) [3,17,18,48,129,130,144,257,258,272,384] r9544 c9544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9151
  · exact u9152
  · exact u9153
  · exact u9154
  · exact u9155
  · exact u9156
  · exact u9157
  · exact u9158
  · exact u9159
  · exact u9160
  · exact u9161

def b9545 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 19 494 494 510 494 494 494 494), lower := (rows 113 19 4 8 16 32 64 128 256), losses := [] }

theorem u9545 : Upper (D 1) (R 1) [112,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9546 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9546 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9546 : Upper (D 1) (R 1) [112,20] 13 := by
  apply FastRouting.sound _ _ [112,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160,257,258,264,288,384] r9546 c9546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9162
  · exact u9163
  · exact u9164
  · exact u9165
  · exact u9166
  · exact u9167
  · exact u9168
  · exact u9169
  · exact u9170
  · exact u9171
  · exact u9172
  · exact u9173
  · exact u9174
  · exact u9175
  · exact u9176
  · exact u9177

def b9547 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 463 463 479 495 463 463 463), lower := (rows 113 50 4 8 16 32 64 128 256), losses := [] }

theorem u9547 : Upper (D 1) (R 1) [112,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9548 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9548 : Nat → Fin 9 := (fun _ => 0)

theorem u9548 : Upper (D 1) (R 1) [112,129] 13 := by
  apply FastRouting.sound _ _ [112,129] 13 (by decide) (choices 2) [10,18,24,48,130,136,144,258,264,272,384] r9548 c9548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9178
  · exact u9179
  · exact u9180
  · exact u9181
  · exact u9182
  · exact u9183
  · exact u9184
  · exact u9185
  · exact u9186
  · exact u9187
  · exact u9188

def r9549 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9549 : Nat → Fin 9 := (fun _ => 0)

theorem u9549 : Upper (D 1) (R 1) [112,132] 13 := by
  apply FastRouting.sound _ _ [112,132] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,129,130,136,144,257,258,264,272,384] r9549 c9549
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9189
  · exact u9190
  · exact u9191
  · exact u9192
  · exact u9193
  · exact u9194
  · exact u9195
  · exact u9196
  · exact u9197
  · exact u9198
  · exact u9199
  · exact u9200
  · exact u9201
  · exact u9202
  · exact u9203
  · exact u9204

def r9550 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9550 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9550 : Upper (D 1) (R 1) [112,144] 13 := by
  apply FastRouting.sound _ _ [112,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160,257,258,264,288,384] r9550 c9550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9205
  · exact u9206
  · exact u9207
  · exact u9208
  · exact u9209
  · exact u9210
  · exact u9211
  · exact u9212
  · exact u9213
  · exact u9214
  · exact u9215
  · exact u9216
  · exact u9217
  · exact u9218
  · exact u9219
  · exact u9220

def r9551 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9551 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9551 : Upper (D 1) (R 1) [112,257] 13 := by
  apply FastRouting.sound _ _ [112,257] 13 (by decide) (choices 2) [10,18,24,48,130,136,144] r9551 c9551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9221
  · exact u9222
  · exact u9223
  · exact u9224
  · exact u9225
  · exact u9226
  · exact u9227

def r9552 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9552 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9552 : Upper (D 1) (R 1) [112,260] 13 := by
  apply FastRouting.sound _ _ [112,260] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,129,130,136,144] r9552 c9552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9228
  · exact u9229
  · exact u9230
  · exact u9231
  · exact u9232
  · exact u9233
  · exact u9234
  · exact u9235
  · exact u9236
  · exact u9237
  · exact u9238

def r9553 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9553 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9553 : Upper (D 1) (R 1) [112,272] 13 := by
  apply FastRouting.sound _ _ [112,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160] r9553 c9553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9239
  · exact u9240
  · exact u9241
  · exact u9242
  · exact u9243
  · exact u9244
  · exact u9245
  · exact u9246
  · exact u9247
  · exact u9248
  · exact u9249

def r9554 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9554 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9554 : Upper (D 1) (R 1) [112,384] 13 := by
  apply FastRouting.sound _ _ [112,384] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,129,130,136,144] r9554 c9554
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9250
  · exact u9251
  · exact u9252
  · exact u9253
  · exact u9254
  · exact u9255
  · exact u9256
  · exact u9257
  · exact u9258
  · exact u9259
  · exact u9260

def r9555 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 130 => (18,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9555 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9555 : Upper (D 1) (R 1) [262,9] 13 := by
  apply FastRouting.sound _ _ [262,9] 13 (by decide) (choices 2) [18,48] r9555 c9555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9261
  · exact u9262

def r9556 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9556 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9556 : Upper (D 1) (R 1) [262,17] 13 := by
  apply FastRouting.sound _ _ [262,17] 13 (by decide) (choices 2) [10,18,24,34,40,48,96] r9556 c9556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9263
  · exact u9264
  · exact u9265
  · exact u9266
  · exact u9267
  · exact u9268
  · exact u9269

def r9557 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9557 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9557 : Upper (D 1) (R 1) [262,24] 13 := by
  apply FastRouting.sound _ _ [262,24] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r9557 c9557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9270
  · exact u9271
  · exact u9272
  · exact u9273
  · exact u9274
  · exact u9275
  · exact u9276

def r9558 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9558 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9558 : Upper (D 1) (R 1) [262,48] 13 := by
  apply FastRouting.sound _ _ [262,48] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192] r9558 c9558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9277
  · exact u9278
  · exact u9279
  · exact u9280
  · exact u9281
  · exact u9282
  · exact u9283
  · exact u9284
  · exact u9285
  · exact u9286
  · exact u9287
  · exact u9288

def r9559 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9559 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9559 : Upper (D 1) (R 1) [268,17] 13 := by
  apply FastRouting.sound _ _ [268,17] 13 (by decide) (choices 2) [18,34,48,96] r9559 c9559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9289
  · exact u9290
  · exact u9291
  · exact u9292

def r9560 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9560 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9560 : Upper (D 1) (R 1) [268,48] 13 := by
  apply FastRouting.sound _ _ [268,48] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9560 c9560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9293
  · exact u9294
  · exact u9295
  · exact u9296
  · exact u9297
  · exact u9298
  · exact u9299
  · exact u9300

def r9561 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9561 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9561 : Upper (D 1) (R 1) [274,5] 13 := by
  apply FastRouting.sound _ _ [274,5] 13 (by decide) (choices 2) [10,18,24,34,40,48,96] r9561 c9561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9301
  · exact u9302
  · exact u9303
  · exact u9304
  · exact u9305
  · exact u9306
  · exact u9307

def r9562 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9562 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9562 : Upper (D 1) (R 1) [274,12] 13 := by
  apply FastRouting.sound _ _ [274,12] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r9562 c9562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9308
  · exact u9309
  · exact u9310
  · exact u9311
  · exact u9312
  · exact u9313
  · exact u9314

def b9563 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 275 19 238 238 254 238 238 238 494), lower := (rows 275 19 4 8 16 32 64 128 256), losses := [] }

theorem u9563 : Upper (D 1) (R 1) [274,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9564 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 236, targets := 16 }], pairs := [(2,4)], upper := (rows 275 22 239 235 251 235 235 235 491), lower := (rows 275 22 4 8 16 32 64 128 256), losses := [] }

theorem u9564 : Upper (D 1) (R 1) [274,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9565 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9565 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9565 : Upper (D 1) (R 1) [274,33] 13 := by
  apply FastRouting.sound _ _ [274,33] 13 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96,192] r9565 c9565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9315
  · exact u9316
  · exact u9317
  · exact u9318
  · exact u9319
  · exact u9320
  · exact u9321
  · exact u9322
  · exact u9323
  · exact u9324
  · exact u9325

def r9566 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9566 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9566 : Upper (D 1) (R 1) [274,36] 13 := by
  apply FastRouting.sound _ _ [274,36] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192] r9566 c9566
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9326
  · exact u9327
  · exact u9328
  · exact u9329
  · exact u9330
  · exact u9331
  · exact u9332
  · exact u9333
  · exact u9334
  · exact u9335
  · exact u9336
  · exact u9337
  · exact u9338
  · exact u9339
  · exact u9340
  · exact u9341

def b9567 : PairBound 9 := { available := 239, camps := [{ cop := 0, region := 236, targets := 16 }], pairs := [(2,4)], upper := (rows 275 50 239 239 255 239 239 239 495), lower := (rows 275 50 4 8 16 32 64 128 256), losses := [] }

theorem u9567 : Upper (D 1) (R 1) [274,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9568 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9568 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9568 : Upper (D 1) (R 1) [274,96] 13 := by
  apply FastRouting.sound _ _ [274,96] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,96,129,130,136,144,160] r9568 c9568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9342
  · exact u9343
  · exact u9344
  · exact u9345
  · exact u9346
  · exact u9347
  · exact u9348
  · exact u9349
  · exact u9350
  · exact u9351
  · exact u9352
  · exact u9353
  · exact u9354
  · exact u9355
  · exact u9356
  · exact u9357

def r9569 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9569 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9569 : Upper (D 1) (R 1) [276,9] 13 := by
  apply FastRouting.sound _ _ [276,9] 13 (by decide) (choices 2) [18,34,48,96] r9569 c9569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9358
  · exact u9359
  · exact u9360
  · exact u9361

def b9570 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 277 19 238 234 250 234 234 234 490), lower := (rows 277 19 4 8 16 32 64 128 256), losses := [] }

theorem u9570 : Upper (D 1) (R 1) [276,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9571 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9571 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 257 => 8 | 10 => 3 | 18 => 4 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9571 : Upper (D 1) (R 1) [276,24] 13 := by
  apply FastRouting.sound _ _ [276,24] 13 (by decide) (choices 2) [3,33,34,96] r9571 c9571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9362
  · exact u9363
  · exact u9364
  · exact u9365

def r9572 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9572 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9572 : Upper (D 1) (R 1) [276,33] 13 := by
  apply FastRouting.sound _ _ [276,33] 13 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96,192] r9572 c9572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9366
  · exact u9367
  · exact u9368
  · exact u9369
  · exact u9370
  · exact u9371
  · exact u9372
  · exact u9373
  · exact u9374
  · exact u9375
  · exact u9376

def r9573 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9573 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9573 : Upper (D 1) (R 1) [276,40] 13 := by
  apply FastRouting.sound _ _ [276,40] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r9573 c9573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9377
  · exact u9378
  · exact u9379
  · exact u9380
  · exact u9381
  · exact u9382
  · exact u9383
  · exact u9384
  · exact u9385
  · exact u9386
  · exact u9387

def r9574 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9574 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9574 : Upper (D 1) (R 1) [276,48] 13 := by
  apply FastRouting.sound _ _ [276,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r9574 c9574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9388
  · exact u9389
  · exact u9390
  · exact u9391
  · exact u9392
  · exact u9393
  · exact u9394
  · exact u9395
  · exact u9396
  · exact u9397
  · exact u9398

def r9575 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9575 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9575 : Upper (D 1) (R 1) [276,96] 13 := by
  apply FastRouting.sound _ _ [276,96] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,96,129,130,136,144,160] r9575 c9575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9399
  · exact u9400
  · exact u9401
  · exact u9402
  · exact u9403
  · exact u9404
  · exact u9405
  · exact u9406
  · exact u9407
  · exact u9408
  · exact u9409
  · exact u9410
  · exact u9411
  · exact u9412
  · exact u9413
  · exact u9414

def r9576 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9576 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9576 : Upper (D 1) (R 1) [304,5] 13 := by
  apply FastRouting.sound _ _ [304,5] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192] r9576 c9576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9415
  · exact u9416
  · exact u9417
  · exact u9418
  · exact u9419
  · exact u9420
  · exact u9421
  · exact u9422

def r9577 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9577 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9577 : Upper (D 1) (R 1) [304,12] 13 := by
  apply FastRouting.sound _ _ [304,12] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9577 c9577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9423
  · exact u9424
  · exact u9425
  · exact u9426
  · exact u9427
  · exact u9428
  · exact u9429
  · exact u9430

def b9578 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 19 238 238 254 238 238 238 494), lower := (rows 305 19 4 8 16 32 64 128 256), losses := [] }

theorem u9578 : Upper (D 1) (R 1) [304,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9578
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9579 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9579 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9579 : Upper (D 1) (R 1) [304,20] 13 := by
  apply FastRouting.sound _ _ [304,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r9579 c9579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9431
  · exact u9432
  · exact u9433
  · exact u9434
  · exact u9435
  · exact u9436
  · exact u9437
  · exact u9438
  · exact u9439
  · exact u9440
  · exact u9441

def b9580 : PairBound 9 := { available := 207, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 207 207 223 239 207 207 463), lower := (rows 305 50 4 8 16 32 64 128 256), losses := [] }

theorem u9580 : Upper (D 1) (R 1) [304,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9581 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9581 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9581 : Upper (D 1) (R 1) [304,65] 13 := by
  apply FastRouting.sound _ _ [304,65] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,130,136,144,192] r9581 c9581
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9442
  · exact u9443
  · exact u9444
  · exact u9445
  · exact u9446
  · exact u9447
  · exact u9448
  · exact u9449
  · exact u9450
  · exact u9451
  · exact u9452

def r9582 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9582 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9582 : Upper (D 1) (R 1) [304,68] 13 := by
  apply FastRouting.sound _ _ [304,68] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192] r9582 c9582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9453
  · exact u9454
  · exact u9455
  · exact u9456
  · exact u9457
  · exact u9458
  · exact u9459
  · exact u9460
  · exact u9461
  · exact u9462
  · exact u9463
  · exact u9464
  · exact u9465
  · exact u9466
  · exact u9467
  · exact u9468

def r9583 : Route 9 := (fun mask => (mask,id))

def c9583 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 24 => 4 | 264 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9583 : Upper (D 1) (R 1) [304,80] 13 := by
  apply FastRouting.sound _ _ [304,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r9583 c9583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9469
  · exact u9470
  · exact u9471
  · exact u9472
  · exact u9473
  · exact u9474
  · exact u9475
  · exact u9476
  · exact u9477
  · exact u9478
  · exact u9479
  · exact u9480
  · exact u9481
  · exact u9482
  · exact u9483

def r9584 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9584 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9584 : Upper (D 1) (R 1) [304,192] 13 := by
  apply FastRouting.sound _ _ [304,192] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192] r9584 c9584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9484
  · exact u9485
  · exact u9486
  · exact u9487
  · exact u9488
  · exact u9489
  · exact u9490
  · exact u9491
  · exact u9492
  · exact u9493
  · exact u9494
  · exact u9495

def r9585 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 384 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

def c9585 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9585 : Upper (D 1) (R 1) [14] 13 := by
  apply FastRouting.sound _ _ [14] 13 (by decide) (choices 2) [17,48,257,272] r9585 c9585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9496
  · exact u9497
  · exact u9498
  · exact u9499

def r9586 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9586 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9586 : Upper (D 1) (R 1) [22] 13 := by
  apply FastRouting.sound _ _ [22] 13 (by decide) (choices 2) [9,17,24,33,40,48,96,257,264,272,288] r9586 c9586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9500
  · exact u9501
  · exact u9502
  · exact u9503
  · exact u9504
  · exact u9505
  · exact u9506
  · exact u9507
  · exact u9508
  · exact u9509
  · exact u9510

def r9587 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9587 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9587 : Upper (D 1) (R 1) [28] 13 := by
  apply FastRouting.sound _ _ [28] 13 (by decide) (choices 2) [17,33,48,96,257,272,288] r9587 c9587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9511
  · exact u9512
  · exact u9513
  · exact u9514
  · exact u9515
  · exact u9516
  · exact u9517

def r9588 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9588 : Nat → Fin 9 := (fun _ => 0)

theorem u9588 : Upper (D 1) (R 1) [50] 13 := by
  apply FastRouting.sound _ _ [50] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192,257,260,272,320] r9588 c9588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9518
  · exact u9519
  · exact u9520
  · exact u9521
  · exact u9522
  · exact u9523
  · exact u9524
  · exact u9525
  · exact u9526
  · exact u9527
  · exact u9528
  · exact u9529
  · exact u9530

def r9589 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9589 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9589 : Upper (D 1) (R 1) [52] 13 := by
  apply FastRouting.sound _ _ [52] 13 (by decide) (choices 2) [9,17,24,48,65,72,80,192,257,264,272,320] r9589 c9589
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9531
  · exact u9532
  · exact u9533
  · exact u9534
  · exact u9535
  · exact u9536
  · exact u9537
  · exact u9538
  · exact u9539
  · exact u9540
  · exact u9541
  · exact u9542

def r9590 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 264 => (260,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9590 : Nat → Fin 9 := (fun _ => 0)

theorem u9590 : Upper (D 1) (R 1) [112] 13 := by
  apply FastRouting.sound _ _ [112] 13 (by decide) (choices 2) [5,12,17,20,48,129,132,144,257,260,272,384] r9590 c9590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9543
  · exact u9544
  · exact u9545
  · exact u9546
  · exact u9547
  · exact u9548
  · exact u9549
  · exact u9550
  · exact u9551
  · exact u9552
  · exact u9553
  · exact u9554

def r9591 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 136 => (24,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9591 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9591 : Upper (D 1) (R 1) [262] 13 := by
  apply FastRouting.sound _ _ [262] 13 (by decide) (choices 2) [9,17,24,48] r9591 c9591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9555
  · exact u9556
  · exact u9557
  · exact u9558

def r9592 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9592 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9592 : Upper (D 1) (R 1) [268] 13 := by
  apply FastRouting.sound _ _ [268] 13 (by decide) (choices 2) [17,48] r9592 c9592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9559
  · exact u9560

def r9593 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 72 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (36,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9593 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9593 : Upper (D 1) (R 1) [274] 13 := by
  apply FastRouting.sound _ _ [274] 13 (by decide) (choices 2) [5,12,17,20,33,36,48,96] r9593 c9593
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9561
  · exact u9562
  · exact u9563
  · exact u9564
  · exact u9565
  · exact u9566
  · exact u9567
  · exact u9568

def r9594 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9594 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9594 : Upper (D 1) (R 1) [276] 13 := by
  apply FastRouting.sound _ _ [276] 13 (by decide) (choices 2) [9,17,24,33,40,48,96] r9594 c9594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9569
  · exact u9570
  · exact u9571
  · exact u9572
  · exact u9573
  · exact u9574
  · exact u9575

def r9595 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 24 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 40 => (20,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9595 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 260 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9595 : Upper (D 1) (R 1) [304] 13 := by
  apply FastRouting.sound _ _ [304] 13 (by decide) (choices 2) [5,12,17,20,48,65,68,80,192] r9595 c9595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9576
  · exact u9577
  · exact u9578
  · exact u9579
  · exact u9580
  · exact u9581
  · exact u9582
  · exact u9583
  · exact u9584

def r9596 : Route 9 := (fun mask => match mask with | 38 => (22,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 70 => (22,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 134 => (22,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 26 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 42 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 74 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 138 => (22,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 266 => (262,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 82 => (50,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 146 => (50,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 98 => (50,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 162 => (50,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 290 => (274,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 194 => (50,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 322 => (274,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 386 => (274,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 44 => (28,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 76 => (28,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 140 => (28,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 84 => (52,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 148 => (52,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 100 => (52,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 164 => (52,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 292 => (276,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 196 => (52,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 324 => (276,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 388 => (276,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 56 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 88 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 6 | 6 => 5 | _ => i)) | 152 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | 5 => 7 | 7 => 5 | _ => i)) | 280 => (276,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 104 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 168 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 296 => (276,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | _ => i)) | 200 => (52,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 328 => (276,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 6 | 6 => 4 | _ => i)) | 392 => (276,(fun i => match i.val with | 2 => 3 | 3 => 2 | 4 => 7 | 7 => 4 | _ => i)) | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 336 => (304,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 400 => (304,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 224 => (112,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 352 => (304,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 416 => (304,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 448 => (304,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9596 : Nat → Fin 9 := (fun _ => 0)

theorem u9596 : Upper (D 1) (R 1) [] 13 := by
  apply FastRouting.sound _ _ [] 13 (by decide) (choices 3) [14,22,28,50,52,112,262,268,274,276,304] r9596 c9596
    (by exact cover_three)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9585
  · exact u9586
  · exact u9587
  · exact u9588
  · exact u9589
  · exact u9590
  · exact u9591
  · exact u9592
  · exact u9593
  · exact u9594
  · exact u9595

#print axioms u9596
end Delivery.IrregularNine14.P01
