import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0136
import IrregularNine14P08C0137
import IrregularNine14P08C0138
import IrregularNine14P08C0139

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19200 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 88 433 417 481 417 417), lower := (rows 35 7 76 88 16 32 64 128 256), losses := [] }

theorem u19200 : Upper (D 8) (R 8) [34,5,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19201 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 104 433 433 497 433 433), lower := (rows 35 7 76 104 16 32 64 128 256), losses := [] }

theorem u19201 : Upper (D 8) (R 8) [34,5,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19202 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 137 496 496 496 496 496), lower := (rows 35 7 76 137 16 32 64 128 256), losses := [] }

theorem u19202 : Upper (D 8) (R 8) [34,5,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19203 : Route 9 := (fun mask => (mask,id))

def c19203 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19203 : Upper (D 8) (R 8) [34,5,72,144] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19203 c19203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8188
  · exact u8189
  · exact u8190
  · exact u8191
  · exact u8192
  · exact u8193
  · exact u8194
  · exact u8195
  · exact u8196
  · exact u8197

def r19204 : Route 9 := (fun mask => (mask,id))

def c19204 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19204 : Upper (D 8) (R 8) [34,5,72,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19204 c19204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8198
  · exact u8199
  · exact u8200
  · exact u8201
  · exact u8202
  · exact u8203
  · exact u8204
  · exact u8205
  · exact u8206
  · exact u8207

def b19205 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 200 433 433 497 433 433), lower := (rows 35 7 76 200 16 32 64 128 256), losses := [] }

theorem u19205 : Upper (D 8) (R 8) [34,5,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19206 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 265 240 240 240 240 496), lower := (rows 35 7 76 265 16 32 64 128 256), losses := [] }

theorem u19206 : Upper (D 8) (R 8) [34,5,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19207 : Route 9 := (fun mask => (mask,id))

def c19207 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19207 : Upper (D 8) (R 8) [34,5,72,272] 13 := by
  apply FastRouting.sound _ _ [34,5,72,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19207 c19207
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8208
  · exact u8209
  · exact u8210
  · exact u8211
  · exact u8212
  · exact u8213

def r19208 : Route 9 := (fun mask => (mask,id))

def c19208 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19208 : Upper (D 8) (R 8) [34,5,72,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19208 c19208
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8214
  · exact u8215
  · exact u8216
  · exact u8217
  · exact u8218
  · exact u8219

def b19209 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 328 177 177 241 177 433), lower := (rows 35 7 76 328 16 32 64 128 256), losses := [] }

theorem u19209 : Upper (D 8) (R 8) [34,5,72,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19210 : Route 9 := (fun mask => (mask,id))

def c19210 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19210 : Upper (D 8) (R 8) [34,5,72,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19210 c19210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8220
  · exact u8221
  · exact u8222
  · exact u8223
  · exact u8224
  · exact u8225

def b19211 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 25 504 488 488 488 488), lower := (rows 35 7 196 25 16 32 64 128 256), losses := [] }

theorem u19211 : Upper (D 8) (R 8) [34,5,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19211 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19212 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 41 504 504 504 504 504), lower := (rows 35 7 196 41 16 32 64 128 256), losses := [] }

theorem u19212 : Upper (D 8) (R 8) [34,5,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19213_9 : Upper (D 8) (R 8) [34,5,192,48,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8226

theorem m19213_33 : Upper (D 8) (R 8) [34,5,192,48,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8232

def r19213 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19213 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19213 : Upper (D 8) (R 8) [34,5,192,48] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r19213 c19213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19213_9
  · exact m19213_33
  · exact u8238
  · exact u8239
  · exact u8240
  · exact u8241
  · exact u8242
  · exact u8243
  · exact u8244
  · exact u8245
  · exact u8246

def b19214 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 73 440 440 504 440 440), lower := (rows 35 7 196 73 16 32 64 128 256), losses := [] }

theorem u19214 : Upper (D 8) (R 8) [34,5,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19215_9 : Upper (D 8) (R 8) [34,5,192,80,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8227

theorem m19215_33 : Upper (D 8) (R 8) [34,5,192,80,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8233

theorem m19215_40 : Upper (D 8) (R 8) [34,5,192,80,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8240

theorem m19215_129 : Upper (D 8) (R 8) [34,5,192,80,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8247

def r19215 : Route 9 := (fun mask => (mask,id))

def c19215 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19215 : Upper (D 8) (R 8) [34,5,192,80] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19215 c19215
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19215_9
  · exact m19215_33
  · exact m19215_40
  · exact m19215_129
  · exact u8252
  · exact u8253
  · exact u8254
  · exact u8255
  · exact u8256
  · exact u8257

theorem m19216_9 : Upper (D 8) (R 8) [34,5,192,96,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8228

theorem m19216_33 : Upper (D 8) (R 8) [34,5,192,96,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8234

theorem m19216_40 : Upper (D 8) (R 8) [34,5,192,96,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8241

theorem m19216_129 : Upper (D 8) (R 8) [34,5,192,96,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8248

theorem m19216_136 : Upper (D 8) (R 8) [34,5,192,96,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8253

def r19216 : Route 9 := (fun mask => (mask,id))

def c19216 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19216 : Upper (D 8) (R 8) [34,5,192,96] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19216 c19216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19216_9
  · exact m19216_33
  · exact m19216_40
  · exact m19216_129
  · exact m19216_136
  · exact u8258
  · exact u8259
  · exact u8260
  · exact u8261
  · exact u8262

def b19217 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 313 313 377 441 313), lower := (rows 35 7 196 200 16 32 64 128 256), losses := [] }

theorem u19217 : Upper (D 8) (R 8) [34,5,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19218 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 265 248 248 248 248 504), lower := (rows 35 7 196 265 16 32 64 128 256), losses := [] }

theorem u19218 : Upper (D 8) (R 8) [34,5,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19219_9 : Upper (D 8) (R 8) [34,5,192,272,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8229

theorem m19219_33 : Upper (D 8) (R 8) [34,5,192,272,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8235

theorem m19219_40 : Upper (D 8) (R 8) [34,5,192,272,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8244

theorem m19219_65 : Upper (D 8) (R 8) [34,5,192,272,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8249

theorem m19219_72 : Upper (D 8) (R 8) [34,5,192,272,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8255

theorem m19219_96 : Upper (D 8) (R 8) [34,5,192,272,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8260

theorem m19219_192 : Upper (D 8) (R 8) [34,5,192,272,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8263

def r19219 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19219 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19219 : Upper (D 8) (R 8) [34,5,192,272] 13 := by
  apply FastRouting.sound _ _ [34,5,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19219 c19219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19219_9
  · exact m19219_33
  · exact m19219_40
  · exact m19219_65
  · exact m19219_72
  · exact m19219_96
  · exact m19219_192

theorem m19220_9 : Upper (D 8) (R 8) [34,5,192,288,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8230

theorem m19220_33 : Upper (D 8) (R 8) [34,5,192,288,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8236

theorem m19220_40 : Upper (D 8) (R 8) [34,5,192,288,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8245

theorem m19220_65 : Upper (D 8) (R 8) [34,5,192,288,65] 13 :=
  permutation_upper _ _ _ [34,5,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8250

theorem m19220_72 : Upper (D 8) (R 8) [34,5,192,288,72] 13 :=
  permutation_upper _ _ _ [34,5,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8256

theorem m19220_96 : Upper (D 8) (R 8) [34,5,192,288,96] 13 :=
  permutation_upper _ _ _ [34,5,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8261

theorem m19220_192 : Upper (D 8) (R 8) [34,5,192,288,192] 13 :=
  permutation_upper _ _ _ [34,5,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8264

def r19220 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19220 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19220 : Upper (D 8) (R 8) [34,5,192,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r19220 c19220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19220_9
  · exact m19220_33
  · exact m19220_40
  · exact m19220_65
  · exact m19220_72
  · exact m19220_96
  · exact m19220_192

theorem m19221_9 : Upper (D 8) (R 8) [34,5,192,320,9] 13 :=
  permutation_upper _ _ _ [34,5,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8231

theorem m19221_33 : Upper (D 8) (R 8) [34,5,192,320,33] 13 :=
  permutation_upper _ _ _ [34,5,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8237

theorem m19221_40 : Upper (D 8) (R 8) [34,5,192,320,40] 13 :=
  permutation_upper _ _ _ [34,5,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8246

theorem m19221_129 : Upper (D 8) (R 8) [34,5,192,320,129] 13 :=
  permutation_upper _ _ _ [34,5,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8251

theorem m19221_136 : Upper (D 8) (R 8) [34,5,192,320,136] 13 :=
  permutation_upper _ _ _ [34,5,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8257

theorem m19221_160 : Upper (D 8) (R 8) [34,5,192,320,160] 13 :=
  permutation_upper _ _ _ [34,5,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8262

def r19221 : Route 9 := (fun mask => (mask,id))

def c19221 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19221 : Upper (D 8) (R 8) [34,5,192,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19221 c19221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19221_9
  · exact m19221_33
  · exact m19221_40
  · exact m19221_129
  · exact m19221_136
  · exact m19221_160

def b19222 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 25 240 224 224 224 480), lower := (rows 35 7 268 25 16 32 64 128 256), losses := [] }

theorem u19222 : Upper (D 8) (R 8) [34,5,264,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19223 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 268 41 240 240 240 240 496), lower := (rows 35 7 268 41 16 32 64 128 256), losses := [] }

theorem u19223 : Upper (D 8) (R 8) [34,5,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19224 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19224 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19224 : Upper (D 8) (R 8) [34,5,264,48] 13 := by
  apply FastRouting.sound _ _ [34,5,264,48] 13 (by decide) (choices 2) [33,65,96,192] r19224 c19224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8265
  · exact u8266
  · exact u8267
  · exact u8268

def b19225 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 268 73 240 240 240 240 496), lower := (rows 35 7 268 73 16 32 64 128 256), losses := [] }

theorem u19225 : Upper (D 8) (R 8) [34,5,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19226 : Route 9 := (fun mask => (mask,id))

def c19226 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19226 : Upper (D 8) (R 8) [34,5,264,80] 13 := by
  apply FastRouting.sound _ _ [34,5,264,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19226 c19226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8269
  · exact u8270
  · exact u8271
  · exact u8272
  · exact u8273
  · exact u8274

def r19227 : Route 9 := (fun mask => (mask,id))

def c19227 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19227 : Upper (D 8) (R 8) [34,5,264,96] 13 := by
  apply FastRouting.sound _ _ [34,5,264,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19227 c19227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8275
  · exact u8276
  · exact u8277
  · exact u8278
  · exact u8279
  · exact u8280

def r19228 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19228 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19228 : Upper (D 8) (R 8) [34,5,264,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,192] 13 (by decide) (choices 2) [33,65,96,192] r19228 c19228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8281
  · exact u8282
  · exact u8283
  · exact u8284

def b19229 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 25 248 232 232 232 488), lower := (rows 35 7 324 25 16 32 64 128 256), losses := [] }

theorem u19229 : Upper (D 8) (R 8) [34,5,320,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19230 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 41 248 248 248 248 504), lower := (rows 35 7 324 41 16 32 64 128 256), losses := [] }

theorem u19230 : Upper (D 8) (R 8) [34,5,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19231_9 : Upper (D 8) (R 8) [34,5,320,48,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8285

theorem m19231_33 : Upper (D 8) (R 8) [34,5,320,48,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8291

def r19231 : Route 9 := (fun mask => (mask,id))

def c19231 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19231 : Upper (D 8) (R 8) [34,5,320,48] 13 := by
  apply FastRouting.sound _ _ [34,5,320,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19231 c19231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19231_9
  · exact m19231_33
  · exact u8297
  · exact u8298
  · exact u8299
  · exact u8300
  · exact u8301
  · exact u8302
  · exact u8303
  · exact u8304

def b19232 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 73 184 184 248 184 440), lower := (rows 35 7 324 73 16 32 64 128 256), losses := [] }

theorem u19232 : Upper (D 8) (R 8) [34,5,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19233_9 : Upper (D 8) (R 8) [34,5,320,80,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8286

theorem m19233_33 : Upper (D 8) (R 8) [34,5,320,80,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8292

theorem m19233_40 : Upper (D 8) (R 8) [34,5,320,80,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8299

def r19233 : Route 9 := (fun mask => (mask,id))

def c19233 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19233 : Upper (D 8) (R 8) [34,5,320,80] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19233 c19233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19233_9
  · exact m19233_33
  · exact m19233_40
  · exact u8307
  · exact u8308
  · exact u8309

theorem m19234_9 : Upper (D 8) (R 8) [34,5,320,96,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8287

theorem m19234_33 : Upper (D 8) (R 8) [34,5,320,96,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8293

theorem m19234_40 : Upper (D 8) (R 8) [34,5,320,96,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8300

def r19234 : Route 9 := (fun mask => (mask,id))

def c19234 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19234 : Upper (D 8) (R 8) [34,5,320,96] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19234 c19234
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19234_9
  · exact m19234_33
  · exact m19234_40
  · exact u8310
  · exact u8311
  · exact u8312

def b19235 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 137 248 248 248 248 504), lower := (rows 35 7 324 137 16 32 64 128 256), losses := [] }

theorem u19235 : Upper (D 8) (R 8) [34,5,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19236_9 : Upper (D 8) (R 8) [34,5,320,144,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8288

theorem m19236_33 : Upper (D 8) (R 8) [34,5,320,144,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8294

theorem m19236_40 : Upper (D 8) (R 8) [34,5,320,144,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8302

theorem m19236_65 : Upper (D 8) (R 8) [34,5,320,144,65] 13 :=
  permutation_upper _ _ _ [34,5,320,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8305

theorem m19236_72 : Upper (D 8) (R 8) [34,5,320,144,72] 13 :=
  permutation_upper _ _ _ [34,5,320,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8308

theorem m19236_96 : Upper (D 8) (R 8) [34,5,320,144,96] 13 :=
  permutation_upper _ _ _ [34,5,320,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8311

theorem m19236_129 : Upper (D 8) (R 8) [34,5,320,144,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8313

def r19236 : Route 9 := (fun mask => (mask,id))

def c19236 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19236 : Upper (D 8) (R 8) [34,5,320,144] 13 := by
  apply FastRouting.sound _ _ [34,5,320,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19236 c19236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19236_9
  · exact m19236_33
  · exact m19236_40
  · exact m19236_65
  · exact m19236_72
  · exact m19236_96
  · exact m19236_129
  · exact u8316
  · exact u8317
  · exact u8318

theorem m19237_9 : Upper (D 8) (R 8) [34,5,320,160,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8289

theorem m19237_33 : Upper (D 8) (R 8) [34,5,320,160,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8295

theorem m19237_40 : Upper (D 8) (R 8) [34,5,320,160,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8303

theorem m19237_65 : Upper (D 8) (R 8) [34,5,320,160,65] 13 :=
  permutation_upper _ _ _ [34,5,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8306

theorem m19237_72 : Upper (D 8) (R 8) [34,5,320,160,72] 13 :=
  permutation_upper _ _ _ [34,5,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8309

theorem m19237_96 : Upper (D 8) (R 8) [34,5,320,160,96] 13 :=
  permutation_upper _ _ _ [34,5,320,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8312

theorem m19237_129 : Upper (D 8) (R 8) [34,5,320,160,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8314

theorem m19237_136 : Upper (D 8) (R 8) [34,5,320,160,136] 13 :=
  permutation_upper _ _ _ [34,5,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8317

def r19237 : Route 9 := (fun mask => (mask,id))

def c19237 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19237 : Upper (D 8) (R 8) [34,5,320,160] 13 := by
  apply FastRouting.sound _ _ [34,5,320,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19237 c19237
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19237_9
  · exact m19237_33
  · exact m19237_40
  · exact m19237_65
  · exact m19237_72
  · exact m19237_96
  · exact m19237_129
  · exact m19237_136
  · exact u8319
  · exact u8320

theorem m19238_9 : Upper (D 8) (R 8) [34,5,320,192,9] 13 :=
  permutation_upper _ _ _ [34,5,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8290

theorem m19238_33 : Upper (D 8) (R 8) [34,5,320,192,33] 13 :=
  permutation_upper _ _ _ [34,5,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8296

theorem m19238_40 : Upper (D 8) (R 8) [34,5,320,192,40] 13 :=
  permutation_upper _ _ _ [34,5,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8304

theorem m19238_129 : Upper (D 8) (R 8) [34,5,320,192,129] 13 :=
  permutation_upper _ _ _ [34,5,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8315

theorem m19238_136 : Upper (D 8) (R 8) [34,5,320,192,136] 13 :=
  permutation_upper _ _ _ [34,5,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8318

theorem m19238_160 : Upper (D 8) (R 8) [34,5,320,192,160] 13 :=
  permutation_upper _ _ _ [34,5,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8320

def r19238 : Route 9 := (fun mask => (mask,id))

def c19238 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19238 : Upper (D 8) (R 8) [34,5,320,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19238 c19238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19238_9
  · exact m19238_33
  · exact m19238_40
  · exact m19238_129
  · exact m19238_136
  · exact m19238_160

def b19239 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 21 41 496 480 480 480 480), lower := (rows 35 14 21 41 16 32 64 128 256), losses := [] }

theorem u19239 : Upper (D 8) (R 8) [34,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19240 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 21 73 496 480 480 480 480), lower := (rows 35 14 21 73 16 32 64 128 256), losses := [] }

theorem u19240 : Upper (D 8) (R 8) [34,12,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19241 : Route 9 := (fun mask => (mask,id))

def c19241 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19241 : Upper (D 8) (R 8) [34,12,17,96] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19241 c19241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8321
  · exact u8322
  · exact u8323
  · exact u8324
  · exact u8325
  · exact u8326
  · exact u8327
  · exact u8328
  · exact u8329
  · exact u8330

def r19242 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19242 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19242 : Upper (D 8) (R 8) [34,12,17,192] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r19242 c19242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8331
  · exact u8332
  · exact u8333
  · exact u8334
  · exact u8335
  · exact u8336
  · exact u8337

def b19243 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 21 265 240 224 224 224 480), lower := (rows 35 14 21 265 16 32 64 128 256), losses := [] }

theorem u19243 : Upper (D 8) (R 8) [34,12,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19244 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19244 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19244 : Upper (D 8) (R 8) [34,12,17,288] 13 := by
  apply FastRouting.sound _ _ [34,12,17,288] 13 (by decide) (choices 2) [33,65,96,192] r19244 c19244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8338
  · exact u8339
  · exact u8340
  · exact u8341

def r19245 : Route 9 := (fun mask => (mask,id))

def c19245 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19245 : Upper (D 8) (R 8) [34,12,17,320] 13 := by
  apply FastRouting.sound _ _ [34,12,17,320] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19245 c19245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8342
  · exact u8343
  · exact u8344
  · exact u8345
  · exact u8346
  · exact u8347

def b19246 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 37 56 465 481 449 449 449), lower := (rows 35 14 37 56 16 32 64 128 256), losses := [] }

theorem u19246 : Upper (D 8) (R 8) [34,12,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19247 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 73 496 496 496 496 496), lower := (rows 35 14 37 73 16 32 64 128 256), losses := [] }

theorem u19247 : Upper (D 8) (R 8) [34,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19248 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 88 497 481 481 481 481), lower := (rows 35 14 37 88 16 32 64 128 256), losses := [] }

theorem u19248 : Upper (D 8) (R 8) [34,12,33,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19249 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 37 104 465 497 465 465 465), lower := (rows 35 14 37 104 16 32 64 128 256), losses := [] }

theorem u19249 : Upper (D 8) (R 8) [34,12,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19250 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 200 497 497 497 497 497), lower := (rows 35 14 37 200 16 32 64 128 256), losses := [] }

theorem u19250 : Upper (D 8) (R 8) [34,12,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19251 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 265 240 240 240 240 496), lower := (rows 35 14 37 265 16 32 64 128 256), losses := [] }

theorem u19251 : Upper (D 8) (R 8) [34,12,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19252 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 280 241 225 225 225 481), lower := (rows 35 14 37 280 16 32 64 128 256), losses := [] }

theorem u19252 : Upper (D 8) (R 8) [34,12,33,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19253 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 37 296 209 241 209 209 465), lower := (rows 35 14 37 296 16 32 64 128 256), losses := [] }

theorem u19253 : Upper (D 8) (R 8) [34,12,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19254 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 37 328 241 241 241 241 497), lower := (rows 35 14 37 328 16 32 64 128 256), losses := [] }

theorem u19254 : Upper (D 8) (R 8) [34,12,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19255 : Route 9 := (fun mask => (mask,id))

def c19255 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19255 : Upper (D 8) (R 8) [34,12,48,65] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19255 c19255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8348
  · exact u8349
  · exact u8350
  · exact u8351
  · exact u8352
  · exact u8353
  · exact u8354
  · exact u8355
  · exact u8356
  · exact u8357

def b19256 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 52 104 465 481 449 449 449), lower := (rows 35 14 52 104 16 32 64 128 256), losses := [] }

theorem u19256 : Upper (D 8) (R 8) [34,12,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19257 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19257 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19257 : Upper (D 8) (R 8) [34,12,48,192] 13 := by
  apply FastRouting.sound _ _ [34,12,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r19257 c19257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8358
  · exact u8359
  · exact u8360
  · exact u8361
  · exact u8362
  · exact u8363
  · exact u8364

def r19258 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c19258 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19258 : Upper (D 8) (R 8) [34,12,48,257] 13 := by
  apply FastRouting.sound _ _ [34,12,48,257] 13 (by decide) (choices 2) [33,65,96,192] r19258 c19258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8365
  · exact u8366
  · exact u8367
  · exact u8368

def b19259 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 14 52 296 209 225 193 193 449), lower := (rows 35 14 52 296 16 32 64 128 256), losses := [] }

theorem u19259 : Upper (D 8) (R 8) [34,12,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19259
end Delivery.IrregularNine14.P08
