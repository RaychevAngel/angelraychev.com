import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0387
import IrregularNine14P07C0388
import IrregularNine14P07C0389

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37140 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,7)], upper := (rows 37 74 134 152 112 291 323 387 259), lower := (rows 37 74 134 152 112 32 64 128 256), losses := [] }

theorem u37140 : Upper (D 7) (R 7) [36,72,130,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37141 : Route 9 := (fun mask => (mask,id))

def c37141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37141 : Upper (D 7) (R 7) [36,72,130,144,257] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,257] 13 (by decide) (choices 1) [1,2,64] r37141 c37141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23257
  · exact u23258
  · exact u23259

def r37142 : Route 9 := (fun mask => (mask,id))

def c37142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37142 : Upper (D 7) (R 7) [36,72,130,144,258] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,258] 13 (by decide) (choices 1) [1,64] r37142 c37142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23260
  · exact u23261

def r37143 : Route 9 := (fun mask => (mask,id))

def c37143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37143 : Upper (D 7) (R 7) [36,72,130,144,288] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,288] 13 (by decide) (choices 1) [1,2,64] r37143 c37143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23262
  · exact u23263
  · exact u23264

def b37144 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,7)], upper := (rows 37 74 134 152 336 35 99 163 291), lower := (rows 37 74 134 152 336 32 64 128 256), losses := [] }

theorem u37144 : Upper (D 7) (R 7) [36,72,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37145 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 452, targets := 32 }], pairs := [(0,7),(2,5),(3,1),(4,7)], upper := (rows 37 74 134 168 19 369 337 465 337), lower := (rows 37 74 134 168 19 32 64 128 256), losses := [] }

theorem u37145 : Upper (D 7) (R 7) [36,72,130,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37146 : Route 9 := (fun mask => (mask,id))

def c37146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37146 : Upper (D 7) (R 7) [36,72,130,160,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,65] 13 (by decide) (choices 1) [1,2,16,256] r37146 c37146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23265
  · exact u23266
  · exact u23267
  · exact u23268

def b37147 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 168 82 305 337 401 273), lower := (rows 37 74 134 168 82 32 64 128 256), losses := [] }

theorem u37147 : Upper (D 7) (R 7) [36,72,130,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37148 : Route 9 := (fun mask => (mask,id))

def c37148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37148 : Upper (D 7) (R 7) [36,72,130,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,257] 13 (by decide) (choices 1) [1,2,16,64] r37148 c37148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23269
  · exact u23270
  · exact u23271
  · exact u23272

def r37149 : Route 9 := (fun mask => (mask,id))

def c37149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37149 : Upper (D 7) (R 7) [36,72,130,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,258] 13 (by decide) (choices 1) [1,16,64] r37149 c37149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23273
  · exact u23274
  · exact u23275

def r37150 : Route 9 := (fun mask => (mask,id))

def c37150 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37150 : Upper (D 7) (R 7) [36,72,130,160,320] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,320] 13 (by decide) (choices 1) [1,2,16] r37150 c37150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23276
  · exact u23277
  · exact u23278

def r37151 : Route 9 := (fun mask => (mask,id))

def c37151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37151 : Upper (D 7) (R 7) [36,72,130,257,3] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,3] 13 (by decide) (choices 1) [16,64,128] r37151 c37151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23279
  · exact u23280
  · exact u23281

def b37152 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 134 265 49 242 210 210 466), lower := (rows 37 74 134 265 49 32 64 128 256), losses := [] }

theorem u37152 : Upper (D 7) (R 7) [36,72,130,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37153 : Route 9 := (fun mask => (mask,id))

def c37153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37153 : Upper (D 7) (R 7) [36,72,130,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,34] 13 (by decide) (choices 1) [1,16,64,128] r37153 c37153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23282
  · exact u23283
  · exact u23284
  · exact u23285

def r37154 : Route 9 := (fun mask => (mask,id))

def c37154 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37154 : Upper (D 7) (R 7) [36,72,130,257,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,65] 13 (by decide) (choices 1) [2,16,128] r37154 c37154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23286
  · exact u23287
  · exact u23288

def b37155 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 265 82 177 241 177 433), lower := (rows 37 74 134 265 82 32 64 128 256), losses := [] }

theorem u37155 : Upper (D 7) (R 7) [36,72,130,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37156 : Route 9 := (fun mask => (mask,id))

def c37156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37156 : Upper (D 7) (R 7) [36,72,130,257,96] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,96] 13 (by decide) (choices 1) [1,2,16,128] r37156 c37156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23289
  · exact u23290
  · exact u23291
  · exact u23292

def r37157 : Route 9 := (fun mask => (mask,id))

def c37157 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37157 : Upper (D 7) (R 7) [36,72,130,257,129] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,129] 13 (by decide) (choices 1) [2,16,64] r37157 c37157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23293
  · exact u23294
  · exact u23295

def b37158 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 134 265 146 113 113 241 369), lower := (rows 37 74 134 265 146 32 64 128 256), losses := [] }

theorem u37158 : Upper (D 7) (R 7) [36,72,130,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37159 : Route 9 := (fun mask => (mask,id))

def c37159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37159 : Upper (D 7) (R 7) [36,72,130,257,160] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,160] 13 (by decide) (choices 1) [1,2,16,64] r37159 c37159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23296
  · exact u23297
  · exact u23298
  · exact u23299

def r37160 : Route 9 := (fun mask => (mask,id))

def c37160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37160 : Upper (D 7) (R 7) [36,72,130,257,192] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,192] 13 (by decide) (choices 1) [1,2,16] r37160 c37160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23300
  · exact u23301
  · exact u23302

def b37161 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 74 134 266 49 241 209 209 465), lower := (rows 37 74 134 266 49 32 64 128 256), losses := [] }

theorem u37161 : Upper (D 7) (R 7) [36,72,130,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37162 : Route 9 := (fun mask => (mask,id))

def c37162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37162 : Upper (D 7) (R 7) [36,72,130,258,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258,65] 13 (by decide) (choices 1) [1,16,128] r37162 c37162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23303
  · exact u23304
  · exact u23305

def r37163 : Route 9 := (fun mask => (mask,id))

def c37163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37163 : Upper (D 7) (R 7) [36,72,130,258,96] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258,96] 13 (by decide) (choices 1) [1,16,128] r37163 c37163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23306
  · exact u23307
  · exact u23308

def b37164 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 134 266 145 113 113 241 369), lower := (rows 37 74 134 266 145 32 64 128 256), losses := [] }

theorem u37164 : Upper (D 7) (R 7) [36,72,130,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37165 : Route 9 := (fun mask => (mask,id))

def c37165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37165 : Upper (D 7) (R 7) [36,72,130,258,160] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258,160] 13 (by decide) (choices 1) [1,16,64] r37165 c37165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23309
  · exact u23310
  · exact u23311

def r37166 : Route 9 := (fun mask => (mask,id))

def c37166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37166 : Upper (D 7) (R 7) [36,72,130,258,192] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258,192] 13 (by decide) (choices 1) [1,16] r37166 c37166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23312
  · exact u23313

def r37167 : Route 9 := (fun mask => (mask,id))

def c37167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37167 : Upper (D 7) (R 7) [36,72,130,272,3] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,3] 13 (by decide) (choices 1) [1,64,128] r37167 c37167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23314
  · exact u23315
  · exact u23316

def b37168 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 134 280 49 227 195 195 451), lower := (rows 37 74 134 280 49 32 64 128 256), losses := [] }

theorem u37168 : Upper (D 7) (R 7) [36,72,130,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37169 : Route 9 := (fun mask => (mask,id))

def c37169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37169 : Upper (D 7) (R 7) [36,72,130,272,34] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,34] 13 (by decide) (choices 1) [1,64,128] r37169 c37169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23317
  · exact u23318
  · exact u23319

def r37170 : Route 9 := (fun mask => (mask,id))

def c37170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37170 : Upper (D 7) (R 7) [36,72,130,272,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,65] 13 (by decide) (choices 1) [1,2,128] r37170 c37170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23320
  · exact u23321
  · exact u23322

def b37171 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 280 82 161 225 161 417), lower := (rows 37 74 134 280 82 32 64 128 256), losses := [] }

theorem u37171 : Upper (D 7) (R 7) [36,72,130,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37172 : Route 9 := (fun mask => (mask,id))

def c37172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37172 : Upper (D 7) (R 7) [36,72,130,272,96] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,96] 13 (by decide) (choices 1) [1,2,128] r37172 c37172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23323
  · exact u23324
  · exact u23325

def r37173 : Route 9 := (fun mask => (mask,id))

def c37173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37173 : Upper (D 7) (R 7) [36,72,130,272,129] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,129] 13 (by decide) (choices 1) [1,2,64] r37173 c37173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23326
  · exact u23327
  · exact u23328

def b37174 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 134 280 146 97 97 225 353), lower := (rows 37 74 134 280 146 32 64 128 256), losses := [] }

theorem u37174 : Upper (D 7) (R 7) [36,72,130,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37175 : Route 9 := (fun mask => (mask,id))

def c37175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37175 : Upper (D 7) (R 7) [36,72,130,272,160] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,160] 13 (by decide) (choices 1) [1,2,64] r37175 c37175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23329
  · exact u23330
  · exact u23331

def r37176 : Route 9 := (fun mask => (mask,id))

def c37176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37176 : Upper (D 7) (R 7) [36,72,130,272,192] 13 := by
  apply FastRouting.sound _ _ [36,72,130,272,192] 13 (by decide) (choices 1) [1,2] r37176 c37176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23332
  · exact u23333

def r37177 : Route 9 := (fun mask => (mask,id))

def c37177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37177 : Upper (D 7) (R 7) [36,72,130,288,3] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,3] 13 (by decide) (choices 1) [1,16,64,128] r37177 c37177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23334
  · exact u23335
  · exact u23336
  · exact u23337

def r37178 : Route 9 := (fun mask => (mask,id))

def c37178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37178 : Upper (D 7) (R 7) [36,72,130,288,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,65] 13 (by decide) (choices 1) [1,2,16,128] r37178 c37178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23338
  · exact u23339
  · exact u23340
  · exact u23341

def b37179 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 296 82 177 209 145 401), lower := (rows 37 74 134 296 82 32 64 128 256), losses := [] }

theorem u37179 : Upper (D 7) (R 7) [36,72,130,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37180 : Route 9 := (fun mask => (mask,id))

def c37180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37180 : Upper (D 7) (R 7) [36,72,130,288,129] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,129] 13 (by decide) (choices 1) [1,2,16,64] r37180 c37180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23342
  · exact u23343
  · exact u23344
  · exact u23345

def b37181 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 97 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,6)], upper := (rows 37 74 134 296 146 113 81 209 337), lower := (rows 37 74 134 296 146 32 64 128 256), losses := [] }

theorem u37181 : Upper (D 7) (R 7) [36,72,130,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37182 : Route 9 := (fun mask => (mask,id))

def c37182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37182 : Upper (D 7) (R 7) [36,72,130,288,192] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,192] 13 (by decide) (choices 1) [1,2,16] r37182 c37182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23346
  · exact u23347
  · exact u23348

def r37183 : Route 9 := (fun mask => (mask,id))

def c37183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37183 : Upper (D 7) (R 7) [36,72,130,384,3] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384,3] 13 (by decide) (choices 1) [1,16,64] r37183 c37183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23349
  · exact u23350
  · exact u23351

def b37184 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 134 392 49 115 83 211 339), lower := (rows 37 74 134 392 49 32 64 128 256), losses := [] }

theorem u37184 : Upper (D 7) (R 7) [36,72,130,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37185 : Route 9 := (fun mask => (mask,id))

def c37185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37185 : Upper (D 7) (R 7) [36,72,130,384,34] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384,34] 13 (by decide) (choices 1) [1,16,64] r37185 c37185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23352
  · exact u23353
  · exact u23354

def r37186 : Route 9 := (fun mask => (mask,id))

def c37186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37186 : Upper (D 7) (R 7) [36,72,130,384,65] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384,65] 13 (by decide) (choices 1) [1,2,16] r37186 c37186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23355
  · exact u23356
  · exact u23357

def b37187 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 134 392 82 49 113 177 305), lower := (rows 37 74 134 392 82 32 64 128 256), losses := [] }

theorem u37187 : Upper (D 7) (R 7) [36,72,130,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37188 : Route 9 := (fun mask => (mask,id))

def c37188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37188 : Upper (D 7) (R 7) [36,72,130,384,96] 13 := by
  apply FastRouting.sound _ _ [36,72,130,384,96] 13 (by decide) (choices 1) [1,2,16] r37188 c37188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23358
  · exact u23359
  · exact u23360

def r37189 : Route 9 := (fun mask => (mask,id))

def c37189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37189 : Upper (D 7) (R 7) [36,72,144,160,3] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,3] 13 (by decide) (choices 1) [1,2,64,256] r37189 c37189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23361
  · exact u23362
  · exact u23363
  · exact u23364

def r37190 : Route 9 := (fun mask => (mask,id))

def c37190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37190 : Upper (D 7) (R 7) [36,72,144,160,65] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,65] 13 (by decide) (choices 1) [1,2,256] r37190 c37190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23365
  · exact u23366
  · exact u23367

def b37191 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 148 168 82 291 323 387 259), lower := (rows 37 74 148 168 82 32 64 128 256), losses := [] }

theorem u37191 : Upper (D 7) (R 7) [36,72,144,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37192 : Route 9 := (fun mask => (mask,id))

def c37192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37192 : Upper (D 7) (R 7) [36,72,144,160,257] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,257] 13 (by decide) (choices 1) [1,2,64] r37192 c37192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23368
  · exact u23369
  · exact u23370

def r37193 : Route 9 := (fun mask => (mask,id))

def c37193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37193 : Upper (D 7) (R 7) [36,72,144,160,258] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,258] 13 (by decide) (choices 1) [1,2,64] r37193 c37193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23371
  · exact u23372
  · exact u23373

def r37194 : Route 9 := (fun mask => (mask,id))

def c37194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37194 : Upper (D 7) (R 7) [36,72,144,160,320] 13 := by
  apply FastRouting.sound _ _ [36,72,144,160,320] 13 (by decide) (choices 1) [1,2] r37194 c37194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23374
  · exact u23375

def r37195 : Route 9 := (fun mask => (mask,id))

def c37195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37195 : Upper (D 7) (R 7) [36,72,144,257,3] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,3] 13 (by decide) (choices 1) [2,64,128] r37195 c37195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23376
  · exact u23377
  · exact u23378

def b37196 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 74 148 265 49 226 194 194 450), lower := (rows 37 74 148 265 49 32 64 128 256), losses := [] }

theorem u37196 : Upper (D 7) (R 7) [36,72,144,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37197 : Route 9 := (fun mask => (mask,id))

def c37197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37197 : Upper (D 7) (R 7) [36,72,144,257,34] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,34] 13 (by decide) (choices 1) [1,2,64,128] r37197 c37197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23379
  · exact u23380
  · exact u23381
  · exact u23382

def r37198 : Route 9 := (fun mask => (mask,id))

def c37198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37198 : Upper (D 7) (R 7) [36,72,144,257,65] 13 := by
  apply FastRouting.sound _ _ [36,72,144,257,65] 13 (by decide) (choices 1) [2,128] r37198 c37198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23383
  · exact u23384

def b37199 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 74 148 265 82 163 227 163 419), lower := (rows 37 74 148 265 82 32 64 128 256), losses := [] }

theorem u37199 : Upper (D 7) (R 7) [36,72,144,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37199
end Delivery.IrregularNine14.P07
