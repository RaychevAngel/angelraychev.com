import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0421
import IrregularNine14P07C0422
import IrregularNine14P07C0423

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38160 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 26 50 417 449 385 385), lower := (rows 37 194 76 26 50 32 64 128 256), losses := [] }

theorem u38160 : Upper (D 7) (R 7) [36,192,72,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38161 : Route 9 := (fun mask => (mask,id))

def c38161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38161 : Upper (D 7) (R 7) [36,192,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,129] 13 (by decide) (choices 1) [1,2,256] r38161 c38161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25280
  · exact u25281
  · exact u25282

def b38162 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 28, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 194 76 26 146 289 353 417 289), lower := (rows 37 194 76 26 146 32 64 128 256), losses := [] }

theorem u38162 : Upper (D 7) (R 7) [36,192,72,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38163 : Route 9 := (fun mask => (mask,id))

def c38163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38163 : Upper (D 7) (R 7) [36,192,72,18,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,160] 13 (by decide) (choices 1) [1,2,256] r38163 c38163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25283
  · exact u25284
  · exact u25285

def r38164 : Route 9 := (fun mask => (mask,id))

def c38164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38164 : Upper (D 7) (R 7) [36,192,72,18,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,257] 13 (by decide) (choices 1) [1,2,128] r38164 c38164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25286
  · exact u25287
  · exact u25288

def b38165 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 194 76 26 274 161 225 161 417), lower := (rows 37 194 76 26 274 32 64 128 256), losses := [] }

theorem u38165 : Upper (D 7) (R 7) [36,192,72,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38166 : Route 9 := (fun mask => (mask,id))

def c38166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38166 : Upper (D 7) (R 7) [36,192,72,18,288] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,288] 13 (by decide) (choices 1) [1,2,128] r38166 c38166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25289
  · exact u25290
  · exact u25291

def r38167 : Route 9 := (fun mask => (mask,id))

def c38167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38167 : Upper (D 7) (R 7) [36,192,72,18,384] 13 := by
  apply FastRouting.sound _ _ [36,192,72,18,384] 13 (by decide) (choices 1) [1,2] r38167 c38167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25292
  · exact u25293

def r38168 : Route 9 := (fun mask => (mask,id))

def c38168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u38168 : Upper (D 7) (R 7) [36,192,72,34,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,3] 13 (by decide) (choices 1) [1,16,128,256] r38168 c38168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25294
  · exact u25295
  · exact u25296
  · exact u25297

def r38169 : Route 9 := (fun mask => (mask,id))

def c38169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38169 : Upper (D 7) (R 7) [36,192,72,34,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,129] 13 (by decide) (choices 1) [1,2,16,256] r38169 c38169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25298
  · exact u25299
  · exact u25300
  · exact u25301

def b38170 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 42 146 305 337 401 273), lower := (rows 37 194 76 42 146 32 64 128 256), losses := [] }

theorem u38170 : Upper (D 7) (R 7) [36,192,72,34,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38171 : Route 9 := (fun mask => (mask,id))

def c38171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38171 : Upper (D 7) (R 7) [36,192,72,34,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,257] 13 (by decide) (choices 1) [1,2,16,128] r38171 c38171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25302
  · exact u25303
  · exact u25304
  · exact u25305

def r38172 : Route 9 := (fun mask => (mask,id))

def c38172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38172 : Upper (D 7) (R 7) [36,192,72,34,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,258] 13 (by decide) (choices 1) [1,16,128] r38172 c38172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25306
  · exact u25307
  · exact u25308

def r38173 : Route 9 := (fun mask => (mask,id))

def c38173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38173 : Upper (D 7) (R 7) [36,192,72,34,384] 13 := by
  apply FastRouting.sound _ _ [36,192,72,34,384] 13 (by decide) (choices 1) [1,2,16] r38173 c38173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25309
  · exact u25310
  · exact u25311

def b38174 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 37 194 76 56 19 419 451 387 387), lower := (rows 37 194 76 56 19 32 64 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 194 78 478 467 0 64 128 256) }] }

theorem u38174 : Upper (D 7) (R 7) [36,192,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38175 : Route 9 := (fun mask => (mask,id))

def c38175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38175 : Upper (D 7) (R 7) [36,192,72,48,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,129] 13 (by decide) (choices 1) [1,2,256] r38175 c38175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25312
  · exact u25313
  · exact u25314

def b38176 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 56 146 291 323 387 259), lower := (rows 37 194 76 56 146 32 64 128 256), losses := [] }

theorem u38176 : Upper (D 7) (R 7) [36,192,72,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38177 : Route 9 := (fun mask => (mask,id))

def c38177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38177 : Upper (D 7) (R 7) [36,192,72,48,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,257] 13 (by decide) (choices 1) [1,2,128] r38177 c38177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25315
  · exact u25316
  · exact u25317

def r38178 : Route 9 := (fun mask => (mask,id))

def c38178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38178 : Upper (D 7) (R 7) [36,192,72,48,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,258] 13 (by decide) (choices 1) [1,2,128] r38178 c38178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25318
  · exact u25319
  · exact u25320

def r38179 : Route 9 := (fun mask => (mask,id))

def c38179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38179 : Upper (D 7) (R 7) [36,192,72,48,384] 13 := by
  apply FastRouting.sound _ _ [36,192,72,48,384] 13 (by decide) (choices 1) [1,2] r38179 c38179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25321
  · exact u25322

def r38180 : Route 9 := (fun mask => (mask,id))

def c38180 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38180 : Upper (D 7) (R 7) [36,192,72,129,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,3] 13 (by decide) (choices 1) [2,16,256] r38180 c38180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25323
  · exact u25324
  · exact u25325

def b38181 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 137 49 306 338 402 274), lower := (rows 37 194 76 137 49 32 64 128 256), losses := [] }

theorem u38181 : Upper (D 7) (R 7) [36,192,72,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38182 : Route 9 := (fun mask => (mask,id))

def c38182 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38182 : Upper (D 7) (R 7) [36,192,72,129,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,34] 13 (by decide) (choices 1) [1,2,16,256] r38182 c38182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25326
  · exact u25327
  · exact u25328
  · exact u25329

def r38183 : Route 9 := (fun mask => (mask,id))

def c38183 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38183 : Upper (D 7) (R 7) [36,192,72,129,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,257] 13 (by decide) (choices 1) [2,16] r38183 c38183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25330
  · exact u25331

def r38184 : Route 9 := (fun mask => (mask,id))

def c38184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38184 : Upper (D 7) (R 7) [36,192,72,129,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,258] 13 (by decide) (choices 1) [1,2,16] r38184 c38184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25332
  · exact u25333
  · exact u25334

def r38185 : Route 9 := (fun mask => (mask,id))

def c38185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38185 : Upper (D 7) (R 7) [36,192,72,129,288] 13 := by
  apply FastRouting.sound _ _ [36,192,72,129,288] 13 (by decide) (choices 1) [1,2,16] r38185 c38185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25335
  · exact u25336
  · exact u25337

def r38186 : Route 9 := (fun mask => (mask,id))

def c38186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38186 : Upper (D 7) (R 7) [36,192,72,144,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,3] 13 (by decide) (choices 1) [1,2,256] r38186 c38186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25338
  · exact u25339
  · exact u25340

def b38187 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 152 49 291 323 387 259), lower := (rows 37 194 76 152 49 32 64 128 256), losses := [] }

theorem u38187 : Upper (D 7) (R 7) [36,192,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38188 : Route 9 := (fun mask => (mask,id))

def c38188 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38188 : Upper (D 7) (R 7) [36,192,72,144,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,34] 13 (by decide) (choices 1) [1,2,256] r38188 c38188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25341
  · exact u25342
  · exact u25343

def r38189 : Route 9 := (fun mask => (mask,id))

def c38189 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38189 : Upper (D 7) (R 7) [36,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,257] 13 (by decide) (choices 1) [1,2] r38189 c38189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25344
  · exact u25345

def r38190 : Route 9 := (fun mask => (mask,id))

def c38190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38190 : Upper (D 7) (R 7) [36,192,72,144,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,258] 13 (by decide) (choices 1) [1,2] r38190 c38190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25346
  · exact u25347

def r38191 : Route 9 := (fun mask => (mask,id))

def c38191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38191 : Upper (D 7) (R 7) [36,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [36,192,72,144,288] 13 (by decide) (choices 1) [1,2] r38191 c38191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25348
  · exact u25349

def r38192 : Route 9 := (fun mask => (mask,id))

def c38192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38192 : Upper (D 7) (R 7) [36,192,72,160,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,160,3] 13 (by decide) (choices 1) [1,2,16,256] r38192 c38192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25350
  · exact u25351
  · exact u25352
  · exact u25353

def r38193 : Route 9 := (fun mask => (mask,id))

def c38193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38193 : Upper (D 7) (R 7) [36,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [36,192,72,160,257] 13 (by decide) (choices 1) [1,2,16] r38193 c38193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25354
  · exact u25355
  · exact u25356

def r38194 : Route 9 := (fun mask => (mask,id))

def c38194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38194 : Upper (D 7) (R 7) [36,192,72,160,258] 13 := by
  apply FastRouting.sound _ _ [36,192,72,160,258] 13 (by decide) (choices 1) [1,2,16] r38194 c38194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25357
  · exact u25358
  · exact u25359

def r38195 : Route 9 := (fun mask => (mask,id))

def c38195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38195 : Upper (D 7) (R 7) [36,192,72,257,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,3] 13 (by decide) (choices 1) [2,16,128] r38195 c38195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25360
  · exact u25361
  · exact u25362

def b38196 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 265 49 178 210 146 402), lower := (rows 37 194 76 265 49 32 64 128 256), losses := [] }

theorem u38196 : Upper (D 7) (R 7) [36,192,72,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38197 : Route 9 := (fun mask => (mask,id))

def c38197 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38197 : Upper (D 7) (R 7) [36,192,72,257,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,34] 13 (by decide) (choices 1) [1,2,16,128] r38197 c38197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25363
  · exact u25364
  · exact u25365
  · exact u25366

def r38198 : Route 9 := (fun mask => (mask,id))

def c38198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38198 : Upper (D 7) (R 7) [36,192,72,257,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,129] 13 (by decide) (choices 1) [2,16] r38198 c38198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25367
  · exact u25368

def b38199 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 265 146 51 115 179 307), lower := (rows 37 194 76 265 146 32 64 128 256), losses := [] }

theorem u38199 : Upper (D 7) (R 7) [36,192,72,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38200 : Route 9 := (fun mask => (mask,id))

def c38200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38200 : Upper (D 7) (R 7) [36,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,257,160] 13 (by decide) (choices 1) [1,2,16] r38200 c38200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25369
  · exact u25370
  · exact u25371

def r38201 : Route 9 := (fun mask => (mask,id))

def c38201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38201 : Upper (D 7) (R 7) [36,192,72,258,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,3] 13 (by decide) (choices 1) [1,16,128] r38201 c38201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25372
  · exact u25373
  · exact u25374

def b38202 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 266 49 179 211 147 403), lower := (rows 37 194 76 266 49 32 64 128 256), losses := [] }

theorem u38202 : Upper (D 7) (R 7) [36,192,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38203 : Route 9 := (fun mask => (mask,id))

def c38203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38203 : Upper (D 7) (R 7) [36,192,72,258,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,34] 13 (by decide) (choices 1) [1,16,128] r38203 c38203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25375
  · exact u25376
  · exact u25377

def r38204 : Route 9 := (fun mask => (mask,id))

def c38204 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38204 : Upper (D 7) (R 7) [36,192,72,258,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,129] 13 (by decide) (choices 1) [1,2,16] r38204 c38204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25378
  · exact u25379
  · exact u25380

def b38205 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 266 146 49 113 177 305), lower := (rows 37 194 76 266 146 32 64 128 256), losses := [] }

theorem u38205 : Upper (D 7) (R 7) [36,192,72,258,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38206 : Route 9 := (fun mask => (mask,id))

def c38206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38206 : Upper (D 7) (R 7) [36,192,72,258,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,258,160] 13 (by decide) (choices 1) [1,2,16] r38206 c38206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25381
  · exact u25382
  · exact u25383

def r38207 : Route 9 := (fun mask => (mask,id))

def c38207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38207 : Upper (D 7) (R 7) [36,192,72,272,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,3] 13 (by decide) (choices 1) [1,2,128] r38207 c38207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25384
  · exact u25385
  · exact u25386

def b38208 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 280 49 163 195 131 387), lower := (rows 37 194 76 280 49 32 64 128 256), losses := [] }

theorem u38208 : Upper (D 7) (R 7) [36,192,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38209 : Route 9 := (fun mask => (mask,id))

def c38209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38209 : Upper (D 7) (R 7) [36,192,72,272,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,34] 13 (by decide) (choices 1) [1,2,128] r38209 c38209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25387
  · exact u25388
  · exact u25389

def r38210 : Route 9 := (fun mask => (mask,id))

def c38210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38210 : Upper (D 7) (R 7) [36,192,72,272,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,129] 13 (by decide) (choices 1) [1,2] r38210 c38210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25390
  · exact u25391

def b38211 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 280 146 35 99 163 291), lower := (rows 37 194 76 280 146 32 64 128 256), losses := [] }

theorem u38211 : Upper (D 7) (R 7) [36,192,72,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38212 : Route 9 := (fun mask => (mask,id))

def c38212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38212 : Upper (D 7) (R 7) [36,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [36,192,72,272,160] 13 (by decide) (choices 1) [1,2] r38212 c38212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25392
  · exact u25393

def r38213 : Route 9 := (fun mask => (mask,id))

def c38213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38213 : Upper (D 7) (R 7) [36,192,72,288,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,3] 13 (by decide) (choices 1) [1,2,16,128] r38213 c38213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25394
  · exact u25395
  · exact u25396
  · exact u25397

def r38214 : Route 9 := (fun mask => (mask,id))

def c38214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38214 : Upper (D 7) (R 7) [36,192,72,288,129] 13 := by
  apply FastRouting.sound _ _ [36,192,72,288,129] 13 (by decide) (choices 1) [1,2,16] r38214 c38214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25398
  · exact u25399
  · exact u25400

def b38215 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 37 194 76 296 146 51 83 147 275), lower := (rows 37 194 76 296 146 32 64 128 256), losses := [] }

theorem u38215 : Upper (D 7) (R 7) [36,192,72,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38216 : Route 9 := (fun mask => (mask,id))

def c38216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38216 : Upper (D 7) (R 7) [36,192,72,384,3] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,3] 13 (by decide) (choices 1) [1,2,16] r38216 c38216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25401
  · exact u25402
  · exact u25403

def b38217 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 194 76 392 49 51 83 147 275), lower := (rows 37 194 76 392 49 32 64 128 256), losses := [] }

theorem u38217 : Upper (D 7) (R 7) [36,192,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38218 : Route 9 := (fun mask => (mask,id))

def c38218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38218 : Upper (D 7) (R 7) [36,192,72,384,34] 13 := by
  apply FastRouting.sound _ _ [36,192,72,384,34] 13 (by decide) (choices 1) [1,2,16] r38218 c38218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25404
  · exact u25405
  · exact u25406

def b38219 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 194 261 11 26 240 240 240 496), lower := (rows 37 194 261 11 26 32 64 128 256), losses := [] }

theorem u38219 : Upper (D 7) (R 7) [36,192,257,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38219
end Delivery.IrregularNine14.P07
