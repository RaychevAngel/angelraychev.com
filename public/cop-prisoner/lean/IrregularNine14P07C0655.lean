import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0453
import IrregularNine14P07C0454
import IrregularNine14P07C0455

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39300 : Route 9 := (fun mask => (mask,id))

def c39300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39300 : Upper (D 7) (R 7) [36,320,3,130,160] 13 := by
  apply FastRouting.sound _ _ [36,320,3,130,160] 13 (by decide) (choices 1) [1,8,16,64] r39300 c39300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27207
  · exact u27208
  · exact u27209
  · exact u27210

def r39301 : Route 9 := (fun mask => (mask,id))

def c39301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39301 : Upper (D 7) (R 7) [36,320,3,130,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,130,192] 13 (by decide) (choices 1) [1,8,16] r39301 c39301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27211
  · exact u27212
  · exact u27213

def b39302 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 7 152 152 99 99 227 355), lower := (rows 37 322 7 152 152 32 64 128 256), losses := [] }

theorem u39302 : Upper (D 7) (R 7) [36,320,3,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39303 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 7 152 176 107 75 203 331), lower := (rows 37 322 7 152 176 32 64 128 256), losses := [] }

theorem u39303 : Upper (D 7) (R 7) [36,320,3,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39304 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 7 152 208 43 107 171 299), lower := (rows 37 322 7 152 208 32 64 128 256), losses := [] }

theorem u39304 : Upper (D 7) (R 7) [36,320,3,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39305 : Route 9 := (fun mask => (mask,id))

def c39305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39305 : Upper (D 7) (R 7) [36,320,3,160,192] 13 := by
  apply FastRouting.sound _ _ [36,320,3,160,192] 13 (by decide) (choices 1) [1,2,8,16] r39305 c39305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27214
  · exact u27215
  · exact u27216
  · exact u27217

def b39306 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 37 322 13 26 19 224 224 224 480), lower := (rows 37 322 13 26 19 32 64 128 256), losses := [] }

theorem u39306 : Upper (D 7) (R 7) [36,320,9,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39307 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 13 26 49 226 194 194 450), lower := (rows 37 322 13 26 49 32 64 128 256), losses := [] }

theorem u39307 : Upper (D 7) (R 7) [36,320,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39308 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 13 26 50 225 193 193 449), lower := (rows 37 322 13 26 50 32 64 128 256), losses := [] }

theorem u39308 : Upper (D 7) (R 7) [36,320,9,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39309 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 322 13 26 81 162 226 162 418), lower := (rows 37 322 13 26 81 32 64 128 256), losses := [] }

theorem u39309 : Upper (D 7) (R 7) [36,320,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39310 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 322 13 26 82 161 225 161 417), lower := (rows 37 322 13 26 82 32 64 128 256), losses := [] }

theorem u39310 : Upper (D 7) (R 7) [36,320,9,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39311 : Route 9 := (fun mask => (mask,id))

def c39311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39311 : Upper (D 7) (R 7) [36,320,9,18,96] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18,96] 13 (by decide) (choices 1) [1,2,128] r39311 c39311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27218
  · exact u27219
  · exact u27220

def r39312 : Route 9 := (fun mask => (mask,id))

def c39312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39312 : Upper (D 7) (R 7) [36,320,9,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18,129] 13 (by decide) (choices 1) [2,64,128] r39312 c39312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27221
  · exact u27222
  · exact u27223

def b39313 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 13 26 146 225 225 225 481), lower := (rows 37 322 13 26 146 32 64 128 256), losses := [] }

theorem u39313 : Upper (D 7) (R 7) [36,320,9,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39314 : Route 9 := (fun mask => (mask,id))

def c39314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39314 : Upper (D 7) (R 7) [36,320,9,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18,160] 13 (by decide) (choices 1) [1,2,64,128] r39314 c39314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27224
  · exact u27225
  · exact u27226
  · exact u27227

def r39315 : Route 9 := (fun mask => (mask,id))

def c39315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39315 : Upper (D 7) (R 7) [36,320,9,18,192] 13 := by
  apply FastRouting.sound _ _ [36,320,9,18,192] 13 (by decide) (choices 1) [1,2,128] r39315 c39315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27228
  · exact u27229
  · exact u27230

def b39316 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 322 13 88 19 162 226 162 418), lower := (rows 37 322 13 88 19 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 146 274), good := (rows 37 418 13 445 435 32 0 128 256) }] }

theorem u39316 : Upper (D 7) (R 7) [36,320,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39317 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 13 88 49 162 194 130 386), lower := (rows 37 322 13 88 49 32 64 128 256), losses := [] }

theorem u39317 : Upper (D 7) (R 7) [36,320,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39318 : Route 9 := (fun mask => (mask,id))

def c39318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39318 : Upper (D 7) (R 7) [36,320,9,80,34] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,34] 13 (by decide) (choices 1) [1,2,128] r39318 c39318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27231
  · exact u27232
  · exact u27233

def r39319 : Route 9 := (fun mask => (mask,id))

def c39319 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39319 : Upper (D 7) (R 7) [36,320,9,80,129] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,129] 13 (by decide) (choices 1) [2,128] r39319 c39319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27234
  · exact u27235

def r39320 : Route 9 := (fun mask => (mask,id))

def c39320 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39320 : Upper (D 7) (R 7) [36,320,9,80,130] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,130] 13 (by decide) (choices 1) [1,2,128] r39320 c39320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27236
  · exact u27237
  · exact u27238

def r39321 : Route 9 := (fun mask => (mask,id))

def c39321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39321 : Upper (D 7) (R 7) [36,320,9,80,160] 13 := by
  apply FastRouting.sound _ _ [36,320,9,80,160] 13 (by decide) (choices 1) [1,2,128] r39321 c39321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27239
  · exact u27240
  · exact u27241

def r39322 : Route 9 := (fun mask => (mask,id))

def c39322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39322 : Upper (D 7) (R 7) [36,320,9,130,3] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,3] 13 (by decide) (choices 1) [16,64,128] r39322 c39322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27242
  · exact u27243
  · exact u27244

def b39323 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 13 138 49 242 210 210 466), lower := (rows 37 322 13 138 49 32 64 128 256), losses := [] }

theorem u39323 : Upper (D 7) (R 7) [36,320,9,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39324 : Route 9 := (fun mask => (mask,id))

def c39324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39324 : Upper (D 7) (R 7) [36,320,9,130,34] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,34] 13 (by decide) (choices 1) [1,16,64,128] r39324 c39324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27245
  · exact u27246
  · exact u27247
  · exact u27248

def r39325 : Route 9 := (fun mask => (mask,id))

def c39325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39325 : Upper (D 7) (R 7) [36,320,9,130,65] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,65] 13 (by decide) (choices 1) [2,16,128] r39325 c39325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27249
  · exact u27250
  · exact u27251

def b39326 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 13 138 82 177 241 177 433), lower := (rows 37 322 13 138 82 32 64 128 256), losses := [] }

theorem u39326 : Upper (D 7) (R 7) [36,320,9,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39327 : Route 9 := (fun mask => (mask,id))

def c39327 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39327 : Upper (D 7) (R 7) [36,320,9,130,96] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,96] 13 (by decide) (choices 1) [1,2,16,128] r39327 c39327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27252
  · exact u27253
  · exact u27254
  · exact u27255

def r39328 : Route 9 := (fun mask => (mask,id))

def c39328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39328 : Upper (D 7) (R 7) [36,320,9,130,129] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,129] 13 (by decide) (choices 1) [2,16,64] r39328 c39328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27256
  · exact u27257
  · exact u27258

def b39329 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 13 138 146 113 113 241 369), lower := (rows 37 322 13 138 146 32 64 128 256), losses := [] }

theorem u39329 : Upper (D 7) (R 7) [36,320,9,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39330 : Route 9 := (fun mask => (mask,id))

def c39330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39330 : Upper (D 7) (R 7) [36,320,9,130,160] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,160] 13 (by decide) (choices 1) [1,2,16,64] r39330 c39330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27259
  · exact u27260
  · exact u27261
  · exact u27262

def r39331 : Route 9 := (fun mask => (mask,id))

def c39331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39331 : Upper (D 7) (R 7) [36,320,9,130,192] 13 := by
  apply FastRouting.sound _ _ [36,320,9,130,192] 13 (by decide) (choices 1) [1,2,16] r39331 c39331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27263
  · exact u27264
  · exact u27265

def r39332 : Route 9 := (fun mask => (mask,id))

def c39332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39332 : Upper (D 7) (R 7) [36,320,9,144,3] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,3] 13 (by decide) (choices 1) [2,64,128] r39332 c39332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27266
  · exact u27267
  · exact u27268

def b39333 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 13 152 49 226 194 194 450), lower := (rows 37 322 13 152 49 32 64 128 256), losses := [] }

theorem u39333 : Upper (D 7) (R 7) [36,320,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39334 : Route 9 := (fun mask => (mask,id))

def c39334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39334 : Upper (D 7) (R 7) [36,320,9,144,34] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,34] 13 (by decide) (choices 1) [1,2,64,128] r39334 c39334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27269
  · exact u27270
  · exact u27271
  · exact u27272

def r39335 : Route 9 := (fun mask => (mask,id))

def c39335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39335 : Upper (D 7) (R 7) [36,320,9,144,65] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,65] 13 (by decide) (choices 1) [2,128] r39335 c39335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27273
  · exact u27274

def b39336 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 13 152 82 163 227 163 419), lower := (rows 37 322 13 152 82 32 64 128 256), losses := [] }

theorem u39336 : Upper (D 7) (R 7) [36,320,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39337 : Route 9 := (fun mask => (mask,id))

def c39337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39337 : Upper (D 7) (R 7) [36,320,9,144,96] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,96] 13 (by decide) (choices 1) [1,2,128] r39337 c39337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27275
  · exact u27276
  · exact u27277

def b39338 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 322 13 152 145 98 98 226 354), lower := (rows 37 322 13 152 145 32 64 128 256), losses := [] }

theorem u39338 : Upper (D 7) (R 7) [36,320,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39339 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 13 152 146 99 99 227 355), lower := (rows 37 322 13 152 146 32 64 128 256), losses := [] }

theorem u39339 : Upper (D 7) (R 7) [36,320,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39340 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 13, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 176 99 67 195 323), lower := (rows 37 322 13 152 176 32 64 128 256), losses := [] }

theorem u39340 : Upper (D 7) (R 7) [36,320,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39341 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 13 152 208 35 99 163 291), lower := (rows 37 322 13 152 208 32 64 128 256), losses := [] }

theorem u39341 : Upper (D 7) (R 7) [36,320,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39342 : Route 9 := (fun mask => (mask,id))

def c39342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39342 : Upper (D 7) (R 7) [36,320,9,192,3] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,3] 13 (by decide) (choices 1) [2,16,128] r39342 c39342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27278
  · exact u27279
  · exact u27280

def b39343 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 13 200 49 178 210 146 402), lower := (rows 37 322 13 200 49 32 64 128 256), losses := [] }

theorem u39343 : Upper (D 7) (R 7) [36,320,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39344 : Route 9 := (fun mask => (mask,id))

def c39344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39344 : Upper (D 7) (R 7) [36,320,9,192,34] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,34] 13 (by decide) (choices 1) [1,2,16,128] r39344 c39344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27281
  · exact u27282
  · exact u27283
  · exact u27284

def r39345 : Route 9 := (fun mask => (mask,id))

def c39345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39345 : Upper (D 7) (R 7) [36,320,9,192,129] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,129] 13 (by decide) (choices 1) [2,16] r39345 c39345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27285
  · exact u27286

def r39346 : Route 9 := (fun mask => (mask,id))

def c39346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39346 : Upper (D 7) (R 7) [36,320,9,192,130] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,130] 13 (by decide) (choices 1) [1,2,16] r39346 c39346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27287
  · exact u27288
  · exact u27289

def r39347 : Route 9 := (fun mask => (mask,id))

def c39347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39347 : Upper (D 7) (R 7) [36,320,9,192,160] 13 := by
  apply FastRouting.sound _ _ [36,320,9,192,160] 13 (by decide) (choices 1) [1,2,16] r39347 c39347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27290
  · exact u27291
  · exact u27292

def b39348 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 37 322 14 25 19 224 224 224 480), lower := (rows 37 322 14 25 19 32 64 128 256), losses := [] }

theorem u39348 : Upper (D 7) (R 7) [36,320,10,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39349 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 14 25 49 226 194 194 450), lower := (rows 37 322 14 25 49 32 64 128 256), losses := [] }

theorem u39349 : Upper (D 7) (R 7) [36,320,10,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39350 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 14 25 50 225 193 193 449), lower := (rows 37 322 14 25 50 32 64 128 256), losses := [] }

theorem u39350 : Upper (D 7) (R 7) [36,320,10,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39351 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 14 25 81 162 226 162 418), lower := (rows 37 322 14 25 81 32 64 128 256), losses := [] }

theorem u39351 : Upper (D 7) (R 7) [36,320,10,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39352 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 14 25 82 161 225 161 417), lower := (rows 37 322 14 25 82 32 64 128 256), losses := [] }

theorem u39352 : Upper (D 7) (R 7) [36,320,10,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39353 : Route 9 := (fun mask => (mask,id))

def c39353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39353 : Upper (D 7) (R 7) [36,320,10,17,96] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,96] 13 (by decide) (choices 1) [1,2,128] r39353 c39353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27293
  · exact u27294
  · exact u27295

def b39354 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 14 25 145 226 226 226 482), lower := (rows 37 322 14 25 145 32 64 128 256), losses := [] }

theorem u39354 : Upper (D 7) (R 7) [36,320,10,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39355 : Route 9 := (fun mask => (mask,id))

def c39355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39355 : Upper (D 7) (R 7) [36,320,10,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,130] 13 (by decide) (choices 1) [1,64,128] r39355 c39355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27296
  · exact u27297
  · exact u27298

def r39356 : Route 9 := (fun mask => (mask,id))

def c39356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39356 : Upper (D 7) (R 7) [36,320,10,17,160] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,160] 13 (by decide) (choices 1) [1,2,64,128] r39356 c39356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27299
  · exact u27300
  · exact u27301
  · exact u27302

def r39357 : Route 9 := (fun mask => (mask,id))

def c39357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39357 : Upper (D 7) (R 7) [36,320,10,17,192] 13 := by
  apply FastRouting.sound _ _ [36,320,10,17,192] 13 (by decide) (choices 1) [1,2,128] r39357 c39357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27303
  · exact u27304
  · exact u27305

def b39358 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 225, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,1),(1,5),(3,1),(4,5)], upper := (rows 37 322 14 56 19 225 193 193 449), lower := (rows 37 322 14 56 19 32 64 128 256), losses := [] }

theorem u39358 : Upper (D 7) (R 7) [36,320,10,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39359 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(4,5)], upper := (rows 37 322 14 56 81 163 195 131 387), lower := (rows 37 322 14 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 322 14 478 467 0 64 128 256) }] }

theorem u39359 : Upper (D 7) (R 7) [36,320,10,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39359
end Delivery.IrregularNine14.P07
