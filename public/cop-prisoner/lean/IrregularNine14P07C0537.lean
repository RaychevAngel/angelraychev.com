import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0255
import IrregularNine14P07C0256
import IrregularNine14P07C0257

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32220 : Route 9 := (fun mask => (mask,id))

def c32220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32220 : Upper (D 7) (R 7) [6,288,72,130,65] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,65] 13 (by decide) (choices 1) [1,16,128] r32220 c32220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15349
  · exact u15350
  · exact u15351

def r32221 : Route 9 := (fun mask => (mask,id))

def c32221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32221 : Upper (D 7) (R 7) [6,288,72,130,96] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,96] 13 (by decide) (choices 1) [1,16,128] r32221 c32221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15352
  · exact u15353
  · exact u15354

def r32222 : Route 9 := (fun mask => (mask,id))

def c32222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32222 : Upper (D 7) (R 7) [6,288,72,130,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,129] 13 (by decide) (choices 1) [1,16,64] r32222 c32222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15355
  · exact u15356
  · exact u15357

def r32223 : Route 9 := (fun mask => (mask,id))

def c32223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32223 : Upper (D 7) (R 7) [6,288,72,130,160] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,160] 13 (by decide) (choices 1) [1,16,64] r32223 c32223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15358
  · exact u15359
  · exact u15360

def r32224 : Route 9 := (fun mask => (mask,id))

def c32224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32224 : Upper (D 7) (R 7) [6,288,72,130,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,130,192] 13 (by decide) (choices 1) [1,16] r32224 c32224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15361
  · exact u15362

def b32225 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 290 76 152 19 225 225 225 481), lower := (rows 7 290 76 152 19 32 64 128 256), losses := [] }

theorem u32225 : Upper (D 7) (R 7) [6,288,72,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32226 : Route 9 := (fun mask => (mask,id))

def c32226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32226 : Upper (D 7) (R 7) [6,288,72,144,33] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,33] 13 (by decide) (choices 1) [1,2,64,128] r32226 c32226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15363
  · exact u15364
  · exact u15365
  · exact u15366

def b32227 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 205, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 290 76 152 50 225 193 193 449), lower := (rows 7 290 76 152 50 32 64 128 256), losses := [] }

theorem u32227 : Upper (D 7) (R 7) [6,288,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32228 : Route 9 := (fun mask => (mask,id))

def c32228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32228 : Upper (D 7) (R 7) [6,288,72,144,65] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,65] 13 (by decide) (choices 1) [1,2,128] r32228 c32228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15367
  · exact u15368
  · exact u15369

def r32229 : Route 9 := (fun mask => (mask,id))

def c32229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32229 : Upper (D 7) (R 7) [6,288,72,144,66] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,66] 13 (by decide) (choices 1) [1,128] r32229 c32229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15370
  · exact u15371

def r32230 : Route 9 := (fun mask => (mask,id))

def c32230 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32230 : Upper (D 7) (R 7) [6,288,72,144,96] 13 := by
  apply FastRouting.sound _ _ [6,288,72,144,96] 13 (by decide) (choices 1) [1,2,128] r32230 c32230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15372
  · exact u15373
  · exact u15374

def b32231 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 76 152 145 99 99 227 355), lower := (rows 7 290 76 152 145 32 64 128 256), losses := [] }

theorem u32231 : Upper (D 7) (R 7) [6,288,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32232 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 76 152 146 97 97 225 353), lower := (rows 7 290 76 152 146 32 64 128 256), losses := [] }

theorem u32232 : Upper (D 7) (R 7) [6,288,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32233 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 76 152 176 99 67 195 323), lower := (rows 7 290 76 152 176 32 64 128 256), losses := [] }

theorem u32233 : Upper (D 7) (R 7) [6,288,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32234 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 7 290 76 152 208 35 99 163 291), lower := (rows 7 290 76 152 208 32 64 128 256), losses := [] }

theorem u32234 : Upper (D 7) (R 7) [6,288,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32235 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 290 76 168 19 241 209 209 465), lower := (rows 7 290 76 168 19 32 64 128 256), losses := [] }

theorem u32235 : Upper (D 7) (R 7) [6,288,72,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32236 : Route 9 := (fun mask => (mask,id))

def c32236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32236 : Upper (D 7) (R 7) [6,288,72,160,65] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,65] 13 (by decide) (choices 1) [1,2,16,128] r32236 c32236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15375
  · exact u15376
  · exact u15377
  · exact u15378

def r32237 : Route 9 := (fun mask => (mask,id))

def c32237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32237 : Upper (D 7) (R 7) [6,288,72,160,66] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,66] 13 (by decide) (choices 1) [1,16,128] r32237 c32237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15379
  · exact u15380
  · exact u15381

def r32238 : Route 9 := (fun mask => (mask,id))

def c32238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32238 : Upper (D 7) (R 7) [6,288,72,160,129] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,129] 13 (by decide) (choices 1) [1,2,16,64] r32238 c32238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15382
  · exact u15383
  · exact u15384
  · exact u15385

def r32239 : Route 9 := (fun mask => (mask,id))

def c32239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32239 : Upper (D 7) (R 7) [6,288,72,160,130] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,130] 13 (by decide) (choices 1) [1,16,64] r32239 c32239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15386
  · exact u15387
  · exact u15388

def r32240 : Route 9 := (fun mask => (mask,id))

def c32240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32240 : Upper (D 7) (R 7) [6,288,72,160,192] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,192] 13 (by decide) (choices 1) [1,2,16] r32240 c32240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15389
  · exact u15390
  · exact u15391

def b32241 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 290 100 11 25 240 208 208 464), lower := (rows 7 290 100 11 25 32 64 128 256), losses := [] }

theorem u32241 : Upper (D 7) (R 7) [6,288,96,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32242 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 100 11 88 177 209 145 401), lower := (rows 7 290 100 11 88 32 64 128 256), losses := [] }

theorem u32242 : Upper (D 7) (R 7) [6,288,96,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32243 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 100 11 145 248 216 216 472), lower := (rows 7 290 100 11 145 32 64 128 256), losses := [] }

theorem u32243 : Upper (D 7) (R 7) [6,288,96,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32244 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 100 11 152 241 209 209 465), lower := (rows 7 290 100 11 152 32 64 128 256), losses := [] }

theorem u32244 : Upper (D 7) (R 7) [6,288,96,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32245 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 100 11 208 185 217 153 409), lower := (rows 7 290 100 11 208 32 64 128 256), losses := [] }

theorem u32245 : Upper (D 7) (R 7) [6,288,96,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32246 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 7 290 100 25 25 226 194 194 450), lower := (rows 7 290 100 25 25 32 64 128 256), losses := [] }

theorem u32246 : Upper (D 7) (R 7) [6,288,96,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32247 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 290 100 25 26 225 193 193 449), lower := (rows 7 290 100 25 26 32 64 128 256), losses := [] }

theorem u32247 : Upper (D 7) (R 7) [6,288,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32248 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 290 100 25 81 170 202 138 394), lower := (rows 7 290 100 25 81 32 64 128 256), losses := [] }

theorem u32248 : Upper (D 7) (R 7) [6,288,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32249 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 228, targets := 2 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(2,1),(3,5),(4,5)], upper := (rows 7 290 100 25 82 169 201 137 393), lower := (rows 7 290 100 25 82 32 64 128 256), losses := [] }

theorem u32249 : Upper (D 7) (R 7) [6,288,96,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32250 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 7 290 100 25 88 163 195 131 387), lower := (rows 7 290 100 25 88 32 64 128 256), losses := [] }

theorem u32250 : Upper (D 7) (R 7) [6,288,96,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32251 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 100 25 145 234 202 202 458), lower := (rows 7 290 100 25 145 32 64 128 256), losses := [] }

theorem u32251 : Upper (D 7) (R 7) [6,288,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32252 : Route 9 := (fun mask => (mask,id))

def c32252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32252 : Upper (D 7) (R 7) [6,288,96,17,130] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,130] 13 (by decide) (choices 1) [1,8,64,128] r32252 c32252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15392
  · exact u15393
  · exact u15394
  · exact u15395

def r32253 : Route 9 := (fun mask => (mask,id))

def c32253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32253 : Upper (D 7) (R 7) [6,288,96,17,136] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,136] 13 (by decide) (choices 1) [1,2,64,128] r32253 c32253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15396
  · exact u15397
  · exact u15398
  · exact u15399

def r32254 : Route 9 := (fun mask => (mask,id))

def c32254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32254 : Upper (D 7) (R 7) [6,288,96,17,192] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,192] 13 (by decide) (choices 1) [1,2,8,128] r32254 c32254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15400
  · exact u15401
  · exact u15402
  · exact u15403

def b32255 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,5),(3,6),(4,5)], upper := (rows 7 290 100 26 81 169 201 137 393), lower := (rows 7 290 100 26 81 32 64 128 256), losses := [] }

theorem u32255 : Upper (D 7) (R 7) [6,288,96,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32256 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 7 290 100 26 88 161 193 129 385), lower := (rows 7 290 100 26 88 32 64 128 256), losses := [] }

theorem u32256 : Upper (D 7) (R 7) [6,288,96,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32257 : Route 9 := (fun mask => (mask,id))

def c32257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32257 : Upper (D 7) (R 7) [6,288,96,18,129] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,129] 13 (by decide) (choices 1) [1,8,64,128] r32257 c32257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15404
  · exact u15405
  · exact u15406
  · exact u15407

def r32258 : Route 9 := (fun mask => (mask,id))

def c32258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32258 : Upper (D 7) (R 7) [6,288,96,18,136] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,136] 13 (by decide) (choices 1) [1,64,128] r32258 c32258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15408
  · exact u15409
  · exact u15410

def r32259 : Route 9 := (fun mask => (mask,id))

def c32259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32259 : Upper (D 7) (R 7) [6,288,96,18,192] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,192] 13 (by decide) (choices 1) [1,8,128] r32259 c32259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15411
  · exact u15412
  · exact u15413

def b32260 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 7 290 100 73 145 186 218 154 410), lower := (rows 7 290 100 73 145 32 64 128 256), losses := [] }

theorem u32260 : Upper (D 7) (R 7) [6,288,96,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32261 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 7 290 100 73 146 185 217 153 409), lower := (rows 7 290 100 73 146 32 64 128 256), losses := [] }

theorem u32261 : Upper (D 7) (R 7) [6,288,96,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32262 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 7 290 100 73 152 179 211 147 403), lower := (rows 7 290 100 73 152 32 64 128 256), losses := [] }

theorem u32262 : Upper (D 7) (R 7) [6,288,96,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32263 : Route 9 := (fun mask => (mask,id))

def c32263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32263 : Upper (D 7) (R 7) [6,288,96,66,129] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66,129] 13 (by decide) (choices 1) [1,8,16,128] r32263 c32263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15414
  · exact u15415
  · exact u15416
  · exact u15417

def r32264 : Route 9 := (fun mask => (mask,id))

def c32264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32264 : Upper (D 7) (R 7) [6,288,96,66,136] 13 := by
  apply FastRouting.sound _ _ [6,288,96,66,136] 13 (by decide) (choices 1) [1,16,128] r32264 c32264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15418
  · exact u15419
  · exact u15420

def r32265 : Route 9 := (fun mask => (mask,id))

def c32265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32265 : Upper (D 7) (R 7) [6,288,96,80,129] 13 := by
  apply FastRouting.sound _ _ [6,288,96,80,129] 13 (by decide) (choices 1) [1,2,8,128] r32265 c32265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15421
  · exact u15422
  · exact u15423
  · exact u15424

def r32266 : Route 9 := (fun mask => (mask,id))

def c32266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32266 : Upper (D 7) (R 7) [6,288,96,80,130] 13 := by
  apply FastRouting.sound _ _ [6,288,96,80,130] 13 (by decide) (choices 1) [1,8,128] r32266 c32266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15425
  · exact u15426
  · exact u15427

def b32267 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 7 290 100 88 152 163 195 131 387), lower := (rows 7 290 100 88 152 32 64 128 256), losses := [] }

theorem u32267 : Upper (D 7) (R 7) [6,288,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32268 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 290 100 137 145 122 90 218 346), lower := (rows 7 290 100 137 145 32 64 128 256), losses := [] }

theorem u32268 : Upper (D 7) (R 7) [6,288,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32269 : Route 9 := (fun mask => (mask,id))

def c32269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32269 : Upper (D 7) (R 7) [6,288,96,129,130] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,130] 13 (by decide) (choices 1) [1,8,16,64] r32269 c32269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15428
  · exact u15429
  · exact u15430
  · exact u15431

def b32270 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 290 100 137 152 115 83 211 339), lower := (rows 7 290 100 137 152 32 64 128 256), losses := [] }

theorem u32270 : Upper (D 7) (R 7) [6,288,96,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32271 : Route 9 := (fun mask => (mask,id))

def c32271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32271 : Upper (D 7) (R 7) [6,288,96,129,192] 13 := by
  apply FastRouting.sound _ _ [6,288,96,129,192] 13 (by decide) (choices 1) [1,2,8,16] r32271 c32271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15432
  · exact u15433
  · exact u15434
  · exact u15435

def b32272 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 290 100 138 152 113 81 209 337), lower := (rows 7 290 100 138 152 32 64 128 256), losses := [] }

theorem u32272 : Upper (D 7) (R 7) [6,288,96,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32273 : Route 9 := (fun mask => (mask,id))

def c32273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32273 : Upper (D 7) (R 7) [6,288,96,130,192] 13 := by
  apply FastRouting.sound _ _ [6,288,96,130,192] 13 (by decide) (choices 1) [1,8,16] r32273 c32273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15436
  · exact u15437
  · exact u15438

def b32274 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 100 152 152 99 67 195 323), lower := (rows 7 290 100 152 152 32 64 128 256), losses := [] }

theorem u32274 : Upper (D 7) (R 7) [6,288,96,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32275 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 290 100 152 208 43 75 139 267), lower := (rows 7 290 100 152 208 32 64 128 256), losses := [] }

theorem u32275 : Upper (D 7) (R 7) [6,288,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32276 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 290 196 11 25 240 240 240 496), lower := (rows 7 290 196 11 25 32 64 128 256), losses := [] }

theorem u32276 : Upper (D 7) (R 7) [6,288,192,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32277 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 49 248 216 216 472), lower := (rows 7 290 196 11 49 32 64 128 256), losses := [] }

theorem u32277 : Upper (D 7) (R 7) [6,288,192,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32278 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 56 241 209 209 465), lower := (rows 7 290 196 11 56 32 64 128 256), losses := [] }

theorem u32278 : Upper (D 7) (R 7) [6,288,192,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32279 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 290 196 11 81 184 248 184 440), lower := (rows 7 290 196 11 81 32 64 128 256), losses := [] }

theorem u32279 : Upper (D 7) (R 7) [6,288,192,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u32279
end Delivery.IrregularNine14.P07
