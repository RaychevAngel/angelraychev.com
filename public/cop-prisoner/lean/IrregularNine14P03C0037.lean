import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0006
import IrregularNine14P03C0007

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 145 480 480 480 480), lower := (rows 7 11 37 88 145 32 64 128 256), losses := [] }

theorem u2220 : Upper (D 3) (R 3) [6,9,33,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2220
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2221 : Route 9 := (fun mask => (mask,id))

def c2221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2221 : Upper (D 3) (R 3) [6,9,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160] 13 (by decide) (choices 1) [1,64,128,256] r2221 c2221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u377
  · exact u378
  · exact u379
  · exact u380

def b2222 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 88 208 417 481 417 417), lower := (rows 7 11 37 88 208 32 64 128 256), losses := [] }

theorem u2222 : Upper (D 3) (R 3) [6,9,33,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 273 224 224 224 480), lower := (rows 7 11 37 88 273 32 64 128 256), losses := [] }

theorem u2223 : Upper (D 3) (R 3) [6,9,33,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2224 : Route 9 := (fun mask => (mask,id))

def c2224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2224 : Upper (D 3) (R 3) [6,9,33,80,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,288] 13 (by decide) (choices 1) [1,64,128] r2224 c2224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u381
  · exact u382
  · exact u383

def b2225 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 88 336 161 225 161 417), lower := (rows 7 11 37 88 336 32 64 128 256), losses := [] }

theorem u2225 : Upper (D 3) (R 3) [6,9,33,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2226 : Route 9 := (fun mask => (mask,id))

def c2226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2226 : Upper (D 3) (R 3) [6,9,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,384] 13 (by decide) (choices 1) [1,64,128] r2226 c2226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u384
  · exact u385
  · exact u386

def b2227 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 37 200 49 496 464 464 464), lower := (rows 7 11 37 200 49 32 64 128 256), losses := [] }

theorem u2227 : Upper (D 3) (R 3) [6,9,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 81 432 496 432 432), lower := (rows 7 11 37 200 81 32 64 128 256), losses := [] }

theorem u2228 : Upper (D 3) (R 3) [6,9,33,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2229 : Route 9 := (fun mask => (mask,id))

def c2229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2229 : Upper (D 3) (R 3) [6,9,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96] 13 (by decide) (choices 1) [1,16,128,256] r2229 c2229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u387
  · exact u388
  · exact u389
  · exact u390

def b2230 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 37 200 208 305 369 433 305), lower := (rows 7 11 37 200 208 32 64 128 256), losses := [] }

theorem u2230 : Upper (D 3) (R 3) [6,9,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 273 240 240 240 496), lower := (rows 7 11 37 200 273 32 64 128 256), losses := [] }

theorem u2231 : Upper (D 3) (R 3) [6,9,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2232 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2232 : Upper (D 3) (R 3) [6,9,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,288] 13 (by decide) (choices 1) [1,16,64] r2232 c2232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u391
  · exact u392
  · exact u393

def r2233 : Route 9 := (fun mask => (mask,id))

def c2233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2233 : Upper (D 3) (R 3) [6,9,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320] 13 (by decide) (choices 1) [1,16,128] r2233 c2233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u394
  · exact u395
  · exact u396

def b2234 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 37 280 49 224 192 192 448), lower := (rows 7 11 37 280 49 32 64 128 256), losses := [] }

theorem u2234 : Upper (D 3) (R 3) [6,9,33,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 280 81 224 224 224 480), lower := (rows 7 11 37 280 81 32 64 128 256), losses := [] }

theorem u2235 : Upper (D 3) (R 3) [6,9,33,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2236 : Route 9 := (fun mask => (mask,id))

def c2236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2236 : Upper (D 3) (R 3) [6,9,33,272,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,96] 13 (by decide) (choices 1) [1,64,128] r2236 c2236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u397
  · exact u398
  · exact u399

def r2237 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2237 : Upper (D 3) (R 3) [6,9,33,272,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,192] 13 (by decide) (choices 1) [1,64] r2237 c2237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u400
  · exact u401

def b2238 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 37 328 49 240 208 208 464), lower := (rows 7 11 37 328 49 32 64 128 256), losses := [] }

theorem u2238 : Upper (D 3) (R 3) [6,9,33,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2239 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 328 81 176 240 176 432), lower := (rows 7 11 37 328 81 32 64 128 256), losses := [] }

theorem u2239 : Upper (D 3) (R 3) [6,9,33,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2239
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2240 : Route 9 := (fun mask => (mask,id))

def c2240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2240 : Upper (D 3) (R 3) [6,9,33,320,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,96] 13 (by decide) (choices 1) [1,16,128] r2240 c2240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u402
  · exact u403
  · exact u404

def b2241 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 328 145 240 240 240 496), lower := (rows 7 11 37 328 145 32 64 128 256), losses := [] }

theorem u2241 : Upper (D 3) (R 3) [6,9,33,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2242 : Route 9 := (fun mask => (mask,id))

def c2242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2242 : Upper (D 3) (R 3) [6,9,33,320,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,160] 13 (by decide) (choices 1) [1,16,64,128] r2242 c2242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u405
  · exact u406
  · exact u407
  · exact u408

def r2243 : Route 9 := (fun mask => (mask,id))

def c2243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2243 : Upper (D 3) (R 3) [6,9,33,320,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192] 13 (by decide) (choices 1) [1,16,128] r2243 c2243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u409
  · exact u410
  · exact u411

def b2244 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 200 49 481 449 449 449), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u2244 : Upper (D 3) (R 3) [6,9,48,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 11 52 200 81 417 481 417 417), lower := (rows 7 11 52 200 81 32 64 128 256), losses := [] }

theorem u2245 : Upper (D 3) (R 3) [6,9,48,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 200 112 417 449 385 385), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u2246 : Upper (D 3) (R 3) [6,9,48,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 52 200 208 289 353 417 289), lower := (rows 7 11 52 200 208 32 64 128 256), losses := [] }

theorem u2247 : Upper (D 3) (R 3) [6,9,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2248 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2248 : Upper (D 3) (R 3) [6,9,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257] 13 (by decide) (choices 1) [1,64] r2248 c2248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u412
  · exact u413

def b2249 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 200 304 225 193 193 449), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u2249 : Upper (D 3) (R 3) [6,9,48,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2250 : Route 9 := (fun mask => (mask,id))

def c2250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2250 : Upper (D 3) (R 3) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [1,128] r2250 c2250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u414
  · exact u415

def b2251 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 328 49 225 193 193 449), lower := (rows 7 11 52 328 49 32 64 128 256), losses := [] }

theorem u2251 : Upper (D 3) (R 3) [6,9,48,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 7 11 52 328 81 161 225 161 417), lower := (rows 7 11 52 328 81 32 64 128 256), losses := [] }

theorem u2252 : Upper (D 3) (R 3) [6,9,48,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 328 112 161 193 129 385), lower := (rows 7 11 52 328 112 32 64 128 256), losses := [] }

theorem u2253 : Upper (D 3) (R 3) [6,9,48,320,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2254 : Route 9 := (fun mask => (mask,id))

def c2254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2254 : Upper (D 3) (R 3) [6,9,48,320,129] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,129] 13 (by decide) (choices 1) [1,64,128] r2254 c2254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u416
  · exact u417
  · exact u418

def b2255 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 52 328 176 225 193 193 449), lower := (rows 7 11 52 328 176 32 64 128 256), losses := [] }

theorem u2255 : Upper (D 3) (R 3) [6,9,48,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2256 : Route 9 := (fun mask => (mask,id))

def c2256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2256 : Upper (D 3) (R 3) [6,9,48,320,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192] 13 (by decide) (choices 1) [1,128] r2256 c2256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u419
  · exact u420

def b2257 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 152 49 481 449 449 449), lower := (rows 7 11 100 152 49 32 64 128 256), losses := [] }

theorem u2257 : Upper (D 3) (R 3) [6,9,96,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 152 112 417 449 385 385), lower := (rows 7 11 100 152 112 32 64 128 256), losses := [] }

theorem u2258 : Upper (D 3) (R 3) [6,9,96,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 152 145 353 353 481 353), lower := (rows 7 11 100 152 145 32 64 128 256), losses := [] }

theorem u2259 : Upper (D 3) (R 3) [6,9,96,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2259
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 152 176 353 321 449 321), lower := (rows 7 11 100 152 176 32 64 128 256), losses := [] }

theorem u2260 : Upper (D 3) (R 3) [6,9,96,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2261 : Route 9 := (fun mask => (mask,id))

def c2261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2261 : Upper (D 3) (R 3) [6,9,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257] 13 (by decide) (choices 1) [1,64,128] r2261 c2261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u421
  · exact u422
  · exact u423

def r2262 : Route 9 := (fun mask => (mask,id))

def c2262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2262 : Upper (D 3) (R 3) [6,9,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288] 13 (by decide) (choices 1) [1,64,128] r2262 c2262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u424
  · exact u425
  · exact u426

def b2263 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 152 400 97 97 225 353), lower := (rows 7 11 100 152 400 32 64 128 256), losses := [] }

theorem u2263 : Upper (D 3) (R 3) [6,9,96,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2263
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 280 49 225 193 193 449), lower := (rows 7 11 100 280 49 32 64 128 256), losses := [] }

theorem u2264 : Upper (D 3) (R 3) [6,9,96,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 280 112 161 193 129 385), lower := (rows 7 11 100 280 112 32 64 128 256), losses := [] }

theorem u2265 : Upper (D 3) (R 3) [6,9,96,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2266 : Route 9 := (fun mask => (mask,id))

def c2266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2266 : Upper (D 3) (R 3) [6,9,96,272,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,129] 13 (by decide) (choices 1) [1,64,128] r2266 c2266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u427
  · exact u428
  · exact u429

def r2267 : Route 9 := (fun mask => (mask,id))

def c2267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2267 : Upper (D 3) (R 3) [6,9,96,272,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,160] 13 (by decide) (choices 1) [1,64,128] r2267 c2267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u430
  · exact u431
  · exact u432

def b2268 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 100 392 49 241 209 209 465), lower := (rows 7 11 100 392 49 32 64 128 256), losses := [] }

theorem u2268 : Upper (D 3) (R 3) [6,9,96,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 392 112 177 209 145 401), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u2269 : Upper (D 3) (R 3) [6,9,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 7 11 100 392 145 113 113 241 369), lower := (rows 7 11 100 392 145 32 64 128 256), losses := [] }

theorem u2270 : Upper (D 3) (R 3) [6,9,96,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2271 : Route 9 := (fun mask => (mask,id))

def c2271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2271 : Upper (D 3) (R 3) [6,9,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160] 13 (by decide) (choices 1) [1,16,64] r2271 c2271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u433
  · exact u434
  · exact u435

def b2272 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 11 261 56 49 224 192 192 448), lower := (rows 7 11 261 56 49 32 64 128 256), losses := [] }

theorem u2272 : Upper (D 3) (R 3) [6,9,257,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 56 81 224 224 224 480), lower := (rows 7 11 261 56 81 32 64 128 256), losses := [] }

theorem u2273 : Upper (D 3) (R 3) [6,9,257,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 261 56 112 225 193 193 449), lower := (rows 7 11 261 56 112 32 64 128 256), losses := [] }

theorem u2274 : Upper (D 3) (R 3) [6,9,257,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2275 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2275 : Upper (D 3) (R 3) [6,9,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,257,48,192] 13 (by decide) (choices 1) [1,64] r2275 c2275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u436
  · exact u437

def b2276 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 104 49 240 208 208 464), lower := (rows 7 11 261 104 49 32 64 128 256), losses := [] }

theorem u2276 : Upper (D 3) (R 3) [6,9,257,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 261 104 112 177 209 145 401), lower := (rows 7 11 261 104 112 32 64 128 256), losses := [] }

theorem u2277 : Upper (D 3) (R 3) [6,9,257,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 104 145 240 240 240 496), lower := (rows 7 11 261 104 145 32 64 128 256), losses := [] }

theorem u2278 : Upper (D 3) (R 3) [6,9,257,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2279 : Route 9 := (fun mask => (mask,id))

def c2279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2279 : Upper (D 3) (R 3) [6,9,257,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,257,96,160] 13 (by decide) (choices 1) [1,16,64,128] r2279 c2279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u438
  · exact u439
  · exact u440
  · exact u441

#print axioms u2279
end Delivery.IrregularNine14.P03
