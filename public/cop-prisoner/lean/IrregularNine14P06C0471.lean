import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0155
import IrregularNine14P06C0156

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28260 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 69 26 84 424 488 424 424), lower := (rows 7 35 69 26 84 32 64 128 256), losses := [] }

theorem u28260 : Upper (D 6) (R 6) [6,33,65,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28260
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28261 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 26 88 420 484 420 420), lower := (rows 7 35 69 26 88 32 64 128 256), losses := [] }

theorem u28261 : Upper (D 6) (R 6) [6,33,65,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28261
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28262 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 26 112 428 460 396 396), lower := (rows 7 35 69 26 112 32 64 128 256), losses := [] }

theorem u28262 : Upper (D 6) (R 6) [6,33,65,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28262
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28263 : Route 9 := (fun mask => (mask,id))

def c28263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28263 : Upper (D 6) (R 6) [6,33,65,18,132] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,132] 13 (by decide) (choices 1) [8,64,256] r28263 c28263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9347
  · exact u9348
  · exact u9349

def b28264 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 26 152 356 356 484 356), lower := (rows 7 35 69 26 152 32 64 128 256), losses := [] }

theorem u28264 : Upper (D 6) (R 6) [6,33,65,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28264
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28265 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 26 176 364 332 460 332), lower := (rows 7 35 69 26 176 32 64 128 256), losses := [] }

theorem u28265 : Upper (D 6) (R 6) [6,33,65,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28265
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28266 : Route 9 := (fun mask => (mask,id))

def c28266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28266 : Upper (D 6) (R 6) [6,33,65,18,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,192] 13 (by decide) (choices 1) [4,8,256] r28266 c28266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9350
  · exact u9351
  · exact u9352

def r28267 : Route 9 := (fun mask => (mask,id))

def c28267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28267 : Upper (D 6) (R 6) [6,33,65,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,384] 13 (by decide) (choices 1) [4,8,64] r28267 c28267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9353
  · exact u9354
  · exact u9355

def b28268 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 88 436 468 404 404), lower := (rows 7 35 69 42 88 32 64 128 256), losses := [] }

theorem u28268 : Upper (D 6) (R 6) [6,33,65,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28268
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28269 : PairBound 9 := { available := 344, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 148 376 344 472 344), lower := (rows 7 35 69 42 148 32 64 128 256), losses := [] }

theorem u28269 : Upper (D 6) (R 6) [6,33,65,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28269
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28270 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 152 372 340 468 340), lower := (rows 7 35 69 42 152 32 64 128 256), losses := [] }

theorem u28270 : Upper (D 6) (R 6) [6,33,65,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28270
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28271 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 208 316 348 412 284), lower := (rows 7 35 69 42 208 32 64 128 256), losses := [] }

theorem u28271 : Upper (D 6) (R 6) [6,33,65,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28271
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28272 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 400 124 92 220 348), lower := (rows 7 35 69 42 400 32 64 128 256), losses := [] }

theorem u28272 : Upper (D 6) (R 6) [6,33,65,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28272
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28273 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 88 434 466 402 402), lower := (rows 7 35 69 44 88 32 64 128 256), losses := [] }

theorem u28273 : Upper (D 6) (R 6) [6,33,65,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28273
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28274 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 146 376 344 472 344), lower := (rows 7 35 69 44 146 32 64 128 256), losses := [] }

theorem u28274 : Upper (D 6) (R 6) [6,33,65,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28274
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28275 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 152 370 338 466 338), lower := (rows 7 35 69 44 152 32 64 128 256), losses := [] }

theorem u28275 : Upper (D 6) (R 6) [6,33,65,36,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28275
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28276 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 208 314 346 410 282), lower := (rows 7 35 69 44 208 32 64 128 256), losses := [] }

theorem u28276 : Upper (D 6) (R 6) [6,33,65,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28276
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28277 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 400 122 90 218 346), lower := (rows 7 35 69 44 400 32 64 128 256), losses := [] }

theorem u28277 : Upper (D 6) (R 6) [6,33,65,36,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28277
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28278 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 56 88 422 454 390 390), lower := (rows 7 35 69 56 88 32 64 128 256), losses := [] }

theorem u28278 : Upper (D 6) (R 6) [6,33,65,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28278
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28279 : Route 9 := (fun mask => (mask,id))

def c28279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28279 : Upper (D 6) (R 6) [6,33,65,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,130] 13 (by decide) (choices 1) [4,8,64,256] r28279 c28279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9356
  · exact u9357
  · exact u9358
  · exact u9359

def r28280 : Route 9 := (fun mask => (mask,id))

def c28280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28280 : Upper (D 6) (R 6) [6,33,65,48,132] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,132] 13 (by decide) (choices 1) [2,8,64,256] r28280 c28280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9360
  · exact u9361
  · exact u9362
  · exact u9363

def b28281 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 56 152 358 326 454 326), lower := (rows 7 35 69 56 152 32 64 128 256), losses := [] }

theorem u28281 : Upper (D 6) (R 6) [6,33,65,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28281
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28282 : Route 9 := (fun mask => (mask,id))

def c28282 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28282 : Upper (D 6) (R 6) [6,33,65,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192] 13 (by decide) (choices 1) [2,4,8,256] r28282 c28282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9364
  · exact u9365
  · exact u9366
  · exact u9367

def r28283 : Route 9 := (fun mask => (mask,id))

def c28283 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28283 : Upper (D 6) (R 6) [6,33,65,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,384] 13 (by decide) (choices 1) [2,4,8,64] r28283 c28283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9368
  · exact u9369
  · exact u9370
  · exact u9371

def r28284 : Route 9 := (fun mask => (mask,id))

def c28284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28284 : Upper (D 6) (R 6) [6,33,65,96,130] 13 := by
  apply FastRouting.sound _ _ [6,33,65,96,130] 13 (by decide) (choices 1) [4,8,16,256] r28284 c28284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9372
  · exact u9373
  · exact u9374
  · exact u9375

def r28285 : Route 9 := (fun mask => (mask,id))

def c28285 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28285 : Upper (D 6) (R 6) [6,33,65,96,136] 13 := by
  apply FastRouting.sound _ _ [6,33,65,96,136] 13 (by decide) (choices 1) [2,4,16,256] r28285 c28285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9376
  · exact u9377
  · exact u9378
  · exact u9379

def r28286 : Route 9 := (fun mask => (mask,id))

def c28286 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28286 : Upper (D 6) (R 6) [6,33,65,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,96,384] 13 (by decide) (choices 1) [2,4,8,16] r28286 c28286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9380
  · exact u9381
  · exact u9382
  · exact u9383

def r28287 : Route 9 := (fun mask => (mask,id))

def c28287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28287 : Upper (D 6) (R 6) [6,33,65,130,260] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,260] 13 (by decide) (choices 1) [8,16,64] r28287 c28287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9384
  · exact u9385
  · exact u9386

def r28288 : Route 9 := (fun mask => (mask,id))

def c28288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28288 : Upper (D 6) (R 6) [6,33,65,130,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,264] 13 (by decide) (choices 1) [4,16,64] r28288 c28288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9387
  · exact u9388
  · exact u9389

def r28289 : Route 9 := (fun mask => (mask,id))

def c28289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28289 : Upper (D 6) (R 6) [6,33,65,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,288] 13 (by decide) (choices 1) [4,8,16,64] r28289 c28289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9390
  · exact u9391
  · exact u9392
  · exact u9393

def r28290 : Route 9 := (fun mask => (mask,id))

def c28290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28290 : Upper (D 6) (R 6) [6,33,65,130,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,320] 13 (by decide) (choices 1) [4,8,16] r28290 c28290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9394
  · exact u9395
  · exact u9396

def r28291 : Route 9 := (fun mask => (mask,id))

def c28291 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28291 : Upper (D 6) (R 6) [6,33,65,144,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,264] 13 (by decide) (choices 1) [2,4,64] r28291 c28291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9397
  · exact u9398
  · exact u9399

def r28292 : Route 9 := (fun mask => (mask,id))

def c28292 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28292 : Upper (D 6) (R 6) [6,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288] 13 (by decide) (choices 1) [2,4,8,64] r28292 c28292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9400
  · exact u9401
  · exact u9402
  · exact u9403

def r28293 : Route 9 := (fun mask => (mask,id))

def c28293 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28293 : Upper (D 6) (R 6) [6,33,65,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,320] 13 (by decide) (choices 1) [2,4,8,16] r28293 c28293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9404
  · exact u9405
  · exact u9406
  · exact u9407

def b28294 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 76 25 22 480 480 480 480), lower := (rows 7 35 76 25 22 32 64 128 256), losses := [] }

theorem u28294 : Upper (D 6) (R 6) [6,33,72,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28294
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28295 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 76 25 50 484 452 452 452), lower := (rows 7 35 76 25 50 32 64 128 256), losses := [] }

theorem u28295 : Upper (D 6) (R 6) [6,33,72,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28295
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28296 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 25 52 482 450 450 450), lower := (rows 7 35 76 25 52 32 64 128 256), losses := [] }

theorem u28296 : Upper (D 6) (R 6) [6,33,72,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28296
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28297 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 13, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 25 82 420 484 420 420), lower := (rows 7 35 76 25 82 32 64 128 256), losses := [] }

theorem u28297 : Upper (D 6) (R 6) [6,33,72,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28297
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28298 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 25 84 418 482 418 418), lower := (rows 7 35 76 25 84 32 64 128 256), losses := [] }

theorem u28298 : Upper (D 6) (R 6) [6,33,72,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28298
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28299 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 76 25 112 422 454 390 390), lower := (rows 7 35 76 25 112 32 64 128 256), losses := [] }

theorem u28299 : Upper (D 6) (R 6) [6,33,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28299
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28300 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 496, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 25 146 356 356 484 356), lower := (rows 7 35 76 25 146 32 64 128 256), losses := [] }

theorem u28300 : Upper (D 6) (R 6) [6,33,72,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28300
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28301 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 76 25 148 354 354 482 354), lower := (rows 7 35 76 25 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 35 67 131 259), good := (rows 502 498 92 508 148 32 64 128 256) }] }

theorem u28301 : Upper (D 6) (R 6) [6,33,72,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28301
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28302 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 496, targets := 1 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 7 35 76 25 176 358 326 454 326), lower := (rows 7 35 76 25 176 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 33 65 129 257), good := (rows 502 498 92 508 176 32 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 65 129 257), good := (rows 455 451 76 477 144 0 64 128 256) }] }

theorem u28302 : Upper (D 6) (R 6) [6,33,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28302
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28303 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 76 25 208 294 358 422 294), lower := (rows 7 35 76 25 208 32 64 128 256), losses := [] }

theorem u28303 : Upper (D 6) (R 6) [6,33,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28303
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28304 : Route 9 := (fun mask => (mask,id))

def c28304 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28304 : Upper (D 6) (R 6) [6,33,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,384] 13 (by decide) (choices 1) [2,4,64] r28304 c28304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9408
  · exact u9409
  · exact u9410

def b28305 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 76 26 21 480 480 480 480), lower := (rows 7 35 76 26 21 32 64 128 256), losses := [] }

theorem u28305 : Upper (D 6) (R 6) [6,33,72,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28305
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28306 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 76 26 49 484 452 452 452), lower := (rows 7 35 76 26 49 32 64 128 256), losses := [] }

theorem u28306 : Upper (D 6) (R 6) [6,33,72,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28306
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28307 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 26 52 481 449 449 449), lower := (rows 7 35 76 26 52 32 64 128 256), losses := [] }

theorem u28307 : Upper (D 6) (R 6) [6,33,72,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28307
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28308 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 7 35 76 26 81 420 484 420 420), lower := (rows 7 35 76 26 81 32 64 128 256), losses := [] }

theorem u28308 : Upper (D 6) (R 6) [6,33,72,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28308
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28309 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 26 84 417 481 417 417), lower := (rows 7 35 76 26 84 32 64 128 256), losses := [] }

theorem u28309 : Upper (D 6) (R 6) [6,33,72,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28309
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28310 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(0,6),(1,6)], upper := (rows 7 35 76 26 112 421 453 389 389), lower := (rows 7 35 76 26 112 32 64 128 256), losses := [] }

theorem u28310 : Upper (D 6) (R 6) [6,33,72,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28310
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28311 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 76 26 145 356 356 484 356), lower := (rows 7 35 76 26 145 32 64 128 256), losses := [] }

theorem u28311 : Upper (D 6) (R 6) [6,33,72,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28311
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28312 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 76 26 148 353 353 481 353), lower := (rows 7 35 76 26 148 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 35 67 131 259), good := (rows 501 497 92 508 148 32 64 128 256) }] }

theorem u28312 : Upper (D 6) (R 6) [6,33,72,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28312
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28313 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 325, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 35 76 26 176 357 325 453 325), lower := (rows 7 35 76 26 176 32 64 128 256), losses := [] }

theorem u28313 : Upper (D 6) (R 6) [6,33,72,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28313
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28314 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 76 26 208 293 357 421 293), lower := (rows 7 35 76 26 208 32 64 128 256), losses := [] }

theorem u28314 : Upper (D 6) (R 6) [6,33,72,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28314
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28315 : Route 9 := (fun mask => (mask,id))

def c28315 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28315 : Upper (D 6) (R 6) [6,33,72,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,384] 13 (by decide) (choices 1) [1,4,64] r28315 c28315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9411
  · exact u9412
  · exact u9413

def b28316 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 76 28 19 480 480 480 480), lower := (rows 7 35 76 28 19 32 64 128 256), losses := [] }

theorem u28316 : Upper (D 6) (R 6) [6,33,72,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28316
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28317 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 498, targets := 4 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 76 28 49 482 450 450 450), lower := (rows 7 35 76 28 49 32 64 128 256), losses := [] }

theorem u28317 : Upper (D 6) (R 6) [6,33,72,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28317
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28318 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 28 50 481 449 449 449), lower := (rows 7 35 76 28 50 32 64 128 256), losses := [] }

theorem u28318 : Upper (D 6) (R 6) [6,33,72,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28318
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28319 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 76 28 81 418 482 418 418), lower := (rows 7 35 76 28 81 32 64 128 256), losses := [] }

theorem u28319 : Upper (D 6) (R 6) [6,33,72,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28319
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28319
end Delivery.IrregularNine14.P06
