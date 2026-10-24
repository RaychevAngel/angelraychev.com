import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0040
import IrregularNine14P01C0041

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6300 : Route 9 := (fun mask => (mask,id))

def c6300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u6300 : Upper (D 1) (R 1) [50,5,72,144] 13 := by
  apply FastRouting.sound _ _ [50,5,72,144] 13 (by decide) (choices 1) [2,32,64,128,256] r6300 c6300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2459
  · exact u2460
  · exact u2461
  · exact u2462
  · exact u2463

def b6301 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 200 434 434 498 434 434), lower := (rows 51 7 76 200 16 32 64 128 256), losses := [] }

theorem u6301 : Upper (D 1) (R 1) [50,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6302 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 266 240 240 240 240 496), lower := (rows 51 7 76 266 16 32 64 128 256), losses := [] }

theorem u6302 : Upper (D 1) (R 1) [50,5,72,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6303 : Route 9 := (fun mask => (mask,id))

def c6303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6303 : Upper (D 1) (R 1) [50,5,72,272] 13 := by
  apply FastRouting.sound _ _ [50,5,72,272] 13 (by decide) (choices 1) [2,32,64,128] r6303 c6303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2464
  · exact u2465
  · exact u2466
  · exact u2467

def b6304 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 328 178 178 242 178 434), lower := (rows 51 7 76 328 16 32 64 128 256), losses := [] }

theorem u6304 : Upper (D 1) (R 1) [50,5,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6305 : Route 9 := (fun mask => (mask,id))

def c6305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6305 : Upper (D 1) (R 1) [50,5,72,384] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384] 13 (by decide) (choices 1) [2,32,64,128] r6305 c6305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2468
  · exact u2469
  · exact u2470
  · exact u2471

def b6306 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 196 26 504 488 488 488 488), lower := (rows 51 7 196 26 16 32 64 128 256), losses := [] }

theorem u6306 : Upper (D 1) (R 1) [50,5,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 196 56 474 490 458 458 458), lower := (rows 51 7 196 56 16 32 64 128 256), losses := [] }

theorem u6307 : Upper (D 1) (R 1) [50,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6308 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 196 74 440 440 504 440 440), lower := (rows 51 7 196 74 16 32 64 128 256), losses := [] }

theorem u6308 : Upper (D 1) (R 1) [50,5,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6309 : Route 9 := (fun mask => (mask,id))

def c6309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u6309 : Upper (D 1) (R 1) [50,5,192,80] 13 := by
  apply FastRouting.sound _ _ [50,5,192,80] 13 (by decide) (choices 1) [2,8,32,128,256] r6309 c6309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2472
  · exact u2473
  · exact u2474
  · exact u2475
  · exact u2476

def b6310 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 196 200 314 314 378 442 314), lower := (rows 51 7 196 200 16 32 64 128 256), losses := [] }

theorem u6310 : Upper (D 1) (R 1) [50,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6311 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 196 266 248 248 248 248 504), lower := (rows 51 7 196 266 16 32 64 128 256), losses := [] }

theorem u6311 : Upper (D 1) (R 1) [50,5,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6312 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6312 : Upper (D 1) (R 1) [50,5,192,272] 13 := by
  apply FastRouting.sound _ _ [50,5,192,272] 13 (by decide) (choices 1) [2,8,32,64] r6312 c6312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2477
  · exact u2478
  · exact u2479
  · exact u2480

def r6313 : Route 9 := (fun mask => (mask,id))

def c6313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6313 : Upper (D 1) (R 1) [50,5,192,320] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320] 13 (by decide) (choices 1) [2,8,32,128] r6313 c6313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2481
  · exact u2482
  · exact u2483
  · exact u2484

def b6314 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 268 26 240 224 224 224 480), lower := (rows 51 7 268 26 16 32 64 128 256), losses := [] }

theorem u6314 : Upper (D 1) (R 1) [50,5,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6315 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 268 56 210 226 194 194 450), lower := (rows 51 7 268 56 16 32 64 128 256), losses := [] }

theorem u6315 : Upper (D 1) (R 1) [50,5,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6316 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 74 240 240 240 240 496), lower := (rows 51 7 268 74 16 32 64 128 256), losses := [] }

theorem u6316 : Upper (D 1) (R 1) [50,5,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6317 : Route 9 := (fun mask => (mask,id))

def c6317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6317 : Upper (D 1) (R 1) [50,5,264,80] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80] 13 (by decide) (choices 1) [2,32,64,128] r6317 c6317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2485
  · exact u2486
  · exact u2487
  · exact u2488

def r6318 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6318 : Upper (D 1) (R 1) [50,5,264,192] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192] 13 (by decide) (choices 1) [2,32,64] r6318 c6318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2489
  · exact u2490
  · exact u2491

def b6319 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 7 324 26 248 232 232 232 488), lower := (rows 51 7 324 26 16 32 64 128 256), losses := [] }

theorem u6319 : Upper (D 1) (R 1) [50,5,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6320 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 324 56 218 234 202 202 458), lower := (rows 51 7 324 56 16 32 64 128 256), losses := [] }

theorem u6320 : Upper (D 1) (R 1) [50,5,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6321 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 74 184 184 248 184 440), lower := (rows 51 7 324 74 16 32 64 128 256), losses := [] }

theorem u6321 : Upper (D 1) (R 1) [50,5,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6322 : Route 9 := (fun mask => (mask,id))

def c6322 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6322 : Upper (D 1) (R 1) [50,5,320,80] 13 := by
  apply FastRouting.sound _ _ [50,5,320,80] 13 (by decide) (choices 1) [2,8,32,128] r6322 c6322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2492
  · exact u2493
  · exact u2494
  · exact u2495

def b6323 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 138 248 248 248 248 504), lower := (rows 51 7 324 138 16 32 64 128 256), losses := [] }

theorem u6323 : Upper (D 1) (R 1) [50,5,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6324 : Route 9 := (fun mask => (mask,id))

def c6324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6324 : Upper (D 1) (R 1) [50,5,320,144] 13 := by
  apply FastRouting.sound _ _ [50,5,320,144] 13 (by decide) (choices 1) [2,8,32,64,128] r6324 c6324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2496
  · exact u2497
  · exact u2498
  · exact u2499
  · exact u2500

def r6325 : Route 9 := (fun mask => (mask,id))

def c6325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6325 : Upper (D 1) (R 1) [50,5,320,192] 13 := by
  apply FastRouting.sound _ _ [50,5,320,192] 13 (by decide) (choices 1) [2,8,32,128] r6325 c6325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2501
  · exact u2502
  · exact u2503
  · exact u2504

def b6326 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 7 200 496 496 496 496 496), lower := (rows 51 14 7 200 16 32 64 128 256), losses := [] }

theorem u6326 : Upper (D 1) (R 1) [50,12,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 7 328 240 240 240 240 496), lower := (rows 51 14 7 328 16 32 64 128 256), losses := [] }

theorem u6327 : Upper (D 1) (R 1) [50,12,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6327
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6328 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 21 200 498 482 482 482 482), lower := (rows 51 14 21 200 16 32 64 128 256), losses := [] }

theorem u6328 : Upper (D 1) (R 1) [50,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6329 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 21 328 242 226 226 226 482), lower := (rows 51 14 21 328 16 32 64 128 256), losses := [] }

theorem u6329 : Upper (D 1) (R 1) [50,12,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6330 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 22 73 496 480 480 480 480), lower := (rows 51 14 22 73 16 32 64 128 256), losses := [] }

theorem u6330 : Upper (D 1) (R 1) [50,12,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6331 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 22 200 497 481 481 481 481), lower := (rows 51 14 22 200 16 32 64 128 256), losses := [] }

theorem u6331 : Upper (D 1) (R 1) [50,12,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6332 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 22 265 240 224 224 224 480), lower := (rows 51 14 22 265 16 32 64 128 256), losses := [] }

theorem u6332 : Upper (D 1) (R 1) [50,12,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6333 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 14 22 328 241 225 225 225 481), lower := (rows 51 14 22 328 16 32 64 128 256), losses := [] }

theorem u6333 : Upper (D 1) (R 1) [50,12,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6334 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 52 73 466 482 450 450 450), lower := (rows 51 14 52 73 16 32 64 128 256), losses := [] }

theorem u6334 : Upper (D 1) (R 1) [50,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6335 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 52 200 467 483 451 451 451), lower := (rows 51 14 52 200 16 32 64 128 256), losses := [] }

theorem u6335 : Upper (D 1) (R 1) [50,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6336 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 52 265 210 226 194 194 450), lower := (rows 51 14 52 265 16 32 64 128 256), losses := [] }

theorem u6336 : Upper (D 1) (R 1) [50,12,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6336
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6337 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 52 328 211 227 195 195 451), lower := (rows 51 14 52 328 16 32 64 128 256), losses := [] }

theorem u6337 : Upper (D 1) (R 1) [50,12,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6338 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 69 74 432 432 496 432 432), lower := (rows 51 14 69 74 16 32 64 128 256), losses := [] }

theorem u6338 : Upper (D 1) (R 1) [50,12,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6339 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 452, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 88 434 418 482 418 418), lower := (rows 51 14 69 88 16 32 64 128 256), losses := [] }

theorem u6339 : Upper (D 1) (R 1) [50,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6340 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 69 138 496 496 496 496 496), lower := (rows 51 14 69 138 16 32 64 128 256), losses := [] }

theorem u6340 : Upper (D 1) (R 1) [50,12,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6341 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 452, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 152 498 482 482 482 482), lower := (rows 51 14 69 152 16 32 64 128 256), losses := [] }

theorem u6341 : Upper (D 1) (R 1) [50,12,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6342 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 69 200 434 434 498 434 434), lower := (rows 51 14 69 200 16 32 64 128 256), losses := [] }

theorem u6342 : Upper (D 1) (R 1) [50,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6343 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 69 266 240 240 240 240 496), lower := (rows 51 14 69 266 16 32 64 128 256), losses := [] }

theorem u6343 : Upper (D 1) (R 1) [50,12,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6344 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 280 242 226 226 226 482), lower := (rows 51 14 69 280 16 32 64 128 256), losses := [] }

theorem u6344 : Upper (D 1) (R 1) [50,12,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6345 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 69 328 178 178 242 178 434), lower := (rows 51 14 69 328 16 32 64 128 256), losses := [] }

theorem u6345 : Upper (D 1) (R 1) [50,12,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6346 : Route 9 := (fun mask => (mask,id))

def c6346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6346 : Upper (D 1) (R 1) [50,12,65,384] 13 := by
  apply FastRouting.sound _ _ [50,12,65,384] 13 (by decide) (choices 1) [2,32,64,128] r6346 c6346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2505
  · exact u2506
  · exact u2507
  · exact u2508

def b6347 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 70 200 433 433 497 433 433), lower := (rows 51 14 70 200 16 32 64 128 256), losses := [] }

theorem u6347 : Upper (D 1) (R 1) [50,12,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6347
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6348 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 14 70 265 240 240 240 240 496), lower := (rows 51 14 70 265 16 32 64 128 256), losses := [] }

theorem u6348 : Upper (D 1) (R 1) [50,12,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6349 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 70 328 177 177 241 177 433), lower := (rows 51 14 70 328 16 32 64 128 256), losses := [] }

theorem u6349 : Upper (D 1) (R 1) [50,12,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6349
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6350 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 14 70 392 241 241 241 241 497), lower := (rows 51 14 70 392 16 32 64 128 256), losses := [] }

theorem u6350 : Upper (D 1) (R 1) [50,12,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6350
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6351 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 200 435 419 483 419 419), lower := (rows 51 14 84 200 16 32 64 128 256), losses := [] }

theorem u6351 : Upper (D 1) (R 1) [50,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6352 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 265 242 226 226 226 482), lower := (rows 51 14 84 265 16 32 64 128 256), losses := [] }

theorem u6352 : Upper (D 1) (R 1) [50,12,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6352
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6353 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 328 179 163 227 163 419), lower := (rows 51 14 84 328 16 32 64 128 256), losses := [] }

theorem u6353 : Upper (D 1) (R 1) [50,12,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6354 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 392 243 227 227 227 483), lower := (rows 51 14 84 392 16 32 64 128 256), losses := [] }

theorem u6354 : Upper (D 1) (R 1) [50,12,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6354
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6355 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 51 14 196 200 307 307 371 435 307), lower := (rows 51 14 196 200 16 32 64 128 256), losses := [] }

theorem u6355 : Upper (D 1) (R 1) [50,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6355
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6356 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6356 : Upper (D 1) (R 1) [50,12,192,257] 13 := by
  apply FastRouting.sound _ _ [50,12,192,257] 13 (by decide) (choices 1) [2,32,64] r6356 c6356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2509
  · exact u2510
  · exact u2511

def b6357 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 196 266 241 241 241 241 497), lower := (rows 51 14 196 266 16 32 64 128 256), losses := [] }

theorem u6357 : Upper (D 1) (R 1) [50,12,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6358 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 196 280 243 227 227 227 483), lower := (rows 51 14 196 280 16 32 64 128 256), losses := [] }

theorem u6358 : Upper (D 1) (R 1) [50,12,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6359 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 196 328 179 179 243 179 435), lower := (rows 51 14 196 328 16 32 64 128 256), losses := [] }

theorem u6359 : Upper (D 1) (R 1) [50,12,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6359
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6359
end Delivery.IrregularNine14.P01
