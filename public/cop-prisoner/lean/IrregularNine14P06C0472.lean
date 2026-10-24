import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0156
import IrregularNine14P06C0157
import IrregularNine14P06C0158

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28320 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 28 82 417 481 417 417), lower := (rows 7 35 76 28 82 32 64 128 256), losses := [] }

theorem u28320 : Upper (D 6) (R 6) [6,33,72,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28320
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28321 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 76 28 112 419 451 387 387), lower := (rows 7 35 76 28 112 32 64 128 256), losses := [] }

theorem u28321 : Upper (D 6) (R 6) [6,33,72,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28321
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28322 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 498, targets := 4 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 35 76 28 145 354 354 482 354), lower := (rows 7 35 76 28 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 76 28 508 32 64 128 256) }] }

theorem u28322 : Upper (D 6) (R 6) [6,33,72,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28322
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28323 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 498, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 35 76 28 146 353 353 481 353), lower := (rows 7 35 76 28 146 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 76 28 508 32 64 128 256) }] }

theorem u28323 : Upper (D 6) (R 6) [6,33,72,20,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28323
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28324 : Route 9 := (fun mask => (mask,id))

def c28324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28324 : Upper (D 6) (R 6) [6,33,72,20,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,160] 13 (by decide) (choices 1) [1,2,64,256] r28324 c28324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9414
  · exact u9415
  · exact u9416
  · exact u9417

def b28325 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 76 28 208 291 355 419 291), lower := (rows 7 35 76 28 208 32 64 128 256), losses := [] }

theorem u28325 : Upper (D 6) (R 6) [6,33,72,20,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28325
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28326 : Route 9 := (fun mask => (mask,id))

def c28326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28326 : Upper (D 6) (R 6) [6,33,72,20,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,384] 13 (by decide) (choices 1) [1,2,64] r28326 c28326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9418
  · exact u9419
  · exact u9420

def b28327 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 76 56 19 484 452 452 452), lower := (rows 7 35 76 56 19 32 64 128 256), losses := [] }

theorem u28327 : Upper (D 6) (R 6) [6,33,72,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28327
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28328 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 482, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 35 76 56 21 482 450 450 450), lower := (rows 7 35 76 56 21 32 64 128 256), losses := [] }

theorem u28328 : Upper (D 6) (R 6) [6,33,72,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28328
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28329 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 482, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 76 56 22 481 449 449 449), lower := (rows 7 35 76 56 22 32 64 128 256), losses := [] }

theorem u28329 : Upper (D 6) (R 6) [6,33,72,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28329
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28330 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 76 56 81 422 454 390 390), lower := (rows 7 35 76 56 81 32 64 128 256), losses := [] }

theorem u28330 : Upper (D 6) (R 6) [6,33,72,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28330
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28331 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 76 56 82 421 453 389 389), lower := (rows 7 35 76 56 82 32 64 128 256), losses := [] }

theorem u28331 : Upper (D 6) (R 6) [6,33,72,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28331
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28332 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 56 84 419 451 387 387), lower := (rows 7 35 76 56 84 32 64 128 256), losses := [] }

theorem u28332 : Upper (D 6) (R 6) [6,33,72,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28332
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28333 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(3,0),(4,5)], upper := (rows 7 35 76 56 145 358 326 454 326), lower := (rows 7 35 76 56 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 33 65 129 257), good := (rows 486 482 76 60 508 32 64 128 256) }] }

theorem u28333 : Upper (D 6) (R 6) [6,33,72,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28333
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28334 : Route 9 := (fun mask => (mask,id))

def c28334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28334 : Upper (D 6) (R 6) [6,33,72,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,130] 13 (by decide) (choices 1) [1,4,64,256] r28334 c28334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9421
  · exact u9422
  · exact u9423
  · exact u9424

def r28335 : Route 9 := (fun mask => (mask,id))

def c28335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28335 : Upper (D 6) (R 6) [6,33,72,48,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,132] 13 (by decide) (choices 1) [1,2,64,256] r28335 c28335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9425
  · exact u9426
  · exact u9427
  · exact u9428

def b28336 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(4,5)], upper := (rows 7 35 76 56 208 295 327 391 263), lower := (rows 7 35 76 56 208 32 64 128 256), losses := [] }

theorem u28336 : Upper (D 6) (R 6) [6,33,72,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28336
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28337 : Route 9 := (fun mask => (mask,id))

def c28337 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28337 : Upper (D 6) (R 6) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [1,2,4,64] r28337 c28337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9429
  · exact u9430
  · exact u9431
  · exact u9432

def b28338 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 76 137 22 368 368 496 368), lower := (rows 7 35 76 137 22 32 64 128 256), losses := [] }

theorem u28338 : Upper (D 6) (R 6) [6,33,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28338
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28339 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 76 137 50 372 340 468 340), lower := (rows 7 35 76 137 50 32 64 128 256), losses := [] }

theorem u28339 : Upper (D 6) (R 6) [6,33,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28339
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28340 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 76 137 52 370 338 466 338), lower := (rows 7 35 76 137 52 32 64 128 256), losses := [] }

theorem u28340 : Upper (D 6) (R 6) [6,33,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28340
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28341 : Route 9 := (fun mask => (mask,id))

def c28341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28341 : Upper (D 6) (R 6) [6,33,72,129,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,66] 13 (by decide) (choices 1) [4,16,256] r28341 c28341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9433
  · exact u9434
  · exact u9435

def b28342 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 137 84 306 370 434 306), lower := (rows 7 35 76 137 84 32 64 128 256), losses := [] }

theorem u28342 : Upper (D 6) (R 6) [6,33,72,129,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28342
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28343 : Route 9 := (fun mask => (mask,id))

def c28343 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28343 : Upper (D 6) (R 6) [6,33,72,129,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96] 13 (by decide) (choices 1) [2,4,16,256] r28343 c28343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9436
  · exact u9437
  · exact u9438
  · exact u9439

def r28344 : Route 9 := (fun mask => (mask,id))

def c28344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28344 : Upper (D 6) (R 6) [6,33,72,129,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,258] 13 (by decide) (choices 1) [4,16,64] r28344 c28344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9440
  · exact u9441
  · exact u9442

def r28345 : Route 9 := (fun mask => (mask,id))

def c28345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28345 : Upper (D 6) (R 6) [6,33,72,129,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,260] 13 (by decide) (choices 1) [2,16,64] r28345 c28345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9443
  · exact u9444
  · exact u9445

def r28346 : Route 9 := (fun mask => (mask,id))

def c28346 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28346 : Upper (D 6) (R 6) [6,33,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,288] 13 (by decide) (choices 1) [2,4,16,64] r28346 c28346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9446
  · exact u9447
  · exact u9448
  · exact u9449

def r28347 : Route 9 := (fun mask => (mask,id))

def c28347 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28347 : Upper (D 6) (R 6) [6,33,72,129,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320] 13 (by decide) (choices 1) [2,4,16] r28347 c28347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9450
  · exact u9451
  · exact u9452

def b28348 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 138 21 368 368 496 368), lower := (rows 7 35 76 138 21 32 64 128 256), losses := [] }

theorem u28348 : Upper (D 6) (R 6) [6,33,72,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28348
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28349 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 138 49 372 340 468 340), lower := (rows 7 35 76 138 49 32 64 128 256), losses := [] }

theorem u28349 : Upper (D 6) (R 6) [6,33,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28349
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28350 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 76 138 52 369 337 465 337), lower := (rows 7 35 76 138 52 32 64 128 256), losses := [] }

theorem u28350 : Upper (D 6) (R 6) [6,33,72,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28350
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28351 : Route 9 := (fun mask => (mask,id))

def c28351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28351 : Upper (D 6) (R 6) [6,33,72,130,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,65] 13 (by decide) (choices 1) [4,16,256] r28351 c28351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9453
  · exact u9454
  · exact u9455

def b28352 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 138 84 305 369 433 305), lower := (rows 7 35 76 138 84 32 64 128 256), losses := [] }

theorem u28352 : Upper (D 6) (R 6) [6,33,72,130,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28352
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28353 : Route 9 := (fun mask => (mask,id))

def c28353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28353 : Upper (D 6) (R 6) [6,33,72,130,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,96] 13 (by decide) (choices 1) [1,4,16,256] r28353 c28353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9456
  · exact u9457
  · exact u9458
  · exact u9459

def r28354 : Route 9 := (fun mask => (mask,id))

def c28354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28354 : Upper (D 6) (R 6) [6,33,72,130,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,257] 13 (by decide) (choices 1) [4,16,64] r28354 c28354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9460
  · exact u9461
  · exact u9462

def r28355 : Route 9 := (fun mask => (mask,id))

def c28355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28355 : Upper (D 6) (R 6) [6,33,72,130,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,260] 13 (by decide) (choices 1) [1,16,64] r28355 c28355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9463
  · exact u9464
  · exact u9465

def r28356 : Route 9 := (fun mask => (mask,id))

def c28356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28356 : Upper (D 6) (R 6) [6,33,72,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,288] 13 (by decide) (choices 1) [1,4,16,64] r28356 c28356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9466
  · exact u9467
  · exact u9468
  · exact u9469

def r28357 : Route 9 := (fun mask => (mask,id))

def c28357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28357 : Upper (D 6) (R 6) [6,33,72,130,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,320] 13 (by decide) (choices 1) [1,4,16] r28357 c28357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9470
  · exact u9471
  · exact u9472

def b28358 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 140 19 368 368 496 368), lower := (rows 7 35 76 140 19 32 64 128 256), losses := [] }

theorem u28358 : Upper (D 6) (R 6) [6,33,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28358
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28359 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 76 140 49 370 338 466 338), lower := (rows 7 35 76 140 49 32 64 128 256), losses := [] }

theorem u28359 : Upper (D 6) (R 6) [6,33,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28359
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28360 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 140 50 369 337 465 337), lower := (rows 7 35 76 140 50 32 64 128 256), losses := [] }

theorem u28360 : Upper (D 6) (R 6) [6,33,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28360
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28361 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 7 35 76 140 81 306 370 434 306), lower := (rows 7 35 76 140 81 32 64 128 256), losses := [] }

theorem u28361 : Upper (D 6) (R 6) [6,33,72,132,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28361
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28362 : Route 9 := (fun mask => (mask,id))

def c28362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28362 : Upper (D 6) (R 6) [6,33,72,132,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,66] 13 (by decide) (choices 1) [1,16,256] r28362 c28362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9473
  · exact u9474
  · exact u9475

def r28363 : Route 9 := (fun mask => (mask,id))

def c28363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28363 : Upper (D 6) (R 6) [6,33,72,132,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,96] 13 (by decide) (choices 1) [1,2,16,256] r28363 c28363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9476
  · exact u9477
  · exact u9478
  · exact u9479

def r28364 : Route 9 := (fun mask => (mask,id))

def c28364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28364 : Upper (D 6) (R 6) [6,33,72,132,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,257] 13 (by decide) (choices 1) [2,16,64] r28364 c28364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9480
  · exact u9481
  · exact u9482

def r28365 : Route 9 := (fun mask => (mask,id))

def c28365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28365 : Upper (D 6) (R 6) [6,33,72,132,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,258] 13 (by decide) (choices 1) [1,16,64] r28365 c28365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9483
  · exact u9484
  · exact u9485

def r28366 : Route 9 := (fun mask => (mask,id))

def c28366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28366 : Upper (D 6) (R 6) [6,33,72,132,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,288] 13 (by decide) (choices 1) [1,2,16,64] r28366 c28366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9486
  · exact u9487
  · exact u9488
  · exact u9489

def r28367 : Route 9 := (fun mask => (mask,id))

def c28367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28367 : Upper (D 6) (R 6) [6,33,72,132,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,320] 13 (by decide) (choices 1) [1,2,16] r28367 c28367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9490
  · exact u9491
  · exact u9492

def b28368 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 152 19 356 356 484 356), lower := (rows 7 35 76 152 19 32 64 128 256), losses := [] }

theorem u28368 : Upper (D 6) (R 6) [6,33,72,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28368
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28369 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 35 76 152 21 354 354 482 354), lower := (rows 7 35 76 152 21 32 64 128 256), losses := [] }

theorem u28369 : Upper (D 6) (R 6) [6,33,72,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28369
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28370 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 35 76 152 22 353 353 481 353), lower := (rows 7 35 76 152 22 32 64 128 256), losses := [] }

theorem u28370 : Upper (D 6) (R 6) [6,33,72,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28370
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28371 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 152 49 358 326 454 326), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u28371 : Upper (D 6) (R 6) [6,33,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28372 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 76 152 50 357 325 453 325), lower := (rows 7 35 76 152 50 32 64 128 256), losses := [] }

theorem u28372 : Upper (D 6) (R 6) [6,33,72,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28372
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28373 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 3, targets := 64 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,6),(1,2),(1,6)], upper := (rows 7 35 76 152 52 355 323 451 323), lower := (rows 7 35 76 152 52 32 64 128 256), losses := [] }

theorem u28373 : Upper (D 6) (R 6) [6,33,72,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28373
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28374 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 7 35 76 152 81 294 358 422 294), lower := (rows 7 35 76 152 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 33 65 129 257), good := (rows 486 482 76 156 508 32 64 128 256) }] }

theorem u28374 : Upper (D 6) (R 6) [6,33,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28375 : Route 9 := (fun mask => (mask,id))

def c28375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28375 : Upper (D 6) (R 6) [6,33,72,144,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,66] 13 (by decide) (choices 1) [1,4,256] r28375 c28375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9493
  · exact u9494
  · exact u9495

def b28376 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 76 152 84 291 355 419 291), lower := (rows 7 35 76 152 84 32 64 128 256), losses := [] }

theorem u28376 : Upper (D 6) (R 6) [6,33,72,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28376
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28377 : Route 9 := (fun mask => (mask,id))

def c28377 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28377 : Upper (D 6) (R 6) [6,33,72,144,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,96] 13 (by decide) (choices 1) [1,2,4,256] r28377 c28377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9496
  · exact u9497
  · exact u9498
  · exact u9499

def r28378 : Route 9 := (fun mask => (mask,id))

def c28378 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28378 : Upper (D 6) (R 6) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [2,4,64] r28378 c28378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9500
  · exact u9501
  · exact u9502

def r28379 : Route 9 := (fun mask => (mask,id))

def c28379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28379 : Upper (D 6) (R 6) [6,33,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258] 13 (by decide) (choices 1) [1,4,64] r28379 c28379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9503
  · exact u9504
  · exact u9505

#print axioms u28379
end Delivery.IrregularNine14.P06
