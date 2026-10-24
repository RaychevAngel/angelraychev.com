import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0522
import IrregularNine14P07C0523
import IrregularNine14P07C0524
import IrregularNine14P07C0525
import IrregularNine14P07C0526

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41340 : Route 9 := (fun mask => (mask,id))

def c41340 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41340 : Upper (D 7) (R 7) [6,96,40,17] 13 := by
  apply FastRouting.sound _ _ [6,96,40,17] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41340 c41340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31339
  · exact u31340
  · exact u31341
  · exact u31342
  · exact u31343
  · exact u31344
  · exact u31345
  · exact u31346
  · exact u31347
  · exact u31348

def r41341 : Route 9 := (fun mask => (mask,id))

def c41341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41341 : Upper (D 7) (R 7) [6,96,40,18] 13 := by
  apply FastRouting.sound _ _ [6,96,40,18] 13 (by decide) (choices 2) [65,129,192,257,320,384] r41341 c41341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31349
  · exact u31350
  · exact u31351
  · exact u31352
  · exact u31353
  · exact u31354

def b41342 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 98 44 73 403 435 467 403 403), lower := (rows 7 98 44 73 16 32 64 128 256), losses := [] }

theorem u41342 : Upper (D 7) (R 7) [6,96,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41343 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 7 98 44 74 401 433 465 401 401), lower := (rows 7 98 44 74 16 32 64 128 256), losses := [] }

theorem u41343 : Upper (D 7) (R 7) [6,96,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41344 : Route 9 := (fun mask => (mask,id))

def c41344 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41344 : Upper (D 7) (R 7) [6,96,40,80] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41344 c41344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31355
  · exact u31356
  · exact u31357
  · exact u31358
  · exact u31359
  · exact u31360

def r41345 : Route 9 := (fun mask => (mask,id))

def c41345 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41345 : Upper (D 7) (R 7) [6,96,40,129] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41345 c41345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31361
  · exact u31362
  · exact u31363
  · exact u31364
  · exact u31365
  · exact u31366
  · exact u31367
  · exact u31368
  · exact u31369
  · exact u31370

def r41346 : Route 9 := (fun mask => (mask,id))

def c41346 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41346 : Upper (D 7) (R 7) [6,96,40,130] 13 := by
  apply FastRouting.sound _ _ [6,96,40,130] 13 (by decide) (choices 2) [65,129,192,257,320,384] r41346 c41346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31371
  · exact u31372
  · exact u31373
  · exact u31374
  · exact u31375
  · exact u31376

def r41347 : Route 9 := (fun mask => (mask,id))

def c41347 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41347 : Upper (D 7) (R 7) [6,96,40,144] 13 := by
  apply FastRouting.sound _ _ [6,96,40,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41347 c41347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31377
  · exact u31378
  · exact u31379
  · exact u31380
  · exact u31381
  · exact u31382
  · exact u31383
  · exact u31384
  · exact u31385
  · exact u31386

def r41348 : Route 9 := (fun mask => (mask,id))

def c41348 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41348 : Upper (D 7) (R 7) [6,96,40,192] 13 := by
  apply FastRouting.sound _ _ [6,96,40,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41348 c41348
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31387
  · exact u31388
  · exact u31389
  · exact u31390
  · exact u31391
  · exact u31392

def r41349 : Route 9 := (fun mask => (mask,id))

def c41349 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41349 : Upper (D 7) (R 7) [6,96,40,257] 13 := by
  apply FastRouting.sound _ _ [6,96,40,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41349 c41349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31393
  · exact u31394
  · exact u31395
  · exact u31396
  · exact u31397
  · exact u31398

def r41350 : Route 9 := (fun mask => (mask,id))

def c41350 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41350 : Upper (D 7) (R 7) [6,96,40,258] 13 := by
  apply FastRouting.sound _ _ [6,96,40,258] 13 (by decide) (choices 2) [65,129,192] r41350 c41350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31399
  · exact u31400
  · exact u31401

def r41351 : Route 9 := (fun mask => (mask,id))

def c41351 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41351 : Upper (D 7) (R 7) [6,96,40,272] 13 := by
  apply FastRouting.sound _ _ [6,96,40,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41351 c41351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31402
  · exact u31403
  · exact u31404
  · exact u31405
  · exact u31406
  · exact u31407

def r41352 : Route 9 := (fun mask => (mask,id))

def c41352 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41352 : Upper (D 7) (R 7) [6,96,40,320] 13 := by
  apply FastRouting.sound _ _ [6,96,40,320] 13 (by decide) (choices 2) [3,129,130] r41352 c41352
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31408
  · exact u31409
  · exact u31410

def r41353 : Route 9 := (fun mask => (mask,id))

def c41353 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41353 : Upper (D 7) (R 7) [6,96,40,384] 13 := by
  apply FastRouting.sound _ _ [6,96,40,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41353 c41353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31411
  · exact u31412
  · exact u31413
  · exact u31414
  · exact u31415
  · exact u31416

def b41354 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7)], upper := (rows 7 98 133 11 504 504 504 504 504), lower := (rows 7 98 133 11 16 32 64 128 256), losses := [] }

theorem u41354 : Upper (D 7) (R 7) [6,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41355 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41355 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u41355 : Upper (D 7) (R 7) [6,96,129,17] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17] 13 (by decide) (choices 2) [10,34,40,96,130,136,160,258,264,288,384] r41355 c41355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31423
  · exact u31424
  · exact u31425
  · exact u31426
  · exact u31427
  · exact u31428
  · exact u31429
  · exact u31430
  · exact u31431
  · exact u31432
  · exact u31433

theorem m41356_9 : Upper (D 7) (R 7) [6,96,129,18,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31423

def r41356 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41356 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u41356 : Upper (D 7) (R 7) [6,96,129,18] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r41356 c41356
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41356_9
  · exact u31434
  · exact u31435
  · exact u31436
  · exact u31437
  · exact u31438
  · exact u31439
  · exact u31440
  · exact u31441
  · exact u31442
  · exact u31443

theorem m41357_10 : Upper (D 7) (R 7) [6,96,129,33,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31434

def r41357 : Route 9 := (fun mask => (mask,id))

def c41357 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41357 : Upper (D 7) (R 7) [6,96,129,33] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33] 13 (by decide) (choices 2) [10,66,72,130,136,192,258,264,320,384] r41357 c41357
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41357_10
  · exact u31444
  · exact u31445
  · exact u31446
  · exact u31447
  · exact u31448
  · exact u31449
  · exact u31450
  · exact u31451
  · exact u31452

def b41358 : PairBound 9 := { available := 473, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 133 42 473 505 473 473 473), lower := (rows 7 98 133 42 16 32 64 128 256), losses := [] }

theorem u41358 : Upper (D 7) (R 7) [6,96,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41359_3 : Upper (D 7) (R 7) [6,96,129,48,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31417

theorem m41359_9 : Upper (D 7) (R 7) [6,96,129,48,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31425

theorem m41359_10 : Upper (D 7) (R 7) [6,96,129,48,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31435

theorem m41359_65 : Upper (D 7) (R 7) [6,96,129,48,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31445

theorem m41359_66 : Upper (D 7) (R 7) [6,96,129,48,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31453

def r41359 : Route 9 := (fun mask => (mask,id))

def c41359 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41359 : Upper (D 7) (R 7) [6,96,129,48] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r41359 c41359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41359_3
  · exact m41359_9
  · exact m41359_10
  · exact m41359_65
  · exact m41359_66
  · exact u31460
  · exact u31461
  · exact u31462
  · exact u31463
  · exact u31464
  · exact u31465
  · exact u31466
  · exact u31467
  · exact u31468
  · exact u31469

def b41360 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 104 411 443 475 411 411), lower := (rows 7 98 133 104 16 32 64 128 256), losses := [] }

theorem u41360 : Upper (D 7) (R 7) [6,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41361 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 7 98 133 137 378 378 378 506 378), lower := (rows 7 98 133 137 16 32 64 128 256), losses := [] }

theorem u41361 : Upper (D 7) (R 7) [6,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41362 : PairBound 9 := { available := 377, camps := [{ cop := 3, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 133 138 377 377 377 505 377), lower := (rows 7 98 133 138 16 32 64 128 256), losses := [] }

theorem u41362 : Upper (D 7) (R 7) [6,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41363_3 : Upper (D 7) (R 7) [6,96,129,144,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31418

theorem m41363_9 : Upper (D 7) (R 7) [6,96,129,144,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31428

theorem m41363_10 : Upper (D 7) (R 7) [6,96,129,144,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31438

theorem m41363_33 : Upper (D 7) (R 7) [6,96,129,144,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31447

theorem m41363_34 : Upper (D 7) (R 7) [6,96,129,144,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31454

theorem m41363_40 : Upper (D 7) (R 7) [6,96,129,144,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31463

theorem m41363_96 : Upper (D 7) (R 7) [6,96,129,144,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31470

def r41363 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41363 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41363 : Upper (D 7) (R 7) [6,96,129,144] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r41363 c41363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41363_3
  · exact m41363_9
  · exact m41363_10
  · exact m41363_33
  · exact m41363_34
  · exact m41363_40
  · exact m41363_96
  · exact u31481
  · exact u31482
  · exact u31483
  · exact u31484

theorem m41364_3 : Upper (D 7) (R 7) [6,96,129,160,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31419

theorem m41364_9 : Upper (D 7) (R 7) [6,96,129,160,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31429

theorem m41364_10 : Upper (D 7) (R 7) [6,96,129,160,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31439

theorem m41364_65 : Upper (D 7) (R 7) [6,96,129,160,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31448

theorem m41364_66 : Upper (D 7) (R 7) [6,96,129,160,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31455

theorem m41364_72 : Upper (D 7) (R 7) [6,96,129,160,72] 13 :=
  permutation_upper _ _ _ [6,96,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31464

def r41364 : Route 9 := (fun mask => (mask,id))

def c41364 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41364 : Upper (D 7) (R 7) [6,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,129,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r41364 c41364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41364_3
  · exact m41364_9
  · exact m41364_10
  · exact m41364_65
  · exact m41364_66
  · exact m41364_72
  · exact u31485
  · exact u31486
  · exact u31487
  · exact u31488

theorem m41365_10 : Upper (D 7) (R 7) [6,96,129,257,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31440

theorem m41365_34 : Upper (D 7) (R 7) [6,96,129,257,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31456

theorem m41365_40 : Upper (D 7) (R 7) [6,96,129,257,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31465

theorem m41365_96 : Upper (D 7) (R 7) [6,96,129,257,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31471

theorem m41365_130 : Upper (D 7) (R 7) [6,96,129,257,130] 13 :=
  permutation_upper _ _ _ [6,96,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31478

theorem m41365_136 : Upper (D 7) (R 7) [6,96,129,257,136] 13 :=
  permutation_upper _ _ _ [6,96,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31481

theorem m41365_160 : Upper (D 7) (R 7) [6,96,129,257,160] 13 :=
  permutation_upper _ _ _ [6,96,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31485

def r41365 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41365 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41365 : Upper (D 7) (R 7) [6,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,96,129,257] 13 (by decide) (choices 2) [10,34,40,96,130,136,160] r41365 c41365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41365_10
  · exact m41365_34
  · exact m41365_40
  · exact m41365_96
  · exact m41365_130
  · exact m41365_136
  · exact m41365_160

theorem m41366_9 : Upper (D 7) (R 7) [6,96,129,258,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31430

theorem m41366_33 : Upper (D 7) (R 7) [6,96,129,258,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31449

theorem m41366_40 : Upper (D 7) (R 7) [6,96,129,258,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31466

theorem m41366_96 : Upper (D 7) (R 7) [6,96,129,258,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31472

theorem m41366_129 : Upper (D 7) (R 7) [6,96,129,258,129] 13 :=
  permutation_upper _ _ _ [6,96,129,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31475

theorem m41366_136 : Upper (D 7) (R 7) [6,96,129,258,136] 13 :=
  permutation_upper _ _ _ [6,96,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31482

theorem m41366_160 : Upper (D 7) (R 7) [6,96,129,258,160] 13 :=
  permutation_upper _ _ _ [6,96,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31486

def r41366 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41366 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41366 : Upper (D 7) (R 7) [6,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,96,129,258] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r41366 c41366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41366_9
  · exact m41366_33
  · exact m41366_40
  · exact m41366_96
  · exact m41366_129
  · exact m41366_136
  · exact m41366_160

theorem m41367_3 : Upper (D 7) (R 7) [6,96,129,272,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31420

theorem m41367_9 : Upper (D 7) (R 7) [6,96,129,272,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31431

theorem m41367_10 : Upper (D 7) (R 7) [6,96,129,272,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31441

theorem m41367_33 : Upper (D 7) (R 7) [6,96,129,272,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31450

theorem m41367_34 : Upper (D 7) (R 7) [6,96,129,272,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31457

theorem m41367_40 : Upper (D 7) (R 7) [6,96,129,272,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31467

theorem m41367_96 : Upper (D 7) (R 7) [6,96,129,272,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31473

theorem m41367_129 : Upper (D 7) (R 7) [6,96,129,272,129] 13 :=
  permutation_upper _ _ _ [6,96,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31476

theorem m41367_130 : Upper (D 7) (R 7) [6,96,129,272,130] 13 :=
  permutation_upper _ _ _ [6,96,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31479

theorem m41367_136 : Upper (D 7) (R 7) [6,96,129,272,136] 13 :=
  permutation_upper _ _ _ [6,96,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31483

theorem m41367_160 : Upper (D 7) (R 7) [6,96,129,272,160] 13 :=
  permutation_upper _ _ _ [6,96,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31487

def r41367 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41367 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41367 : Upper (D 7) (R 7) [6,96,129,272] 13 := by
  apply FastRouting.sound _ _ [6,96,129,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160] r41367 c41367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41367_3
  · exact m41367_9
  · exact m41367_10
  · exact m41367_33
  · exact m41367_34
  · exact m41367_40
  · exact m41367_96
  · exact m41367_129
  · exact m41367_130
  · exact m41367_136
  · exact m41367_160

theorem m41368_3 : Upper (D 7) (R 7) [6,96,129,288,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31421

theorem m41368_9 : Upper (D 7) (R 7) [6,96,129,288,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31432

theorem m41368_10 : Upper (D 7) (R 7) [6,96,129,288,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31442

theorem m41368_65 : Upper (D 7) (R 7) [6,96,129,288,65] 13 :=
  permutation_upper _ _ _ [6,96,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31451

theorem m41368_66 : Upper (D 7) (R 7) [6,96,129,288,66] 13 :=
  permutation_upper _ _ _ [6,96,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31458

theorem m41368_72 : Upper (D 7) (R 7) [6,96,129,288,72] 13 :=
  permutation_upper _ _ _ [6,96,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31468

theorem m41368_129 : Upper (D 7) (R 7) [6,96,129,288,129] 13 :=
  permutation_upper _ _ _ [6,96,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31477

theorem m41368_130 : Upper (D 7) (R 7) [6,96,129,288,130] 13 :=
  permutation_upper _ _ _ [6,96,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31480

theorem m41368_136 : Upper (D 7) (R 7) [6,96,129,288,136] 13 :=
  permutation_upper _ _ _ [6,96,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31484

theorem m41368_192 : Upper (D 7) (R 7) [6,96,129,288,192] 13 :=
  permutation_upper _ _ _ [6,96,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31488

def r41368 : Route 9 := (fun mask => (mask,id))

def c41368 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41368 : Upper (D 7) (R 7) [6,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,96,129,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41368 c41368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41368_3
  · exact m41368_9
  · exact m41368_10
  · exact m41368_65
  · exact m41368_66
  · exact m41368_72
  · exact m41368_129
  · exact m41368_130
  · exact m41368_136
  · exact m41368_192

theorem m41369_3 : Upper (D 7) (R 7) [6,96,129,384,3] 13 :=
  permutation_upper _ _ _ [6,96,129,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31422

theorem m41369_9 : Upper (D 7) (R 7) [6,96,129,384,9] 13 :=
  permutation_upper _ _ _ [6,96,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31433

theorem m41369_10 : Upper (D 7) (R 7) [6,96,129,384,10] 13 :=
  permutation_upper _ _ _ [6,96,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31443

theorem m41369_33 : Upper (D 7) (R 7) [6,96,129,384,33] 13 :=
  permutation_upper _ _ _ [6,96,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31452

theorem m41369_34 : Upper (D 7) (R 7) [6,96,129,384,34] 13 :=
  permutation_upper _ _ _ [6,96,129,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31459

theorem m41369_40 : Upper (D 7) (R 7) [6,96,129,384,40] 13 :=
  permutation_upper _ _ _ [6,96,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31469

theorem m41369_96 : Upper (D 7) (R 7) [6,96,129,384,96] 13 :=
  permutation_upper _ _ _ [6,96,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31474

def r41369 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41369 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41369 : Upper (D 7) (R 7) [6,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,96,129,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r41369 c41369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41369_3
  · exact m41369_9
  · exact m41369_10
  · exact m41369_33
  · exact m41369_34
  · exact m41369_40
  · exact m41369_96

def b41370 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 140 11 497 497 497 497 497), lower := (rows 7 98 140 11 16 32 64 128 256), losses := [] }

theorem u41370 : Upper (D 7) (R 7) [6,96,136,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41371 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41371 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41371 : Upper (D 7) (R 7) [6,96,136,17] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41371 c41371
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31489
  · exact u31490
  · exact u31491
  · exact u31492
  · exact u31493
  · exact u31494
  · exact u31495
  · exact u31496
  · exact u31497
  · exact u31498
  · exact u31499

def r41372 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41372 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41372 : Upper (D 7) (R 7) [6,96,136,18] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r41372 c41372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31500
  · exact u31501
  · exact u31502
  · exact u31503
  · exact u31504
  · exact u31505
  · exact u31506

def r41373 : Route 9 := (fun mask => (mask,id))

def c41373 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41373 : Upper (D 7) (R 7) [6,96,136,33] 13 := by
  apply FastRouting.sound _ _ [6,96,136,33] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41373 c41373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31507
  · exact u31508
  · exact u31509
  · exact u31510
  · exact u31511
  · exact u31512
  · exact u31513
  · exact u31514
  · exact u31515
  · exact u31516

def b41374 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 140 42 465 497 465 465 465), lower := (rows 7 98 140 42 16 32 64 128 256), losses := [] }

theorem u41374 : Upper (D 7) (R 7) [6,96,136,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41375 : Route 9 := (fun mask => (mask,id))

def c41375 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41375 : Upper (D 7) (R 7) [6,96,136,48] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41375 c41375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31517
  · exact u31518
  · exact u31519
  · exact u31520
  · exact u31521
  · exact u31522
  · exact u31523
  · exact u31524
  · exact u31525
  · exact u31526

def b41376 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 140 104 403 435 467 403 403), lower := (rows 7 98 140 104 16 32 64 128 256), losses := [] }

theorem u41376 : Upper (D 7) (R 7) [6,96,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41377 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 7 98 140 137 371 371 371 499 371), lower := (rows 7 98 140 137 16 32 64 128 256), losses := [] }

theorem u41377 : Upper (D 7) (R 7) [6,96,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41378 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 5, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 140 138 369 369 369 497 369), lower := (rows 7 98 140 138 16 32 64 128 256), losses := [] }

theorem u41378 : Upper (D 7) (R 7) [6,96,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41379 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 7 98 140 152 371 355 355 483 355), lower := (rows 7 98 140 152 16 32 64 128 256), losses := [] }

theorem u41379 : Upper (D 7) (R 7) [6,96,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41380 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 7 98 140 168 339 371 339 467 339), lower := (rows 7 98 140 168 16 32 64 128 256), losses := [] }

theorem u41380 : Upper (D 7) (R 7) [6,96,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41381 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41381 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41381 : Upper (D 7) (R 7) [6,96,136,257] 13 := by
  apply FastRouting.sound _ _ [6,96,136,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41381 c41381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31527
  · exact u31528
  · exact u31529
  · exact u31530
  · exact u31531
  · exact u31532
  · exact u31533

def r41382 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41382 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41382 : Upper (D 7) (R 7) [6,96,136,258] 13 := by
  apply FastRouting.sound _ _ [6,96,136,258] 13 (by decide) (choices 2) [33,96,129,160] r41382 c41382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31534
  · exact u31535
  · exact u31536
  · exact u31537

def r41383 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41383 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41383 : Upper (D 7) (R 7) [6,96,136,272] 13 := by
  apply FastRouting.sound _ _ [6,96,136,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41383 c41383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31538
  · exact u31539
  · exact u31540
  · exact u31541
  · exact u31542
  · exact u31543
  · exact u31544

def r41384 : Route 9 := (fun mask => (mask,id))

def c41384 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41384 : Upper (D 7) (R 7) [6,96,136,288] 13 := by
  apply FastRouting.sound _ _ [6,96,136,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41384 c41384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31545
  · exact u31546
  · exact u31547
  · exact u31548
  · exact u31549
  · exact u31550

def b41385 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 7 98 140 392 115 115 115 243 371), lower := (rows 7 98 140 392 16 32 64 128 256), losses := [] }

theorem u41385 : Upper (D 7) (R 7) [6,96,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41386 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 164 11 473 505 473 473 473), lower := (rows 7 98 164 11 16 32 64 128 256), losses := [] }

theorem u41386 : Upper (D 7) (R 7) [6,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41387_3 : Upper (D 7) (R 7) [6,96,160,17,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31551

def r41387 : Route 9 := (fun mask => (mask,id))

def c41387 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41387 : Upper (D 7) (R 7) [6,96,160,17] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r41387 c41387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41387_3
  · exact u31560
  · exact u31561
  · exact u31562
  · exact u31563
  · exact u31564
  · exact u31565
  · exact u31566
  · exact u31567
  · exact u31568
  · exact u31569
  · exact u31570
  · exact u31571
  · exact u31572
  · exact u31573

theorem m41388_9 : Upper (D 7) (R 7) [6,96,160,18,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31561

def r41388 : Route 9 := (fun mask => (mask,id))

def c41388 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41388 : Upper (D 7) (R 7) [6,96,160,18] 13 := by
  apply FastRouting.sound _ _ [6,96,160,18] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r41388 c41388
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41388_9
  · exact u31574
  · exact u31575
  · exact u31576
  · exact u31577
  · exact u31578
  · exact u31579
  · exact u31580
  · exact u31581
  · exact u31582

theorem m41389_3 : Upper (D 7) (R 7) [6,96,160,65,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31552

theorem m41389_9 : Upper (D 7) (R 7) [6,96,160,65,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31562

theorem m41389_10 : Upper (D 7) (R 7) [6,96,160,65,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31574

def r41389 : Route 9 := (fun mask => (mask,id))

def c41389 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41389 : Upper (D 7) (R 7) [6,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r41389 c41389
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41389_3
  · exact m41389_9
  · exact m41389_10
  · exact u31583
  · exact u31584
  · exact u31585
  · exact u31586
  · exact u31587
  · exact u31588
  · exact u31589

def b41390 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 164 74 409 441 473 409 409), lower := (rows 7 98 164 74 16 32 64 128 256), losses := [] }

theorem u41390 : Upper (D 7) (R 7) [6,96,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41391_3 : Upper (D 7) (R 7) [6,96,160,80,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31553

theorem m41391_9 : Upper (D 7) (R 7) [6,96,160,80,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31564

theorem m41391_10 : Upper (D 7) (R 7) [6,96,160,80,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31575

def r41391 : Route 9 := (fun mask => (mask,id))

def c41391 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41391 : Upper (D 7) (R 7) [6,96,160,80] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r41391 c41391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41391_3
  · exact m41391_9
  · exact m41391_10
  · exact u31594
  · exact u31595
  · exact u31596
  · exact u31597
  · exact u31598
  · exact u31599
  · exact u31600

def b41392 : PairBound 9 := { available := 347, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(3,5),(4,5),(4,7)], upper := (rows 7 98 164 137 347 379 347 475 347), lower := (rows 7 98 164 137 16 32 64 128 256), losses := [] }

theorem u41392 : Upper (D 7) (R 7) [6,96,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41393_9 : Upper (D 7) (R 7) [6,96,160,130,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31566

theorem m41393_65 : Upper (D 7) (R 7) [6,96,160,130,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31584

theorem m41393_72 : Upper (D 7) (R 7) [6,96,160,130,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31595

def r41393 : Route 9 := (fun mask => (mask,id))

def c41393 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41393 : Upper (D 7) (R 7) [6,96,160,130] 13 := by
  apply FastRouting.sound _ _ [6,96,160,130] 13 (by decide) (choices 2) [9,65,72,257,264,320] r41393 c41393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41393_9
  · exact m41393_65
  · exact m41393_72
  · exact u31605
  · exact u31606
  · exact u31607

theorem m41394_3 : Upper (D 7) (R 7) [6,96,160,144,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31554

theorem m41394_9 : Upper (D 7) (R 7) [6,96,160,144,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31567

theorem m41394_10 : Upper (D 7) (R 7) [6,96,160,144,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31577

theorem m41394_65 : Upper (D 7) (R 7) [6,96,160,144,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31585

theorem m41394_66 : Upper (D 7) (R 7) [6,96,160,144,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31590

theorem m41394_72 : Upper (D 7) (R 7) [6,96,160,144,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31596

def r41394 : Route 9 := (fun mask => (mask,id))

def c41394 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41394 : Upper (D 7) (R 7) [6,96,160,144] 13 := by
  apply FastRouting.sound _ _ [6,96,160,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r41394 c41394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41394_3
  · exact m41394_9
  · exact m41394_10
  · exact m41394_65
  · exact m41394_66
  · exact m41394_72
  · exact u31608
  · exact u31609
  · exact u31610
  · exact u31611

theorem m41395_3 : Upper (D 7) (R 7) [6,96,160,192,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31555

theorem m41395_9 : Upper (D 7) (R 7) [6,96,160,192,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31568

theorem m41395_10 : Upper (D 7) (R 7) [6,96,160,192,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31578

def r41395 : Route 9 := (fun mask => (mask,id))

def c41395 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41395 : Upper (D 7) (R 7) [6,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192] 13 (by decide) (choices 2) [3,9,10,257,258,264] r41395 c41395
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41395_3
  · exact m41395_9
  · exact m41395_10
  · exact u31612
  · exact u31613
  · exact u31614

theorem m41396_3 : Upper (D 7) (R 7) [6,96,160,257,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31556

theorem m41396_9 : Upper (D 7) (R 7) [6,96,160,257,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31569

theorem m41396_10 : Upper (D 7) (R 7) [6,96,160,257,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31579

theorem m41396_65 : Upper (D 7) (R 7) [6,96,160,257,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31586

theorem m41396_66 : Upper (D 7) (R 7) [6,96,160,257,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31591

theorem m41396_72 : Upper (D 7) (R 7) [6,96,160,257,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31597

theorem m41396_129 : Upper (D 7) (R 7) [6,96,160,257,129] 13 :=
  permutation_upper _ _ _ [6,96,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31601

theorem m41396_130 : Upper (D 7) (R 7) [6,96,160,257,130] 13 :=
  permutation_upper _ _ _ [6,96,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31605

theorem m41396_136 : Upper (D 7) (R 7) [6,96,160,257,136] 13 :=
  permutation_upper _ _ _ [6,96,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31608

theorem m41396_192 : Upper (D 7) (R 7) [6,96,160,257,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31612

def r41396 : Route 9 := (fun mask => (mask,id))

def c41396 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41396 : Upper (D 7) (R 7) [6,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41396 c41396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41396_3
  · exact m41396_9
  · exact m41396_10
  · exact m41396_65
  · exact m41396_66
  · exact m41396_72
  · exact m41396_129
  · exact m41396_130
  · exact m41396_136
  · exact m41396_192

theorem m41397_9 : Upper (D 7) (R 7) [6,96,160,258,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31570

theorem m41397_65 : Upper (D 7) (R 7) [6,96,160,258,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31587

theorem m41397_72 : Upper (D 7) (R 7) [6,96,160,258,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31598

theorem m41397_129 : Upper (D 7) (R 7) [6,96,160,258,129] 13 :=
  permutation_upper _ _ _ [6,96,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31602

theorem m41397_136 : Upper (D 7) (R 7) [6,96,160,258,136] 13 :=
  permutation_upper _ _ _ [6,96,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31609

theorem m41397_192 : Upper (D 7) (R 7) [6,96,160,258,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31613

def r41397 : Route 9 := (fun mask => (mask,id))

def c41397 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41397 : Upper (D 7) (R 7) [6,96,160,258] 13 := by
  apply FastRouting.sound _ _ [6,96,160,258] 13 (by decide) (choices 2) [9,65,72,129,136,192] r41397 c41397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41397_9
  · exact m41397_65
  · exact m41397_72
  · exact m41397_129
  · exact m41397_136
  · exact m41397_192

theorem m41398_3 : Upper (D 7) (R 7) [6,96,160,272,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31557

theorem m41398_9 : Upper (D 7) (R 7) [6,96,160,272,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31571

theorem m41398_10 : Upper (D 7) (R 7) [6,96,160,272,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31580

theorem m41398_65 : Upper (D 7) (R 7) [6,96,160,272,65] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31588

theorem m41398_66 : Upper (D 7) (R 7) [6,96,160,272,66] 13 :=
  permutation_upper _ _ _ [6,96,160,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31592

theorem m41398_72 : Upper (D 7) (R 7) [6,96,160,272,72] 13 :=
  permutation_upper _ _ _ [6,96,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31599

theorem m41398_129 : Upper (D 7) (R 7) [6,96,160,272,129] 13 :=
  permutation_upper _ _ _ [6,96,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31603

theorem m41398_130 : Upper (D 7) (R 7) [6,96,160,272,130] 13 :=
  permutation_upper _ _ _ [6,96,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31606

theorem m41398_136 : Upper (D 7) (R 7) [6,96,160,272,136] 13 :=
  permutation_upper _ _ _ [6,96,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31610

theorem m41398_192 : Upper (D 7) (R 7) [6,96,160,272,192] 13 :=
  permutation_upper _ _ _ [6,96,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31614

def r41398 : Route 9 := (fun mask => (mask,id))

def c41398 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41398 : Upper (D 7) (R 7) [6,96,160,272] 13 := by
  apply FastRouting.sound _ _ [6,96,160,272] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r41398 c41398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41398_3
  · exact m41398_9
  · exact m41398_10
  · exact m41398_65
  · exact m41398_66
  · exact m41398_72
  · exact m41398_129
  · exact m41398_130
  · exact m41398_136
  · exact m41398_192

theorem m41399_3 : Upper (D 7) (R 7) [6,96,160,320,3] 13 :=
  permutation_upper _ _ _ [6,96,160,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31558

theorem m41399_9 : Upper (D 7) (R 7) [6,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31572

theorem m41399_10 : Upper (D 7) (R 7) [6,96,160,320,10] 13 :=
  permutation_upper _ _ _ [6,96,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31581

theorem m41399_129 : Upper (D 7) (R 7) [6,96,160,320,129] 13 :=
  permutation_upper _ _ _ [6,96,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31604

theorem m41399_130 : Upper (D 7) (R 7) [6,96,160,320,130] 13 :=
  permutation_upper _ _ _ [6,96,160,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31607

theorem m41399_136 : Upper (D 7) (R 7) [6,96,160,320,136] 13 :=
  permutation_upper _ _ _ [6,96,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31611

def r41399 : Route 9 := (fun mask => (mask,id))

def c41399 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41399 : Upper (D 7) (R 7) [6,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320] 13 (by decide) (choices 2) [3,9,10,129,130,136] r41399 c41399
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41399_3
  · exact m41399_9
  · exact m41399_10
  · exact m41399_129
  · exact m41399_130
  · exact m41399_136

#print axioms u41399
end Delivery.IrregularNine14.P07
