import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0124
import IrregularNine14P05C0125
import IrregularNine14P05C0126
import IrregularNine14P05C0127
import IrregularNine14P05C0128
import IrregularNine14P05C0129
import IrregularNine14P05C0130

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9300 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9300 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9300 : Upper (D 5) (R 5) [18,68,33,34] 13 := by
  apply FastRouting.sound _ _ [18,68,33,34] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r9300 c9300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7441
  · exact u7442
  · exact u7443
  · exact u7444
  · exact u7445
  · exact u7446
  · exact u7447

def b9301 : PairBound 9 := { available := 395, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 37 44 411 427 459 395 395), lower := (rows 19 70 37 44 16 32 64 128 256), losses := [] }

theorem u9301 : Upper (D 5) (R 5) [18,68,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9301
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9302 : Route 9 := (fun mask => (mask,id))

def c9302 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9302 : Upper (D 5) (R 5) [18,68,33,129] 13 := by
  apply FastRouting.sound _ _ [18,68,33,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9302 c9302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7448
  · exact u7449
  · exact u7450
  · exact u7451
  · exact u7452
  · exact u7453
  · exact u7454
  · exact u7455
  · exact u7456
  · exact u7457

def r9303 : Route 9 := (fun mask => (mask,id))

def c9303 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9303 : Upper (D 5) (R 5) [18,68,33,130] 13 := by
  apply FastRouting.sound _ _ [18,68,33,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9303 c9303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7458
  · exact u7459
  · exact u7460
  · exact u7461
  · exact u7462
  · exact u7463
  · exact u7464
  · exact u7465
  · exact u7466
  · exact u7467

def r9304 : Route 9 := (fun mask => (mask,id))

def c9304 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9304 : Upper (D 5) (R 5) [18,68,33,132] 13 := by
  apply FastRouting.sound _ _ [18,68,33,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9304 c9304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7468
  · exact u7469
  · exact u7470
  · exact u7471
  · exact u7472
  · exact u7473
  · exact u7474
  · exact u7475
  · exact u7476
  · exact u7477

def r9305 : Route 9 := (fun mask => (mask,id))

def c9305 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9305 : Upper (D 5) (R 5) [18,68,33,160] 13 := by
  apply FastRouting.sound _ _ [18,68,33,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9305 c9305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7478
  · exact u7479
  · exact u7480
  · exact u7481
  · exact u7482
  · exact u7483
  · exact u7484
  · exact u7485
  · exact u7486
  · exact u7487

def r9306 : Route 9 := (fun mask => (mask,id))

def c9306 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9306 : Upper (D 5) (R 5) [18,68,33,384] 13 := by
  apply FastRouting.sound _ _ [18,68,33,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9306 c9306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7488
  · exact u7489
  · exact u7490
  · exact u7491
  · exact u7492
  · exact u7493
  · exact u7494
  · exact u7495
  · exact u7496
  · exact u7497

def r9307 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9307 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9307 : Upper (D 5) (R 5) [18,68,34,33] 13 := by
  apply FastRouting.sound _ _ [18,68,34,33] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r9307 c9307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7498
  · exact u7499
  · exact u7500
  · exact u7501
  · exact u7502
  · exact u7503
  · exact u7504

def b9308 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 38 44 409 425 457 393 393), lower := (rows 19 70 38 44 16 32 64 128 256), losses := [] }

theorem u9308 : Upper (D 5) (R 5) [18,68,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9308
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9309 : Route 9 := (fun mask => (mask,id))

def c9309 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9309 : Upper (D 5) (R 5) [18,68,34,129] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9309 c9309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7505
  · exact u7506
  · exact u7507
  · exact u7508
  · exact u7509
  · exact u7510
  · exact u7511
  · exact u7512
  · exact u7513
  · exact u7514

def r9310 : Route 9 := (fun mask => (mask,id))

def c9310 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9310 : Upper (D 5) (R 5) [18,68,34,132] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132] 13 (by decide) (choices 2) [9,33,40,257,264,288] r9310 c9310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7515
  · exact u7516
  · exact u7517
  · exact u7518
  · exact u7519
  · exact u7520

def r9311 : Route 9 := (fun mask => (mask,id))

def c9311 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9311 : Upper (D 5) (R 5) [18,68,34,160] 13 := by
  apply FastRouting.sound _ _ [18,68,34,160] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9311 c9311
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7521
  · exact u7522
  · exact u7523
  · exact u7524
  · exact u7525
  · exact u7526

def r9312 : Route 9 := (fun mask => (mask,id))

def c9312 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9312 : Upper (D 5) (R 5) [18,68,34,384] 13 := by
  apply FastRouting.sound _ _ [18,68,34,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9312 c9312
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7527
  · exact u7528
  · exact u7529
  · exact u7530
  · exact u7531
  · exact u7532

def b9313 : PairBound 9 := { available := 399, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 44 41 415 431 463 399 399), lower := (rows 19 70 44 41 16 32 64 128 256), losses := [] }

theorem u9313 : Upper (D 5) (R 5) [18,68,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9313
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9314 : PairBound 9 := { available := 397, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 44 42 413 429 461 397 397), lower := (rows 19 70 44 42 16 32 64 128 256), losses := [] }

theorem u9314 : Upper (D 5) (R 5) [18,68,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9314
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9315 : PairBound 9 := { available := 395, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 44 44 411 427 459 395 395), lower := (rows 19 70 44 44 16 32 64 128 256), losses := [] }

theorem u9315 : Upper (D 5) (R 5) [18,68,40,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9315
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9316 : Route 9 := (fun mask => (mask,id))

def c9316 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9316 : Upper (D 5) (R 5) [18,68,40,129] 13 := by
  apply FastRouting.sound _ _ [18,68,40,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9316 c9316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7533
  · exact u7534
  · exact u7535
  · exact u7536
  · exact u7537
  · exact u7538
  · exact u7539
  · exact u7540
  · exact u7541
  · exact u7542
  · exact u7543
  · exact u7544
  · exact u7545
  · exact u7546
  · exact u7547

def r9317 : Route 9 := (fun mask => (mask,id))

def c9317 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9317 : Upper (D 5) (R 5) [18,68,40,130] 13 := by
  apply FastRouting.sound _ _ [18,68,40,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9317 c9317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7548
  · exact u7549
  · exact u7550
  · exact u7551
  · exact u7552
  · exact u7553
  · exact u7554
  · exact u7555
  · exact u7556
  · exact u7557

def r9318 : Route 9 := (fun mask => (mask,id))

def c9318 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9318 : Upper (D 5) (R 5) [18,68,40,132] 13 := by
  apply FastRouting.sound _ _ [18,68,40,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9318 c9318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7558
  · exact u7559
  · exact u7560
  · exact u7561
  · exact u7562
  · exact u7563
  · exact u7564
  · exact u7565
  · exact u7566
  · exact u7567

def b9319 : PairBound 9 := { available := 271, camps := [{ cop := 2, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 44 168 287 303 335 399 271), lower := (rows 19 70 44 168 16 32 64 128 256), losses := [] }

theorem u9319 : Upper (D 5) (R 5) [18,68,40,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9319
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9320 : Route 9 := (fun mask => (mask,id))

def c9320 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9320 : Upper (D 5) (R 5) [18,68,40,384] 13 := by
  apply FastRouting.sound _ _ [18,68,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9320 c9320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7568
  · exact u7569
  · exact u7570
  · exact u7571
  · exact u7572
  · exact u7573
  · exact u7574
  · exact u7575
  · exact u7576
  · exact u7577

def r9321 : Route 9 := (fun mask => (mask,id))

def c9321 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9321 : Upper (D 5) (R 5) [18,68,129,33] 13 := by
  apply FastRouting.sound _ _ [18,68,129,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r9321 c9321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7578
  · exact u7579
  · exact u7580
  · exact u7581
  · exact u7582
  · exact u7583
  · exact u7584
  · exact u7585
  · exact u7586
  · exact u7587

def r9322 : Route 9 := (fun mask => (mask,id))

def c9322 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9322 : Upper (D 5) (R 5) [18,68,129,34] 13 := by
  apply FastRouting.sound _ _ [18,68,129,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9322 c9322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7588
  · exact u7589
  · exact u7590
  · exact u7591
  · exact u7592
  · exact u7593
  · exact u7594
  · exact u7595
  · exact u7596
  · exact u7597

def r9323 : Route 9 := (fun mask => (mask,id))

def c9323 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9323 : Upper (D 5) (R 5) [18,68,129,36] 13 := by
  apply FastRouting.sound _ _ [18,68,129,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9323 c9323
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7598
  · exact u7599
  · exact u7600
  · exact u7601
  · exact u7602
  · exact u7603
  · exact u7604
  · exact u7605
  · exact u7606
  · exact u7607

def r9324 : Route 9 := (fun mask => (mask,id))

def c9324 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9324 : Upper (D 5) (R 5) [18,68,129,257] 13 := by
  apply FastRouting.sound _ _ [18,68,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9324 c9324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7608
  · exact u7609
  · exact u7610
  · exact u7611
  · exact u7612
  · exact u7613

def r9325 : Route 9 := (fun mask => (mask,id))

def c9325 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9325 : Upper (D 5) (R 5) [18,68,129,258] 13 := by
  apply FastRouting.sound _ _ [18,68,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9325 c9325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7614
  · exact u7615
  · exact u7616
  · exact u7617
  · exact u7618
  · exact u7619

def r9326 : Route 9 := (fun mask => (mask,id))

def c9326 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9326 : Upper (D 5) (R 5) [18,68,129,260] 13 := by
  apply FastRouting.sound _ _ [18,68,129,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9326 c9326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7620
  · exact u7621
  · exact u7622
  · exact u7623
  · exact u7624
  · exact u7625

def r9327 : Route 9 := (fun mask => (mask,id))

def c9327 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9327 : Upper (D 5) (R 5) [18,68,129,288] 13 := by
  apply FastRouting.sound _ _ [18,68,129,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9327 c9327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7626
  · exact u7627
  · exact u7628
  · exact u7629
  · exact u7630
  · exact u7631
  · exact u7632
  · exact u7633
  · exact u7634
  · exact u7635

def r9328 : Route 9 := (fun mask => (mask,id))

def c9328 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9328 : Upper (D 5) (R 5) [18,68,130,33] 13 := by
  apply FastRouting.sound _ _ [18,68,130,33] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9328 c9328
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7636
  · exact u7637
  · exact u7638
  · exact u7639
  · exact u7640
  · exact u7641
  · exact u7642
  · exact u7643
  · exact u7644
  · exact u7645

def r9329 : Route 9 := (fun mask => (mask,id))

def c9329 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9329 : Upper (D 5) (R 5) [18,68,130,36] 13 := by
  apply FastRouting.sound _ _ [18,68,130,36] 13 (by decide) (choices 2) [9,33,40,257,264,288] r9329 c9329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7646
  · exact u7647
  · exact u7648
  · exact u7649
  · exact u7650
  · exact u7651

def r9330 : Route 9 := (fun mask => (mask,id))

def c9330 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9330 : Upper (D 5) (R 5) [18,68,130,257] 13 := by
  apply FastRouting.sound _ _ [18,68,130,257] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9330 c9330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7652
  · exact u7653
  · exact u7654
  · exact u7655
  · exact u7656
  · exact u7657

def r9331 : Route 9 := (fun mask => (mask,id))

def c9331 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9331 : Upper (D 5) (R 5) [18,68,130,260] 13 := by
  apply FastRouting.sound _ _ [18,68,130,260] 13 (by decide) (choices 2) [9,33,40] r9331 c9331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7658
  · exact u7659
  · exact u7660

def r9332 : Route 9 := (fun mask => (mask,id))

def c9332 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9332 : Upper (D 5) (R 5) [18,68,130,288] 13 := by
  apply FastRouting.sound _ _ [18,68,130,288] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9332 c9332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7661
  · exact u7662
  · exact u7663
  · exact u7664
  · exact u7665
  · exact u7666

def r9333 : Route 9 := (fun mask => (mask,id))

def c9333 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9333 : Upper (D 5) (R 5) [18,68,136,33] 13 := by
  apply FastRouting.sound _ _ [18,68,136,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r9333 c9333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7667
  · exact u7668
  · exact u7669
  · exact u7670
  · exact u7671
  · exact u7672
  · exact u7673
  · exact u7674
  · exact u7675
  · exact u7676
  · exact u7677
  · exact u7678
  · exact u7679
  · exact u7680
  · exact u7681

def r9334 : Route 9 := (fun mask => (mask,id))

def c9334 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9334 : Upper (D 5) (R 5) [18,68,136,34] 13 := by
  apply FastRouting.sound _ _ [18,68,136,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r9334 c9334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7682
  · exact u7683
  · exact u7684
  · exact u7685
  · exact u7686
  · exact u7687
  · exact u7688
  · exact u7689
  · exact u7690
  · exact u7691

def r9335 : Route 9 := (fun mask => (mask,id))

def c9335 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9335 : Upper (D 5) (R 5) [18,68,136,36] 13 := by
  apply FastRouting.sound _ _ [18,68,136,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r9335 c9335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7692
  · exact u7693
  · exact u7694
  · exact u7695
  · exact u7696
  · exact u7697
  · exact u7698
  · exact u7699
  · exact u7700
  · exact u7701

def r9336 : Route 9 := (fun mask => (mask,id))

def c9336 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9336 : Upper (D 5) (R 5) [18,68,136,257] 13 := by
  apply FastRouting.sound _ _ [18,68,136,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9336 c9336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7702
  · exact u7703
  · exact u7704
  · exact u7705
  · exact u7706
  · exact u7707
  · exact u7708
  · exact u7709
  · exact u7710
  · exact u7711

def r9337 : Route 9 := (fun mask => (mask,id))

def c9337 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9337 : Upper (D 5) (R 5) [18,68,136,258] 13 := by
  apply FastRouting.sound _ _ [18,68,136,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9337 c9337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7712
  · exact u7713
  · exact u7714
  · exact u7715
  · exact u7716
  · exact u7717

def r9338 : Route 9 := (fun mask => (mask,id))

def c9338 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9338 : Upper (D 5) (R 5) [18,68,136,260] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9338 c9338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7718
  · exact u7719
  · exact u7720
  · exact u7721
  · exact u7722
  · exact u7723

def r9339 : Route 9 := (fun mask => (mask,id))

def c9339 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9339 : Upper (D 5) (R 5) [18,68,136,288] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9339 c9339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7724
  · exact u7725
  · exact u7726
  · exact u7727
  · exact u7728
  · exact u7729
  · exact u7730
  · exact u7731
  · exact u7732
  · exact u7733

def r9340 : Route 9 := (fun mask => (mask,id))

def c9340 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9340 : Upper (D 5) (R 5) [18,68,160,33] 13 := by
  apply FastRouting.sound _ _ [18,68,160,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9340 c9340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7734
  · exact u7735
  · exact u7736
  · exact u7737
  · exact u7738
  · exact u7739
  · exact u7740
  · exact u7741
  · exact u7742
  · exact u7743

def r9341 : Route 9 := (fun mask => (mask,id))

def c9341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9341 : Upper (D 5) (R 5) [18,68,160,34] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9341 c9341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7744
  · exact u7745
  · exact u7746
  · exact u7747
  · exact u7748
  · exact u7749

def b9342 : PairBound 9 := { available := 267, camps := [{ cop := 3, region := 339, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 164 44 283 299 331 395 267), lower := (rows 19 70 164 44 16 32 64 128 256), losses := [] }

theorem u9342 : Upper (D 5) (R 5) [18,68,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9343 : Route 9 := (fun mask => (mask,id))

def c9343 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9343 : Upper (D 5) (R 5) [18,68,160,257] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9343 c9343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7750
  · exact u7751
  · exact u7752
  · exact u7753
  · exact u7754
  · exact u7755
  · exact u7756
  · exact u7757
  · exact u7758
  · exact u7759

def r9344 : Route 9 := (fun mask => (mask,id))

def c9344 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9344 : Upper (D 5) (R 5) [18,68,160,258] 13 := by
  apply FastRouting.sound _ _ [18,68,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9344 c9344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7760
  · exact u7761
  · exact u7762
  · exact u7763
  · exact u7764
  · exact u7765

def r9345 : Route 9 := (fun mask => (mask,id))

def c9345 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9345 : Upper (D 5) (R 5) [18,68,160,260] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9345 c9345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7766
  · exact u7767
  · exact u7768
  · exact u7769
  · exact u7770
  · exact u7771

def r9346 : Route 9 := (fun mask => (mask,id))

def c9346 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9346 : Upper (D 5) (R 5) [18,68,160,288] 13 := by
  apply FastRouting.sound _ _ [18,68,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9346 c9346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7772
  · exact u7773
  · exact u7774
  · exact u7775
  · exact u7776
  · exact u7777

def r9347 : Route 9 := (fun mask => (mask,id))

def c9347 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9347 : Upper (D 5) (R 5) [18,68,384,33] 13 := by
  apply FastRouting.sound _ _ [18,68,384,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9347 c9347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7778
  · exact u7779
  · exact u7780
  · exact u7781
  · exact u7782
  · exact u7783
  · exact u7784
  · exact u7785
  · exact u7786
  · exact u7787

def r9348 : Route 9 := (fun mask => (mask,id))

def c9348 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9348 : Upper (D 5) (R 5) [18,68,384,34] 13 := by
  apply FastRouting.sound _ _ [18,68,384,34] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9348 c9348
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7788
  · exact u7789
  · exact u7790
  · exact u7791
  · exact u7792
  · exact u7793

def r9349 : Route 9 := (fun mask => (mask,id))

def c9349 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9349 : Upper (D 5) (R 5) [18,68,384,36] 13 := by
  apply FastRouting.sound _ _ [18,68,384,36] 13 (by decide) (choices 2) [3,9,10,33,34,40] r9349 c9349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7794
  · exact u7795
  · exact u7796
  · exact u7797
  · exact u7798
  · exact u7799

def r9350 : Route 9 := (fun mask => (mask,id))

def c9350 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9350 : Upper (D 5) (R 5) [18,96,33,129] 13 := by
  apply FastRouting.sound _ _ [18,96,33,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r9350 c9350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7800
  · exact u7801
  · exact u7802
  · exact u7803
  · exact u7804
  · exact u7805

def r9351 : Route 9 := (fun mask => (mask,id))

def c9351 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9351 : Upper (D 5) (R 5) [18,96,33,130] 13 := by
  apply FastRouting.sound _ _ [18,96,33,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9351 c9351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7806
  · exact u7807
  · exact u7808
  · exact u7809
  · exact u7810
  · exact u7811

def r9352 : Route 9 := (fun mask => (mask,id))

def c9352 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9352 : Upper (D 5) (R 5) [18,96,33,132] 13 := by
  apply FastRouting.sound _ _ [18,96,33,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9352 c9352
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7812
  · exact u7813
  · exact u7814
  · exact u7815
  · exact u7816
  · exact u7817
  · exact u7818
  · exact u7819
  · exact u7820
  · exact u7821

def r9353 : Route 9 := (fun mask => (mask,id))

def c9353 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9353 : Upper (D 5) (R 5) [18,96,33,384] 13 := by
  apply FastRouting.sound _ _ [18,96,33,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9353 c9353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7822
  · exact u7823
  · exact u7824
  · exact u7825
  · exact u7826
  · exact u7827

def b9354 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 98 38 137 285 301 333 397 269), lower := (rows 19 98 38 137 16 32 64 128 256), losses := [] }

theorem u9354 : Upper (D 5) (R 5) [18,96,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9355 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 98 38 140 285 301 333 397 269), lower := (rows 19 98 38 140 16 32 64 128 256), losses := [] }

theorem u9355 : Upper (D 5) (R 5) [18,96,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9356 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 98 38 392 29 45 77 141 269), lower := (rows 19 98 38 392 16 32 64 128 256), losses := [] }

theorem u9356 : Upper (D 5) (R 5) [18,96,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9357 : Route 9 := (fun mask => (mask,id))

def c9357 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9357 : Upper (D 5) (R 5) [18,96,40,129] 13 := by
  apply FastRouting.sound _ _ [18,96,40,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9357 c9357
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7828
  · exact u7829
  · exact u7830
  · exact u7831
  · exact u7832
  · exact u7833
  · exact u7834
  · exact u7835
  · exact u7836
  · exact u7837

def r9358 : Route 9 := (fun mask => (mask,id))

def c9358 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9358 : Upper (D 5) (R 5) [18,96,40,130] 13 := by
  apply FastRouting.sound _ _ [18,96,40,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9358 c9358
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7838
  · exact u7839
  · exact u7840
  · exact u7841
  · exact u7842
  · exact u7843

def r9359 : Route 9 := (fun mask => (mask,id))

def c9359 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9359 : Upper (D 5) (R 5) [18,96,40,132] 13 := by
  apply FastRouting.sound _ _ [18,96,40,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r9359 c9359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7844
  · exact u7845
  · exact u7846
  · exact u7847
  · exact u7848
  · exact u7849
  · exact u7850
  · exact u7851
  · exact u7852
  · exact u7853

#print axioms u9359
end Delivery.IrregularNine14.P05
