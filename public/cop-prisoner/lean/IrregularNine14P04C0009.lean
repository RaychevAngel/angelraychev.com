import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0003
import IrregularNine14P04C0004
import IrregularNine14P04C0005

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 104 413 445 477 413 413), lower := (rows 7 11 22 104 16 32 64 128 256), losses := [] }

theorem u540 : Upper (D 4) (R 4) [6,9,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b540
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 470, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 28 41 470 502 470 470 470), lower := (rows 7 11 28 41 16 32 64 128 256), losses := [] }

theorem u541 : Upper (D 4) (R 4) [6,9,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b541
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 455, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 56 471 487 455 455 455), lower := (rows 7 11 28 56 16 32 64 128 256), losses := [] }

theorem u542 : Upper (D 4) (R 4) [6,9,24,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b542
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 104 407 439 471 407 407), lower := (rows 7 11 28 104 16 32 64 128 256), losses := [] }

theorem u543 : Upper (D 4) (R 4) [6,9,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b543
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 76 410 442 474 410 410), lower := (rows 7 11 37 76 16 32 64 128 256), losses := [] }

theorem u544 : Upper (D 4) (R 4) [6,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b544
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 414 446 478 414 414), lower := (rows 7 11 37 88 16 32 64 128 256), losses := [] }

theorem u545 : Upper (D 4) (R 4) [6,9,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b545
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 286, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 286 318 350 414 286), lower := (rows 7 11 37 200 16 32 64 128 256), losses := [] }

theorem u546 : Upper (D 4) (R 4) [6,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b546
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 76 409 441 473 409 409), lower := (rows 7 11 38 76 16 32 64 128 256), losses := [] }

theorem u547 : Upper (D 4) (R 4) [6,9,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b547
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 413 445 477 413 413), lower := (rows 7 11 38 88 16 32 64 128 256), losses := [] }

theorem u548 : Upper (D 4) (R 4) [6,9,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b548
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 200 285 317 349 413 285), lower := (rows 7 11 38 200 16 32 64 128 256), losses := [] }

theorem u549 : Upper (D 4) (R 4) [6,9,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b549
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 44 76 403 435 467 403 403), lower := (rows 7 11 44 76 16 32 64 128 256), losses := [] }

theorem u550 : Upper (D 4) (R 4) [6,9,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b550
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 88 407 439 471 407 407), lower := (rows 7 11 44 88 16 32 64 128 256), losses := [] }

theorem u551 : Upper (D 4) (R 4) [6,9,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b551
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 44 200 279 311 343 407 279), lower := (rows 7 11 44 200 16 32 64 128 256), losses := [] }

theorem u552 : Upper (D 4) (R 4) [6,9,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b552
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m553_9 : Upper (D 4) (R 4) [6,9,48,80,9] 13 :=
  permutation_upper _ _ _ [6,9,48,80,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u315

theorem m553_10 : Upper (D 4) (R 4) [6,9,48,80,10] 13 :=
  permutation_upper _ _ _ [6,9,48,80,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u314

theorem m553_130 : Upper (D 4) (R 4) [6,9,48,80,130] 13 :=
  permutation_upper _ _ _ [6,9,48,80,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m553_136 : Upper (D 4) (R 4) [6,9,48,80,136] 13 :=
  permutation_upper _ _ _ [6,9,48,80,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

def r553 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c553 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u553 : Upper (D 4) (R 4) [6,9,48,80] 13 := by
  apply FastRouting.sound _ _ [6,9,48,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r553 c553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u313
  · exact u314
  · exact u315
  · exact m553_9
  · exact m553_10
  · exact u316
  · exact u317
  · exact m553_130
  · exact u318
  · exact m553_136
  · exact u319

def r554 : Route 9 := (fun mask => (mask,id))

def c554 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u554 : Upper (D 4) (R 4) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r554 c554
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u320
  · exact u321
  · exact u322
  · exact u323
  · exact u324
  · exact u325
  · exact u326
  · exact u327
  · exact u328
  · exact u329

theorem m555_9 : Upper (D 4) (R 4) [6,9,96,384,9] 13 :=
  permutation_upper _ _ _ [6,9,96,384,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u332

theorem m555_10 : Upper (D 4) (R 4) [6,9,96,384,10] 13 :=
  permutation_upper _ _ _ [6,9,96,384,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u331

def r555 : Route 9 := (fun mask => (mask,id))

def c555 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u555 : Upper (D 4) (R 4) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r555 c555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u330
  · exact u331
  · exact u332
  · exact m555_9
  · exact m555_10
  · exact u333

def b556 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 21 41 474 506 474 474 474), lower := (rows 7 14 21 41 16 32 64 128 256), losses := [] }

theorem u556 : Upper (D 4) (R 4) [6,12,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b556
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 21 42 473 505 473 473 473), lower := (rows 7 14 21 42 16 32 64 128 256), losses := [] }

theorem u557 : Upper (D 4) (R 4) [6,12,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b557
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 21 104 411 443 475 411 411), lower := (rows 7 14 21 104 16 32 64 128 256), losses := [] }

theorem u558 : Upper (D 4) (R 4) [6,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b558
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 41 467 499 467 467 467), lower := (rows 7 14 28 41 16 32 64 128 256), losses := [] }

theorem u559 : Upper (D 4) (R 4) [6,12,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b559
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 28 104 403 435 467 403 403), lower := (rows 7 14 28 104 16 32 64 128 256), losses := [] }

theorem u560 : Upper (D 4) (R 4) [6,12,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b560
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 73 410 442 474 410 410), lower := (rows 7 14 37 73 16 32 64 128 256), losses := [] }

theorem u561 : Upper (D 4) (R 4) [6,12,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b561
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 74 409 441 473 409 409), lower := (rows 7 14 37 74 16 32 64 128 256), losses := [] }

theorem u562 : Upper (D 4) (R 4) [6,12,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b562
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 88 411 443 475 411 411), lower := (rows 7 14 37 88 16 32 64 128 256), losses := [] }

theorem u563 : Upper (D 4) (R 4) [6,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b563
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 37 200 283 315 347 411 283), lower := (rows 7 14 37 200 16 32 64 128 256), losses := [] }

theorem u564 : Upper (D 4) (R 4) [6,12,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b564
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 25 473 505 473 473 473), lower := (rows 7 14 38 25 16 32 64 128 256), losses := [] }

theorem u565 : Upper (D 4) (R 4) [6,12,34,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b565
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 73 409 441 473 409 409), lower := (rows 7 14 38 73 16 32 64 128 256), losses := [] }

theorem u566 : Upper (D 4) (R 4) [6,12,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b566
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 200 281 313 345 409 281), lower := (rows 7 14 38 200 16 32 64 128 256), losses := [] }

theorem u567 : Upper (D 4) (R 4) [6,12,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b567
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 73 403 435 467 403 403), lower := (rows 7 14 44 73 16 32 64 128 256), losses := [] }

theorem u568 : Upper (D 4) (R 4) [6,12,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b568
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 200 275 307 339 403 275), lower := (rows 7 14 44 200 16 32 64 128 256), losses := [] }

theorem u569 : Upper (D 4) (R 4) [6,12,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b569
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 73 411 443 475 411 411), lower := (rows 7 14 52 73 16 32 64 128 256), losses := [] }

theorem u570 : Upper (D 4) (R 4) [6,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b570
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 200 283 315 347 411 283), lower := (rows 7 14 52 200 16 32 64 128 256), losses := [] }

theorem u571 : Upper (D 4) (R 4) [6,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b571
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 25 411 443 475 411 411), lower := (rows 7 14 100 25 16 32 64 128 256), losses := [] }

theorem u572 : Upper (D 4) (R 4) [6,12,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b572
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 137 283 315 347 411 283), lower := (rows 7 14 100 137 16 32 64 128 256), losses := [] }

theorem u573 : Upper (D 4) (R 4) [6,12,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b573
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 138 281 313 345 409 281), lower := (rows 7 14 100 138 16 32 64 128 256), losses := [] }

theorem u574 : Upper (D 4) (R 4) [6,12,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b574
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 392 27 59 91 155 283), lower := (rows 7 14 100 392 16 32 64 128 256), losses := [] }

theorem u575 : Upper (D 4) (R 4) [6,12,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b575
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 398, camps := [{ cop := 4, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 21 104 414 430 462 398 398), lower := (rows 7 19 21 104 16 32 64 128 256), losses := [] }

theorem u576 : Upper (D 4) (R 4) [6,17,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b576
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 460, camps := [{ cop := 4, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 22 41 476 492 460 460 460), lower := (rows 7 19 22 41 16 32 64 128 256), losses := [] }

theorem u577 : Upper (D 4) (R 4) [6,17,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b577
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 397, camps := [{ cop := 4, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 22 104 413 429 461 397 397), lower := (rows 7 19 22 104 16 32 64 128 256), losses := [] }

theorem u578 : Upper (D 4) (R 4) [6,17,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b578
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 462, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 28 41 478 494 462 462 462), lower := (rows 7 19 28 41 16 32 64 128 256), losses := [] }

theorem u579 : Upper (D 4) (R 4) [6,17,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b579
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 399, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 28 104 415 431 463 399 399), lower := (rows 7 19 28 104 16 32 64 128 256), losses := [] }

theorem u580 : Upper (D 4) (R 4) [6,17,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b580
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 37 76 410 442 474 410 410), lower := (rows 7 19 37 76 16 32 64 128 256), losses := [] }

theorem u581 : Upper (D 4) (R 4) [6,17,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b581
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 286, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 37 200 286 318 350 414 286), lower := (rows 7 19 37 200 16 32 64 128 256), losses := [] }

theorem u582 : Upper (D 4) (R 4) [6,17,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b582
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 412, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 38 73 412 444 476 412 412), lower := (rows 7 19 38 73 16 32 64 128 256), losses := [] }

theorem u583 : Upper (D 4) (R 4) [6,17,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b583
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 38 76 409 441 473 409 409), lower := (rows 7 19 38 76 16 32 64 128 256), losses := [] }

theorem u584 : Upper (D 4) (R 4) [6,17,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b584
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 19 38 200 285 317 349 413 285), lower := (rows 7 19 38 200 16 32 64 128 256), losses := [] }

theorem u585 : Upper (D 4) (R 4) [6,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b585
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 44 14 473 505 473 473 473), lower := (rows 7 19 44 14 16 32 64 128 256), losses := [] }

theorem u586 : Upper (D 4) (R 4) [6,17,40,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b586
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m587_6 : Upper (D 4) (R 4) [6,17,40,65,6] 13 :=
  permutation_upper _ _ _ [6,9,9,48,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u243

theorem m587_10 : Upper (D 4) (R 4) [6,17,40,65,10] 13 :=
  permutation_upper _ _ _ [6,9,17,36,72] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u251

theorem m587_12 : Upper (D 4) (R 4) [6,17,40,65,12] 13 :=
  permutation_upper _ _ _ [6,9,24,48,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u275

theorem m587_130 : Upper (D 4) (R 4) [6,17,40,65,130] 13 :=
  permutation_upper _ _ _ [6,9,33,80,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u285

theorem m587_132 : Upper (D 4) (R 4) [6,17,40,65,132] 13 :=
  permutation_upper _ _ _ [6,9,40,80,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u307

theorem m587_136 : Upper (D 4) (R 4) [6,17,40,65,136] 13 :=
  permutation_upper _ _ _ [6,9,48,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m587_384 : Upper (D 4) (R 4) [6,17,40,65,384] 13 :=
  permutation_upper _ _ _ [6,9,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u326

def r587 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c587 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u587 : Upper (D 4) (R 4) [6,17,40,65] 13 := by
  apply FastRouting.sound _ _ [6,17,40,65] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r587 c587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m587_6
  · exact m587_10
  · exact m587_12
  · exact m587_130
  · exact m587_132
  · exact m587_136
  · exact m587_384

theorem m588_5 : Upper (D 4) (R 4) [6,17,40,66,5] 13 :=
  permutation_upper _ _ _ [6,9,10,48,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u247

theorem m588_9 : Upper (D 4) (R 4) [6,17,40,66,9] 13 :=
  permutation_upper _ _ _ [6,9,18,48,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u257

theorem m588_12 : Upper (D 4) (R 4) [6,17,40,66,12] 13 :=
  permutation_upper _ _ _ [6,9,24,48,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u274

theorem m588_129 : Upper (D 4) (R 4) [6,17,40,66,129] 13 :=
  permutation_upper _ _ _ [6,9,34,80,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u296

theorem m588_132 : Upper (D 4) (R 4) [6,17,40,66,132] 13 :=
  permutation_upper _ _ _ [6,9,40,80,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u306

theorem m588_136 : Upper (D 4) (R 4) [6,17,40,66,136] 13 :=
  permutation_upper _ _ _ [6,9,48,80,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m588_384 : Upper (D 4) (R 4) [6,17,40,66,384] 13 :=
  permutation_upper _ _ _ [6,9,48,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u327

def r588 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c588 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u588 : Upper (D 4) (R 4) [6,17,40,66] 13 := by
  apply FastRouting.sound _ _ [6,17,40,66] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r588 c588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m588_5
  · exact m588_9
  · exact m588_12
  · exact m588_129
  · exact m588_132
  · exact m588_136
  · exact m588_384

theorem m589_3 : Upper (D 4) (R 4) [6,17,40,68,3] 13 :=
  permutation_upper _ _ _ [6,5,9,48,72] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u219

theorem m589_9 : Upper (D 4) (R 4) [6,17,40,68,9] 13 :=
  permutation_upper _ _ _ [6,9,18,48,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u259

theorem m589_10 : Upper (D 4) (R 4) [6,17,40,68,10] 13 :=
  permutation_upper _ _ _ [6,9,17,48,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u253

theorem m589_129 : Upper (D 4) (R 4) [6,17,40,68,129] 13 :=
  permutation_upper _ _ _ [6,9,34,80,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u298

theorem m589_130 : Upper (D 4) (R 4) [6,17,40,68,130] 13 :=
  permutation_upper _ _ _ [6,9,33,80,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u287

theorem m589_136 : Upper (D 4) (R 4) [6,17,40,68,136] 13 :=
  permutation_upper _ _ _ [6,9,48,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

theorem m589_384 : Upper (D 4) (R 4) [6,17,40,68,384] 13 :=
  permutation_upper _ _ _ [6,9,48,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u328

def r589 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c589 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u589 : Upper (D 4) (R 4) [6,17,40,68] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r589 c589
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m589_3
  · exact m589_9
  · exact m589_10
  · exact m589_129
  · exact m589_130
  · exact m589_136
  · exact m589_384

theorem m590_3 : Upper (D 4) (R 4) [6,17,40,192,3] 13 :=
  permutation_upper _ _ _ [6,5,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u220

theorem m590_5 : Upper (D 4) (R 4) [6,17,40,192,5] 13 :=
  permutation_upper _ _ _ [6,9,10,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u248

theorem m590_6 : Upper (D 4) (R 4) [6,17,40,192,6] 13 :=
  permutation_upper _ _ _ [6,9,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u244

theorem m590_9 : Upper (D 4) (R 4) [6,17,40,192,9] 13 :=
  permutation_upper _ _ _ [6,9,18,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u260

theorem m590_10 : Upper (D 4) (R 4) [6,17,40,192,10] 13 :=
  permutation_upper _ _ _ [6,9,17,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u254

theorem m590_12 : Upper (D 4) (R 4) [6,17,40,192,12] 13 :=
  permutation_upper _ _ _ [6,9,24,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u276

theorem m590_257 : Upper (D 4) (R 4) [6,17,40,192,257] 13 :=
  permutation_upper _ _ _ [6,9,34,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u299

theorem m590_258 : Upper (D 4) (R 4) [6,17,40,192,258] 13 :=
  permutation_upper _ _ _ [6,9,33,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u288

theorem m590_260 : Upper (D 4) (R 4) [6,17,40,192,260] 13 :=
  permutation_upper _ _ _ [6,9,40,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u309

theorem m590_264 : Upper (D 4) (R 4) [6,17,40,192,264] 13 :=
  permutation_upper _ _ _ [6,9,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u319

def r590 : Route 9 := (fun mask => (mask,id))

def c590 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u590 : Upper (D 4) (R 4) [6,17,40,192] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r590 c590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m590_3
  · exact m590_5
  · exact m590_6
  · exact m590_9
  · exact m590_10
  · exact m590_12
  · exact m590_257
  · exact m590_258
  · exact m590_260
  · exact m590_264

def b591 : PairBound 9 := { available := 398, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 52 73 414 430 462 398 398), lower := (rows 7 19 52 73 16 32 64 128 256), losses := [] }

theorem u591 : Upper (D 4) (R 4) [6,17,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b591
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 271, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 19 52 200 287 303 335 399 271), lower := (rows 7 19 52 200 16 32 64 128 256), losses := [] }

theorem u592 : Upper (D 4) (R 4) [6,17,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b592
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 19 100 14 409 441 473 409 409), lower := (rows 7 19 100 14 16 32 64 128 256), losses := [] }

theorem u593 : Upper (D 4) (R 4) [6,17,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b593
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m594_6 : Upper (D 4) (R 4) [6,17,96,129,6] 13 :=
  permutation_upper _ _ _ [6,9,9,96,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u245

theorem m594_10 : Upper (D 4) (R 4) [6,17,96,129,10] 13 :=
  permutation_upper _ _ _ [6,9,17,36,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u252

theorem m594_12 : Upper (D 4) (R 4) [6,17,96,129,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u278

theorem m594_258 : Upper (D 4) (R 4) [6,17,96,129,258] 13 :=
  permutation_upper _ _ _ [6,9,33,192,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u290

theorem m594_260 : Upper (D 4) (R 4) [6,17,96,129,260] 13 :=
  permutation_upper _ _ _ [6,9,40,192,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u311

theorem m594_264 : Upper (D 4) (R 4) [6,17,96,129,264] 13 :=
  permutation_upper _ _ _ [6,9,48,192,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u327

def r594 : Route 9 := (fun mask => (mask,id))

def c594 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u594 : Upper (D 4) (R 4) [6,17,96,129] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r594 c594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m594_6
  · exact m594_10
  · exact m594_12
  · exact m594_258
  · exact m594_260
  · exact m594_264

theorem m595_5 : Upper (D 4) (R 4) [6,17,96,130,5] 13 :=
  permutation_upper _ _ _ [6,9,10,96,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u249

theorem m595_9 : Upper (D 4) (R 4) [6,17,96,130,9] 13 :=
  permutation_upper _ _ _ [6,9,18,96,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u261

theorem m595_12 : Upper (D 4) (R 4) [6,17,96,130,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u277

theorem m595_257 : Upper (D 4) (R 4) [6,17,96,130,257] 13 :=
  permutation_upper _ _ _ [6,9,34,192,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u301

theorem m595_260 : Upper (D 4) (R 4) [6,17,96,130,260] 13 :=
  permutation_upper _ _ _ [6,9,40,192,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u310

theorem m595_264 : Upper (D 4) (R 4) [6,17,96,130,264] 13 :=
  permutation_upper _ _ _ [6,9,48,192,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u326

def r595 : Route 9 := (fun mask => (mask,id))

def c595 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u595 : Upper (D 4) (R 4) [6,17,96,130] 13 := by
  apply FastRouting.sound _ _ [6,17,96,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r595 c595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m595_5
  · exact m595_9
  · exact m595_12
  · exact m595_257
  · exact m595_260
  · exact m595_264

theorem m596_3 : Upper (D 4) (R 4) [6,17,96,132,3] 13 :=
  permutation_upper _ _ _ [6,5,9,96,136] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u221

theorem m596_9 : Upper (D 4) (R 4) [6,17,96,132,9] 13 :=
  permutation_upper _ _ _ [6,9,18,96,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u263

theorem m596_10 : Upper (D 4) (R 4) [6,17,96,132,10] 13 :=
  permutation_upper _ _ _ [6,9,17,48,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u254

theorem m596_257 : Upper (D 4) (R 4) [6,17,96,132,257] 13 :=
  permutation_upper _ _ _ [6,9,34,192,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u303

theorem m596_258 : Upper (D 4) (R 4) [6,17,96,132,258] 13 :=
  permutation_upper _ _ _ [6,9,33,192,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u292

theorem m596_264 : Upper (D 4) (R 4) [6,17,96,132,264] 13 :=
  permutation_upper _ _ _ [6,9,48,192,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u329

def r596 : Route 9 := (fun mask => (mask,id))

def c596 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u596 : Upper (D 4) (R 4) [6,17,96,132] 13 := by
  apply FastRouting.sound _ _ [6,17,96,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r596 c596
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m596_3
  · exact m596_9
  · exact m596_10
  · exact m596_257
  · exact m596_258
  · exact m596_264

theorem m597_3 : Upper (D 4) (R 4) [6,17,96,384,3] 13 :=
  permutation_upper _ _ _ [6,5,9,96,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u222

theorem m597_5 : Upper (D 4) (R 4) [6,17,96,384,5] 13 :=
  permutation_upper _ _ _ [6,9,10,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u250

theorem m597_6 : Upper (D 4) (R 4) [6,17,96,384,6] 13 :=
  permutation_upper _ _ _ [6,9,9,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u246

theorem m597_9 : Upper (D 4) (R 4) [6,17,96,384,9] 13 :=
  permutation_upper _ _ _ [6,9,18,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u264

theorem m597_10 : Upper (D 4) (R 4) [6,17,96,384,10] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u255

theorem m597_12 : Upper (D 4) (R 4) [6,17,96,384,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u280

def r597 : Route 9 := (fun mask => (mask,id))

def c597 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u597 : Upper (D 4) (R 4) [6,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,17,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r597 c597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m597_3
  · exact m597_5
  · exact m597_6
  · exact m597_9
  · exact m597_10
  · exact m597_12

def b598 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 488, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 28 41 475 491 459 459 459), lower := (rows 7 22 28 41 16 32 64 128 256), losses := [] }

theorem u598 : Upper (D 4) (R 4) [6,20,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b598
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 488, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 28 104 411 427 459 395 395), lower := (rows 7 22 28 104 16 32 64 128 256), losses := [] }

theorem u599 : Upper (D 4) (R 4) [6,20,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b599
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P04
