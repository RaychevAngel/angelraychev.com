import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0069
import IrregularNine14P01C0070
import IrregularNine14P01C0071

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 334, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 168 350 366 334 462 334), lower := (rows 113 146 7 168 16 32 64 128 256), losses := [] }

theorem u7560 : Upper (D 1) (R 1) [112,144,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7560
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7561 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 266 252 236 236 236 492), lower := (rows 113 146 7 266 16 32 64 128 256), losses := [] }

theorem u7561 : Upper (D 1) (R 1) [112,144,3,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7562 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 268 250 234 234 234 490), lower := (rows 113 146 7 268 16 32 64 128 256), losses := [] }

theorem u7562 : Upper (D 1) (R 1) [112,144,3,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7563 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 296 222 238 206 206 462), lower := (rows 113 146 7 296 16 32 64 128 256), losses := [] }

theorem u7563 : Upper (D 1) (R 1) [112,144,3,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7564 : PairBound 9 := { available := 110, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 392 126 110 110 238 366), lower := (rows 113 146 7 392 16 32 64 128 256), losses := [] }

theorem u7564 : Upper (D 1) (R 1) [112,144,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7565 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u7565 : Upper (D 1) (R 1) [112,144,9,6] 13 := by
  apply FastRouting.sound _ _ [112,144,9,6] 13 (by decide) (choices 1) [2,32,128,256] r7565 c7565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4175
  · exact u4176
  · exact u4177
  · exact u4178

def b7566 : PairBound 9 := { available := 454, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 42 470 486 454 454 454), lower := (rows 113 146 13 42 16 32 64 128 256), losses := [] }

theorem u7566 : Upper (D 1) (R 1) [112,144,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7567 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 13 44 466 482 450 450 450), lower := (rows 113 146 13 44 16 32 64 128 256), losses := [] }

theorem u7567 : Upper (D 1) (R 1) [112,144,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7568 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 13 104 406 422 454 390 390), lower := (rows 113 146 13 104 16 32 64 128 256), losses := [] }

theorem u7568 : Upper (D 1) (R 1) [112,144,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7569 : PairBound 9 := { available := 358, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 13 138 374 358 358 486 358), lower := (rows 113 146 13 138 16 32 64 128 256), losses := [] }

theorem u7569 : Upper (D 1) (R 1) [112,144,9,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7570 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 13 140 370 354 354 482 354), lower := (rows 113 146 13 140 16 32 64 128 256), losses := [] }

theorem u7570 : Upper (D 1) (R 1) [112,144,9,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7571 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 168 342 358 326 454 326), lower := (rows 113 146 13 168 16 32 64 128 256), losses := [] }

theorem u7571 : Upper (D 1) (R 1) [112,144,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7572 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7572 : Upper (D 1) (R 1) [112,144,9,258] 13 := by
  apply FastRouting.sound _ _ [112,144,9,258] 13 (by decide) (choices 1) [2,4,32,128] r7572 c7572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4179
  · exact u4180
  · exact u4181
  · exact u4182

def r7573 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7573 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7573 : Upper (D 1) (R 1) [112,144,9,260] 13 := by
  apply FastRouting.sound _ _ [112,144,9,260] 13 (by decide) (choices 1) [2,32,128] r7573 c7573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4183
  · exact u4184
  · exact u4185

def b7574 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 13 296 214 230 198 198 454), lower := (rows 113 146 13 296 16 32 64 128 256), losses := [] }

theorem u7574 : Upper (D 1) (R 1) [112,144,9,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7575 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7575 : Upper (D 1) (R 1) [112,144,9,384] 13 := by
  apply FastRouting.sound _ _ [112,144,9,384] 13 (by decide) (choices 1) [2,4,32] r7575 c7575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4186
  · exact u4187
  · exact u4188

def b7576 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 14 14 497 481 481 481 481), lower := (rows 113 146 14 14 16 32 64 128 256), losses := [] }

theorem u7576 : Upper (D 1) (R 1) [112,144,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7577 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 146 14 41 470 486 454 454 454), lower := (rows 113 146 14 41 16 32 64 128 256), losses := [] }

theorem u7577 : Upper (D 1) (R 1) [112,144,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7578 : PairBound 9 := { available := 453, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 14 42 469 485 453 453 453), lower := (rows 113 146 14 42 16 32 64 128 256), losses := [] }

theorem u7578 : Upper (D 1) (R 1) [112,144,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7578
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7579 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 14 44 467 483 451 451 451), lower := (rows 113 146 14 44 16 32 64 128 256), losses := [] }

theorem u7579 : Upper (D 1) (R 1) [112,144,10,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7579
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7580 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 146 14 104 407 423 455 391 391), lower := (rows 113 146 14 104 16 32 64 128 256), losses := [] }

theorem u7580 : Upper (D 1) (R 1) [112,144,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7581 : PairBound 9 := { available := 358, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 137 374 358 358 486 358), lower := (rows 113 146 14 137 16 32 64 128 256), losses := [] }

theorem u7581 : Upper (D 1) (R 1) [112,144,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7582 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 14 138 373 357 357 485 357), lower := (rows 113 146 14 138 16 32 64 128 256), losses := [] }

theorem u7582 : Upper (D 1) (R 1) [112,144,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7583 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 14 140 371 355 355 483 355), lower := (rows 113 146 14 140 16 32 64 128 256), losses := [] }

theorem u7583 : Upper (D 1) (R 1) [112,144,10,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7584 : PairBound 9 := { available := 327, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 168 343 359 327 455 327), lower := (rows 113 146 14 168 16 32 64 128 256), losses := [] }

theorem u7584 : Upper (D 1) (R 1) [112,144,10,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7585 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7585 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7585 : Upper (D 1) (R 1) [112,144,10,257] 13 := by
  apply FastRouting.sound _ _ [112,144,10,257] 13 (by decide) (choices 1) [2,4,32,128] r7585 c7585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4189
  · exact u4190
  · exact u4191
  · exact u4192

def b7586 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 14 266 245 229 229 229 485), lower := (rows 113 146 14 266 16 32 64 128 256), losses := [] }

theorem u7586 : Upper (D 1) (R 1) [112,144,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7587 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7587 : Upper (D 1) (R 1) [112,144,10,260] 13 := by
  apply FastRouting.sound _ _ [112,144,10,260] 13 (by decide) (choices 1) [1,2,32,128] r7587 c7587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4193
  · exact u4194
  · exact u4195
  · exact u4196

def r7588 : Route 9 := (fun mask => (mask,id))

def c7588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7588 : Upper (D 1) (R 1) [112,144,10,288] 13 := by
  apply FastRouting.sound _ _ [112,144,10,288] 13 (by decide) (choices 1) [1,2,4,64,128] r7588 c7588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4197
  · exact u4198
  · exact u4199
  · exact u4200
  · exact u4201

def b7589 : PairBound 9 := { available := 103, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 14 392 119 103 103 231 359), lower := (rows 113 146 14 392 16 32 64 128 256), losses := [] }

theorem u7589 : Upper (D 1) (R 1) [112,144,10,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7590 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 74 414 430 462 398 398), lower := (rows 113 146 37 74 16 32 64 128 256), losses := [] }

theorem u7590 : Upper (D 1) (R 1) [112,144,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7591 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 76 410 426 458 394 394), lower := (rows 113 146 37 76 16 32 64 128 256), losses := [] }

theorem u7591 : Upper (D 1) (R 1) [112,144,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7592 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 140 346 362 330 458 330), lower := (rows 113 146 37 140 16 32 64 128 256), losses := [] }

theorem u7592 : Upper (D 1) (R 1) [112,144,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7593 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 200 286 302 334 398 270), lower := (rows 113 146 37 200 16 32 64 128 256), losses := [] }

theorem u7593 : Upper (D 1) (R 1) [112,144,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 266 222 238 206 206 462), lower := (rows 113 146 37 266 16 32 64 128 256), losses := [] }

theorem u7594 : Upper (D 1) (R 1) [112,144,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7595 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 268 218 234 202 202 458), lower := (rows 113 146 37 268 16 32 64 128 256), losses := [] }

theorem u7595 : Upper (D 1) (R 1) [112,144,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7596 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 328 158 174 206 142 398), lower := (rows 113 146 37 328 16 32 64 128 256), losses := [] }

theorem u7596 : Upper (D 1) (R 1) [112,144,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7597 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 37 392 94 110 78 206 334), lower := (rows 113 146 37 392 16 32 64 128 256), losses := [] }

theorem u7597 : Upper (D 1) (R 1) [112,144,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7597
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7598_8 : Upper (D 1) (R 1) [112,144,34,66,8] 13 :=
  permutation_upper _ _ _ [112,144,34,66,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4203

def r7598 : Route 9 := (fun mask => (mask,id))

def c7598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | _ => 0)

theorem u7598 : Upper (D 1) (R 1) [112,144,34,66] 13 := by
  apply FastRouting.sound _ _ [112,144,34,66] 13 (by decide) (choices 1) [1,4,8,128,256] r7598 c7598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4202
  · exact u4203
  · exact m7598_8
  · exact u4204
  · exact u4205

def r7599 : Route 9 := (fun mask => (mask,id))

def c7599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u7599 : Upper (D 1) (R 1) [112,144,34,68] 13 := by
  apply FastRouting.sound _ _ [112,144,34,68] 13 (by decide) (choices 1) [1,2,8,128,256] r7599 c7599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4206
  · exact u4207
  · exact u4208
  · exact u4209
  · exact u4210

def r7600 : Route 9 := (fun mask => (mask,id))

def c7600 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | _ => 0)

theorem u7600 : Upper (D 1) (R 1) [112,144,34,129] 13 := by
  apply FastRouting.sound _ _ [112,144,34,129] 13 (by decide) (choices 1) [2,4,8,64,256] r7600 c7600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4211
  · exact u4212
  · exact u4213
  · exact u4214
  · exact u4215

def b7601 : PairBound 9 := { available := 333, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 38 138 349 365 333 461 333), lower := (rows 113 146 38 138 16 32 64 128 256), losses := [] }

theorem u7601 : Upper (D 1) (R 1) [112,144,34,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7602 : Route 9 := (fun mask => (mask,id))

def c7602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u7602 : Upper (D 1) (R 1) [112,144,34,132] 13 := by
  apply FastRouting.sound _ _ [112,144,34,132] 13 (by decide) (choices 1) [1,2,8,64,256] r7602 c7602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4216
  · exact u4217
  · exact u4218
  · exact u4219
  · exact u4220

def r7603 : Route 9 := (fun mask => (mask,id))

def c7603 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7603 : Upper (D 1) (R 1) [112,144,34,192] 13 := by
  apply FastRouting.sound _ _ [112,144,34,192] 13 (by decide) (choices 1) [1,2,4,8,256] r7603 c7603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4221
  · exact u4222
  · exact u4223
  · exact u4224
  · exact u4225

def r7604 : Route 9 := (fun mask => (mask,id))

def c7604 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u7604 : Upper (D 1) (R 1) [112,144,34,257] 13 := by
  apply FastRouting.sound _ _ [112,144,34,257] 13 (by decide) (choices 1) [2,4,8,64,128] r7604 c7604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4226
  · exact u4227
  · exact u4228
  · exact u4229
  · exact u4230

def r7605 : Route 9 := (fun mask => (mask,id))

def c7605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7605 : Upper (D 1) (R 1) [112,144,34,258] 13 := by
  apply FastRouting.sound _ _ [112,144,34,258] 13 (by decide) (choices 1) [1,4,8,64,128] r7605 c7605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4231
  · exact u4232
  · exact u4233
  · exact u4234
  · exact u4235

def r7606 : Route 9 := (fun mask => (mask,id))

def c7606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7606 : Upper (D 1) (R 1) [112,144,34,260] 13 := by
  apply FastRouting.sound _ _ [112,144,34,260] 13 (by decide) (choices 1) [1,2,8,64,128] r7606 c7606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4236
  · exact u4237
  · exact u4238
  · exact u4239
  · exact u4240

def r7607 : Route 9 := (fun mask => (mask,id))

def c7607 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7607 : Upper (D 1) (R 1) [112,144,34,320] 13 := by
  apply FastRouting.sound _ _ [112,144,34,320] 13 (by decide) (choices 1) [1,2,4,8,128] r7607 c7607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4241
  · exact u4242
  · exact u4243
  · exact u4244
  · exact u4245

def r7608 : Route 9 := (fun mask => (mask,id))

def c7608 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7608 : Upper (D 1) (R 1) [112,144,34,384] 13 := by
  apply FastRouting.sound _ _ [112,144,34,384] 13 (by decide) (choices 1) [1,2,4,8,64] r7608 c7608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4246
  · exact u4247
  · exact u4248
  · exact u4249
  · exact u4250

def b7609 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 44 76 403 419 451 387 387), lower := (rows 113 146 44 76 16 32 64 128 256), losses := [] }

theorem u7609 : Upper (D 1) (R 1) [112,144,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 137 342 358 326 454 326), lower := (rows 113 146 44 137 16 32 64 128 256), losses := [] }

theorem u7610 : Upper (D 1) (R 1) [112,144,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7611 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 44 138 343 359 327 455 327), lower := (rows 113 146 44 138 16 32 64 128 256), losses := [] }

theorem u7611 : Upper (D 1) (R 1) [112,144,40,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7612 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 140 339 355 323 451 323), lower := (rows 113 146 44 140 16 32 64 128 256), losses := [] }

theorem u7612 : Upper (D 1) (R 1) [112,144,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7613 : Route 9 := (fun mask => (mask,id))

def c7613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7613 : Upper (D 1) (R 1) [112,144,40,192] 13 := by
  apply FastRouting.sound _ _ [112,144,40,192] 13 (by decide) (choices 1) [1,2,4,256] r7613 c7613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4251
  · exact u4252
  · exact u4253
  · exact u4254

def b7614 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 265 214 230 198 198 454), lower := (rows 113 146 44 265 16 32 64 128 256), losses := [] }

theorem u7614 : Upper (D 1) (R 1) [112,144,40,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7615 : Route 9 := (fun mask => (mask,id))

def c7615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7615 : Upper (D 1) (R 1) [112,144,40,258] 13 := by
  apply FastRouting.sound _ _ [112,144,40,258] 13 (by decide) (choices 1) [1,2,4,64,128] r7615 c7615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4255
  · exact u4256
  · exact u4257
  · exact u4258
  · exact u4259

def b7616 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 44 268 211 227 195 195 451), lower := (rows 113 146 44 268 16 32 64 128 256), losses := [] }

theorem u7616 : Upper (D 1) (R 1) [112,144,40,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7617 : Route 9 := (fun mask => (mask,id))

def c7617 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7617 : Upper (D 1) (R 1) [112,144,40,320] 13 := by
  apply FastRouting.sound _ _ [112,144,40,320] 13 (by decide) (choices 1) [1,2,4,128] r7617 c7617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4260
  · exact u4261
  · exact u4262
  · exact u4263

def r7618 : Route 9 := (fun mask => (mask,id))

def c7618 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7618 : Upper (D 1) (R 1) [112,144,40,384] 13 := by
  apply FastRouting.sound _ _ [112,144,40,384] 13 (by decide) (choices 1) [1,2,4,64] r7618 c7618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4264
  · exact u4265
  · exact u4266
  · exact u4267

def b7619 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 137 286 302 334 398 270), lower := (rows 113 146 100 137 16 32 64 128 256), losses := [] }

theorem u7619 : Upper (D 1) (R 1) [112,144,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7619
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7619
end Delivery.IrregularNine14.P01
