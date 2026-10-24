import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0088
import IrregularNine14P05C0089
import IrregularNine14P05C0090
import IrregularNine14P05C0091
import IrregularNine14P05C0092
import IrregularNine14P05C0093

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 168 283 299 331 395 267), lower := (rows 7 22 100 168 16 32 64 128 256), losses := [] }

theorem u8760 : Upper (D 5) (R 5) [6,20,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8760
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 392 59 43 107 171 299), lower := (rows 7 22 100 392 16 32 64 128 256), losses := [] }

theorem u8761 : Upper (D 5) (R 5) [6,20,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8762 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 41 315 299 363 427 299), lower := (rows 7 22 196 41 16 32 64 128 256), losses := [] }

theorem u8762 : Upper (D 5) (R 5) [6,20,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8763 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 42 313 297 361 425 297), lower := (rows 7 22 196 42 16 32 64 128 256), losses := [] }

theorem u8763 : Upper (D 5) (R 5) [6,20,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8763
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8764 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 265 59 43 107 171 299), lower := (rows 7 22 196 265 16 32 64 128 256), losses := [] }

theorem u8764 : Upper (D 5) (R 5) [6,20,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8764
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8765 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 266 57 41 105 169 297), lower := (rows 7 22 196 266 16 32 64 128 256), losses := [] }

theorem u8765 : Upper (D 5) (R 5) [6,20,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8765
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8766 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 296 59 43 107 171 299), lower := (rows 7 22 196 296 16 32 64 128 256), losses := [] }

theorem u8766 : Upper (D 5) (R 5) [6,20,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8767 : PairBound 9 := { available := 462, camps := [{ cop := 2, region := 8, targets := 2 },{ cop := 2, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 26 37 41 478 494 462 462 462), lower := (rows 7 26 37 41 16 32 64 128 256), losses := [] }

theorem u8767 : Upper (D 5) (R 5) [6,24,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8768 : PairBound 9 := { available := 461, camps := [{ cop := 3, region := 5, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 42 477 493 461 461 461), lower := (rows 7 26 37 42 16 32 64 128 256), losses := [] }

theorem u8768 : Upper (D 5) (R 5) [6,24,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8768
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8769 : PairBound 9 := { available := 459, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 37 44 475 491 459 459 459), lower := (rows 7 26 37 44 16 32 64 128 256), losses := [] }

theorem u8769 : Upper (D 5) (R 5) [6,24,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8770 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8770 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8770 : Upper (D 5) (R 5) [6,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8770 c8770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5315
  · exact u5316
  · exact u5317
  · exact u5318
  · exact u5319
  · exact u5320
  · exact u5321
  · exact u5322
  · exact u5323
  · exact u5324
  · exact u5325

def r8771 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8771 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8771 : Upper (D 5) (R 5) [6,24,33,66] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8771 c8771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5326
  · exact u5327
  · exact u5328
  · exact u5329
  · exact u5330
  · exact u5331
  · exact u5332
  · exact u5333
  · exact u5334
  · exact u5335
  · exact u5336

def r8772 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8772 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8772 : Upper (D 5) (R 5) [6,24,33,68] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8772 c8772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5337
  · exact u5338
  · exact u5339
  · exact u5340
  · exact u5341
  · exact u5342
  · exact u5343
  · exact u5344
  · exact u5345
  · exact u5346
  · exact u5347

def r8773 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8773 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8773 : Upper (D 5) (R 5) [6,24,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r8773 c8773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5348
  · exact u5349
  · exact u5350
  · exact u5351
  · exact u5352
  · exact u5353
  · exact u5354
  · exact u5355
  · exact u5356
  · exact u5357
  · exact u5358

def r8774 : Route 9 := (fun mask => (mask,id))

def c8774 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8774 : Upper (D 5) (R 5) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8774 c8774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5359
  · exact u5360
  · exact u5361
  · exact u5362
  · exact u5363
  · exact u5364
  · exact u5365
  · exact u5366
  · exact u5367
  · exact u5368
  · exact u5369
  · exact u5370
  · exact u5371
  · exact u5372
  · exact u5373

def b8775 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 41 477 493 461 461 461), lower := (rows 7 26 38 41 16 32 64 128 256), losses := [] }

theorem u8775 : Upper (D 5) (R 5) [6,24,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8776 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 73 445 429 493 429 429), lower := (rows 7 26 38 73 16 32 64 128 256), losses := [] }

theorem u8776 : Upper (D 5) (R 5) [6,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8776
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8777 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 76 441 425 489 425 425), lower := (rows 7 26 38 76 16 32 64 128 256), losses := [] }

theorem u8777 : Upper (D 5) (R 5) [6,24,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8777
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8778 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 104 413 429 461 397 397), lower := (rows 7 26 38 104 16 32 64 128 256), losses := [] }

theorem u8778 : Upper (D 5) (R 5) [6,24,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8779 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 200 317 301 365 429 301), lower := (rows 7 26 38 200 16 32 64 128 256), losses := [] }

theorem u8779 : Upper (D 5) (R 5) [6,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8780 : PairBound 9 := { available := 455, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 41 471 487 455 455 455), lower := (rows 7 26 44 41 16 32 64 128 256), losses := [] }

theorem u8780 : Upper (D 5) (R 5) [6,24,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8781 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 42 469 485 453 453 453), lower := (rows 7 26 44 42 16 32 64 128 256), losses := [] }

theorem u8781 : Upper (D 5) (R 5) [6,24,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8782 : PairBound 9 := { available := 451, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 44 44 467 483 451 451 451), lower := (rows 7 26 44 44 16 32 64 128 256), losses := [] }

theorem u8782 : Upper (D 5) (R 5) [6,24,40,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8783 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8783 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8783 : Upper (D 5) (R 5) [6,24,40,65] 13 := by
  apply FastRouting.sound _ _ [6,24,40,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r8783 c8783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5374
  · exact u5375
  · exact u5376
  · exact u5377
  · exact u5378
  · exact u5379
  · exact u5380
  · exact u5381
  · exact u5382
  · exact u5383
  · exact u5384

def b8784 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 44 74 437 421 485 421 421), lower := (rows 7 26 44 74 16 32 64 128 256), losses := [] }

theorem u8784 : Upper (D 5) (R 5) [6,24,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8785 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 44 76 435 419 483 419 419), lower := (rows 7 26 44 76 16 32 64 128 256), losses := [] }

theorem u8785 : Upper (D 5) (R 5) [6,24,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8786 : PairBound 9 := { available := 391, camps := [{ cop := 2, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 104 407 423 455 391 391), lower := (rows 7 26 44 104 16 32 64 128 256), losses := [] }

theorem u8786 : Upper (D 5) (R 5) [6,24,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8786
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8787 : Route 9 := (fun mask => (mask,id))

def c8787 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8787 : Upper (D 5) (R 5) [6,24,40,192] 13 := by
  apply FastRouting.sound _ _ [6,24,40,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r8787 c8787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5385
  · exact u5386
  · exact u5387
  · exact u5388
  · exact u5389
  · exact u5390
  · exact u5391
  · exact u5392
  · exact u5393
  · exact u5394

def r8788 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8788 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8788 : Upper (D 5) (R 5) [6,24,65,33] 13 := by
  apply FastRouting.sound _ _ [6,24,65,33] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160,384] r8788 c8788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5395
  · exact u5396
  · exact u5397
  · exact u5398
  · exact u5399
  · exact u5400
  · exact u5401
  · exact u5402
  · exact u5403
  · exact u5404
  · exact u5405

def r8789 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8789 : Upper (D 5) (R 5) [6,24,65,34] 13 := by
  apply FastRouting.sound _ _ [6,24,65,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,384] r8789 c8789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5406
  · exact u5407
  · exact u5408
  · exact u5409
  · exact u5410
  · exact u5411
  · exact u5412
  · exact u5413
  · exact u5414
  · exact u5415
  · exact u5416

def r8790 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8790 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8790 : Upper (D 5) (R 5) [6,24,65,36] 13 := by
  apply FastRouting.sound _ _ [6,24,65,36] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r8790 c8790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5417
  · exact u5418
  · exact u5419
  · exact u5420
  · exact u5421
  · exact u5422
  · exact u5423
  · exact u5424
  · exact u5425
  · exact u5426
  · exact u5427

def r8791 : Route 9 := (fun mask => (mask,id))

def c8791 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8791 : Upper (D 5) (R 5) [6,24,65,129] 13 := by
  apply FastRouting.sound _ _ [6,24,65,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r8791 c8791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5428
  · exact u5429
  · exact u5430
  · exact u5431
  · exact u5432
  · exact u5433
  · exact u5434
  · exact u5435
  · exact u5436
  · exact u5437

def r8792 : Route 9 := (fun mask => (mask,id))

def c8792 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8792 : Upper (D 5) (R 5) [6,24,65,130] 13 := by
  apply FastRouting.sound _ _ [6,24,65,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8792 c8792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5438
  · exact u5439
  · exact u5440
  · exact u5441
  · exact u5442
  · exact u5443
  · exact u5444
  · exact u5445
  · exact u5446
  · exact u5447

def r8793 : Route 9 := (fun mask => (mask,id))

def c8793 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8793 : Upper (D 5) (R 5) [6,24,65,132] 13 := by
  apply FastRouting.sound _ _ [6,24,65,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8793 c8793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5448
  · exact u5449
  · exact u5450
  · exact u5451
  · exact u5452
  · exact u5453
  · exact u5454
  · exact u5455
  · exact u5456
  · exact u5457

def r8794 : Route 9 := (fun mask => (mask,id))

def c8794 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8794 : Upper (D 5) (R 5) [6,24,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8794 c8794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5458
  · exact u5459
  · exact u5460
  · exact u5461
  · exact u5462
  · exact u5463
  · exact u5464
  · exact u5465
  · exact u5466
  · exact u5467
  · exact u5468
  · exact u5469
  · exact u5470
  · exact u5471
  · exact u5472

def r8795 : Route 9 := (fun mask => (mask,id))

def c8795 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8795 : Upper (D 5) (R 5) [6,24,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8795 c8795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5473
  · exact u5474
  · exact u5475
  · exact u5476
  · exact u5477
  · exact u5478
  · exact u5479
  · exact u5480
  · exact u5481
  · exact u5482

def b8796 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 41 445 429 493 429 429), lower := (rows 7 26 70 41 16 32 64 128 256), losses := [] }

theorem u8796 : Upper (D 5) (R 5) [6,24,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8797 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 44 441 425 489 425 425), lower := (rows 7 26 70 44 16 32 64 128 256), losses := [] }

theorem u8797 : Upper (D 5) (R 5) [6,24,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8798 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 137 317 301 365 429 301), lower := (rows 7 26 70 137 16 32 64 128 256), losses := [] }

theorem u8798 : Upper (D 5) (R 5) [6,24,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8799 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 140 313 297 361 425 297), lower := (rows 7 26 70 140 16 32 64 128 256), losses := [] }

theorem u8799 : Upper (D 5) (R 5) [6,24,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8799
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8800 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 168 317 301 365 429 301), lower := (rows 7 26 70 168 16 32 64 128 256), losses := [] }

theorem u8800 : Upper (D 5) (R 5) [6,24,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8801 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 392 61 45 109 173 301), lower := (rows 7 26 70 392 16 32 64 128 256), losses := [] }

theorem u8801 : Upper (D 5) (R 5) [6,24,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8802 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8802 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8802 : Upper (D 5) (R 5) [6,24,72,33] 13 := by
  apply FastRouting.sound _ _ [6,24,72,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r8802 c8802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5483
  · exact u5484
  · exact u5485
  · exact u5486
  · exact u5487
  · exact u5488
  · exact u5489
  · exact u5490
  · exact u5491
  · exact u5492
  · exact u5493

def b8803 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 76 42 437 421 485 421 421), lower := (rows 7 26 76 42 16 32 64 128 256), losses := [] }

theorem u8803 : Upper (D 5) (R 5) [6,24,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8804 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 432, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 76 44 435 419 483 419 419), lower := (rows 7 26 76 44 16 32 64 128 256), losses := [] }

theorem u8804 : Upper (D 5) (R 5) [6,24,72,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8805 : Route 9 := (fun mask => (mask,id))

def c8805 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8805 : Upper (D 5) (R 5) [6,24,72,129] 13 := by
  apply FastRouting.sound _ _ [6,24,72,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r8805 c8805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5494
  · exact u5495
  · exact u5496
  · exact u5497
  · exact u5498
  · exact u5499
  · exact u5500
  · exact u5501
  · exact u5502
  · exact u5503

def b8806 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 76 138 309 293 357 421 293), lower := (rows 7 26 76 138 16 32 64 128 256), losses := [] }

theorem u8806 : Upper (D 5) (R 5) [6,24,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8807 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 304, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 76 140 307 291 355 419 291), lower := (rows 7 26 76 140 16 32 64 128 256), losses := [] }

theorem u8807 : Upper (D 5) (R 5) [6,24,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8808 : Route 9 := (fun mask => (mask,id))

def c8808 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8808 : Upper (D 5) (R 5) [6,24,72,160] 13 := by
  apply FastRouting.sound _ _ [6,24,72,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r8808 c8808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5504
  · exact u5505
  · exact u5506
  · exact u5507
  · exact u5508
  · exact u5509
  · exact u5510
  · exact u5511
  · exact u5512
  · exact u5513

def r8809 : Route 9 := (fun mask => (mask,id))

def c8809 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8809 : Upper (D 5) (R 5) [6,24,72,384] 13 := by
  apply FastRouting.sound _ _ [6,24,72,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r8809 c8809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5514
  · exact u5515
  · exact u5516
  · exact u5517
  · exact u5518
  · exact u5519

def r8810 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8810 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8810 : Upper (D 5) (R 5) [6,24,96,33] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r8810 c8810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5520
  · exact u5521
  · exact u5522
  · exact u5523
  · exact u5524
  · exact u5525
  · exact u5526
  · exact u5527
  · exact u5528
  · exact u5529
  · exact u5530

def r8811 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8811 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8811 : Upper (D 5) (R 5) [6,24,96,34] 13 := by
  apply FastRouting.sound _ _ [6,24,96,34] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r8811 c8811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5531
  · exact u5532
  · exact u5533
  · exact u5534
  · exact u5535
  · exact u5536
  · exact u5537

def b8812 : PairBound 9 := { available := 395, camps := [{ cop := 3, region := 403, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 100 44 411 427 459 395 395), lower := (rows 7 26 100 44 16 32 64 128 256), losses := [] }

theorem u8812 : Upper (D 5) (R 5) [6,24,96,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8813 : Route 9 := (fun mask => (mask,id))

def c8813 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8813 : Upper (D 5) (R 5) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8813 c8813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5538
  · exact u5539
  · exact u5540
  · exact u5541
  · exact u5542
  · exact u5543
  · exact u5544
  · exact u5545
  · exact u5546
  · exact u5547
  · exact u5548
  · exact u5549
  · exact u5550
  · exact u5551
  · exact u5552

def r8814 : Route 9 := (fun mask => (mask,id))

def c8814 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8814 : Upper (D 5) (R 5) [6,24,96,130] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8814 c8814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5553
  · exact u5554
  · exact u5555
  · exact u5556
  · exact u5557
  · exact u5558
  · exact u5559
  · exact u5560
  · exact u5561
  · exact u5562

def r8815 : Route 9 := (fun mask => (mask,id))

def c8815 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8815 : Upper (D 5) (R 5) [6,24,96,132] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r8815 c8815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5563
  · exact u5564
  · exact u5565
  · exact u5566
  · exact u5567
  · exact u5568
  · exact u5569
  · exact u5570
  · exact u5571
  · exact u5572

def r8816 : Route 9 := (fun mask => (mask,id))

def c8816 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8816 : Upper (D 5) (R 5) [6,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8816 c8816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5573
  · exact u5574
  · exact u5575
  · exact u5576
  · exact u5577
  · exact u5578
  · exact u5579
  · exact u5580
  · exact u5581
  · exact u5582

def r8817 : Route 9 := (fun mask => (mask,id))

def c8817 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8817 : Upper (D 5) (R 5) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8817 c8817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5583
  · exact u5584
  · exact u5585
  · exact u5586
  · exact u5587
  · exact u5588
  · exact u5589
  · exact u5590
  · exact u5591
  · exact u5592

def r8818 : Route 9 := (fun mask => (mask,id))

def c8818 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8818 : Upper (D 5) (R 5) [6,24,192,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8818 c8818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5593
  · exact u5594
  · exact u5595
  · exact u5596
  · exact u5597
  · exact u5598
  · exact u5599
  · exact u5600
  · exact u5601
  · exact u5602
  · exact u5603
  · exact u5604
  · exact u5605
  · exact u5606
  · exact u5607

def r8819 : Route 9 := (fun mask => (mask,id))

def c8819 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8819 : Upper (D 5) (R 5) [6,24,192,34] 13 := by
  apply FastRouting.sound _ _ [6,24,192,34] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r8819 c8819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5608
  · exact u5609
  · exact u5610
  · exact u5611
  · exact u5612
  · exact u5613
  · exact u5614
  · exact u5615
  · exact u5616
  · exact u5617

#print axioms u8819
end Delivery.IrregularNine14.P05
