import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0405
import IrregularNine14P07C0406
import IrregularNine14P07C0407

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37620 : Route 9 := (fun mask => (mask,id))

def c37620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37620 : Upper (D 7) (R 7) [36,96,136,65,257] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,257] 13 (by decide) (choices 1) [2,16,128] r37620 c37620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24306
  · exact u24307
  · exact u24308

def r37621 : Route 9 := (fun mask => (mask,id))

def c37621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37621 : Upper (D 7) (R 7) [36,96,136,65,258] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,258] 13 (by decide) (choices 1) [1,2,16,128] r37621 c37621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24309
  · exact u24310
  · exact u24311
  · exact u24312

def r37622 : Route 9 := (fun mask => (mask,id))

def c37622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37622 : Upper (D 7) (R 7) [36,96,136,65,384] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,384] 13 (by decide) (choices 1) [1,2,16] r37622 c37622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24313
  · exact u24314
  · exact u24315

def b37623 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(0,6),(2,5),(2,6),(3,5)], upper := (rows 37 98 140 88 19 419 451 387 387), lower := (rows 37 98 140 88 19 32 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 48 0 144 272), good := (rows 37 34 141 445 435 32 0 128 256) }] }

theorem u37623 : Upper (D 7) (R 7) [36,96,136,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37624 : Route 9 := (fun mask => (mask,id))

def c37624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37624 : Upper (D 7) (R 7) [36,96,136,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,129] 13 (by decide) (choices 1) [1,2,256] r37624 c37624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24316
  · exact u24317
  · exact u24318

def r37625 : Route 9 := (fun mask => (mask,id))

def c37625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37625 : Upper (D 7) (R 7) [36,96,136,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,130] 13 (by decide) (choices 1) [1,2,256] r37625 c37625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24319
  · exact u24320
  · exact u24321

def r37626 : Route 9 := (fun mask => (mask,id))

def c37626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37626 : Upper (D 7) (R 7) [36,96,136,80,257] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,257] 13 (by decide) (choices 1) [1,2,128] r37626 c37626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24322
  · exact u24323
  · exact u24324

def r37627 : Route 9 := (fun mask => (mask,id))

def c37627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37627 : Upper (D 7) (R 7) [36,96,136,80,258] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,258] 13 (by decide) (choices 1) [1,2,128] r37627 c37627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24325
  · exact u24326
  · exact u24327

def r37628 : Route 9 := (fun mask => (mask,id))

def c37628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37628 : Upper (D 7) (R 7) [36,96,136,80,384] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,384] 13 (by decide) (choices 1) [1,2] r37628 c37628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24328
  · exact u24329

def r37629 : Route 9 := (fun mask => (mask,id))

def c37629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37629 : Upper (D 7) (R 7) [36,96,136,257,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,3] 13 (by decide) (choices 1) [2,16,64,128] r37629 c37629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24330
  · exact u24331
  · exact u24332
  · exact u24333

def r37630 : Route 9 := (fun mask => (mask,id))

def c37630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37630 : Upper (D 7) (R 7) [36,96,136,257,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,65] 13 (by decide) (choices 1) [2,16,128] r37630 c37630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24334
  · exact u24335
  · exact u24336

def b37631 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 140 265 82 179 211 147 403), lower := (rows 37 98 140 265 82 32 64 128 256), losses := [] }

theorem u37631 : Upper (D 7) (R 7) [36,96,136,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37632 : Route 9 := (fun mask => (mask,id))

def c37632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37632 : Upper (D 7) (R 7) [36,96,136,257,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,129] 13 (by decide) (choices 1) [2,16,64] r37632 c37632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24337
  · exact u24338
  · exact u24339

def r37633 : Route 9 := (fun mask => (mask,id))

def c37633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37633 : Upper (D 7) (R 7) [36,96,136,257,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,130] 13 (by decide) (choices 1) [1,2,16,64] r37633 c37633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24340
  · exact u24341
  · exact u24342
  · exact u24343

def r37634 : Route 9 := (fun mask => (mask,id))

def c37634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37634 : Upper (D 7) (R 7) [36,96,136,257,192] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,192] 13 (by decide) (choices 1) [1,2,16] r37634 c37634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24344
  · exact u24345
  · exact u24346

def r37635 : Route 9 := (fun mask => (mask,id))

def c37635 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u37635 : Upper (D 7) (R 7) [36,96,136,258,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,3] 13 (by decide) (choices 1) [1,16,64,128] r37635 c37635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24347
  · exact u24348
  · exact u24349
  · exact u24350

def r37636 : Route 9 := (fun mask => (mask,id))

def c37636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37636 : Upper (D 7) (R 7) [36,96,136,258,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,65] 13 (by decide) (choices 1) [1,2,16,128] r37636 c37636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24351
  · exact u24352
  · exact u24353
  · exact u24354

def b37637 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 140 266 82 177 209 145 401), lower := (rows 37 98 140 266 82 32 64 128 256), losses := [] }

theorem u37637 : Upper (D 7) (R 7) [36,96,136,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37638 : Route 9 := (fun mask => (mask,id))

def c37638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37638 : Upper (D 7) (R 7) [36,96,136,258,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,129] 13 (by decide) (choices 1) [1,2,16,64] r37638 c37638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24355
  · exact u24356
  · exact u24357
  · exact u24358

def r37639 : Route 9 := (fun mask => (mask,id))

def c37639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37639 : Upper (D 7) (R 7) [36,96,136,258,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,130] 13 (by decide) (choices 1) [1,16,64] r37639 c37639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24359
  · exact u24360
  · exact u24361

def r37640 : Route 9 := (fun mask => (mask,id))

def c37640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37640 : Upper (D 7) (R 7) [36,96,136,258,192] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,192] 13 (by decide) (choices 1) [1,2,16] r37640 c37640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24362
  · exact u24363
  · exact u24364

def r37641 : Route 9 := (fun mask => (mask,id))

def c37641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37641 : Upper (D 7) (R 7) [36,96,136,272,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,3] 13 (by decide) (choices 1) [1,2,64,128] r37641 c37641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24365
  · exact u24366
  · exact u24367
  · exact u24368

def r37642 : Route 9 := (fun mask => (mask,id))

def c37642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37642 : Upper (D 7) (R 7) [36,96,136,272,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,65] 13 (by decide) (choices 1) [1,2,128] r37642 c37642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24369
  · exact u24370
  · exact u24371

def b37643 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 140 280 82 163 195 131 387), lower := (rows 37 98 140 280 82 32 64 128 256), losses := [] }

theorem u37643 : Upper (D 7) (R 7) [36,96,136,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37644 : Route 9 := (fun mask => (mask,id))

def c37644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37644 : Upper (D 7) (R 7) [36,96,136,272,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,129] 13 (by decide) (choices 1) [1,2,64] r37644 c37644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24372
  · exact u24373
  · exact u24374

def r37645 : Route 9 := (fun mask => (mask,id))

def c37645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37645 : Upper (D 7) (R 7) [36,96,136,272,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,130] 13 (by decide) (choices 1) [1,2,64] r37645 c37645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24375
  · exact u24376
  · exact u24377

def r37646 : Route 9 := (fun mask => (mask,id))

def c37646 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37646 : Upper (D 7) (R 7) [36,96,136,272,192] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272,192] 13 (by decide) (choices 1) [1,2] r37646 c37646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24378
  · exact u24379

def r37647 : Route 9 := (fun mask => (mask,id))

def c37647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37647 : Upper (D 7) (R 7) [36,96,136,320,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,3] 13 (by decide) (choices 1) [1,2,16,128] r37647 c37647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24380
  · exact u24381
  · exact u24382
  · exact u24383

def r37648 : Route 9 := (fun mask => (mask,id))

def c37648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37648 : Upper (D 7) (R 7) [36,96,136,320,129] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,129] 13 (by decide) (choices 1) [1,2,16] r37648 c37648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24384
  · exact u24385
  · exact u24386

def r37649 : Route 9 := (fun mask => (mask,id))

def c37649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37649 : Upper (D 7) (R 7) [36,96,136,320,130] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320,130] 13 (by decide) (choices 1) [1,2,16] r37649 c37649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24387
  · exact u24388
  · exact u24389

def b37650 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 64 },{ cop := 3, region := 16, targets := 128 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 196 11 19 440 472 408 408), lower := (rows 37 98 196 11 19 32 64 128 256), losses := [] }

theorem u37650 : Upper (D 7) (R 7) [36,96,192,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37651 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 16, targets := 130 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,1),(4,5),(4,7)], upper := (rows 37 98 196 11 25 434 466 402 402), lower := (rows 37 98 196 11 25 32 64 128 256), losses := [] }

theorem u37651 : Upper (D 7) (R 7) [36,96,192,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37652 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 16, targets := 129 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,0),(4,5),(4,7)], upper := (rows 37 98 196 11 26 433 465 401 401), lower := (rows 37 98 196 11 26 32 64 128 256), losses := [] }

theorem u37652 : Upper (D 7) (R 7) [36,96,192,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37653 : PairBound 9 := { available := 282, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 196 11 145 314 346 410 282), lower := (rows 37 98 196 11 145 32 64 128 256), losses := [] }

theorem u37653 : Upper (D 7) (R 7) [36,96,192,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37654 : Route 9 := (fun mask => (mask,id))

def c37654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37654 : Upper (D 7) (R 7) [36,96,192,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,130] 13 (by decide) (choices 1) [1,8,16,256] r37654 c37654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24390
  · exact u24391
  · exact u24392
  · exact u24393

def r37655 : Route 9 := (fun mask => (mask,id))

def c37655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37655 : Upper (D 7) (R 7) [36,96,192,3,136] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,136] 13 (by decide) (choices 1) [1,2,16,256] r37655 c37655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24394
  · exact u24395
  · exact u24396
  · exact u24397

def r37656 : Route 9 := (fun mask => (mask,id))

def c37656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37656 : Upper (D 7) (R 7) [36,96,192,3,257] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,257] 13 (by decide) (choices 1) [2,8,16,128] r37656 c37656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24398
  · exact u24399
  · exact u24400
  · exact u24401

def r37657 : Route 9 := (fun mask => (mask,id))

def c37657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37657 : Upper (D 7) (R 7) [36,96,192,3,258] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,258] 13 (by decide) (choices 1) [1,8,16,128] r37657 c37657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24402
  · exact u24403
  · exact u24404
  · exact u24405

def r37658 : Route 9 := (fun mask => (mask,id))

def c37658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37658 : Upper (D 7) (R 7) [36,96,192,3,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,264] 13 (by decide) (choices 1) [1,2,16,128] r37658 c37658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24406
  · exact u24407
  · exact u24408
  · exact u24409

def r37659 : Route 9 := (fun mask => (mask,id))

def c37659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37659 : Upper (D 7) (R 7) [36,96,192,3,384] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3,384] 13 (by decide) (choices 1) [1,2,8,16] r37659 c37659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24410
  · exact u24411
  · exact u24412
  · exact u24413

def b37660 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 196 25 25 418 450 386 386), lower := (rows 37 98 196 25 25 32 64 128 256), losses := [] }

theorem u37660 : Upper (D 7) (R 7) [36,96,192,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37661 : Route 9 := (fun mask => (mask,id))

def c37661 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u37661 : Upper (D 7) (R 7) [36,96,192,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,10] 13 (by decide) (choices 1) [1,2,128,256] r37661 c37661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24414
  · exact u24415
  · exact u24416
  · exact u24417

def b37662 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 196 25 145 298 330 394 266), lower := (rows 37 98 196 25 145 32 64 128 256), losses := [] }

theorem u37662 : Upper (D 7) (R 7) [36,96,192,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37663 : Route 9 := (fun mask => (mask,id))

def c37663 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37663 : Upper (D 7) (R 7) [36,96,192,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,130] 13 (by decide) (choices 1) [1,2,8,256] r37663 c37663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24418
  · exact u24419
  · exact u24420
  · exact u24421

def r37664 : Route 9 := (fun mask => (mask,id))

def c37664 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37664 : Upper (D 7) (R 7) [36,96,192,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,136] 13 (by decide) (choices 1) [1,2,256] r37664 c37664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24422
  · exact u24423
  · exact u24424

def b37665 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 196 25 273 170 202 138 394), lower := (rows 37 98 196 25 273 32 64 128 256), losses := [] }

theorem u37665 : Upper (D 7) (R 7) [36,96,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37666 : Route 9 := (fun mask => (mask,id))

def c37666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37666 : Upper (D 7) (R 7) [36,96,192,17,258] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,258] 13 (by decide) (choices 1) [1,2,8,128] r37666 c37666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24425
  · exact u24426
  · exact u24427
  · exact u24428

def r37667 : Route 9 := (fun mask => (mask,id))

def c37667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37667 : Upper (D 7) (R 7) [36,96,192,17,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,264] 13 (by decide) (choices 1) [1,2,128] r37667 c37667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24429
  · exact u24430
  · exact u24431

def r37668 : Route 9 := (fun mask => (mask,id))

def c37668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37668 : Upper (D 7) (R 7) [36,96,192,17,384] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,384] 13 (by decide) (choices 1) [1,2,8] r37668 c37668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24432
  · exact u24433
  · exact u24434

def b37669 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 196 26 26 417 449 385 385), lower := (rows 37 98 196 26 26 32 64 128 256), losses := [] }

theorem u37669 : Upper (D 7) (R 7) [36,96,192,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37670 : Route 9 := (fun mask => (mask,id))

def c37670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37670 : Upper (D 7) (R 7) [36,96,192,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,129] 13 (by decide) (choices 1) [1,2,8,256] r37670 c37670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24435
  · exact u24436
  · exact u24437
  · exact u24438

def b37671 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 196 26 146 297 329 393 265), lower := (rows 37 98 196 26 146 32 64 128 256), losses := [] }

theorem u37671 : Upper (D 7) (R 7) [36,96,192,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37672 : Route 9 := (fun mask => (mask,id))

def c37672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37672 : Upper (D 7) (R 7) [36,96,192,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,136] 13 (by decide) (choices 1) [1,2,256] r37672 c37672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24439
  · exact u24440
  · exact u24441

def r37673 : Route 9 := (fun mask => (mask,id))

def c37673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37673 : Upper (D 7) (R 7) [36,96,192,18,257] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,257] 13 (by decide) (choices 1) [1,2,8,128] r37673 c37673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24442
  · exact u24443
  · exact u24444
  · exact u24445

def b37674 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 196 26 274 169 201 137 393), lower := (rows 37 98 196 26 274 32 64 128 256), losses := [] }

theorem u37674 : Upper (D 7) (R 7) [36,96,192,18,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37675 : Route 9 := (fun mask => (mask,id))

def c37675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37675 : Upper (D 7) (R 7) [36,96,192,18,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,264] 13 (by decide) (choices 1) [1,2,128] r37675 c37675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24446
  · exact u24447
  · exact u24448

def r37676 : Route 9 := (fun mask => (mask,id))

def c37676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37676 : Upper (D 7) (R 7) [36,96,192,18,384] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,384] 13 (by decide) (choices 1) [1,2,8] r37676 c37676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24449
  · exact u24450
  · exact u24451

def r37677 : Route 9 := (fun mask => (mask,id))

def c37677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37677 : Upper (D 7) (R 7) [36,96,192,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,257] 13 (by decide) (choices 1) [2,8,16] r37677 c37677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24452
  · exact u24453
  · exact u24454

def r37678 : Route 9 := (fun mask => (mask,id))

def c37678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37678 : Upper (D 7) (R 7) [36,96,192,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,258] 13 (by decide) (choices 1) [1,2,8,16] r37678 c37678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24455
  · exact u24456
  · exact u24457
  · exact u24458

def r37679 : Route 9 := (fun mask => (mask,id))

def c37679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37679 : Upper (D 7) (R 7) [36,96,192,129,264] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,264] 13 (by decide) (choices 1) [1,2,16] r37679 c37679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24459
  · exact u24460
  · exact u24461

#print axioms u37679
end Delivery.IrregularNine14.P07
