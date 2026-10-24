import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0138
import IrregularNine14P05C0139
import IrregularNine14P05C0140
import IrregularNine14P05C0141
import IrregularNine14P05C0142

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9480 : Route 9 := (fun mask => (mask,id))

def c9480 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9480 : Upper (D 5) (R 5) [34,68,160,272] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9480 c9480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8327
  · exact u8328
  · exact u8329
  · exact u8330
  · exact u8331
  · exact u8332

def b9481 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 8, targets := 4 }], pairs := [(3,0),(3,2)], upper := (rows 35 70 388 42 29 61 93 157 285), lower := (rows 35 70 388 42 16 32 64 128 256), losses := [] }

theorem u9481 : Upper (D 5) (R 5) [34,68,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9482 : Route 9 := (fun mask => (mask,id))

def c9482 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9482 : Upper (D 5) (R 5) [34,68,384,36] 13 := by
  apply FastRouting.sound _ _ [34,68,384,36] 13 (by decide) (choices 2) [3,9,10] r9482 c9482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8333
  · exact u8334
  · exact u8335

def r9483 : Route 9 := (fun mask => (mask,id))

def c9483 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9483 : Upper (D 5) (R 5) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9483 c9483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8336
  · exact u8337
  · exact u8338
  · exact u8339
  · exact u8340
  · exact u8341

def b9484 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 82 38 137 285 301 333 397 269), lower := (rows 35 82 38 137 16 32 64 128 256), losses := [] }

theorem u9484 : Upper (D 5) (R 5) [34,80,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9485 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 82 38 392 29 45 77 141 269), lower := (rows 35 82 38 392 16 32 64 128 256), losses := [] }

theorem u9485 : Upper (D 5) (R 5) [34,80,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9486 : Route 9 := (fun mask => (mask,id))

def c9486 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9486 : Upper (D 5) (R 5) [34,80,40,384] 13 := by
  apply FastRouting.sound _ _ [34,80,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9486 c9486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8342
  · exact u8343
  · exact u8344
  · exact u8345
  · exact u8346
  · exact u8347

theorem m9487_10 : Upper (D 5) (R 5) [34,80,129,257,10] 13 :=
  permutation_upper _ _ _ [34,80,129,257,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8348

theorem m9487_40 : Upper (D 5) (R 5) [34,80,129,257,40] 13 :=
  permutation_upper _ _ _ [34,80,129,257,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8351

def r9487 : Route 9 := (fun mask => (mask,id))

def c9487 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9487 : Upper (D 5) (R 5) [34,80,129,257] 13 := by
  apply FastRouting.sound _ _ [34,80,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9487 c9487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8348
  · exact m9487_10
  · exact u8349
  · exact u8350
  · exact u8351
  · exact m9487_40

def r9488 : Route 9 := (fun mask => (mask,id))

def c9488 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9488 : Upper (D 5) (R 5) [34,80,129,258] 13 := by
  apply FastRouting.sound _ _ [34,80,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9488 c9488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8352
  · exact u8353
  · exact u8354
  · exact u8355
  · exact u8356
  · exact u8357

def r9489 : Route 9 := (fun mask => (mask,id))

def c9489 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9489 : Upper (D 5) (R 5) [34,80,129,260] 13 := by
  apply FastRouting.sound _ _ [34,80,129,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9489 c9489
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8358
  · exact u8359
  · exact u8360
  · exact u8361
  · exact u8362
  · exact u8363
  · exact u8364
  · exact u8365
  · exact u8366
  · exact u8367

def r9490 : Route 9 := (fun mask => (mask,id))

def c9490 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9490 : Upper (D 5) (R 5) [34,80,129,288] 13 := by
  apply FastRouting.sound _ _ [34,80,129,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9490 c9490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8368
  · exact u8369
  · exact u8370
  · exact u8371
  · exact u8372
  · exact u8373

def r9491 : Route 9 := (fun mask => (mask,id))

def c9491 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9491 : Upper (D 5) (R 5) [34,80,130,260] 13 := by
  apply FastRouting.sound _ _ [34,80,130,260] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9491 c9491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8374
  · exact u8375
  · exact u8376
  · exact u8377
  · exact u8378
  · exact u8379

def r9492 : Route 9 := (fun mask => (mask,id))

def c9492 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9492 : Upper (D 5) (R 5) [34,80,130,288] 13 := by
  apply FastRouting.sound _ _ [34,80,130,288] 13 (by decide) (choices 2) [5,9,12] r9492 c9492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8380
  · exact u8381
  · exact u8382

theorem m9493_9 : Upper (D 5) (R 5) [34,80,136,260,9] 13 :=
  permutation_upper _ _ _ [34,80,136,260,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8384

theorem m9493_10 : Upper (D 5) (R 5) [34,80,136,260,10] 13 :=
  permutation_upper _ _ _ [34,80,136,260,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8385

theorem m9493_40 : Upper (D 5) (R 5) [34,80,136,260,40] 13 :=
  permutation_upper _ _ _ [34,80,136,260,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8389

def r9493 : Route 9 := (fun mask => (mask,id))

def c9493 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9493 : Upper (D 5) (R 5) [34,80,136,260] 13 := by
  apply FastRouting.sound _ _ [34,80,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9493 c9493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8383
  · exact u8384
  · exact u8385
  · exact m9493_9
  · exact m9493_10
  · exact u8386
  · exact u8387
  · exact u8388
  · exact u8389
  · exact m9493_40

def r9494 : Route 9 := (fun mask => (mask,id))

def c9494 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9494 : Upper (D 5) (R 5) [34,80,136,288] 13 := by
  apply FastRouting.sound _ _ [34,80,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9494 c9494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8390
  · exact u8391
  · exact u8392
  · exact u8393
  · exact u8394
  · exact u8395

def b9495 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 133 266 29 61 93 157 285), lower := (rows 35 98 133 266 16 32 64 128 256), losses := [] }

theorem u9495 : Upper (D 5) (R 5) [34,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9496 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 133 268 31 63 95 159 287), lower := (rows 35 98 133 268 16 32 64 128 256), losses := [] }

theorem u9496 : Upper (D 5) (R 5) [34,96,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9497 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 133 280 31 47 79 143 271), lower := (rows 35 98 133 280 16 32 64 128 256), losses := [] }

theorem u9497 : Upper (D 5) (R 5) [34,96,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9498 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 134 268 29 61 93 157 285), lower := (rows 35 98 134 268 16 32 64 128 256), losses := [] }

theorem u9498 : Upper (D 5) (R 5) [34,96,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9499 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 134 280 29 45 77 141 269), lower := (rows 35 98 134 280 16 32 64 128 256), losses := [] }

theorem u9499 : Upper (D 5) (R 5) [34,96,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9500 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 140 268 31 63 95 159 287), lower := (rows 35 98 140 268 16 32 64 128 256), losses := [] }

theorem u9500 : Upper (D 5) (R 5) [34,96,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9501 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 412, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 98 140 280 31 47 79 143 271), lower := (rows 35 98 140 280 16 32 64 128 256), losses := [] }

theorem u9501 : Upper (D 5) (R 5) [34,96,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9502 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 194 38 265 29 61 93 157 285), lower := (rows 35 194 38 265 16 32 64 128 256), losses := [] }

theorem u9502 : Upper (D 5) (R 5) [34,192,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9503 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 194 38 280 29 45 77 141 269), lower := (rows 35 194 38 280 16 32 64 128 256), losses := [] }

theorem u9503 : Upper (D 5) (R 5) [34,192,34,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9504 : Route 9 := (fun mask => (mask,id))

def c9504 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9504 : Upper (D 5) (R 5) [34,192,48,257] 13 := by
  apply FastRouting.sound _ _ [34,192,48,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9504 c9504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8396
  · exact u8397
  · exact u8398
  · exact u8399
  · exact u8400
  · exact u8401

def r9505 : Route 9 := (fun mask => (mask,id))

def c9505 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9505 : Upper (D 5) (R 5) [34,192,48,258] 13 := by
  apply FastRouting.sound _ _ [34,192,48,258] 13 (by decide) (choices 2) [5,9,12] r9505 c9505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8402
  · exact u8403
  · exact u8404

def r9506 : Route 9 := (fun mask => (mask,id))

def c9506 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9506 : Upper (D 5) (R 5) [34,192,48,260] 13 := by
  apply FastRouting.sound _ _ [34,192,48,260] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9506 c9506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8405
  · exact u8406
  · exact u8407
  · exact u8408
  · exact u8409
  · exact u8410

def r9507 : Route 9 := (fun mask => (mask,id))

def c9507 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9507 : Upper (D 5) (R 5) [48,65,129,258] 13 := by
  apply FastRouting.sound _ _ [48,65,129,258] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9507 c9507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8411
  · exact u8412
  · exact u8413
  · exact u8414
  · exact u8415
  · exact u8416

theorem m9508_12 : Upper (D 5) (R 5) [48,65,129,288,12] 13 :=
  permutation_upper _ _ _ [48,65,129,288,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8418

def r9508 : Route 9 := (fun mask => (mask,id))

def c9508 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9508 : Upper (D 5) (R 5) [48,65,129,288] 13 := by
  apply FastRouting.sound _ _ [48,65,129,288] 13 (by decide) (choices 2) [6,10,12] r9508 c9508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8417
  · exact u8418
  · exact m9508_12

theorem m9509_9 : Upper (D 5) (R 5) [48,65,130,258,9] 13 :=
  permutation_upper _ _ _ [48,65,130,258,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8419

theorem m9509_40 : Upper (D 5) (R 5) [48,65,130,258,40] 13 :=
  permutation_upper _ _ _ [48,65,130,258,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8422

def r9509 : Route 9 := (fun mask => (mask,id))

def c9509 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9509 : Upper (D 5) (R 5) [48,65,130,258] 13 := by
  apply FastRouting.sound _ _ [48,65,130,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9509 c9509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8419
  · exact m9509_9
  · exact u8420
  · exact u8421
  · exact u8422
  · exact m9509_40

def r9510 : Route 9 := (fun mask => (mask,id))

def c9510 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9510 : Upper (D 5) (R 5) [48,65,130,260] 13 := by
  apply FastRouting.sound _ _ [48,65,130,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9510 c9510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8423
  · exact u8424
  · exact u8425
  · exact u8426
  · exact u8427
  · exact u8428
  · exact u8429
  · exact u8430
  · exact u8431
  · exact u8432

def r9511 : Route 9 := (fun mask => (mask,id))

def c9511 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9511 : Upper (D 5) (R 5) [48,65,130,288] 13 := by
  apply FastRouting.sound _ _ [48,65,130,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9511 c9511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8433
  · exact u8434
  · exact u8435
  · exact u8436
  · exact u8437
  · exact u8438

theorem m9512_9 : Upper (D 5) (R 5) [48,65,136,260,9] 13 :=
  permutation_upper _ _ _ [48,65,136,260,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8440

theorem m9512_10 : Upper (D 5) (R 5) [48,65,136,260,10] 13 :=
  permutation_upper _ _ _ [48,65,136,260,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8441

theorem m9512_40 : Upper (D 5) (R 5) [48,65,136,260,40] 13 :=
  permutation_upper _ _ _ [48,65,136,260,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8445

def r9512 : Route 9 := (fun mask => (mask,id))

def c9512 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9512 : Upper (D 5) (R 5) [48,65,136,260] 13 := by
  apply FastRouting.sound _ _ [48,65,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9512 c9512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8439
  · exact u8440
  · exact u8441
  · exact m9512_9
  · exact m9512_10
  · exact u8442
  · exact u8443
  · exact u8444
  · exact u8445
  · exact m9512_40

def r9513 : Route 9 := (fun mask => (mask,id))

def c9513 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9513 : Upper (D 5) (R 5) [48,65,136,288] 13 := by
  apply FastRouting.sound _ _ [48,65,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9513 c9513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8446
  · exact u8447
  · exact u8448
  · exact u8449
  · exact u8450
  · exact u8451

def r9514 : Route 9 := (fun mask => (mask,id))

def c9514 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9514 : Upper (D 5) (R 5) [48,68,130,258] 13 := by
  apply FastRouting.sound _ _ [48,68,130,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9514 c9514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8452
  · exact u8453
  · exact u8454
  · exact u8455
  · exact u8456
  · exact u8457

theorem m9515_5 : Upper (D 5) (R 5) [48,68,130,288,5] 13 :=
  permutation_upper _ _ _ [48,68,130,288,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8458

theorem m9515_12 : Upper (D 5) (R 5) [48,68,130,288,12] 13 :=
  permutation_upper _ _ _ [48,68,130,288,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8461

def r9515 : Route 9 := (fun mask => (mask,id))

def c9515 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9515 : Upper (D 5) (R 5) [48,68,130,288] 13 := by
  apply FastRouting.sound _ _ [48,68,130,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9515 c9515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8458
  · exact m9515_5
  · exact u8459
  · exact u8460
  · exact u8461
  · exact m9515_12

theorem m9516_5 : Upper (D 5) (R 5) [48,68,136,258,5] 13 :=
  permutation_upper _ _ _ [48,68,136,258,3] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8462

theorem m9516_9 : Upper (D 5) (R 5) [48,68,136,258,9] 13 :=
  permutation_upper _ _ _ [48,68,136,258,3] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8462

theorem m9516_10 : Upper (D 5) (R 5) [48,68,136,258,10] 13 :=
  permutation_upper _ _ _ [48,68,136,258,6] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8463

theorem m9516_12 : Upper (D 5) (R 5) [48,68,136,258,12] 13 :=
  permutation_upper _ _ _ [48,68,136,258,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8463

theorem m9516_36 : Upper (D 5) (R 5) [48,68,136,258,36] 13 :=
  permutation_upper _ _ _ [48,68,136,258,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8465

theorem m9516_40 : Upper (D 5) (R 5) [48,68,136,258,40] 13 :=
  permutation_upper _ _ _ [48,68,136,258,34] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8465

def r9516 : Route 9 := (fun mask => (mask,id))

def c9516 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9516 : Upper (D 5) (R 5) [48,68,136,258] 13 := by
  apply FastRouting.sound _ _ [48,68,136,258] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9516 c9516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8462
  · exact m9516_5
  · exact u8463
  · exact m9516_9
  · exact m9516_10
  · exact m9516_12
  · exact u8464
  · exact u8465
  · exact m9516_36
  · exact m9516_40

def r9517 : Route 9 := (fun mask => (mask,id))

def c9517 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9517 : Upper (D 5) (R 5) [48,68,136,288] 13 := by
  apply FastRouting.sound _ _ [48,68,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9517 c9517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8466
  · exact u8467
  · exact u8468
  · exact u8469
  · exact u8470
  · exact u8471

theorem m9518_9 : Upper (D 5) (R 5) [48,68,160,260,9] 13 :=
  permutation_upper _ _ _ [48,68,160,260,3] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8472

def r9518 : Route 9 := (fun mask => (mask,id))

def c9518 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9518 : Upper (D 5) (R 5) [48,68,160,260] 13 := by
  apply FastRouting.sound _ _ [48,68,160,260] 13 (by decide) (choices 2) [3,9,10] r9518 c9518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8472
  · exact m9518_9
  · exact u8473

def b9519 : PairBound 9 := { available := 506, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 13 506 506 506 506 506 506), lower := (rows 7 7 13 8 16 32 64 128 256), losses := [] }

theorem u9519 : Upper (D 5) (R 5) [6,5,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9520 : PairBound 9 := { available := 490, camps := [{ cop := 4, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 21 490 506 490 490 490 490), lower := (rows 7 7 21 8 16 32 64 128 256), losses := [] }

theorem u9520 : Upper (D 5) (R 5) [6,5,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9521 : PairBound 9 := { available := 491, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 28 491 507 491 491 491 491), lower := (rows 7 7 28 8 16 32 64 128 256), losses := [] }

theorem u9521 : Upper (D 5) (R 5) [6,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9522 : PairBound 9 := { available := 506, camps := [{ cop := 1, region := 504, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 7 37 506 506 506 506 506 506), lower := (rows 7 7 37 8 16 32 64 128 256), losses := [] }

theorem u9522 : Upper (D 5) (R 5) [6,5,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9523 : PairBound 9 := { available := 507, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 44 507 507 507 507 507 507), lower := (rows 7 7 44 8 16 32 64 128 256), losses := [] }

theorem u9523 : Upper (D 5) (R 5) [6,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9524 : PairBound 9 := { available := 491, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 52 491 507 491 491 491 491), lower := (rows 7 7 52 8 16 32 64 128 256), losses := [] }

theorem u9524 : Upper (D 5) (R 5) [6,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9525 : PairBound 9 := { available := 442, camps := [{ cop := 6, region := 7, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 69 442 442 442 506 442 442), lower := (rows 7 7 69 8 16 32 64 128 256), losses := [] }

theorem u9525 : Upper (D 5) (R 5) [6,5,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9526 : PairBound 9 := { available := 443, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 76 443 443 443 507 443 443), lower := (rows 7 7 76 8 16 32 64 128 256), losses := [] }

theorem u9526 : Upper (D 5) (R 5) [6,5,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9527 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 84 427 443 427 491 427 427), lower := (rows 7 7 84 8 16 32 64 128 256), losses := [] }

theorem u9527 : Upper (D 5) (R 5) [6,5,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9528 : PairBound 9 := { available := 443, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 100 443 443 443 507 443 443), lower := (rows 7 7 100 8 16 32 64 128 256), losses := [] }

theorem u9528 : Upper (D 5) (R 5) [6,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9529 : PairBound 9 := { available := 315, camps := [{ cop := 2, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 7 196 315 315 315 379 443 315), lower := (rows 7 7 196 8 16 32 64 128 256), losses := [] }

theorem u9529 : Upper (D 5) (R 5) [6,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9530 : PairBound 9 := { available := 502, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 13 510 502 502 502 502 502), lower := (rows 7 11 13 8 16 32 64 128 256), losses := [] }

theorem u9530 : Upper (D 5) (R 5) [6,9,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9531 : PairBound 9 := { available := 501, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 14 509 501 501 501 501 501), lower := (rows 7 11 14 8 16 32 64 128 256), losses := [] }

theorem u9531 : Upper (D 5) (R 5) [6,9,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9532 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 21 494 510 494 494 494 494), lower := (rows 7 11 21 8 16 32 64 128 256), losses := [] }

theorem u9532 : Upper (D 5) (R 5) [6,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9533 : PairBound 9 := { available := 493, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 22 493 509 493 493 493 493), lower := (rows 7 11 22 8 16 32 64 128 256), losses := [] }

theorem u9533 : Upper (D 5) (R 5) [6,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9534 : PairBound 9 := { available := 487, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 28 495 503 487 487 487 487), lower := (rows 7 11 28 8 16 32 64 128 256), losses := [] }

theorem u9534 : Upper (D 5) (R 5) [6,9,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9535 : PairBound 9 := { available := 510, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 37 510 510 510 510 510 510), lower := (rows 7 11 37 8 16 32 64 128 256), losses := [] }

theorem u9535 : Upper (D 5) (R 5) [6,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9536 : PairBound 9 := { available := 509, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 38 509 509 509 509 509 509), lower := (rows 7 11 38 8 16 32 64 128 256), losses := [] }

theorem u9536 : Upper (D 5) (R 5) [6,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9537 : PairBound 9 := { available := 503, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 44 511 503 503 503 503 503), lower := (rows 7 11 44 8 16 32 64 128 256), losses := [] }

theorem u9537 : Upper (D 5) (R 5) [6,9,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9537
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9538_3 : Upper (D 5) (R 5) [6,9,48,3] 13 :=
  permutation_upper _ _ _ [6,5,9,48] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8474

theorem m9538_5 : Upper (D 5) (R 5) [6,9,48,5] 13 :=
  permutation_upper _ _ _ [6,9,10,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8528

theorem m9538_6 : Upper (D 5) (R 5) [6,9,48,6] 13 :=
  permutation_upper _ _ _ [6,9,9,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8524

theorem m9538_33 : Upper (D 5) (R 5) [6,9,48,33] 13 :=
  permutation_upper _ _ _ [6,9,34,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8553

theorem m9538_34 : Upper (D 5) (R 5) [6,9,48,34] 13 :=
  permutation_upper _ _ _ [6,9,33,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8548

theorem m9538_36 : Upper (D 5) (R 5) [6,9,48,36] 13 :=
  permutation_upper _ _ _ [6,9,40,48] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8558

def r9538 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9538 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9538 : Upper (D 5) (R 5) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9538 c9538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9538_3
  · exact m9538_5
  · exact m9538_6
  · exact m9538_33
  · exact m9538_34
  · exact m9538_36
  · exact u8565
  · exact u8566
  · exact u8567
  · exact u8568
  · exact u8569

def b9539 : PairBound 9 := { available := 446, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 69 446 446 446 510 446 446), lower := (rows 7 11 69 8 16 32 64 128 256), losses := [] }

theorem u9539 : Upper (D 5) (R 5) [6,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9539
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u9539
end Delivery.IrregularNine14.P05
