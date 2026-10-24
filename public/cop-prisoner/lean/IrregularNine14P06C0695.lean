import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0538
import IrregularNine14P06C0539
import IrregularNine14P06C0540
import IrregularNine14P06C0541
import IrregularNine14P06C0542
import IrregularNine14P06C0543

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41700 : Route 9 := (fun mask => (mask,id))

def c41700 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41700 : Upper (D 6) (R 6) [10,96,48,129] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41700 c41700
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32338
  · exact u32339
  · exact u32340
  · exact u32341
  · exact u32342
  · exact u32343
  · exact u32344
  · exact u32345
  · exact u32346
  · exact u32347

def b41701 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 52 138 341 357 325 453 325), lower := (rows 11 98 52 138 16 32 64 128 256), losses := [] }

theorem u41701 : Upper (D 6) (R 6) [10,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41702 : Route 9 := (fun mask => (mask,id))

def c41702 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41702 : Upper (D 6) (R 6) [10,96,48,132] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41702 c41702
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32348
  · exact u32349
  · exact u32350
  · exact u32351
  · exact u32352
  · exact u32353
  · exact u32354
  · exact u32355
  · exact u32356
  · exact u32357

def r41703 : Route 9 := (fun mask => (mask,id))

def c41703 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41703 : Upper (D 6) (R 6) [10,96,48,192] 13 := by
  apply FastRouting.sound _ _ [10,96,48,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41703 c41703
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32358
  · exact u32359
  · exact u32360
  · exact u32361
  · exact u32362
  · exact u32363

def r41704 : Route 9 := (fun mask => (mask,id))

def c41704 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41704 : Upper (D 6) (R 6) [10,96,48,384] 13 := by
  apply FastRouting.sound _ _ [10,96,48,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41704 c41704
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32364
  · exact u32365
  · exact u32366
  · exact u32367
  · exact u32368
  · exact u32369

def b41705 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 11 372 372 372 500 372), lower := (rows 11 98 133 11 16 32 64 128 256), losses := [] }

theorem u41705 : Upper (D 6) (R 6) [10,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41706 : PairBound 9 := { available := 374, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 98 133 13 374 374 374 502 374), lower := (rows 11 98 133 13 16 32 64 128 256), losses := [] }

theorem u41706 : Upper (D 6) (R 6) [10,96,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41707 : PairBound 9 := { available := 373, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 14 373 373 373 501 373), lower := (rows 11 98 133 14 16 32 64 128 256), losses := [] }

theorem u41707 : Upper (D 6) (R 6) [10,96,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41708 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41708 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41708 : Upper (D 6) (R 6) [10,96,129,17] 13 := by
  apply FastRouting.sound _ _ [10,96,129,17] 13 (by decide) (choices 2) [6,34,36,96,258,260,288] r41708 c41708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32370
  · exact u32371
  · exact u32372
  · exact u32373
  · exact u32374
  · exact u32375
  · exact u32376

def b41709 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 26 373 357 357 485 357), lower := (rows 11 98 133 26 16 32 64 128 256), losses := [] }

theorem u41709 : Upper (D 6) (R 6) [10,96,129,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41710 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41710 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41710 : Upper (D 6) (R 6) [10,96,129,20] 13 := by
  apply FastRouting.sound _ _ [10,96,129,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41710 c41710
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32377
  · exact u32378
  · exact u32379
  · exact u32380
  · exact u32381
  · exact u32382
  · exact u32383
  · exact u32384
  · exact u32385
  · exact u32386
  · exact u32387

def b41711 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 133 41 342 374 342 470 342), lower := (rows 11 98 133 41 16 32 64 128 256), losses := [] }

theorem u41711 : Upper (D 6) (R 6) [10,96,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41712 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 133 42 341 373 341 469 341), lower := (rows 11 98 133 42 16 32 64 128 256), losses := [] }

theorem u41712 : Upper (D 6) (R 6) [10,96,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41713 : Route 9 := (fun mask => (mask,id))

def c41713 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41713 : Upper (D 6) (R 6) [10,96,129,36] 13 := by
  apply FastRouting.sound _ _ [10,96,129,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41713 c41713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32388
  · exact u32389
  · exact u32390
  · exact u32391
  · exact u32392
  · exact u32393
  · exact u32394
  · exact u32395
  · exact u32396
  · exact u32397

def r41714 : Route 9 := (fun mask => (mask,id))

def c41714 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41714 : Upper (D 6) (R 6) [10,96,129,48] 13 := by
  apply FastRouting.sound _ _ [10,96,129,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41714 c41714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32398
  · exact u32399
  · exact u32400
  · exact u32401
  · exact u32402
  · exact u32403
  · exact u32404
  · exact u32405
  · exact u32406
  · exact u32407

def b41715 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 133 104 279 311 343 407 279), lower := (rows 11 98 133 104 16 32 64 128 256), losses := [] }

theorem u41715 : Upper (D 6) (R 6) [10,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41716 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41716 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41716 : Upper (D 6) (R 6) [10,96,129,257] 13 := by
  apply FastRouting.sound _ _ [10,96,129,257] 13 (by decide) (choices 2) [6,34,36,96] r41716 c41716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32408
  · exact u32409
  · exact u32410
  · exact u32411

def b41717 : PairBound 9 := { available := 117, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 133 266 117 117 117 245 373), lower := (rows 11 98 133 266 16 32 64 128 256), losses := [] }

theorem u41717 : Upper (D 6) (R 6) [10,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41718 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41718 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41718 : Upper (D 6) (R 6) [10,96,129,260] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41718 c41718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32412
  · exact u32413
  · exact u32414
  · exact u32415
  · exact u32416
  · exact u32417
  · exact u32418

def r41719 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41719 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41719 : Upper (D 6) (R 6) [10,96,129,272] 13 := by
  apply FastRouting.sound _ _ [10,96,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41719 c41719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32419
  · exact u32420
  · exact u32421
  · exact u32422
  · exact u32423
  · exact u32424
  · exact u32425

def r41720 : Route 9 := (fun mask => (mask,id))

def c41720 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41720 : Upper (D 6) (R 6) [10,96,129,288] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41720 c41720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32426
  · exact u32427
  · exact u32428
  · exact u32429
  · exact u32430
  · exact u32431

def b41721 : PairBound 9 := { available := 373, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 134 13 373 373 373 501 373), lower := (rows 11 98 134 13 16 32 64 128 256), losses := [] }

theorem u41721 : Upper (D 6) (R 6) [10,96,130,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41722 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41722 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41722 : Upper (D 6) (R 6) [10,96,130,17] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41722 c41722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32432
  · exact u32433
  · exact u32434
  · exact u32435
  · exact u32436
  · exact u32437
  · exact u32438

def r41723 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41723 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41723 : Upper (D 6) (R 6) [10,96,130,20] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20] 13 (by decide) (choices 2) [5,33,36,96,257,260,288] r41723 c41723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32439
  · exact u32440
  · exact u32441
  · exact u32442
  · exact u32443
  · exact u32444
  · exact u32445

def b41724 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 134 41 341 373 341 469 341), lower := (rows 11 98 134 41 16 32 64 128 256), losses := [] }

theorem u41724 : Upper (D 6) (R 6) [10,96,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41725 : Route 9 := (fun mask => (mask,id))

def c41725 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41725 : Upper (D 6) (R 6) [10,96,130,36] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41725 c41725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32446
  · exact u32447
  · exact u32448
  · exact u32449
  · exact u32450
  · exact u32451

def r41726 : Route 9 := (fun mask => (mask,id))

def c41726 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41726 : Upper (D 6) (R 6) [10,96,130,48] 13 := by
  apply FastRouting.sound _ _ [10,96,130,48] 13 (by decide) (choices 2) [5,65,68,257,260,320] r41726 c41726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32452
  · exact u32453
  · exact u32454
  · exact u32455
  · exact u32456
  · exact u32457

def b41727 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 134 104 277 309 341 405 277), lower := (rows 11 98 134 104 16 32 64 128 256), losses := [] }

theorem u41727 : Upper (D 6) (R 6) [10,96,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41728 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41728 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41728 : Upper (D 6) (R 6) [10,96,130,257] 13 := by
  apply FastRouting.sound _ _ [10,96,130,257] 13 (by decide) (choices 2) [5,33,36,96] r41728 c41728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32458
  · exact u32459
  · exact u32460
  · exact u32461

def r41729 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41729 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41729 : Upper (D 6) (R 6) [10,96,130,260] 13 := by
  apply FastRouting.sound _ _ [10,96,130,260] 13 (by decide) (choices 2) [5,33,36,96] r41729 c41729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32462
  · exact u32463
  · exact u32464
  · exact u32465

def r41730 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41730 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41730 : Upper (D 6) (R 6) [10,96,130,272] 13 := by
  apply FastRouting.sound _ _ [10,96,130,272] 13 (by decide) (choices 2) [5,33,36,96] r41730 c41730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32466
  · exact u32467
  · exact u32468
  · exact u32469

def r41731 : Route 9 := (fun mask => (mask,id))

def c41731 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41731 : Upper (D 6) (R 6) [10,96,130,288] 13 := by
  apply FastRouting.sound _ _ [10,96,130,288] 13 (by decide) (choices 2) [5,65,68] r41731 c41731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32470
  · exact u32471
  · exact u32472

def b41732 : PairBound 9 := { available := 357, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 148 11 373 357 357 485 357), lower := (rows 11 98 148 11 16 32 64 128 256), losses := [] }

theorem u41732 : Upper (D 6) (R 6) [10,96,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41733 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41733 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41733 : Upper (D 6) (R 6) [10,96,144,5] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,257,258,260,288] r41733 c41733
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32473
  · exact u32474
  · exact u32475
  · exact u32476
  · exact u32477
  · exact u32478
  · exact u32479
  · exact u32480
  · exact u32481
  · exact u32482
  · exact u32483

def b41734 : PairBound 9 := { available := 357, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 148 14 373 357 357 485 357), lower := (rows 11 98 148 14 16 32 64 128 256), losses := [] }

theorem u41734 : Upper (D 6) (R 6) [10,96,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41735 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 148 41 343 359 327 455 327), lower := (rows 11 98 148 41 16 32 64 128 256), losses := [] }

theorem u41735 : Upper (D 6) (R 6) [10,96,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41736 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 148 42 341 357 325 453 325), lower := (rows 11 98 148 42 16 32 64 128 256), losses := [] }

theorem u41736 : Upper (D 6) (R 6) [10,96,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41737 : Route 9 := (fun mask => (mask,id))

def c41737 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41737 : Upper (D 6) (R 6) [10,96,144,36] 13 := by
  apply FastRouting.sound _ _ [10,96,144,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41737 c41737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32484
  · exact u32485
  · exact u32486
  · exact u32487
  · exact u32488
  · exact u32489
  · exact u32490
  · exact u32491
  · exact u32492
  · exact u32493

def b41738 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 148 104 279 295 327 391 263), lower := (rows 11 98 148 104 16 32 64 128 256), losses := [] }

theorem u41738 : Upper (D 6) (R 6) [10,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41739 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41739 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41739 : Upper (D 6) (R 6) [10,96,144,257] 13 := by
  apply FastRouting.sound _ _ [10,96,144,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41739 c41739
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32494
  · exact u32495
  · exact u32496
  · exact u32497
  · exact u32498
  · exact u32499
  · exact u32500

def b41740 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 148 266 117 101 101 229 357), lower := (rows 11 98 148 266 16 32 64 128 256), losses := [] }

theorem u41740 : Upper (D 6) (R 6) [10,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41741 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41741 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41741 : Upper (D 6) (R 6) [10,96,144,260] 13 := by
  apply FastRouting.sound _ _ [10,96,144,260] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41741 c41741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32501
  · exact u32502
  · exact u32503
  · exact u32504
  · exact u32505
  · exact u32506
  · exact u32507

def r41742 : Route 9 := (fun mask => (mask,id))

def c41742 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41742 : Upper (D 6) (R 6) [10,96,144,288] 13 := by
  apply FastRouting.sound _ _ [10,96,144,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41742 c41742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32508
  · exact u32509
  · exact u32510
  · exact u32511
  · exact u32512
  · exact u32513

def b41743 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 164 11 341 373 341 469 341), lower := (rows 11 98 164 11 16 32 64 128 256), losses := [] }

theorem u41743 : Upper (D 6) (R 6) [10,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41744 : Route 9 := (fun mask => (mask,id))

def c41744 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41744 : Upper (D 6) (R 6) [10,96,160,5] 13 := by
  apply FastRouting.sound _ _ [10,96,160,5] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41744 c41744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32514
  · exact u32515
  · exact u32516
  · exact u32517
  · exact u32518
  · exact u32519
  · exact u32520
  · exact u32521
  · exact u32522
  · exact u32523

def b41745 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 98 164 14 341 373 341 469 341), lower := (rows 11 98 164 14 16 32 64 128 256), losses := [] }

theorem u41745 : Upper (D 6) (R 6) [10,96,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41746 : Route 9 := (fun mask => (mask,id))

def c41746 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41746 : Upper (D 6) (R 6) [10,96,160,17] 13 := by
  apply FastRouting.sound _ _ [10,96,160,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41746 c41746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32524
  · exact u32525
  · exact u32526
  · exact u32527
  · exact u32528
  · exact u32529
  · exact u32530
  · exact u32531
  · exact u32532
  · exact u32533

def b41747 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 164 26 341 357 325 453 325), lower := (rows 11 98 164 26 16 32 64 128 256), losses := [] }

theorem u41747 : Upper (D 6) (R 6) [10,96,160,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41748 : Route 9 := (fun mask => (mask,id))

def c41748 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41748 : Upper (D 6) (R 6) [10,96,160,20] 13 := by
  apply FastRouting.sound _ _ [10,96,160,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r41748 c41748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32534
  · exact u32535
  · exact u32536
  · exact u32537
  · exact u32538
  · exact u32539
  · exact u32540
  · exact u32541
  · exact u32542
  · exact u32543

def b41749 : PairBound 9 := { available := 279, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 73 279 311 343 407 279), lower := (rows 11 98 164 73 16 32 64 128 256), losses := [] }

theorem u41749 : Upper (D 6) (R 6) [10,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b41750 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 164 74 277 309 341 405 277), lower := (rows 11 98 164 74 16 32 64 128 256), losses := [] }

theorem u41750 : Upper (D 6) (R 6) [10,96,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41751 : Route 9 := (fun mask => (mask,id))

def c41751 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41751 : Upper (D 6) (R 6) [10,96,160,68] 13 := by
  apply FastRouting.sound _ _ [10,96,160,68] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41751 c41751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32544
  · exact u32545
  · exact u32546
  · exact u32547
  · exact u32548
  · exact u32549

def r41752 : Route 9 := (fun mask => (mask,id))

def c41752 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41752 : Upper (D 6) (R 6) [10,96,160,80] 13 := by
  apply FastRouting.sound _ _ [10,96,160,80] 13 (by decide) (choices 2) [3,5,6,257,258,260] r41752 c41752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32550
  · exact u32551
  · exact u32552
  · exact u32553
  · exact u32554
  · exact u32555

def r41753 : Route 9 := (fun mask => (mask,id))

def c41753 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41753 : Upper (D 6) (R 6) [10,96,160,257] 13 := by
  apply FastRouting.sound _ _ [10,96,160,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41753 c41753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32556
  · exact u32557
  · exact u32558
  · exact u32559
  · exact u32560
  · exact u32561

def b41754 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 164 266 85 117 85 213 341), lower := (rows 11 98 164 266 16 32 64 128 256), losses := [] }

theorem u41754 : Upper (D 6) (R 6) [10,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41755 : Route 9 := (fun mask => (mask,id))

def c41755 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41755 : Upper (D 6) (R 6) [10,96,160,260] 13 := by
  apply FastRouting.sound _ _ [10,96,160,260] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41755 c41755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32562
  · exact u32563
  · exact u32564
  · exact u32565
  · exact u32566
  · exact u32567

def r41756 : Route 9 := (fun mask => (mask,id))

def c41756 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41756 : Upper (D 6) (R 6) [10,96,160,272] 13 := by
  apply FastRouting.sound _ _ [10,96,160,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r41756 c41756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32568
  · exact u32569
  · exact u32570
  · exact u32571
  · exact u32572
  · exact u32573

def r41757 : Route 9 := (fun mask => (mask,id))

def c41757 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41757 : Upper (D 6) (R 6) [10,96,160,320] 13 := by
  apply FastRouting.sound _ _ [10,96,160,320] 13 (by decide) (choices 2) [3,5,6] r41757 c41757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32574
  · exact u32575
  · exact u32576

def b41758 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 388 11 117 117 117 245 373), lower := (rows 11 98 388 11 16 32 64 128 256), losses := [] }

theorem u41758 : Upper (D 6) (R 6) [10,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b41758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r41759 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41759 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41759 : Upper (D 6) (R 6) [10,96,384,5] 13 := by
  apply FastRouting.sound _ _ [10,96,384,5] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r41759 c41759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32577
  · exact u32578
  · exact u32579
  · exact u32580
  · exact u32581
  · exact u32582
  · exact u32583

#print axioms u41759
end Delivery.IrregularNine14.P06
