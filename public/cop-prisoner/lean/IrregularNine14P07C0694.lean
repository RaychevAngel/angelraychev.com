import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0540
import IrregularNine14P07C0541
import IrregularNine14P07C0542
import IrregularNine14P07C0543
import IrregularNine14P07C0544
import IrregularNine14P07C0545

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41640 : Route 9 := (fun mask => (mask,id))

def c41640 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41640 : Upper (D 7) (R 7) [12,33,65,130] 13 := by
  apply FastRouting.sound _ _ [12,33,65,130] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41640 c41640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32433
  · exact u32434
  · exact u32435
  · exact u32436
  · exact u32437
  · exact u32438
  · exact u32439
  · exact u32440
  · exact u32441
  · exact u32442

def r41641 : Route 9 := (fun mask => (mask,id))

def c41641 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41641 : Upper (D 7) (R 7) [12,33,65,144] 13 := by
  apply FastRouting.sound _ _ [12,33,65,144] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41641 c41641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32443
  · exact u32444
  · exact u32445
  · exact u32446
  · exact u32447
  · exact u32448
  · exact u32449
  · exact u32450
  · exact u32451
  · exact u32452

def b41642 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 468, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 13 35 69 168 466 498 466 466 466), lower := (rows 13 35 69 168 16 32 64 128 256), losses := [] }

theorem u41642 : Upper (D 7) (R 7) [12,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41643 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 35 69 200 434 434 498 434 434), lower := (rows 13 35 69 200 16 32 64 128 256), losses := [] }

theorem u41643 : Upper (D 7) (R 7) [12,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41644 : Route 9 := (fun mask => (mask,id))

def c41644 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41644 : Upper (D 7) (R 7) [12,33,65,258] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41644 c41644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32453
  · exact u32454
  · exact u32455
  · exact u32456
  · exact u32457
  · exact u32458

def r41645 : Route 9 := (fun mask => (mask,id))

def c41645 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41645 : Upper (D 7) (R 7) [12,33,65,272] 13 := by
  apply FastRouting.sound _ _ [12,33,65,272] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41645 c41645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32459
  · exact u32460
  · exact u32461
  · exact u32462
  · exact u32463
  · exact u32464

def b41646 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(3,0),(4,0),(4,5)], upper := (rows 13 35 69 296 210 242 210 210 466), lower := (rows 13 35 69 296 16 32 64 128 256), losses := [] }

theorem u41646 : Upper (D 7) (R 7) [12,33,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41647 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 35 69 328 178 178 242 178 434), lower := (rows 13 35 69 328 16 32 64 128 256), losses := [] }

theorem u41647 : Upper (D 7) (R 7) [12,33,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41648 : Route 9 := (fun mask => (mask,id))

def c41648 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41648 : Upper (D 7) (R 7) [12,33,65,384] 13 := by
  apply FastRouting.sound _ _ [12,33,65,384] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41648 c41648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32465
  · exact u32466
  · exact u32467
  · exact u32468
  · exact u32469
  · exact u32470

def b41649 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 9, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 35 70 74 433 433 497 433 433), lower := (rows 13 35 70 74 16 32 64 128 256), losses := [] }

theorem u41649 : Upper (D 7) (R 7) [12,33,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41650 : Route 9 := (fun mask => (mask,id))

def c41650 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41650 : Upper (D 7) (R 7) [12,33,66,80] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41650 c41650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32471
  · exact u32472
  · exact u32473
  · exact u32474
  · exact u32475
  · exact u32476
  · exact u32477
  · exact u32478
  · exact u32479
  · exact u32480

def b41651 : PairBound 9 := { available := 403, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 104 403 435 467 403 403), lower := (rows 13 35 70 104 16 32 64 128 256), losses := [] }

theorem u41651 : Upper (D 7) (R 7) [12,33,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41652_129 : Upper (D 7) (R 7) [12,33,66,130,129] 13 :=
  permutation_upper _ _ _ [12,33,66,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32482

theorem m41652_160 : Upper (D 7) (R 7) [12,33,66,130,160] 13 :=
  permutation_upper _ _ _ [12,33,66,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32483

theorem m41652_384 : Upper (D 7) (R 7) [12,33,66,130,384] 13 :=
  permutation_upper _ _ _ [12,33,66,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32487

def r41652 : Route 9 := (fun mask => (mask,id))

def c41652 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41652 : Upper (D 7) (R 7) [12,33,66,130] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41652 c41652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32481
  · exact u32482
  · exact u32483
  · exact m41652_129
  · exact m41652_160
  · exact u32484
  · exact u32485
  · exact u32486
  · exact u32487
  · exact m41652_384

def r41653 : Route 9 := (fun mask => (mask,id))

def c41653 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41653 : Upper (D 7) (R 7) [12,33,66,144] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r41653 c41653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32488
  · exact u32489
  · exact u32490
  · exact u32491
  · exact u32492
  · exact u32493
  · exact u32494
  · exact u32495
  · exact u32496
  · exact u32497
  · exact u32498
  · exact u32499
  · exact u32500
  · exact u32501
  · exact u32502

def r41654 : Route 9 := (fun mask => (mask,id))

def c41654 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41654 : Upper (D 7) (R 7) [12,33,66,160] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41654 c41654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32503
  · exact u32504
  · exact u32505
  · exact u32506
  · exact u32507
  · exact u32508
  · exact u32509
  · exact u32510
  · exact u32511
  · exact u32512

def r41655 : Route 9 := (fun mask => (mask,id))

def c41655 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41655 : Upper (D 7) (R 7) [12,33,66,192] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41655 c41655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32513
  · exact u32514
  · exact u32515
  · exact u32516
  · exact u32517
  · exact u32518
  · exact u32519
  · exact u32520
  · exact u32521
  · exact u32522

def r41656 : Route 9 := (fun mask => (mask,id))

def c41656 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41656 : Upper (D 7) (R 7) [12,33,66,257] 13 := by
  apply FastRouting.sound _ _ [12,33,66,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41656 c41656
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32523
  · exact u32524
  · exact u32525
  · exact u32526
  · exact u32527
  · exact u32528

def r41657 : Route 9 := (fun mask => (mask,id))

def c41657 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41657 : Upper (D 7) (R 7) [12,33,66,258] 13 := by
  apply FastRouting.sound _ _ [12,33,66,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41657 c41657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32529
  · exact u32530
  · exact u32531
  · exact u32532
  · exact u32533
  · exact u32534

def r41658 : Route 9 := (fun mask => (mask,id))

def c41658 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41658 : Upper (D 7) (R 7) [12,33,66,272] 13 := by
  apply FastRouting.sound _ _ [12,33,66,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41658 c41658
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32535
  · exact u32536
  · exact u32537
  · exact u32538
  · exact u32539
  · exact u32540
  · exact u32541
  · exact u32542
  · exact u32543
  · exact u32544

def r41659 : Route 9 := (fun mask => (mask,id))

def c41659 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41659 : Upper (D 7) (R 7) [12,33,66,288] 13 := by
  apply FastRouting.sound _ _ [12,33,66,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41659 c41659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32545
  · exact u32546
  · exact u32547
  · exact u32548
  · exact u32549
  · exact u32550

def r41660 : Route 9 := (fun mask => (mask,id))

def c41660 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41660 : Upper (D 7) (R 7) [12,33,66,320] 13 := by
  apply FastRouting.sound _ _ [12,33,66,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41660 c41660
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32551
  · exact u32552
  · exact u32553
  · exact u32554
  · exact u32555
  · exact u32556

def r41661 : Route 9 := (fun mask => (mask,id))

def c41661 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41661 : Upper (D 7) (R 7) [12,33,66,384] 13 := by
  apply FastRouting.sound _ _ [12,33,66,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41661 c41661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32557
  · exact u32558
  · exact u32559
  · exact u32560
  · exact u32561
  · exact u32562
  · exact u32563
  · exact u32564
  · exact u32565
  · exact u32566

def b41662 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 468, targets := 32 }], pairs := [(1,6),(2,5),(4,5),(4,6)], upper := (rows 13 35 84 104 403 419 451 387 387), lower := (rows 13 35 84 104 16 32 64 128 256), losses := [] }

theorem u41662 : Upper (D 7) (R 7) [12,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41663 : Route 9 := (fun mask => (mask,id))

def c41663 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41663 : Upper (D 7) (R 7) [12,33,80,160] 13 := by
  apply FastRouting.sound _ _ [12,33,80,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41663 c41663
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32567
  · exact u32568
  · exact u32569
  · exact u32570
  · exact u32571
  · exact u32572
  · exact u32573
  · exact u32574
  · exact u32575
  · exact u32576

def r41664 : Route 9 := (fun mask => (mask,id))

def c41664 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41664 : Upper (D 7) (R 7) [12,33,80,192] 13 := by
  apply FastRouting.sound _ _ [12,33,80,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41664 c41664
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32577
  · exact u32578
  · exact u32579
  · exact u32580
  · exact u32581
  · exact u32582
  · exact u32583
  · exact u32584
  · exact u32585
  · exact u32586

def r41665 : Route 9 := (fun mask => (mask,id))

def c41665 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41665 : Upper (D 7) (R 7) [12,33,80,257] 13 := by
  apply FastRouting.sound _ _ [12,33,80,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41665 c41665
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32587
  · exact u32588
  · exact u32589
  · exact u32590
  · exact u32591
  · exact u32592

def r41666 : Route 9 := (fun mask => (mask,id))

def c41666 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41666 : Upper (D 7) (R 7) [12,33,80,258] 13 := by
  apply FastRouting.sound _ _ [12,33,80,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41666 c41666
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32593
  · exact u32594
  · exact u32595
  · exact u32596
  · exact u32597
  · exact u32598
  · exact u32599
  · exact u32600
  · exact u32601
  · exact u32602

def r41667 : Route 9 := (fun mask => (mask,id))

def c41667 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41667 : Upper (D 7) (R 7) [12,33,80,288] 13 := by
  apply FastRouting.sound _ _ [12,33,80,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41667 c41667
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32603
  · exact u32604
  · exact u32605
  · exact u32606
  · exact u32607
  · exact u32608

def r41668 : Route 9 := (fun mask => (mask,id))

def c41668 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41668 : Upper (D 7) (R 7) [12,33,80,320] 13 := by
  apply FastRouting.sound _ _ [12,33,80,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41668 c41668
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32609
  · exact u32610
  · exact u32611
  · exact u32612
  · exact u32613
  · exact u32614

def r41669 : Route 9 := (fun mask => (mask,id))

def c41669 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41669 : Upper (D 7) (R 7) [12,33,80,384] 13 := by
  apply FastRouting.sound _ _ [12,33,80,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41669 c41669
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32615
  · exact u32616
  · exact u32617
  · exact u32618
  · exact u32619
  · exact u32620
  · exact u32621
  · exact u32622
  · exact u32623
  · exact u32624

def b41670 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 100 200 403 435 467 403 403), lower := (rows 13 35 100 200 16 32 64 128 256), losses := [] }

theorem u41670 : Upper (D 7) (R 7) [12,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41671 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 472, targets := 32 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 13 35 100 265 210 242 210 210 466), lower := (rows 13 35 100 265 16 32 64 128 256), losses := [] }

theorem u41671 : Upper (D 7) (R 7) [12,33,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41672 : Route 9 := (fun mask => (mask,id))

def c41672 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41672 : Upper (D 7) (R 7) [12,33,96,258] 13 := by
  apply FastRouting.sound _ _ [12,33,96,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41672 c41672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32625
  · exact u32626
  · exact u32627
  · exact u32628
  · exact u32629
  · exact u32630

def r41673 : Route 9 := (fun mask => (mask,id))

def c41673 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41673 : Upper (D 7) (R 7) [12,33,96,272] 13 := by
  apply FastRouting.sound _ _ [12,33,96,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41673 c41673
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32631
  · exact u32632
  · exact u32633
  · exact u32634
  · exact u32635
  · exact u32636

def b41674 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 100 328 147 179 211 147 403), lower := (rows 13 35 100 328 16 32 64 128 256), losses := [] }

theorem u41674 : Upper (D 7) (R 7) [12,33,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41675 : Route 9 := (fun mask => (mask,id))

def c41675 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41675 : Upper (D 7) (R 7) [12,33,96,384] 13 := by
  apply FastRouting.sound _ _ [12,33,96,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41675 c41675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32637
  · exact u32638
  · exact u32639
  · exact u32640
  · exact u32641
  · exact u32642

def b41676 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 196 200 307 307 371 435 307), lower := (rows 13 35 196 200 16 32 64 128 256), losses := [] }

theorem u41676 : Upper (D 7) (R 7) [12,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41677 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41677 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41677 : Upper (D 7) (R 7) [12,33,192,257] 13 := by
  apply FastRouting.sound _ _ [12,33,192,257] 13 (by decide) (choices 2) [34,66,96,192] r41677 c41677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32643
  · exact u32644
  · exact u32645
  · exact u32646

def r41678 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41678 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41678 : Upper (D 7) (R 7) [12,33,192,258] 13 := by
  apply FastRouting.sound _ _ [12,33,192,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41678 c41678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32647
  · exact u32648
  · exact u32649
  · exact u32650
  · exact u32651
  · exact u32652
  · exact u32653

def r41679 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41679 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41679 : Upper (D 7) (R 7) [12,33,192,272] 13 := by
  apply FastRouting.sound _ _ [12,33,192,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41679 c41679
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32654
  · exact u32655
  · exact u32656
  · exact u32657
  · exact u32658
  · exact u32659
  · exact u32660

def r41680 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41680 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41680 : Upper (D 7) (R 7) [12,33,192,288] 13 := by
  apply FastRouting.sound _ _ [12,33,192,288] 13 (by decide) (choices 2) [3,65,66,192] r41680 c41680
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32661
  · exact u32662
  · exact u32663
  · exact u32664

def r41681 : Route 9 := (fun mask => (mask,id))

def c41681 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41681 : Upper (D 7) (R 7) [12,33,192,320] 13 := by
  apply FastRouting.sound _ _ [12,33,192,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41681 c41681
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32665
  · exact u32666
  · exact u32667
  · exact u32668
  · exact u32669
  · exact u32670

def b41682 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 50 7 11 496 480 480 480 480), lower := (rows 13 50 7 11 16 32 64 128 256), losses := [] }

theorem u41682 : Upper (D 7) (R 7) [12,48,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41683 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 50 7 41 466 482 450 450 450), lower := (rows 13 50 7 41 16 32 64 128 256), losses := [] }

theorem u41683 : Upper (D 7) (R 7) [12,48,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41684 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 50 7 42 465 481 449 449 449), lower := (rows 13 50 7 42 16 32 64 128 256), losses := [] }

theorem u41684 : Upper (D 7) (R 7) [12,48,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41685 : Route 9 := (fun mask => (mask,id))

def c41685 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41685 : Upper (D 7) (R 7) [12,48,3,65] 13 := by
  apply FastRouting.sound _ _ [12,48,3,65] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41685 c41685
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32671
  · exact u32672
  · exact u32673
  · exact u32674
  · exact u32675
  · exact u32676
  · exact u32677
  · exact u32678
  · exact u32679
  · exact u32680

def b41686 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 50 7 74 497 481 481 481 481), lower := (rows 13 50 7 74 16 32 64 128 256), losses := [] }

theorem u41686 : Upper (D 7) (R 7) [12,48,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41687 : Route 9 := (fun mask => (mask,id))

def c41687 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41687 : Upper (D 7) (R 7) [12,48,3,96] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41687 c41687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32681
  · exact u32682
  · exact u32683
  · exact u32684
  · exact u32685
  · exact u32686
  · exact u32687
  · exact u32688
  · exact u32689
  · exact u32690

def r41688 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41688 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41688 : Upper (D 7) (R 7) [12,48,3,192] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r41688 c41688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32691
  · exact u32692
  · exact u32693
  · exact u32694
  · exact u32695
  · exact u32696
  · exact u32697
  · exact u32698
  · exact u32699
  · exact u32700
  · exact u32701

def r41689 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41689 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41689 : Upper (D 7) (R 7) [12,48,3,257] 13 := by
  apply FastRouting.sound _ _ [12,48,3,257] 13 (by decide) (choices 2) [34,66,96,192] r41689 c41689
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32702
  · exact u32703
  · exact u32704
  · exact u32705

def b41690 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 50 7 266 241 225 225 225 481), lower := (rows 13 50 7 266 16 32 64 128 256), losses := [] }

theorem u41690 : Upper (D 7) (R 7) [12,48,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41691 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41691 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41691 : Upper (D 7) (R 7) [12,48,3,288] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288] 13 (by decide) (choices 2) [3,65,66,192] r41691 c41691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32706
  · exact u32707
  · exact u32708
  · exact u32709

def r41692 : Route 9 := (fun mask => (mask,id))

def c41692 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41692 : Upper (D 7) (R 7) [12,48,3,320] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41692 c41692
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32710
  · exact u32711
  · exact u32712
  · exact u32713
  · exact u32714
  · exact u32715
  · exact u32716
  · exact u32717
  · exact u32718
  · exact u32719

def r41693 : Route 9 := (fun mask => (mask,id))

def c41693 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41693 : Upper (D 7) (R 7) [12,48,33,65] 13 := by
  apply FastRouting.sound _ _ [12,48,33,65] 13 (by decide) (choices 2) [66,130,192,258,320,384] r41693 c41693
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32720
  · exact u32721
  · exact u32722
  · exact u32723
  · exact u32724
  · exact u32725

def r41694 : Route 9 := (fun mask => (mask,id))

def c41694 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41694 : Upper (D 7) (R 7) [12,48,33,66] 13 := by
  apply FastRouting.sound _ _ [12,48,33,66] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41694 c41694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32726
  · exact u32727
  · exact u32728
  · exact u32729
  · exact u32730
  · exact u32731
  · exact u32732
  · exact u32733
  · exact u32734
  · exact u32735

def r41695 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41695 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41695 : Upper (D 7) (R 7) [12,48,33,192] 13 := by
  apply FastRouting.sound _ _ [12,48,33,192] 13 (by decide) (choices 2) [3,65,66,192,257,258,320] r41695 c41695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32736
  · exact u32737
  · exact u32738
  · exact u32739
  · exact u32740
  · exact u32741
  · exact u32742

def r41696 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41696 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41696 : Upper (D 7) (R 7) [12,48,33,257] 13 := by
  apply FastRouting.sound _ _ [12,48,33,257] 13 (by decide) (choices 2) [66,192] r41696 c41696
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u32743
  · exact u32744

def r41697 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41697 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41697 : Upper (D 7) (R 7) [12,48,33,258] 13 := by
  apply FastRouting.sound _ _ [12,48,33,258] 13 (by decide) (choices 2) [3,65,66,192] r41697 c41697
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32745
  · exact u32746
  · exact u32747
  · exact u32748

def r41698 : Route 9 := (fun mask => (mask,id))

def c41698 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41698 : Upper (D 7) (R 7) [12,48,33,320] 13 := by
  apply FastRouting.sound _ _ [12,48,33,320] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41698 c41698
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32749
  · exact u32750
  · exact u32751
  · exact u32752
  · exact u32753
  · exact u32754

def b41699 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 73 467 483 451 451 451), lower := (rows 13 50 38 73 16 32 64 128 256), losses := [] }

theorem u41699 : Upper (D 7) (R 7) [12,48,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41699
end Delivery.IrregularNine14.P07
