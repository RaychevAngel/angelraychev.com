import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0474
import IrregularNine14P06C0475
import IrregularNine14P06C0476
import IrregularNine14P06C0477
import IrregularNine14P06C0478
import IrregularNine14P06C0479
import IrregularNine14P06C0480

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40800 : PairBound 9 := { available := 341, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 140 42 341 373 341 469 341), lower := (rows 7 35 140 42 16 32 64 128 256), losses := [] }

theorem u40800 : Upper (D 6) (R 6) [6,33,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40801 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 7 35 140 44 339 371 339 467 339), lower := (rows 7 35 140 44 16 32 64 128 256), losses := [] }

theorem u40801 : Upper (D 6) (R 6) [6,33,136,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40801
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40802 : Route 9 := (fun mask => (mask,id))

def c40802 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40802 : Upper (D 6) (R 6) [6,33,136,48] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40802 c40802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28499
  · exact u28500
  · exact u28501
  · exact u28502
  · exact u28503
  · exact u28504
  · exact u28505
  · exact u28506
  · exact u28507
  · exact u28508

def r40803 : Route 9 := (fun mask => (mask,id))

def c40803 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40803 : Upper (D 6) (R 6) [6,33,136,65] 13 := by
  apply FastRouting.sound _ _ [6,33,136,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40803 c40803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28509
  · exact u28510
  · exact u28511
  · exact u28512
  · exact u28513
  · exact u28514
  · exact u28515
  · exact u28516
  · exact u28517
  · exact u28518

def r40804 : Route 9 := (fun mask => (mask,id))

def c40804 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40804 : Upper (D 6) (R 6) [6,33,136,66] 13 := by
  apply FastRouting.sound _ _ [6,33,136,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40804 c40804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28519
  · exact u28520
  · exact u28521
  · exact u28522
  · exact u28523
  · exact u28524
  · exact u28525
  · exact u28526
  · exact u28527
  · exact u28528

def r40805 : Route 9 := (fun mask => (mask,id))

def c40805 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40805 : Upper (D 6) (R 6) [6,33,136,68] 13 := by
  apply FastRouting.sound _ _ [6,33,136,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40805 c40805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28529
  · exact u28530
  · exact u28531
  · exact u28532
  · exact u28533
  · exact u28534
  · exact u28535
  · exact u28536
  · exact u28537
  · exact u28538

def r40806 : Route 9 := (fun mask => (mask,id))

def c40806 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40806 : Upper (D 6) (R 6) [6,33,136,80] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40806 c40806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28539
  · exact u28540
  · exact u28541
  · exact u28542
  · exact u28543
  · exact u28544
  · exact u28545
  · exact u28546
  · exact u28547
  · exact u28548
  · exact u28549
  · exact u28550
  · exact u28551
  · exact u28552
  · exact u28553

def r40807 : Route 9 := (fun mask => (mask,id))

def c40807 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40807 : Upper (D 6) (R 6) [6,33,136,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,96] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40807 c40807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28554
  · exact u28555
  · exact u28556
  · exact u28557
  · exact u28558
  · exact u28559
  · exact u28560
  · exact u28561
  · exact u28562
  · exact u28563

def r40808 : Route 9 := (fun mask => (mask,id))

def c40808 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40808 : Upper (D 6) (R 6) [6,33,136,257] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r40808 c40808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28564
  · exact u28565
  · exact u28566
  · exact u28567
  · exact u28568
  · exact u28569

def r40809 : Route 9 := (fun mask => (mask,id))

def c40809 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40809 : Upper (D 6) (R 6) [6,33,136,258] 13 := by
  apply FastRouting.sound _ _ [6,33,136,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40809 c40809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28570
  · exact u28571
  · exact u28572
  · exact u28573
  · exact u28574
  · exact u28575

def r40810 : Route 9 := (fun mask => (mask,id))

def c40810 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40810 : Upper (D 6) (R 6) [6,33,136,260] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40810 c40810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28576
  · exact u28577
  · exact u28578
  · exact u28579
  · exact u28580
  · exact u28581

def r40811 : Route 9 := (fun mask => (mask,id))

def c40811 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40811 : Upper (D 6) (R 6) [6,33,136,272] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40811 c40811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28582
  · exact u28583
  · exact u28584
  · exact u28585
  · exact u28586
  · exact u28587
  · exact u28588
  · exact u28589
  · exact u28590
  · exact u28591

def r40812 : Route 9 := (fun mask => (mask,id))

def c40812 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40812 : Upper (D 6) (R 6) [6,33,136,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40812 c40812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28592
  · exact u28593
  · exact u28594
  · exact u28595
  · exact u28596
  · exact u28597

def r40813 : Route 9 := (fun mask => (mask,id))

def c40813 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40813 : Upper (D 6) (R 6) [6,33,136,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40813 c40813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28598
  · exact u28599
  · exact u28600
  · exact u28601
  · exact u28602
  · exact u28603
  · exact u28604
  · exact u28605
  · exact u28606
  · exact u28607

def b40814 : PairBound 9 := { available := 380, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 11 380 380 380 508 380), lower := (rows 7 35 196 11 16 32 64 128 256), losses := [] }

theorem u40814 : Upper (D 6) (R 6) [6,33,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40814
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40815 : PairBound 9 := { available := 378, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 196 13 378 378 378 506 378), lower := (rows 7 35 196 13 16 32 64 128 256), losses := [] }

theorem u40815 : Upper (D 6) (R 6) [6,33,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40815
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40816 : PairBound 9 := { available := 377, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 196 14 377 377 377 505 377), lower := (rows 7 35 196 14 16 32 64 128 256), losses := [] }

theorem u40816 : Upper (D 6) (R 6) [6,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40816
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40817_6 : Upper (D 6) (R 6) [6,33,192,17,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28626

def r40817 : Route 9 := (fun mask => (mask,id))

def c40817 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40817 : Upper (D 6) (R 6) [6,33,192,17] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,258,260,264,288,320] r40817 c40817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40817_6
  · exact u28635
  · exact u28636
  · exact u28637
  · exact u28638
  · exact u28639
  · exact u28640
  · exact u28641
  · exact u28642
  · exact u28643
  · exact u28644
  · exact u28645
  · exact u28646
  · exact u28647
  · exact u28648

theorem m40818_5 : Upper (D 6) (R 6) [6,33,192,18,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28617

theorem m40818_9 : Upper (D 6) (R 6) [6,33,192,18,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28635

def r40818 : Route 9 := (fun mask => (mask,id))

def c40818 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40818 : Upper (D 6) (R 6) [6,33,192,18] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r40818 c40818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40818_5
  · exact m40818_9
  · exact u28649
  · exact u28650
  · exact u28651
  · exact u28652
  · exact u28653
  · exact u28654
  · exact u28655
  · exact u28656
  · exact u28657
  · exact u28658
  · exact u28659
  · exact u28660
  · exact u28661

theorem m40819_3 : Upper (D 6) (R 6) [6,33,192,20,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28608

theorem m40819_9 : Upper (D 6) (R 6) [6,33,192,20,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28636

theorem m40819_10 : Upper (D 6) (R 6) [6,33,192,20,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28649

def r40819 : Route 9 := (fun mask => (mask,id))

def c40819 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40819 : Upper (D 6) (R 6) [6,33,192,20] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r40819 c40819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40819_3
  · exact m40819_9
  · exact m40819_10
  · exact u28662
  · exact u28663
  · exact u28664
  · exact u28665
  · exact u28666
  · exact u28667
  · exact u28668
  · exact u28669
  · exact u28670
  · exact u28671
  · exact u28672
  · exact u28673

def b40820 : PairBound 9 := { available := 350, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 196 41 350 382 350 478 350), lower := (rows 7 35 196 41 16 32 64 128 256), losses := [] }

theorem u40820 : Upper (D 6) (R 6) [6,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40820
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40821 : PairBound 9 := { available := 349, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 349 381 349 477 349), lower := (rows 7 35 196 42 16 32 64 128 256), losses := [] }

theorem u40821 : Upper (D 6) (R 6) [6,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40821
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40822_3 : Upper (D 6) (R 6) [6,33,192,36,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28609

theorem m40822_9 : Upper (D 6) (R 6) [6,33,192,36,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28638

theorem m40822_10 : Upper (D 6) (R 6) [6,33,192,36,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28651

def r40822 : Route 9 := (fun mask => (mask,id))

def c40822 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40822 : Upper (D 6) (R 6) [6,33,192,36] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r40822 c40822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40822_3
  · exact m40822_9
  · exact m40822_10
  · exact u28686
  · exact u28687
  · exact u28688
  · exact u28689
  · exact u28690
  · exact u28691
  · exact u28692

theorem m40823_3 : Upper (D 6) (R 6) [6,33,192,48,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28610

theorem m40823_5 : Upper (D 6) (R 6) [6,33,192,48,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28618

theorem m40823_6 : Upper (D 6) (R 6) [6,33,192,48,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28627

theorem m40823_9 : Upper (D 6) (R 6) [6,33,192,48,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28639

theorem m40823_10 : Upper (D 6) (R 6) [6,33,192,48,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28652

theorem m40823_12 : Upper (D 6) (R 6) [6,33,192,48,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28664

def r40823 : Route 9 := (fun mask => (mask,id))

def c40823 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40823 : Upper (D 6) (R 6) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,257,258,260,264,320] r40823 c40823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40823_3
  · exact m40823_5
  · exact m40823_6
  · exact m40823_9
  · exact m40823_10
  · exact m40823_12
  · exact u28693
  · exact u28694
  · exact u28695
  · exact u28696
  · exact u28697
  · exact u28698
  · exact u28699
  · exact u28700
  · exact u28701

theorem m40824_6 : Upper (D 6) (R 6) [6,33,192,65,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28628

theorem m40824_10 : Upper (D 6) (R 6) [6,33,192,65,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28653

theorem m40824_12 : Upper (D 6) (R 6) [6,33,192,65,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28665

theorem m40824_34 : Upper (D 6) (R 6) [6,33,192,65,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28680

theorem m40824_36 : Upper (D 6) (R 6) [6,33,192,65,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28686

theorem m40824_40 : Upper (D 6) (R 6) [6,33,192,65,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28693

def r40824 : Route 9 := (fun mask => (mask,id))

def c40824 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40824 : Upper (D 6) (R 6) [6,33,192,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r40824 c40824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40824_6
  · exact m40824_10
  · exact m40824_12
  · exact m40824_34
  · exact m40824_36
  · exact m40824_40
  · exact u28702
  · exact u28703
  · exact u28704
  · exact u28705

theorem m40825_5 : Upper (D 6) (R 6) [6,33,192,66,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28619

theorem m40825_9 : Upper (D 6) (R 6) [6,33,192,66,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28640

theorem m40825_12 : Upper (D 6) (R 6) [6,33,192,66,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28666

theorem m40825_33 : Upper (D 6) (R 6) [6,33,192,66,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28674

theorem m40825_36 : Upper (D 6) (R 6) [6,33,192,66,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28687

theorem m40825_40 : Upper (D 6) (R 6) [6,33,192,66,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28694

def r40825 : Route 9 := (fun mask => (mask,id))

def c40825 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40825 : Upper (D 6) (R 6) [6,33,192,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r40825 c40825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40825_5
  · exact m40825_9
  · exact m40825_12
  · exact m40825_33
  · exact m40825_36
  · exact m40825_40
  · exact u28706
  · exact u28707
  · exact u28708
  · exact u28709

def b40826 : PairBound 9 := { available := 315, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 76 315 315 379 443 315), lower := (rows 7 35 196 76 16 32 64 128 256), losses := [] }

theorem u40826 : Upper (D 6) (R 6) [6,33,192,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40826
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40827_3 : Upper (D 6) (R 6) [6,33,192,80,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28611

theorem m40827_5 : Upper (D 6) (R 6) [6,33,192,80,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28620

theorem m40827_6 : Upper (D 6) (R 6) [6,33,192,80,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28629

theorem m40827_9 : Upper (D 6) (R 6) [6,33,192,80,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28642

theorem m40827_10 : Upper (D 6) (R 6) [6,33,192,80,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28655

theorem m40827_12 : Upper (D 6) (R 6) [6,33,192,80,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28667

theorem m40827_33 : Upper (D 6) (R 6) [6,33,192,80,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28675

theorem m40827_34 : Upper (D 6) (R 6) [6,33,192,80,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28681

theorem m40827_36 : Upper (D 6) (R 6) [6,33,192,80,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28688

theorem m40827_40 : Upper (D 6) (R 6) [6,33,192,80,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28696

def r40827 : Route 9 := (fun mask => (mask,id))

def c40827 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40827 : Upper (D 6) (R 6) [6,33,192,80] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r40827 c40827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40827_3
  · exact m40827_5
  · exact m40827_6
  · exact m40827_9
  · exact m40827_10
  · exact m40827_12
  · exact m40827_33
  · exact m40827_34
  · exact m40827_36
  · exact m40827_40
  · exact u28714
  · exact u28715
  · exact u28716
  · exact u28717
  · exact u28718

theorem m40828_3 : Upper (D 6) (R 6) [6,33,192,96,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28612

theorem m40828_5 : Upper (D 6) (R 6) [6,33,192,96,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28621

theorem m40828_6 : Upper (D 6) (R 6) [6,33,192,96,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28630

theorem m40828_9 : Upper (D 6) (R 6) [6,33,192,96,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28643

theorem m40828_10 : Upper (D 6) (R 6) [6,33,192,96,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28656

theorem m40828_12 : Upper (D 6) (R 6) [6,33,192,96,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28668

def r40828 : Route 9 := (fun mask => (mask,id))

def c40828 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40828 : Upper (D 6) (R 6) [6,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r40828 c40828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40828_3
  · exact m40828_5
  · exact m40828_6
  · exact m40828_9
  · exact m40828_10
  · exact m40828_12
  · exact u28719
  · exact u28720
  · exact u28721
  · exact u28722

theorem m40829_6 : Upper (D 6) (R 6) [6,33,192,257,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28631

theorem m40829_10 : Upper (D 6) (R 6) [6,33,192,257,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28657

theorem m40829_12 : Upper (D 6) (R 6) [6,33,192,257,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28669

theorem m40829_34 : Upper (D 6) (R 6) [6,33,192,257,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28682

theorem m40829_36 : Upper (D 6) (R 6) [6,33,192,257,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28689

theorem m40829_40 : Upper (D 6) (R 6) [6,33,192,257,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28697

theorem m40829_66 : Upper (D 6) (R 6) [6,33,192,257,66] 13 :=
  permutation_upper _ _ _ [6,33,192,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28706

theorem m40829_68 : Upper (D 6) (R 6) [6,33,192,257,68] 13 :=
  permutation_upper _ _ _ [6,33,192,68,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28710

theorem m40829_72 : Upper (D 6) (R 6) [6,33,192,257,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28714

theorem m40829_96 : Upper (D 6) (R 6) [6,33,192,257,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28719

def r40829 : Route 9 := (fun mask => (mask,id))

def c40829 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40829 : Upper (D 6) (R 6) [6,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40829 c40829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40829_6
  · exact m40829_10
  · exact m40829_12
  · exact m40829_34
  · exact m40829_36
  · exact m40829_40
  · exact m40829_66
  · exact m40829_68
  · exact m40829_72
  · exact m40829_96

theorem m40830_5 : Upper (D 6) (R 6) [6,33,192,258,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28622

theorem m40830_9 : Upper (D 6) (R 6) [6,33,192,258,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28644

theorem m40830_12 : Upper (D 6) (R 6) [6,33,192,258,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28670

theorem m40830_33 : Upper (D 6) (R 6) [6,33,192,258,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28676

theorem m40830_36 : Upper (D 6) (R 6) [6,33,192,258,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28690

theorem m40830_40 : Upper (D 6) (R 6) [6,33,192,258,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28698

theorem m40830_65 : Upper (D 6) (R 6) [6,33,192,258,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28702

theorem m40830_68 : Upper (D 6) (R 6) [6,33,192,258,68] 13 :=
  permutation_upper _ _ _ [6,33,192,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28711

theorem m40830_72 : Upper (D 6) (R 6) [6,33,192,258,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28715

theorem m40830_96 : Upper (D 6) (R 6) [6,33,192,258,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28720

def r40830 : Route 9 := (fun mask => (mask,id))

def c40830 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40830 : Upper (D 6) (R 6) [6,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r40830 c40830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40830_5
  · exact m40830_9
  · exact m40830_12
  · exact m40830_33
  · exact m40830_36
  · exact m40830_40
  · exact m40830_65
  · exact m40830_68
  · exact m40830_72
  · exact m40830_96

theorem m40831_3 : Upper (D 6) (R 6) [6,33,192,260,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28613

theorem m40831_9 : Upper (D 6) (R 6) [6,33,192,260,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28645

theorem m40831_10 : Upper (D 6) (R 6) [6,33,192,260,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28658

theorem m40831_33 : Upper (D 6) (R 6) [6,33,192,260,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28677

theorem m40831_34 : Upper (D 6) (R 6) [6,33,192,260,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28683

theorem m40831_40 : Upper (D 6) (R 6) [6,33,192,260,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28699

theorem m40831_65 : Upper (D 6) (R 6) [6,33,192,260,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28703

theorem m40831_66 : Upper (D 6) (R 6) [6,33,192,260,66] 13 :=
  permutation_upper _ _ _ [6,33,192,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28707

theorem m40831_72 : Upper (D 6) (R 6) [6,33,192,260,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28716

theorem m40831_96 : Upper (D 6) (R 6) [6,33,192,260,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28721

def r40831 : Route 9 := (fun mask => (mask,id))

def c40831 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40831 : Upper (D 6) (R 6) [6,33,192,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r40831 c40831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40831_3
  · exact m40831_9
  · exact m40831_10
  · exact m40831_33
  · exact m40831_34
  · exact m40831_40
  · exact m40831_65
  · exact m40831_66
  · exact m40831_72
  · exact m40831_96

theorem m40832_3 : Upper (D 6) (R 6) [6,33,192,272,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28614

theorem m40832_5 : Upper (D 6) (R 6) [6,33,192,272,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28623

theorem m40832_6 : Upper (D 6) (R 6) [6,33,192,272,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28632

theorem m40832_9 : Upper (D 6) (R 6) [6,33,192,272,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28646

theorem m40832_10 : Upper (D 6) (R 6) [6,33,192,272,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28659

theorem m40832_12 : Upper (D 6) (R 6) [6,33,192,272,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28671

theorem m40832_33 : Upper (D 6) (R 6) [6,33,192,272,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28678

theorem m40832_34 : Upper (D 6) (R 6) [6,33,192,272,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28684

theorem m40832_36 : Upper (D 6) (R 6) [6,33,192,272,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28691

theorem m40832_40 : Upper (D 6) (R 6) [6,33,192,272,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28700

theorem m40832_65 : Upper (D 6) (R 6) [6,33,192,272,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28704

theorem m40832_66 : Upper (D 6) (R 6) [6,33,192,272,66] 13 :=
  permutation_upper _ _ _ [6,33,192,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28708

theorem m40832_68 : Upper (D 6) (R 6) [6,33,192,272,68] 13 :=
  permutation_upper _ _ _ [6,33,192,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28712

theorem m40832_72 : Upper (D 6) (R 6) [6,33,192,272,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28717

theorem m40832_96 : Upper (D 6) (R 6) [6,33,192,272,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28722

def r40832 : Route 9 := (fun mask => (mask,id))

def c40832 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40832 : Upper (D 6) (R 6) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r40832 c40832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40832_3
  · exact m40832_5
  · exact m40832_6
  · exact m40832_9
  · exact m40832_10
  · exact m40832_12
  · exact m40832_33
  · exact m40832_34
  · exact m40832_36
  · exact m40832_40
  · exact m40832_65
  · exact m40832_66
  · exact m40832_68
  · exact m40832_72
  · exact m40832_96

theorem m40833_3 : Upper (D 6) (R 6) [6,33,192,288,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28615

theorem m40833_5 : Upper (D 6) (R 6) [6,33,192,288,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28624

theorem m40833_6 : Upper (D 6) (R 6) [6,33,192,288,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28633

theorem m40833_9 : Upper (D 6) (R 6) [6,33,192,288,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28647

theorem m40833_10 : Upper (D 6) (R 6) [6,33,192,288,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28660

theorem m40833_12 : Upper (D 6) (R 6) [6,33,192,288,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28672

theorem m40833_65 : Upper (D 6) (R 6) [6,33,192,288,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28705

theorem m40833_66 : Upper (D 6) (R 6) [6,33,192,288,66] 13 :=
  permutation_upper _ _ _ [6,33,192,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28709

theorem m40833_68 : Upper (D 6) (R 6) [6,33,192,288,68] 13 :=
  permutation_upper _ _ _ [6,33,192,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28713

theorem m40833_72 : Upper (D 6) (R 6) [6,33,192,288,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28718

def r40833 : Route 9 := (fun mask => (mask,id))

def c40833 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40833 : Upper (D 6) (R 6) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r40833 c40833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40833_3
  · exact m40833_5
  · exact m40833_6
  · exact m40833_9
  · exact m40833_10
  · exact m40833_12
  · exact m40833_65
  · exact m40833_66
  · exact m40833_68
  · exact m40833_72

theorem m40834_3 : Upper (D 6) (R 6) [6,33,192,320,3] 13 :=
  permutation_upper _ _ _ [6,33,192,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28616

theorem m40834_5 : Upper (D 6) (R 6) [6,33,192,320,5] 13 :=
  permutation_upper _ _ _ [6,33,192,5,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28625

theorem m40834_6 : Upper (D 6) (R 6) [6,33,192,320,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28634

theorem m40834_9 : Upper (D 6) (R 6) [6,33,192,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28648

theorem m40834_10 : Upper (D 6) (R 6) [6,33,192,320,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28661

theorem m40834_12 : Upper (D 6) (R 6) [6,33,192,320,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28673

theorem m40834_33 : Upper (D 6) (R 6) [6,33,192,320,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28679

theorem m40834_34 : Upper (D 6) (R 6) [6,33,192,320,34] 13 :=
  permutation_upper _ _ _ [6,33,192,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28685

theorem m40834_36 : Upper (D 6) (R 6) [6,33,192,320,36] 13 :=
  permutation_upper _ _ _ [6,33,192,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28692

theorem m40834_40 : Upper (D 6) (R 6) [6,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28701

def r40834 : Route 9 := (fun mask => (mask,id))

def c40834 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40834 : Upper (D 6) (R 6) [6,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r40834 c40834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40834_3
  · exact m40834_5
  · exact m40834_6
  · exact m40834_9
  · exact m40834_10
  · exact m40834_12
  · exact m40834_33
  · exact m40834_34
  · exact m40834_36
  · exact m40834_40

def b40835 : PairBound 9 := { available := 124, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 388 11 124 124 124 252 380), lower := (rows 7 35 388 11 16 32 64 128 256), losses := [] }

theorem u40835 : Upper (D 6) (R 6) [6,33,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40835
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40836 : PairBound 9 := { available := 122, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 13 122 122 122 250 378), lower := (rows 7 35 388 13 16 32 64 128 256), losses := [] }

theorem u40836 : Upper (D 6) (R 6) [6,33,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40836
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40837 : PairBound 9 := { available := 121, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 388 14 121 121 121 249 377), lower := (rows 7 35 388 14 16 32 64 128 256), losses := [] }

theorem u40837 : Upper (D 6) (R 6) [6,33,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40837
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40838_6 : Upper (D 6) (R 6) [6,33,384,17,6] 13 :=
  permutation_upper _ _ _ [6,33,384,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28734

def r40838 : Route 9 := (fun mask => (mask,id))

def c40838 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40838 : Upper (D 6) (R 6) [6,33,384,17] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40838 c40838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40838_6
  · exact u28739
  · exact u28740
  · exact u28741
  · exact u28742
  · exact u28743
  · exact u28744
  · exact u28745
  · exact u28746
  · exact u28747

theorem m40839_5 : Upper (D 6) (R 6) [6,33,384,18,5] 13 :=
  permutation_upper _ _ _ [6,33,384,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28729

theorem m40839_9 : Upper (D 6) (R 6) [6,33,384,18,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28739

def r40839 : Route 9 := (fun mask => (mask,id))

def c40839 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40839 : Upper (D 6) (R 6) [6,33,384,18] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r40839 c40839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40839_5
  · exact m40839_9
  · exact u28748
  · exact u28749
  · exact u28750
  · exact u28751
  · exact u28752
  · exact u28753
  · exact u28754
  · exact u28755

theorem m40840_3 : Upper (D 6) (R 6) [6,33,384,20,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28723

theorem m40840_9 : Upper (D 6) (R 6) [6,33,384,20,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28740

theorem m40840_10 : Upper (D 6) (R 6) [6,33,384,20,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28748

def r40840 : Route 9 := (fun mask => (mask,id))

def c40840 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40840 : Upper (D 6) (R 6) [6,33,384,20] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r40840 c40840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40840_3
  · exact m40840_9
  · exact m40840_10
  · exact u28756
  · exact u28757
  · exact u28758
  · exact u28759
  · exact u28760
  · exact u28761
  · exact u28762

def b40841 : PairBound 9 := { available := 94, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 388 41 94 126 94 222 350), lower := (rows 7 35 388 41 16 32 64 128 256), losses := [] }

theorem u40841 : Upper (D 6) (R 6) [6,33,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40842 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 388 42 93 125 93 221 349), lower := (rows 7 35 388 42 16 32 64 128 256), losses := [] }

theorem u40842 : Upper (D 6) (R 6) [6,33,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40842
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40843_3 : Upper (D 6) (R 6) [6,33,384,36,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28724

theorem m40843_9 : Upper (D 6) (R 6) [6,33,384,36,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28742

theorem m40843_10 : Upper (D 6) (R 6) [6,33,384,36,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28750

def r40843 : Route 9 := (fun mask => (mask,id))

def c40843 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40843 : Upper (D 6) (R 6) [6,33,384,36] 13 := by
  apply FastRouting.sound _ _ [6,33,384,36] 13 (by decide) (choices 2) [3,9,10,65,66,72] r40843 c40843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40843_3
  · exact m40843_9
  · exact m40843_10
  · exact u28769
  · exact u28770
  · exact u28771

theorem m40844_3 : Upper (D 6) (R 6) [6,33,384,48,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28725

theorem m40844_5 : Upper (D 6) (R 6) [6,33,384,48,5] 13 :=
  permutation_upper _ _ _ [6,33,384,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28730

theorem m40844_6 : Upper (D 6) (R 6) [6,33,384,48,6] 13 :=
  permutation_upper _ _ _ [6,33,384,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28735

theorem m40844_9 : Upper (D 6) (R 6) [6,33,384,48,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28743

theorem m40844_10 : Upper (D 6) (R 6) [6,33,384,48,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28751

theorem m40844_12 : Upper (D 6) (R 6) [6,33,384,48,12] 13 :=
  permutation_upper _ _ _ [6,33,384,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28758

def r40844 : Route 9 := (fun mask => (mask,id))

def c40844 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40844 : Upper (D 6) (R 6) [6,33,384,48] 13 := by
  apply FastRouting.sound _ _ [6,33,384,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r40844 c40844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40844_3
  · exact m40844_5
  · exact m40844_6
  · exact m40844_9
  · exact m40844_10
  · exact m40844_12
  · exact u28772
  · exact u28773
  · exact u28774
  · exact u28775

theorem m40845_6 : Upper (D 6) (R 6) [6,33,384,65,6] 13 :=
  permutation_upper _ _ _ [6,33,384,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28736

theorem m40845_10 : Upper (D 6) (R 6) [6,33,384,65,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28752

theorem m40845_12 : Upper (D 6) (R 6) [6,33,384,65,12] 13 :=
  permutation_upper _ _ _ [6,33,384,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28759

theorem m40845_34 : Upper (D 6) (R 6) [6,33,384,65,34] 13 :=
  permutation_upper _ _ _ [6,33,384,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28766

theorem m40845_36 : Upper (D 6) (R 6) [6,33,384,65,36] 13 :=
  permutation_upper _ _ _ [6,33,384,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28769

theorem m40845_40 : Upper (D 6) (R 6) [6,33,384,65,40] 13 :=
  permutation_upper _ _ _ [6,33,384,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28772

def r40845 : Route 9 := (fun mask => (mask,id))

def c40845 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40845 : Upper (D 6) (R 6) [6,33,384,65] 13 := by
  apply FastRouting.sound _ _ [6,33,384,65] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40845 c40845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40845_6
  · exact m40845_10
  · exact m40845_12
  · exact m40845_34
  · exact m40845_36
  · exact m40845_40
  · exact u28776
  · exact u28777
  · exact u28778
  · exact u28779

theorem m40846_5 : Upper (D 6) (R 6) [6,33,384,66,5] 13 :=
  permutation_upper _ _ _ [6,33,384,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28731

theorem m40846_9 : Upper (D 6) (R 6) [6,33,384,66,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28744

theorem m40846_12 : Upper (D 6) (R 6) [6,33,384,66,12] 13 :=
  permutation_upper _ _ _ [6,33,384,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28760

theorem m40846_33 : Upper (D 6) (R 6) [6,33,384,66,33] 13 :=
  permutation_upper _ _ _ [6,33,384,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28763

theorem m40846_36 : Upper (D 6) (R 6) [6,33,384,66,36] 13 :=
  permutation_upper _ _ _ [6,33,384,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28770

theorem m40846_40 : Upper (D 6) (R 6) [6,33,384,66,40] 13 :=
  permutation_upper _ _ _ [6,33,384,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28773

theorem m40846_65 : Upper (D 6) (R 6) [6,33,384,66,65] 13 :=
  permutation_upper _ _ _ [6,33,384,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28776

def r40846 : Route 9 := (fun mask => (mask,id))

def c40846 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40846 : Upper (D 6) (R 6) [6,33,384,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r40846 c40846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40846_5
  · exact m40846_9
  · exact m40846_12
  · exact m40846_33
  · exact m40846_36
  · exact m40846_40
  · exact m40846_65
  · exact u28780
  · exact u28781
  · exact u28782

theorem m40847_3 : Upper (D 6) (R 6) [6,33,384,68,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28726

theorem m40847_9 : Upper (D 6) (R 6) [6,33,384,68,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28745

theorem m40847_10 : Upper (D 6) (R 6) [6,33,384,68,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28753

theorem m40847_33 : Upper (D 6) (R 6) [6,33,384,68,33] 13 :=
  permutation_upper _ _ _ [6,33,384,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28764

theorem m40847_34 : Upper (D 6) (R 6) [6,33,384,68,34] 13 :=
  permutation_upper _ _ _ [6,33,384,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28767

theorem m40847_40 : Upper (D 6) (R 6) [6,33,384,68,40] 13 :=
  permutation_upper _ _ _ [6,33,384,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28774

theorem m40847_65 : Upper (D 6) (R 6) [6,33,384,68,65] 13 :=
  permutation_upper _ _ _ [6,33,384,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28777

theorem m40847_66 : Upper (D 6) (R 6) [6,33,384,68,66] 13 :=
  permutation_upper _ _ _ [6,33,384,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28780

def r40847 : Route 9 := (fun mask => (mask,id))

def c40847 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40847 : Upper (D 6) (R 6) [6,33,384,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,68] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r40847 c40847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40847_3
  · exact m40847_9
  · exact m40847_10
  · exact m40847_33
  · exact m40847_34
  · exact m40847_40
  · exact m40847_65
  · exact m40847_66
  · exact u28783
  · exact u28784

theorem m40848_3 : Upper (D 6) (R 6) [6,33,384,80,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28727

theorem m40848_5 : Upper (D 6) (R 6) [6,33,384,80,5] 13 :=
  permutation_upper _ _ _ [6,33,384,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28732

theorem m40848_6 : Upper (D 6) (R 6) [6,33,384,80,6] 13 :=
  permutation_upper _ _ _ [6,33,384,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28737

theorem m40848_9 : Upper (D 6) (R 6) [6,33,384,80,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28746

theorem m40848_10 : Upper (D 6) (R 6) [6,33,384,80,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28754

theorem m40848_12 : Upper (D 6) (R 6) [6,33,384,80,12] 13 :=
  permutation_upper _ _ _ [6,33,384,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28761

theorem m40848_33 : Upper (D 6) (R 6) [6,33,384,80,33] 13 :=
  permutation_upper _ _ _ [6,33,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28765

theorem m40848_34 : Upper (D 6) (R 6) [6,33,384,80,34] 13 :=
  permutation_upper _ _ _ [6,33,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28768

theorem m40848_36 : Upper (D 6) (R 6) [6,33,384,80,36] 13 :=
  permutation_upper _ _ _ [6,33,384,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28771

theorem m40848_40 : Upper (D 6) (R 6) [6,33,384,80,40] 13 :=
  permutation_upper _ _ _ [6,33,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28775

theorem m40848_65 : Upper (D 6) (R 6) [6,33,384,80,65] 13 :=
  permutation_upper _ _ _ [6,33,384,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28778

theorem m40848_66 : Upper (D 6) (R 6) [6,33,384,80,66] 13 :=
  permutation_upper _ _ _ [6,33,384,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28781

theorem m40848_68 : Upper (D 6) (R 6) [6,33,384,80,68] 13 :=
  permutation_upper _ _ _ [6,33,384,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28783

def r40848 : Route 9 := (fun mask => (mask,id))

def c40848 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40848 : Upper (D 6) (R 6) [6,33,384,80] 13 := by
  apply FastRouting.sound _ _ [6,33,384,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r40848 c40848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40848_3
  · exact m40848_5
  · exact m40848_6
  · exact m40848_9
  · exact m40848_10
  · exact m40848_12
  · exact m40848_33
  · exact m40848_34
  · exact m40848_36
  · exact m40848_40
  · exact m40848_65
  · exact m40848_66
  · exact m40848_68
  · exact u28785
  · exact u28786

theorem m40849_3 : Upper (D 6) (R 6) [6,33,384,96,3] 13 :=
  permutation_upper _ _ _ [6,33,384,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28728

theorem m40849_5 : Upper (D 6) (R 6) [6,33,384,96,5] 13 :=
  permutation_upper _ _ _ [6,33,384,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28733

theorem m40849_6 : Upper (D 6) (R 6) [6,33,384,96,6] 13 :=
  permutation_upper _ _ _ [6,33,384,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28738

theorem m40849_9 : Upper (D 6) (R 6) [6,33,384,96,9] 13 :=
  permutation_upper _ _ _ [6,33,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28747

theorem m40849_10 : Upper (D 6) (R 6) [6,33,384,96,10] 13 :=
  permutation_upper _ _ _ [6,33,384,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28755

theorem m40849_12 : Upper (D 6) (R 6) [6,33,384,96,12] 13 :=
  permutation_upper _ _ _ [6,33,384,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28762

theorem m40849_65 : Upper (D 6) (R 6) [6,33,384,96,65] 13 :=
  permutation_upper _ _ _ [6,33,384,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28779

theorem m40849_66 : Upper (D 6) (R 6) [6,33,384,96,66] 13 :=
  permutation_upper _ _ _ [6,33,384,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28782

theorem m40849_68 : Upper (D 6) (R 6) [6,33,384,96,68] 13 :=
  permutation_upper _ _ _ [6,33,384,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28784

theorem m40849_72 : Upper (D 6) (R 6) [6,33,384,96,72] 13 :=
  permutation_upper _ _ _ [6,33,384,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28786

def r40849 : Route 9 := (fun mask => (mask,id))

def c40849 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40849 : Upper (D 6) (R 6) [6,33,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r40849 c40849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40849_3
  · exact m40849_5
  · exact m40849_6
  · exact m40849_9
  · exact m40849_10
  · exact m40849_12
  · exact m40849_65
  · exact m40849_66
  · exact m40849_68
  · exact m40849_72

def b40850 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 11 469 485 453 453 453), lower := (rows 7 42 52 11 16 32 64 128 256), losses := [] }

theorem u40850 : Upper (D 6) (R 6) [6,40,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40851 : PairBound 9 := { available := 451, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 13 467 483 451 451 451), lower := (rows 7 42 52 13 16 32 64 128 256), losses := [] }

theorem u40851 : Upper (D 6) (R 6) [6,40,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40851
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40852 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 14 465 481 449 449 449), lower := (rows 7 42 52 14 16 32 64 128 256), losses := [] }

theorem u40852 : Upper (D 6) (R 6) [6,40,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40852
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40853_3 : Upper (D 6) (R 6) [6,40,48,65,3] 13 :=
  permutation_upper _ _ _ [6,40,48,5,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28791

theorem m40853_5 : Upper (D 6) (R 6) [6,40,48,65,5] 13 :=
  permutation_upper _ _ _ [6,40,48,3,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28787

theorem m40853_6 : Upper (D 6) (R 6) [6,40,48,65,6] 13 :=
  permutation_upper _ _ _ [6,40,48,6,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28795

def r40853 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40853 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40853 : Upper (D 6) (R 6) [6,40,48,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r40853 c40853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40853_3
  · exact m40853_5
  · exact m40853_6
  · exact u28799
  · exact u28800
  · exact u28801
  · exact u28802
  · exact u28803
  · exact u28804
  · exact u28805
  · exact u28806

def b40854 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 74 469 485 453 453 453), lower := (rows 7 42 52 74 16 32 64 128 256), losses := [] }

theorem u40854 : Upper (D 6) (R 6) [6,40,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40854
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40855 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 52 76 467 483 451 451 451), lower := (rows 7 42 52 76 16 32 64 128 256), losses := [] }

theorem u40855 : Upper (D 6) (R 6) [6,40,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40855
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40856_3 : Upper (D 6) (R 6) [6,40,48,129,3] 13 :=
  permutation_upper _ _ _ [6,40,48,5,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28792

theorem m40856_5 : Upper (D 6) (R 6) [6,40,48,129,5] 13 :=
  permutation_upper _ _ _ [6,40,48,3,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28788

theorem m40856_6 : Upper (D 6) (R 6) [6,40,48,129,6] 13 :=
  permutation_upper _ _ _ [6,40,48,6,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28796

theorem m40856_65 : Upper (D 6) (R 6) [6,40,48,129,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28802

theorem m40856_66 : Upper (D 6) (R 6) [6,40,48,129,66] 13 :=
  permutation_upper _ _ _ [6,40,48,68,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28810

theorem m40856_68 : Upper (D 6) (R 6) [6,40,48,129,68] 13 :=
  permutation_upper _ _ _ [6,40,48,66,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28807

def r40856 : Route 9 := (fun mask => (mask,id))

def c40856 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40856 : Upper (D 6) (R 6) [6,40,48,129] 13 := by
  apply FastRouting.sound _ _ [6,40,48,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40856 c40856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40856_3
  · exact m40856_5
  · exact m40856_6
  · exact m40856_65
  · exact m40856_66
  · exact m40856_68
  · exact u28813
  · exact u28814
  · exact u28815
  · exact u28816

def b40857 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 52 138 341 357 325 453 325), lower := (rows 7 42 52 138 16 32 64 128 256), losses := [] }

theorem u40857 : Upper (D 6) (R 6) [6,40,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40858 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 52 140 339 355 323 451 323), lower := (rows 7 42 52 140 16 32 64 128 256), losses := [] }

theorem u40858 : Upper (D 6) (R 6) [6,40,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40858
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40859_3 : Upper (D 6) (R 6) [6,40,48,192,3] 13 :=
  permutation_upper _ _ _ [6,40,48,5,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28793

theorem m40859_5 : Upper (D 6) (R 6) [6,40,48,192,5] 13 :=
  permutation_upper _ _ _ [6,40,48,3,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28789

theorem m40859_6 : Upper (D 6) (R 6) [6,40,48,192,6] 13 :=
  permutation_upper _ _ _ [6,40,48,6,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28797

theorem m40859_65 : Upper (D 6) (R 6) [6,40,48,192,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28805

theorem m40859_66 : Upper (D 6) (R 6) [6,40,48,192,66] 13 :=
  permutation_upper _ _ _ [6,40,48,68,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28811

theorem m40859_68 : Upper (D 6) (R 6) [6,40,48,192,68] 13 :=
  permutation_upper _ _ _ [6,40,48,66,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28808

theorem m40859_257 : Upper (D 6) (R 6) [6,40,48,192,257] 13 :=
  permutation_upper _ _ _ [6,40,48,129,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28816

theorem m40859_258 : Upper (D 6) (R 6) [6,40,48,192,258] 13 :=
  permutation_upper _ _ _ [6,40,48,132,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28818

theorem m40859_260 : Upper (D 6) (R 6) [6,40,48,192,260] 13 :=
  permutation_upper _ _ _ [6,40,48,130,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28817

def r40859 : Route 9 := (fun mask => (mask,id))

def c40859 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40859 : Upper (D 6) (R 6) [6,40,48,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40859 c40859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40859_3
  · exact m40859_5
  · exact m40859_6
  · exact m40859_65
  · exact m40859_66
  · exact m40859_68
  · exact m40859_257
  · exact m40859_258
  · exact m40859_260
  · exact u28819

#print axioms u40859
end Delivery.IrregularNine14.P06
