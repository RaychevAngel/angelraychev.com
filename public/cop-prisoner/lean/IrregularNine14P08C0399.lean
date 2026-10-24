import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0324
import IrregularNine14P08C0325
import IrregularNine14P08C0326
import IrregularNine14P08C0327
import IrregularNine14P08C0328
import IrregularNine14P08C0329
import IrregularNine14P08C0330
import IrregularNine14P08C0331

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23940 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 76 441 433 433 497 433 433), lower := (rows 35 70 76 8 16 32 64 128 256), losses := [] }

theorem u23940 : Upper (D 8) (R 8) [34,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23941 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 100 441 441 441 505 441 441), lower := (rows 35 70 100 8 16 32 64 128 256), losses := [] }

theorem u23941 : Upper (D 8) (R 8) [34,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23942 : Route 9 := (fun mask => (mask,id))

def c23942 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23942 : Upper (D 8) (R 8) [34,68,129] 13 := by
  apply FastRouting.sound _ _ [34,68,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23942 c23942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19460
  · exact u19461
  · exact u19462
  · exact u19463
  · exact u19464
  · exact u19465
  · exact u19466
  · exact u19467
  · exact u19468
  · exact u19469
  · exact u19470
  · exact u19471
  · exact u19472
  · exact u19473
  · exact u19474

def r23943 : Route 9 := (fun mask => (mask,id))

def c23943 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23943 : Upper (D 8) (R 8) [34,68,136] 13 := by
  apply FastRouting.sound _ _ [34,68,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23943 c23943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19475
  · exact u19476
  · exact u19477
  · exact u19478
  · exact u19479
  · exact u19480
  · exact u19481
  · exact u19482
  · exact u19483
  · exact u19484
  · exact u19485
  · exact u19486
  · exact u19487
  · exact u19488
  · exact u19489

def r23944 : Route 9 := (fun mask => (mask,id))

def c23944 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23944 : Upper (D 8) (R 8) [34,68,160] 13 := by
  apply FastRouting.sound _ _ [34,68,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23944 c23944
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19490
  · exact u19491
  · exact u19492
  · exact u19493
  · exact u19494
  · exact u19495
  · exact u19496
  · exact u19497
  · exact u19498
  · exact u19499
  · exact u19500
  · exact u19501
  · exact u19502
  · exact u19503
  · exact u19504

def b23945 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 196 441 441 441 505 441 441), lower := (rows 35 70 196 8 16 32 64 128 256), losses := [] }

theorem u23945 : Upper (D 8) (R 8) [34,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23946 : Route 9 := (fun mask => (mask,id))

def c23946 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23946 : Upper (D 8) (R 8) [34,68,257] 13 := by
  apply FastRouting.sound _ _ [34,68,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23946 c23946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19505
  · exact u19506
  · exact u19507
  · exact u19508
  · exact u19509
  · exact u19510
  · exact u19511
  · exact u19512
  · exact u19513
  · exact u19514

def r23947 : Route 9 := (fun mask => (mask,id))

def c23947 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23947 : Upper (D 8) (R 8) [34,68,264] 13 := by
  apply FastRouting.sound _ _ [34,68,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23947 c23947
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19515
  · exact u19516
  · exact u19517
  · exact u19518
  · exact u19519
  · exact u19520
  · exact u19521
  · exact u19522
  · exact u19523
  · exact u19524

def r23948 : Route 9 := (fun mask => (mask,id))

def c23948 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23948 : Upper (D 8) (R 8) [34,68,288] 13 := by
  apply FastRouting.sound _ _ [34,68,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23948 c23948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19525
  · exact u19526
  · exact u19527
  · exact u19528
  · exact u19529
  · exact u19530
  · exact u19531
  · exact u19532
  · exact u19533
  · exact u19534

def b23949 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 185, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 324 185 185 185 249 185 441), lower := (rows 35 70 324 8 16 32 64 128 256), losses := [] }

theorem u23949 : Upper (D 8) (R 8) [34,68,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23950 : Route 9 := (fun mask => (mask,id))

def c23950 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23950 : Upper (D 8) (R 8) [34,68,384] 13 := by
  apply FastRouting.sound _ _ [34,68,384] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23950 c23950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19535
  · exact u19536
  · exact u19537
  · exact u19538
  · exact u19539
  · exact u19540
  · exact u19541
  · exact u19542
  · exact u19543
  · exact u19544

def r23951 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23951 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u23951 : Upper (D 8) (R 8) [34,192,9] 13 := by
  apply FastRouting.sound _ _ [34,192,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192,257,260,272,288,320] r23951 c23951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19545
  · exact u19546
  · exact u19547
  · exact u19548
  · exact u19549
  · exact u19550
  · exact u19551
  · exact u19552
  · exact u19553
  · exact u19554
  · exact u19555
  · exact u19556
  · exact u19557
  · exact u19558
  · exact u19559
  · exact u19560

theorem m23952_5 : Upper (D 8) (R 8) [34,192,24,5] 13 :=
  permutation_upper _ _ _ [34,192,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19547

def r23952 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23952 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23952 : Upper (D 8) (R 8) [34,192,24] 13 := by
  apply FastRouting.sound _ _ [34,192,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r23952 c23952
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23952_5
  · exact u19568
  · exact u19569
  · exact u19570
  · exact u19571
  · exact u19572
  · exact u19573
  · exact u19574
  · exact u19575
  · exact u19576
  · exact u19577

def b23953 : PairBound 9 := { available := 509, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 37 509 509 509 509 509 509), lower := (rows 35 194 37 8 16 32 64 128 256), losses := [] }

theorem u23953 : Upper (D 8) (R 8) [34,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23954_5 : Upper (D 8) (R 8) [34,192,40,5] 13 :=
  permutation_upper _ _ _ [34,192,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19549

theorem m23954_17 : Upper (D 8) (R 8) [34,192,40,17] 13 :=
  permutation_upper _ _ _ [34,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19561

theorem m23954_20 : Upper (D 8) (R 8) [34,192,40,20] 13 :=
  permutation_upper _ _ _ [34,192,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19569

theorem m23954_33 : Upper (D 8) (R 8) [34,192,40,33] 13 :=
  permutation_upper _ _ _ [34,192,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19578

def r23954 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23954 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u23954 : Upper (D 8) (R 8) [34,192,40] 13 := by
  apply FastRouting.sound _ _ [34,192,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192,257,260,272,288,320] r23954 c23954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23954_5
  · exact m23954_17
  · exact m23954_20
  · exact m23954_33
  · exact u19585
  · exact u19586
  · exact u19587
  · exact u19588
  · exact u19589
  · exact u19590
  · exact u19591
  · exact u19592
  · exact u19593
  · exact u19594
  · exact u19595
  · exact u19596

def b23955 : PairBound 9 := { available := 445, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 69 445 445 445 509 445 445), lower := (rows 35 194 69 8 16 32 64 128 256), losses := [] }

theorem u23955 : Upper (D 8) (R 8) [34,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23956_5 : Upper (D 8) (R 8) [34,192,72,5] 13 :=
  permutation_upper _ _ _ [34,192,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19552

theorem m23956_17 : Upper (D 8) (R 8) [34,192,72,17] 13 :=
  permutation_upper _ _ _ [34,192,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19562

theorem m23956_20 : Upper (D 8) (R 8) [34,192,72,20] 13 :=
  permutation_upper _ _ _ [34,192,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19571

theorem m23956_33 : Upper (D 8) (R 8) [34,192,72,33] 13 :=
  permutation_upper _ _ _ [34,192,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19579

theorem m23956_36 : Upper (D 8) (R 8) [34,192,72,36] 13 :=
  permutation_upper _ _ _ [34,192,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19588

theorem m23956_48 : Upper (D 8) (R 8) [34,192,72,48] 13 :=
  permutation_upper _ _ _ [34,192,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19597

theorem m23956_129 : Upper (D 8) (R 8) [34,192,72,129] 13 :=
  permutation_upper _ _ _ [34,192,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19603

def r23956 : Route 9 := (fun mask => (mask,id))

def c23956 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u23956 : Upper (D 8) (R 8) [34,192,72] 13 := by
  apply FastRouting.sound _ _ [34,192,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r23956 c23956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23956_5
  · exact m23956_17
  · exact m23956_20
  · exact m23956_33
  · exact m23956_36
  · exact m23956_48
  · exact m23956_129
  · exact u19609
  · exact u19610
  · exact u19611
  · exact u19612
  · exact u19613
  · exact u19614
  · exact u19615
  · exact u19616

theorem m23957_5 : Upper (D 8) (R 8) [34,192,96,5] 13 :=
  permutation_upper _ _ _ [34,192,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19554

theorem m23957_17 : Upper (D 8) (R 8) [34,192,96,17] 13 :=
  permutation_upper _ _ _ [34,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19563

theorem m23957_20 : Upper (D 8) (R 8) [34,192,96,20] 13 :=
  permutation_upper _ _ _ [34,192,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19572

theorem m23957_33 : Upper (D 8) (R 8) [34,192,96,33] 13 :=
  permutation_upper _ _ _ [34,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19580

theorem m23957_36 : Upper (D 8) (R 8) [34,192,96,36] 13 :=
  permutation_upper _ _ _ [34,192,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19590

theorem m23957_48 : Upper (D 8) (R 8) [34,192,96,48] 13 :=
  permutation_upper _ _ _ [34,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19598

theorem m23957_129 : Upper (D 8) (R 8) [34,192,96,129] 13 :=
  permutation_upper _ _ _ [34,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19604

theorem m23957_132 : Upper (D 8) (R 8) [34,192,96,132] 13 :=
  permutation_upper _ _ _ [34,192,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19611

theorem m23957_144 : Upper (D 8) (R 8) [34,192,96,144] 13 :=
  permutation_upper _ _ _ [34,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19617

def r23957 : Route 9 := (fun mask => (mask,id))

def c23957 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u23957 : Upper (D 8) (R 8) [34,192,96] 13 := by
  apply FastRouting.sound _ _ [34,192,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r23957 c23957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23957_5
  · exact m23957_17
  · exact m23957_20
  · exact m23957_33
  · exact m23957_36
  · exact m23957_48
  · exact m23957_129
  · exact m23957_132
  · exact m23957_144
  · exact u19622
  · exact u19623
  · exact u19624
  · exact u19625
  · exact u19626
  · exact u19627

def b23958 : PairBound 9 := { available := 317, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 194 196 317 317 317 381 445 317), lower := (rows 35 194 196 8 16 32 64 128 256), losses := [] }

theorem u23958 : Upper (D 8) (R 8) [34,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23959_5 : Upper (D 8) (R 8) [34,192,257,5] 13 :=
  permutation_upper _ _ _ [34,192,9,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19556

theorem m23959_17 : Upper (D 8) (R 8) [34,192,257,17] 13 :=
  permutation_upper _ _ _ [34,192,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19564

theorem m23959_20 : Upper (D 8) (R 8) [34,192,257,20] 13 :=
  permutation_upper _ _ _ [34,192,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19574

theorem m23959_33 : Upper (D 8) (R 8) [34,192,257,33] 13 :=
  permutation_upper _ _ _ [34,192,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19581

theorem m23959_36 : Upper (D 8) (R 8) [34,192,257,36] 13 :=
  permutation_upper _ _ _ [34,192,40,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19592

theorem m23959_48 : Upper (D 8) (R 8) [34,192,257,48] 13 :=
  permutation_upper _ _ _ [34,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19599

theorem m23959_65 : Upper (D 8) (R 8) [34,192,257,65] 13 :=
  permutation_upper _ _ _ [34,192,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19605

theorem m23959_68 : Upper (D 8) (R 8) [34,192,257,68] 13 :=
  permutation_upper _ _ _ [34,192,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19612

theorem m23959_80 : Upper (D 8) (R 8) [34,192,257,80] 13 :=
  permutation_upper _ _ _ [34,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19618

theorem m23959_96 : Upper (D 8) (R 8) [34,192,257,96] 13 :=
  permutation_upper _ _ _ [34,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19623

theorem m23959_192 : Upper (D 8) (R 8) [34,192,257,192] 13 :=
  permutation_upper _ _ _ [34,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19628

def r23959 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23959 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23959 : Upper (D 8) (R 8) [34,192,257] 13 := by
  apply FastRouting.sound _ _ [34,192,257] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r23959 c23959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23959_5
  · exact m23959_17
  · exact m23959_20
  · exact m23959_33
  · exact m23959_36
  · exact m23959_48
  · exact m23959_65
  · exact m23959_68
  · exact m23959_80
  · exact m23959_96
  · exact m23959_192

theorem m23960_5 : Upper (D 8) (R 8) [34,192,264,5] 13 :=
  permutation_upper _ _ _ [34,192,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19557

theorem m23960_17 : Upper (D 8) (R 8) [34,192,264,17] 13 :=
  permutation_upper _ _ _ [34,192,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19565

theorem m23960_20 : Upper (D 8) (R 8) [34,192,264,20] 13 :=
  permutation_upper _ _ _ [34,192,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19575

theorem m23960_33 : Upper (D 8) (R 8) [34,192,264,33] 13 :=
  permutation_upper _ _ _ [34,192,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19582

theorem m23960_36 : Upper (D 8) (R 8) [34,192,264,36] 13 :=
  permutation_upper _ _ _ [34,192,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19593

theorem m23960_48 : Upper (D 8) (R 8) [34,192,264,48] 13 :=
  permutation_upper _ _ _ [34,192,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19600

theorem m23960_65 : Upper (D 8) (R 8) [34,192,264,65] 13 :=
  permutation_upper _ _ _ [34,192,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19606

theorem m23960_68 : Upper (D 8) (R 8) [34,192,264,68] 13 :=
  permutation_upper _ _ _ [34,192,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19613

theorem m23960_80 : Upper (D 8) (R 8) [34,192,264,80] 13 :=
  permutation_upper _ _ _ [34,192,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19619

theorem m23960_96 : Upper (D 8) (R 8) [34,192,264,96] 13 :=
  permutation_upper _ _ _ [34,192,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19624

theorem m23960_192 : Upper (D 8) (R 8) [34,192,264,192] 13 :=
  permutation_upper _ _ _ [34,192,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19629

def r23960 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23960 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23960 : Upper (D 8) (R 8) [34,192,264] 13 := by
  apply FastRouting.sound _ _ [34,192,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r23960 c23960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23960_5
  · exact m23960_17
  · exact m23960_20
  · exact m23960_33
  · exact m23960_36
  · exact m23960_48
  · exact m23960_65
  · exact m23960_68
  · exact m23960_80
  · exact m23960_96
  · exact m23960_192

theorem m23961_5 : Upper (D 8) (R 8) [34,192,288,5] 13 :=
  permutation_upper _ _ _ [34,192,9,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19559

theorem m23961_17 : Upper (D 8) (R 8) [34,192,288,17] 13 :=
  permutation_upper _ _ _ [34,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19566

theorem m23961_20 : Upper (D 8) (R 8) [34,192,288,20] 13 :=
  permutation_upper _ _ _ [34,192,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19576

theorem m23961_33 : Upper (D 8) (R 8) [34,192,288,33] 13 :=
  permutation_upper _ _ _ [34,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19583

theorem m23961_36 : Upper (D 8) (R 8) [34,192,288,36] 13 :=
  permutation_upper _ _ _ [34,192,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19595

theorem m23961_48 : Upper (D 8) (R 8) [34,192,288,48] 13 :=
  permutation_upper _ _ _ [34,192,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19601

theorem m23961_65 : Upper (D 8) (R 8) [34,192,288,65] 13 :=
  permutation_upper _ _ _ [34,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19607

theorem m23961_68 : Upper (D 8) (R 8) [34,192,288,68] 13 :=
  permutation_upper _ _ _ [34,192,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19615

theorem m23961_80 : Upper (D 8) (R 8) [34,192,288,80] 13 :=
  permutation_upper _ _ _ [34,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19620

theorem m23961_96 : Upper (D 8) (R 8) [34,192,288,96] 13 :=
  permutation_upper _ _ _ [34,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19626

theorem m23961_192 : Upper (D 8) (R 8) [34,192,288,192] 13 :=
  permutation_upper _ _ _ [34,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19630

def r23961 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23961 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23961 : Upper (D 8) (R 8) [34,192,288] 13 := by
  apply FastRouting.sound _ _ [34,192,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r23961 c23961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23961_5
  · exact m23961_17
  · exact m23961_20
  · exact m23961_33
  · exact m23961_36
  · exact m23961_48
  · exact m23961_65
  · exact m23961_68
  · exact m23961_80
  · exact m23961_96
  · exact m23961_192

theorem m23962_5 : Upper (D 8) (R 8) [34,192,320,5] 13 :=
  permutation_upper _ _ _ [34,192,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19560

theorem m23962_17 : Upper (D 8) (R 8) [34,192,320,17] 13 :=
  permutation_upper _ _ _ [34,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19567

theorem m23962_20 : Upper (D 8) (R 8) [34,192,320,20] 13 :=
  permutation_upper _ _ _ [34,192,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19577

theorem m23962_33 : Upper (D 8) (R 8) [34,192,320,33] 13 :=
  permutation_upper _ _ _ [34,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19584

theorem m23962_36 : Upper (D 8) (R 8) [34,192,320,36] 13 :=
  permutation_upper _ _ _ [34,192,40,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19596

theorem m23962_48 : Upper (D 8) (R 8) [34,192,320,48] 13 :=
  permutation_upper _ _ _ [34,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19602

theorem m23962_129 : Upper (D 8) (R 8) [34,192,320,129] 13 :=
  permutation_upper _ _ _ [34,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19608

theorem m23962_132 : Upper (D 8) (R 8) [34,192,320,132] 13 :=
  permutation_upper _ _ _ [34,192,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19616

theorem m23962_144 : Upper (D 8) (R 8) [34,192,320,144] 13 :=
  permutation_upper _ _ _ [34,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19621

theorem m23962_160 : Upper (D 8) (R 8) [34,192,320,160] 13 :=
  permutation_upper _ _ _ [34,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19627

def r23962 : Route 9 := (fun mask => (mask,id))

def c23962 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23962 : Upper (D 8) (R 8) [34,192,320] 13 := by
  apply FastRouting.sound _ _ [34,192,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r23962 c23962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23962_5
  · exact m23962_17
  · exact m23962_20
  · exact m23962_33
  · exact m23962_36
  · exact m23962_48
  · exact m23962_129
  · exact m23962_132
  · exact m23962_144
  · exact m23962_160

def b23963 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 13 252 244 244 244 244 500), lower := (rows 35 259 13 8 16 32 64 128 256), losses := [] }

theorem u23963 : Upper (D 8) (R 8) [34,257,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23964_5 : Upper (D 8) (R 8) [34,257,24,5] 13 :=
  permutation_upper _ _ _ [34,257,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19631

def r23964 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23964 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23964 : Upper (D 8) (R 8) [34,257,24] 13 := by
  apply FastRouting.sound _ _ [34,257,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r23964 c23964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23964_5
  · exact u19640
  · exact u19641
  · exact u19642
  · exact u19643
  · exact u19644
  · exact u19645

def b23965 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 259 37 252 252 252 252 252 508), lower := (rows 35 259 37 8 16 32 64 128 256), losses := [] }

theorem u23965 : Upper (D 8) (R 8) [34,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23966_5 : Upper (D 8) (R 8) [34,257,40,5] 13 :=
  permutation_upper _ _ _ [34,257,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19632

theorem m23966_17 : Upper (D 8) (R 8) [34,257,40,17] 13 :=
  permutation_upper _ _ _ [34,257,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19636

theorem m23966_20 : Upper (D 8) (R 8) [34,257,40,20] 13 :=
  permutation_upper _ _ _ [34,257,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19641

theorem m23966_33 : Upper (D 8) (R 8) [34,257,40,33] 13 :=
  permutation_upper _ _ _ [34,257,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19646

def r23966 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23966 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23966 : Upper (D 8) (R 8) [34,257,40] 13 := by
  apply FastRouting.sound _ _ [34,257,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r23966 c23966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23966_5
  · exact m23966_17
  · exact m23966_20
  · exact m23966_33
  · exact u19650
  · exact u19651
  · exact u19652
  · exact u19653
  · exact u19654
  · exact u19655
  · exact u19656

def b23967 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 259 69 252 252 252 252 252 508), lower := (rows 35 259 69 8 16 32 64 128 256), losses := [] }

theorem u23967 : Upper (D 8) (R 8) [34,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23968_5 : Upper (D 8) (R 8) [34,257,72,5] 13 :=
  permutation_upper _ _ _ [34,257,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19633

theorem m23968_17 : Upper (D 8) (R 8) [34,257,72,17] 13 :=
  permutation_upper _ _ _ [34,257,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19637

theorem m23968_20 : Upper (D 8) (R 8) [34,257,72,20] 13 :=
  permutation_upper _ _ _ [34,257,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19643

theorem m23968_33 : Upper (D 8) (R 8) [34,257,72,33] 13 :=
  permutation_upper _ _ _ [34,257,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19647

theorem m23968_36 : Upper (D 8) (R 8) [34,257,72,36] 13 :=
  permutation_upper _ _ _ [34,257,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19653

theorem m23968_48 : Upper (D 8) (R 8) [34,257,72,48] 13 :=
  permutation_upper _ _ _ [34,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19657

theorem m23968_65 : Upper (D 8) (R 8) [34,257,72,65] 13 :=
  permutation_upper _ _ _ [34,257,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19660

theorem m23968_129 : Upper (D 8) (R 8) [34,257,72,129] 13 :=
  permutation_upper _ _ _ [34,257,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19662

def r23968 : Route 9 := (fun mask => (mask,id))

def c23968 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23968 : Upper (D 8) (R 8) [34,257,72] 13 := by
  apply FastRouting.sound _ _ [34,257,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23968 c23968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23968_5
  · exact m23968_17
  · exact m23968_20
  · exact m23968_33
  · exact m23968_36
  · exact m23968_48
  · exact m23968_65
  · exact u19665
  · exact u19666
  · exact u19667
  · exact m23968_129
  · exact u19668
  · exact u19669
  · exact u19670
  · exact u19671

theorem m23969_5 : Upper (D 8) (R 8) [34,257,96,5] 13 :=
  permutation_upper _ _ _ [34,257,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19634

theorem m23969_17 : Upper (D 8) (R 8) [34,257,96,17] 13 :=
  permutation_upper _ _ _ [34,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19638

theorem m23969_20 : Upper (D 8) (R 8) [34,257,96,20] 13 :=
  permutation_upper _ _ _ [34,257,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19644

theorem m23969_33 : Upper (D 8) (R 8) [34,257,96,33] 13 :=
  permutation_upper _ _ _ [34,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19648

theorem m23969_36 : Upper (D 8) (R 8) [34,257,96,36] 13 :=
  permutation_upper _ _ _ [34,257,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19655

theorem m23969_48 : Upper (D 8) (R 8) [34,257,96,48] 13 :=
  permutation_upper _ _ _ [34,257,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19658

theorem m23969_65 : Upper (D 8) (R 8) [34,257,96,65] 13 :=
  permutation_upper _ _ _ [34,257,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19661

theorem m23969_68 : Upper (D 8) (R 8) [34,257,96,68] 13 :=
  permutation_upper _ _ _ [34,257,72,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19667

theorem m23969_80 : Upper (D 8) (R 8) [34,257,96,80] 13 :=
  permutation_upper _ _ _ [34,257,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19672

theorem m23969_129 : Upper (D 8) (R 8) [34,257,96,129] 13 :=
  permutation_upper _ _ _ [34,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19663

theorem m23969_132 : Upper (D 8) (R 8) [34,257,96,132] 13 :=
  permutation_upper _ _ _ [34,257,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19670

theorem m23969_144 : Upper (D 8) (R 8) [34,257,96,144] 13 :=
  permutation_upper _ _ _ [34,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19673

def r23969 : Route 9 := (fun mask => (mask,id))

def c23969 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23969 : Upper (D 8) (R 8) [34,257,96] 13 := by
  apply FastRouting.sound _ _ [34,257,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23969 c23969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23969_5
  · exact m23969_17
  · exact m23969_20
  · exact m23969_33
  · exact m23969_36
  · exact m23969_48
  · exact m23969_65
  · exact m23969_68
  · exact m23969_80
  · exact u19675
  · exact m23969_129
  · exact m23969_132
  · exact m23969_144
  · exact u19676
  · exact u19677

theorem m23970_5 : Upper (D 8) (R 8) [34,257,192,5] 13 :=
  permutation_upper _ _ _ [34,257,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19635

theorem m23970_17 : Upper (D 8) (R 8) [34,257,192,17] 13 :=
  permutation_upper _ _ _ [34,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19639

theorem m23970_20 : Upper (D 8) (R 8) [34,257,192,20] 13 :=
  permutation_upper _ _ _ [34,257,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19645

theorem m23970_33 : Upper (D 8) (R 8) [34,257,192,33] 13 :=
  permutation_upper _ _ _ [34,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19649

theorem m23970_36 : Upper (D 8) (R 8) [34,257,192,36] 13 :=
  permutation_upper _ _ _ [34,257,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19656

theorem m23970_48 : Upper (D 8) (R 8) [34,257,192,48] 13 :=
  permutation_upper _ _ _ [34,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19659

theorem m23970_65 : Upper (D 8) (R 8) [34,257,192,65] 13 :=
  permutation_upper _ _ _ [34,257,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19664

theorem m23970_68 : Upper (D 8) (R 8) [34,257,192,68] 13 :=
  permutation_upper _ _ _ [34,257,72,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19671

theorem m23970_80 : Upper (D 8) (R 8) [34,257,192,80] 13 :=
  permutation_upper _ _ _ [34,257,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19674

theorem m23970_96 : Upper (D 8) (R 8) [34,257,192,96] 13 :=
  permutation_upper _ _ _ [34,257,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19677

def r23970 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23970 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23970 : Upper (D 8) (R 8) [34,257,192] 13 := by
  apply FastRouting.sound _ _ [34,257,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r23970 c23970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23970_5
  · exact m23970_17
  · exact m23970_20
  · exact m23970_33
  · exact m23970_36
  · exact m23970_48
  · exact m23970_65
  · exact m23970_68
  · exact m23970_80
  · exact m23970_96
  · exact u19678

def r23971 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23971 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23971 : Upper (D 8) (R 8) [34,260,9] 13 := by
  apply FastRouting.sound _ _ [34,260,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23971 c23971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19679
  · exact u19680
  · exact u19681
  · exact u19682
  · exact u19683
  · exact u19684
  · exact u19685

def r23972 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23972 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23972 : Upper (D 8) (R 8) [34,260,24] 13 := by
  apply FastRouting.sound _ _ [34,260,24] 13 (by decide) (choices 2) [33,65,96,192] r23972 c23972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19686
  · exact u19687
  · exact u19688
  · exact u19689

def b23973 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 262 37 249 249 249 249 249 505), lower := (rows 35 262 37 8 16 32 64 128 256), losses := [] }

theorem u23973 : Upper (D 8) (R 8) [34,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23974 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23974 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23974 : Upper (D 8) (R 8) [34,260,40] 13 := by
  apply FastRouting.sound _ _ [34,260,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23974 c23974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19690
  · exact u19691
  · exact u19692
  · exact u19693
  · exact u19694
  · exact u19695
  · exact u19696

def r23975 : Route 9 := (fun mask => (mask,id))

def c23975 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23975 : Upper (D 8) (R 8) [34,260,65] 13 := by
  apply FastRouting.sound _ _ [34,260,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23975 c23975
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19697
  · exact u19698
  · exact u19699
  · exact u19700
  · exact u19701
  · exact u19702
  · exact u19703
  · exact u19704
  · exact u19705
  · exact u19706

def r23976 : Route 9 := (fun mask => (mask,id))

def c23976 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23976 : Upper (D 8) (R 8) [34,260,72] 13 := by
  apply FastRouting.sound _ _ [34,260,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23976 c23976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19707
  · exact u19708
  · exact u19709
  · exact u19710
  · exact u19711
  · exact u19712
  · exact u19713
  · exact u19714
  · exact u19715
  · exact u19716

def r23977 : Route 9 := (fun mask => (mask,id))

def c23977 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23977 : Upper (D 8) (R 8) [34,260,96] 13 := by
  apply FastRouting.sound _ _ [34,260,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r23977 c23977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19717
  · exact u19718
  · exact u19719
  · exact u19720
  · exact u19721
  · exact u19722
  · exact u19723
  · exact u19724
  · exact u19725
  · exact u19726

def r23978 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23978 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23978 : Upper (D 8) (R 8) [34,260,192] 13 := by
  apply FastRouting.sound _ _ [34,260,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r23978 c23978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19727
  · exact u19728
  · exact u19729
  · exact u19730
  · exact u19731
  · exact u19732
  · exact u19733

def r23979 : Route 9 := (fun mask => (mask,id))

def c23979 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23979 : Upper (D 8) (R 8) [34,320,9] 13 := by
  apply FastRouting.sound _ _ [34,320,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23979 c23979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19734
  · exact u19735
  · exact u19736
  · exact u19737
  · exact u19738
  · exact u19739
  · exact u19740
  · exact u19741
  · exact u19742
  · exact u19743
  · exact u19744
  · exact u19745
  · exact u19746
  · exact u19747
  · exact u19748

theorem m23980_5 : Upper (D 8) (R 8) [34,320,24,5] 13 :=
  permutation_upper _ _ _ [34,320,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19736

def r23980 : Route 9 := (fun mask => (mask,id))

def c23980 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23980 : Upper (D 8) (R 8) [34,320,24] 13 := by
  apply FastRouting.sound _ _ [34,320,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r23980 c23980
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23980_5
  · exact u19756
  · exact u19757
  · exact u19758
  · exact u19759
  · exact u19760
  · exact u19761
  · exact u19762
  · exact u19763
  · exact u19764

def b23981 : PairBound 9 := { available := 253, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 37 253 253 253 253 253 509), lower := (rows 35 322 37 8 16 32 64 128 256), losses := [] }

theorem u23981 : Upper (D 8) (R 8) [34,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23982_5 : Upper (D 8) (R 8) [34,320,40,5] 13 :=
  permutation_upper _ _ _ [34,320,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19738

theorem m23982_17 : Upper (D 8) (R 8) [34,320,40,17] 13 :=
  permutation_upper _ _ _ [34,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19749

theorem m23982_20 : Upper (D 8) (R 8) [34,320,40,20] 13 :=
  permutation_upper _ _ _ [34,320,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19757

theorem m23982_33 : Upper (D 8) (R 8) [34,320,40,33] 13 :=
  permutation_upper _ _ _ [34,320,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19765

def r23982 : Route 9 := (fun mask => (mask,id))

def c23982 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23982 : Upper (D 8) (R 8) [34,320,40] 13 := by
  apply FastRouting.sound _ _ [34,320,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23982 c23982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23982_5
  · exact m23982_17
  · exact m23982_20
  · exact m23982_33
  · exact u19772
  · exact u19773
  · exact u19774
  · exact u19775
  · exact u19776
  · exact u19777
  · exact u19778
  · exact u19779
  · exact u19780
  · exact u19781
  · exact u19782

def b23983 : PairBound 9 := { available := 189, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 69 189 189 189 253 189 445), lower := (rows 35 322 69 8 16 32 64 128 256), losses := [] }

theorem u23983 : Upper (D 8) (R 8) [34,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23983 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23984_5 : Upper (D 8) (R 8) [34,320,72,5] 13 :=
  permutation_upper _ _ _ [34,320,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19741

theorem m23984_17 : Upper (D 8) (R 8) [34,320,72,17] 13 :=
  permutation_upper _ _ _ [34,320,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19750

theorem m23984_20 : Upper (D 8) (R 8) [34,320,72,20] 13 :=
  permutation_upper _ _ _ [34,320,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19759

theorem m23984_33 : Upper (D 8) (R 8) [34,320,72,33] 13 :=
  permutation_upper _ _ _ [34,320,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19766

theorem m23984_36 : Upper (D 8) (R 8) [34,320,72,36] 13 :=
  permutation_upper _ _ _ [34,320,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19775

theorem m23984_48 : Upper (D 8) (R 8) [34,320,72,48] 13 :=
  permutation_upper _ _ _ [34,320,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19783

def r23984 : Route 9 := (fun mask => (mask,id))

def c23984 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23984 : Upper (D 8) (R 8) [34,320,72] 13 := by
  apply FastRouting.sound _ _ [34,320,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r23984 c23984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23984_5
  · exact m23984_17
  · exact m23984_20
  · exact m23984_33
  · exact m23984_36
  · exact m23984_48
  · exact u19792
  · exact u19793
  · exact u19794
  · exact u19795

theorem m23985_5 : Upper (D 8) (R 8) [34,320,96,5] 13 :=
  permutation_upper _ _ _ [34,320,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19743

theorem m23985_17 : Upper (D 8) (R 8) [34,320,96,17] 13 :=
  permutation_upper _ _ _ [34,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19751

theorem m23985_20 : Upper (D 8) (R 8) [34,320,96,20] 13 :=
  permutation_upper _ _ _ [34,320,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19760

theorem m23985_33 : Upper (D 8) (R 8) [34,320,96,33] 13 :=
  permutation_upper _ _ _ [34,320,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19767

theorem m23985_36 : Upper (D 8) (R 8) [34,320,96,36] 13 :=
  permutation_upper _ _ _ [34,320,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19777

theorem m23985_48 : Upper (D 8) (R 8) [34,320,96,48] 13 :=
  permutation_upper _ _ _ [34,320,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19784

def r23985 : Route 9 := (fun mask => (mask,id))

def c23985 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23985 : Upper (D 8) (R 8) [34,320,96] 13 := by
  apply FastRouting.sound _ _ [34,320,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r23985 c23985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23985_5
  · exact m23985_17
  · exact m23985_20
  · exact m23985_33
  · exact m23985_36
  · exact m23985_48
  · exact u19799
  · exact u19800
  · exact u19801
  · exact u19802

theorem m23986_5 : Upper (D 8) (R 8) [34,320,129,5] 13 :=
  permutation_upper _ _ _ [34,320,9,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19744

theorem m23986_17 : Upper (D 8) (R 8) [34,320,129,17] 13 :=
  permutation_upper _ _ _ [34,320,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19752

theorem m23986_20 : Upper (D 8) (R 8) [34,320,129,20] 13 :=
  permutation_upper _ _ _ [34,320,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19761

theorem m23986_33 : Upper (D 8) (R 8) [34,320,129,33] 13 :=
  permutation_upper _ _ _ [34,320,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19768

theorem m23986_36 : Upper (D 8) (R 8) [34,320,129,36] 13 :=
  permutation_upper _ _ _ [34,320,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19778

theorem m23986_48 : Upper (D 8) (R 8) [34,320,129,48] 13 :=
  permutation_upper _ _ _ [34,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19785

theorem m23986_65 : Upper (D 8) (R 8) [34,320,129,65] 13 :=
  permutation_upper _ _ _ [34,320,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19789

theorem m23986_68 : Upper (D 8) (R 8) [34,320,129,68] 13 :=
  permutation_upper _ _ _ [34,320,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19792

theorem m23986_80 : Upper (D 8) (R 8) [34,320,129,80] 13 :=
  permutation_upper _ _ _ [34,320,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19796

theorem m23986_96 : Upper (D 8) (R 8) [34,320,129,96] 13 :=
  permutation_upper _ _ _ [34,320,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19799

def r23986 : Route 9 := (fun mask => (mask,id))

def c23986 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23986 : Upper (D 8) (R 8) [34,320,129] 13 := by
  apply FastRouting.sound _ _ [34,320,129] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23986 c23986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23986_5
  · exact m23986_17
  · exact m23986_20
  · exact m23986_33
  · exact m23986_36
  · exact m23986_48
  · exact m23986_65
  · exact m23986_68
  · exact m23986_80
  · exact m23986_96
  · exact u19803
  · exact u19804
  · exact u19805
  · exact u19806
  · exact u19807

theorem m23987_5 : Upper (D 8) (R 8) [34,320,136,5] 13 :=
  permutation_upper _ _ _ [34,320,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19745

theorem m23987_17 : Upper (D 8) (R 8) [34,320,136,17] 13 :=
  permutation_upper _ _ _ [34,320,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19753

theorem m23987_20 : Upper (D 8) (R 8) [34,320,136,20] 13 :=
  permutation_upper _ _ _ [34,320,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19762

theorem m23987_33 : Upper (D 8) (R 8) [34,320,136,33] 13 :=
  permutation_upper _ _ _ [34,320,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19769

theorem m23987_36 : Upper (D 8) (R 8) [34,320,136,36] 13 :=
  permutation_upper _ _ _ [34,320,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19779

theorem m23987_48 : Upper (D 8) (R 8) [34,320,136,48] 13 :=
  permutation_upper _ _ _ [34,320,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19786

theorem m23987_65 : Upper (D 8) (R 8) [34,320,136,65] 13 :=
  permutation_upper _ _ _ [34,320,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19790

theorem m23987_68 : Upper (D 8) (R 8) [34,320,136,68] 13 :=
  permutation_upper _ _ _ [34,320,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19793

theorem m23987_80 : Upper (D 8) (R 8) [34,320,136,80] 13 :=
  permutation_upper _ _ _ [34,320,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19797

theorem m23987_96 : Upper (D 8) (R 8) [34,320,136,96] 13 :=
  permutation_upper _ _ _ [34,320,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19800

theorem m23987_129 : Upper (D 8) (R 8) [34,320,136,129] 13 :=
  permutation_upper _ _ _ [34,320,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19804

def r23987 : Route 9 := (fun mask => (mask,id))

def c23987 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23987 : Upper (D 8) (R 8) [34,320,136] 13 := by
  apply FastRouting.sound _ _ [34,320,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23987 c23987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23987_5
  · exact m23987_17
  · exact m23987_20
  · exact m23987_33
  · exact m23987_36
  · exact m23987_48
  · exact m23987_65
  · exact m23987_68
  · exact m23987_80
  · exact m23987_96
  · exact m23987_129
  · exact u19808
  · exact u19809
  · exact u19810
  · exact u19811

theorem m23988_5 : Upper (D 8) (R 8) [34,320,160,5] 13 :=
  permutation_upper _ _ _ [34,320,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19747

theorem m23988_17 : Upper (D 8) (R 8) [34,320,160,17] 13 :=
  permutation_upper _ _ _ [34,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19754

theorem m23988_20 : Upper (D 8) (R 8) [34,320,160,20] 13 :=
  permutation_upper _ _ _ [34,320,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19763

theorem m23988_33 : Upper (D 8) (R 8) [34,320,160,33] 13 :=
  permutation_upper _ _ _ [34,320,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19770

theorem m23988_36 : Upper (D 8) (R 8) [34,320,160,36] 13 :=
  permutation_upper _ _ _ [34,320,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19781

theorem m23988_48 : Upper (D 8) (R 8) [34,320,160,48] 13 :=
  permutation_upper _ _ _ [34,320,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19787

theorem m23988_65 : Upper (D 8) (R 8) [34,320,160,65] 13 :=
  permutation_upper _ _ _ [34,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19791

theorem m23988_68 : Upper (D 8) (R 8) [34,320,160,68] 13 :=
  permutation_upper _ _ _ [34,320,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19795

theorem m23988_80 : Upper (D 8) (R 8) [34,320,160,80] 13 :=
  permutation_upper _ _ _ [34,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19798

theorem m23988_96 : Upper (D 8) (R 8) [34,320,160,96] 13 :=
  permutation_upper _ _ _ [34,320,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19802

theorem m23988_129 : Upper (D 8) (R 8) [34,320,160,129] 13 :=
  permutation_upper _ _ _ [34,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19806

theorem m23988_132 : Upper (D 8) (R 8) [34,320,160,132] 13 :=
  permutation_upper _ _ _ [34,320,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19810

theorem m23988_144 : Upper (D 8) (R 8) [34,320,160,144] 13 :=
  permutation_upper _ _ _ [34,320,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19812

def r23988 : Route 9 := (fun mask => (mask,id))

def c23988 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23988 : Upper (D 8) (R 8) [34,320,160] 13 := by
  apply FastRouting.sound _ _ [34,320,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r23988 c23988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23988_5
  · exact m23988_17
  · exact m23988_20
  · exact m23988_33
  · exact m23988_36
  · exact m23988_48
  · exact m23988_65
  · exact m23988_68
  · exact m23988_80
  · exact m23988_96
  · exact m23988_129
  · exact m23988_132
  · exact m23988_144
  · exact u19814
  · exact u19815

theorem m23989_5 : Upper (D 8) (R 8) [34,320,192,5] 13 :=
  permutation_upper _ _ _ [34,320,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19748

theorem m23989_17 : Upper (D 8) (R 8) [34,320,192,17] 13 :=
  permutation_upper _ _ _ [34,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19755

theorem m23989_20 : Upper (D 8) (R 8) [34,320,192,20] 13 :=
  permutation_upper _ _ _ [34,320,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19764

theorem m23989_33 : Upper (D 8) (R 8) [34,320,192,33] 13 :=
  permutation_upper _ _ _ [34,320,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19771

theorem m23989_36 : Upper (D 8) (R 8) [34,320,192,36] 13 :=
  permutation_upper _ _ _ [34,320,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19782

theorem m23989_48 : Upper (D 8) (R 8) [34,320,192,48] 13 :=
  permutation_upper _ _ _ [34,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19788

theorem m23989_129 : Upper (D 8) (R 8) [34,320,192,129] 13 :=
  permutation_upper _ _ _ [34,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19807

theorem m23989_132 : Upper (D 8) (R 8) [34,320,192,132] 13 :=
  permutation_upper _ _ _ [34,320,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19811

theorem m23989_144 : Upper (D 8) (R 8) [34,320,192,144] 13 :=
  permutation_upper _ _ _ [34,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19813

theorem m23989_160 : Upper (D 8) (R 8) [34,320,192,160] 13 :=
  permutation_upper _ _ _ [34,320,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19815

def r23989 : Route 9 := (fun mask => (mask,id))

def c23989 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23989 : Upper (D 8) (R 8) [34,320,192] 13 := by
  apply FastRouting.sound _ _ [34,320,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r23989 c23989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23989_5
  · exact m23989_17
  · exact m23989_20
  · exact m23989_33
  · exact m23989_36
  · exact m23989_48
  · exact m23989_129
  · exact m23989_132
  · exact m23989_144
  · exact m23989_160

def b23990 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 67 7 13 504 496 496 496 496 496), lower := (rows 67 7 13 8 16 32 64 128 256), losses := [] }

theorem u23990 : Upper (D 8) (R 8) [66,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23991 : Route 9 := (fun mask => (mask,id))

def c23991 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u23991 : Upper (D 8) (R 8) [66,5,24] 13 := by
  apply FastRouting.sound _ _ [66,5,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r23991 c23991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19816
  · exact u19817
  · exact u19818
  · exact u19819
  · exact u19820
  · exact u19821
  · exact u19822
  · exact u19823
  · exact u19824
  · exact u19825

def b23992 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 67 7 37 504 504 504 504 504 504), lower := (rows 67 7 37 8 16 32 64 128 256), losses := [] }

theorem u23992 : Upper (D 8) (R 8) [66,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23993 : Route 9 := (fun mask => (mask,id))

def c23993 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23993 : Upper (D 8) (R 8) [66,5,40] 13 := by
  apply FastRouting.sound _ _ [66,5,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23993 c23993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19826
  · exact u19827
  · exact u19828
  · exact u19829
  · exact u19830
  · exact u19831
  · exact u19832
  · exact u19833
  · exact u19834
  · exact u19835
  · exact u19836
  · exact u19837
  · exact u19838
  · exact u19839
  · exact u19840

def b23994 : PairBound 9 := { available := 440, camps := [{ cop := 6, region := 7, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 69 440 440 440 504 440 440), lower := (rows 67 7 69 8 16 32 64 128 256), losses := [] }

theorem u23994 : Upper (D 8) (R 8) [66,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23995 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 76 441 433 433 497 433 433), lower := (rows 67 7 76 8 16 32 64 128 256), losses := [] }

theorem u23995 : Upper (D 8) (R 8) [66,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23996 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5)], upper := (rows 67 7 100 441 441 441 505 441 441), lower := (rows 67 7 100 8 16 32 64 128 256), losses := [] }

theorem u23996 : Upper (D 8) (R 8) [66,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23997 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 67 7 133 504 504 504 504 504 504), lower := (rows 67 7 133 8 16 32 64 128 256), losses := [] }

theorem u23997 : Upper (D 8) (R 8) [66,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23998 : Route 9 := (fun mask => (mask,id))

def c23998 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23998 : Upper (D 8) (R 8) [66,5,136] 13 := by
  apply FastRouting.sound _ _ [66,5,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23998 c23998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19841
  · exact u19842
  · exact u19843
  · exact u19844
  · exact u19845
  · exact u19846
  · exact u19847
  · exact u19848
  · exact u19849
  · exact u19850
  · exact u19851
  · exact u19852
  · exact u19853
  · exact u19854
  · exact u19855

def r23999 : Route 9 := (fun mask => (mask,id))

def c23999 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u23999 : Upper (D 8) (R 8) [66,5,160] 13 := by
  apply FastRouting.sound _ _ [66,5,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r23999 c23999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u19856
  · exact u19857
  · exact u19858
  · exact u19859
  · exact u19860
  · exact u19861
  · exact u19862
  · exact u19863
  · exact u19864
  · exact u19865
  · exact u19866
  · exact u19867
  · exact u19868
  · exact u19869
  · exact u19870

#print axioms u23999
end Delivery.IrregularNine14.P08
